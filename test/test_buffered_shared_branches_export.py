from copy import deepcopy
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / 'scripts/buffered_shared_branches_export.py'
spec = importlib.util.spec_from_file_location('parallel_export', MODULE)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def fixture(lengths=(3, 8, 2, 7, 1, 5)):
    cases = []
    for k, length in enumerate(lengths):
        cases.append(dict(name=f'case{k}', vectors=[dict(command=dict(command=0, address=k),
            raw_inputs=n % 4) for n in range(length)], checks=[]))
    return dict(schema=mod.INPUT_SCHEMA, cases=cases)


def exports(request, plans):
    return [dict(schema=mod.VECTOR_SCHEMA, cases=[dict(name=request['cases'][k]['name'],
        vectors=[dict(deepcopy(v), state={'scratch': k}) for v in request['cases'][k]['vectors']])
        for k in shard['indices']]) for shard in plans]


class MergeTests(unittest.TestCase):
    def test_partition_deterministic_balanced_bounded_exact_once(self):
        request = fixture()
        plans = mod.plan(request)
        self.assertEqual(plans, mod.plan(request))
        self.assertEqual(sorted(k for p in plans for k in p['indices']), list(range(6)))
        self.assertLessEqual(len(plans), 4)
        self.assertEqual([p['edges'] for p in plans], [8, 7, 6, 5])
        self.assertTrue(all(p['indices'] == sorted(p['indices']) for p in plans))

    def test_recombines_original_order_despite_noncontiguous_shards(self):
        request = fixture()
        plans = mod.plan(request)
        result = mod.merge(request, plans, exports(request, plans))
        self.assertEqual([c['name'] for c in result['cases']], [c['name'] for c in request['cases']])
        self.assertEqual(json.dumps(result, indent=2), json.dumps(mod.merge(request, plans,
            exports(request, plans)), indent=2))

    def test_missing_duplicate_reordered_foreign_cases_reject(self):
        request = fixture((1, 1, 1, 1))
        plans = mod.plan(request, 1)
        for mutation in (lambda x: x[0]['cases'].pop(),
                         lambda x: x[0]['cases'].append(deepcopy(x[0]['cases'][0])),
                         lambda x: x[0]['cases'].reverse(),
                         lambda x: x[0]['cases'][0].update(name='foreign')):
            result = exports(request, plans)
            mutation(result)
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeError):
                mod.merge(request, plans, result)

    def test_wrong_schema_transcript_types_truncated_edges_and_missing_state_reject(self):
        request = fixture((2,))
        plans = mod.plan(request)
        mutations = [lambda x: x[0].update(schema='wrong'),
            lambda x: x[0]['cases'][0]['vectors'].pop(),
            lambda x: x[0]['cases'][0]['vectors'][0]['command'].update(command=True),
            lambda x: x[0]['cases'][0]['vectors'][0].update(raw_inputs=False),
            lambda x: x[0]['cases'][0]['vectors'][0].update(raw_inputs=3),
            lambda x: x[0]['cases'][0]['vectors'][0].pop('state')]
        for mutate in mutations:
            result = exports(request, plans)
            mutate(result)
            with self.subTest(mutation=mutate), self.assertRaises(RuntimeError):
                mod.merge(request, plans, result)

    def test_bad_plan_and_missing_shard_reject(self):
        request = fixture()
        plans = mod.plan(request)
        data = exports(request, plans)
        with self.assertRaises(RuntimeError): mod.merge(request, plans, data[:-1])
        for indices in ([0, 0], [0], [True]):
            invalid = deepcopy(plans)
            invalid[0]['indices'] = indices
            with self.assertRaises(RuntimeError): mod.merge(request, invalid, data)

    def test_jobs_and_duplicate_request_fail_closed(self):
        for jobs in (0, 5, True, 1.5):
            with self.assertRaises(RuntimeError): mod.plan(fixture(), jobs)
        request = fixture(); request['cases'][1]['name'] = request['cases'][0]['name']
        with self.assertRaises(RuntimeError): mod.plan(request)

    def test_each_artifact_anchored_to_native_parity_not_other_shard(self):
        with tempfile.TemporaryDirectory() as temp:
            dirs = [Path(temp) / f'd{k}' for k in range(3)]
            for d in dirs:
                d.mkdir()
                for name in mod.ARTIFACTS: (d / name).write_bytes(b'anchor')
            mod.validate_artifacts(dirs[1:], dirs[0])
            for name in mod.ARTIFACTS:
                for d in dirs[1:]: (d / name).write_bytes(b'same-but-wrong')
                with self.subTest(name=name), self.assertRaises(RuntimeError):
                    mod.validate_artifacts(dirs[1:], dirs[0])
                for d in dirs[1:]: (d / name).write_bytes(b'anchor')


FAKE = '''#!/usr/bin/env python3
import json, os, pathlib, signal, sys, time
request=json.loads(pathlib.Path(sys.argv[1]).read_text())
out=pathlib.Path(sys.argv[2])
name=request['cases'][0]['name'] if request['cases'] else ''
mode=pathlib.Path(__file__).with_suffix('.mode').read_text()
print('started '+name+' group='+str(os.getpgrp()), flush=True)
if mode=='fail' and name=='case0': raise SystemExit(9)
if mode in ('fail','timeout','cancel'):
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    time.sleep(60)
if mode=='reordered': request['cases'].reverse()
for artifact in ('core.mlir','assembly.json'):
    (out/artifact).write_bytes(b'bad' if mode=='artifact' else b'anchor')
cases=[dict(name=c['name'], vectors=[dict(v,state={'scratch':0}) for v in c['vectors']])
       for c in request['cases']]
(out/'vectors.json').write_text(json.dumps(dict(schema='pinwheel-buffered-shared-branches-vectors-v1',cases=cases)))
'''


def accept(request, _actual):
    # An explicit stand-in for process/merge tests; CLI uses the actual gate.
    return dict(cases=len(request['cases']))


def checked_supervise(*args, validator=accept, **kwargs):
    return mod.supervise(*args, validator=validator, **kwargs)


class SupervisorTests(unittest.TestCase):
    def setup_fixture(self, temp, mode='pass'):
        root = Path(temp)
        request = fixture((1, 1, 1, 1))
        source = root / 'input.json'; source.write_text(json.dumps(request))
        reference = root / 'native'; reference.mkdir()
        for name in mod.ARTIFACTS: (reference / name).write_bytes(b'anchor')
        exe = root / 'fake.py'; exe.write_text(FAKE); exe.chmod(0o755)
        exe.with_suffix('.mode').write_text(mode)
        return root, source, reference, exe

    def test_success_records_every_child_group_artifact_and_order(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp)
            report = checked_supervise(exe, source, root, reference, timeout=5)
            self.assertEqual((report['status'], report['jobs'], report['cases']), ('passed', 4, 4))
            self.assertTrue(all(r['direct_child_reaped'] and r['exit_code'] == 0 for r in report['commands']))
            self.assertTrue(all('group='+str(os.getpgrp()) in Path(r['log']).read_text() for r in report['commands']))
            result = json.loads((root / 'vectors.json').read_text())
            self.assertEqual([c['name'] for c in result['cases']], [f'case{k}' for k in range(4)])
            for name in mod.ARTIFACTS: self.assertEqual((root / name).read_bytes(), b'anchor')

    def test_callable_validator_is_mandatory(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp)
            for invalid in (None, False, 1, 'checker'):
                with self.subTest(invalid=invalid), self.assertRaisesRegex(RuntimeError, 'callable'):
                    mod.supervise(exe, source, root, reference, validator=invalid)
            self.assertFalse((root / 'export-shards').exists())

    def test_checker_cli_is_required_exact_and_rejects_incomplete_public_state(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp)
            command = [sys.executable, '-B', MODULE, exe, source, root, reference]
            missing = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(missing.returncode, 0)
            self.assertFalse((root / 'export-shards').exists())
            wrong = subprocess.run(command + ['--checker', exe], capture_output=True, text=True)
            self.assertNotEqual(wrong.returncode, 0)
            self.assertFalse((root / 'export-shards').exists())
            checked = subprocess.run(command + ['--checker', mod.CHECKER_PATH],
                                     capture_output=True, text=True)
            self.assertNotEqual(checked.returncode, 0)
            report = json.loads((root / 'export-shards/report.json').read_text())
            self.assertEqual(report['status'], 'failed')
            self.assertFalse((root / 'vectors.json').exists())

    def test_validator_triggered_sigterm_prevents_publication(self):
        for phase in ('shard', 'full'):
            with self.subTest(phase=phase), tempfile.TemporaryDirectory() as temp:
                root, source, reference, exe = self.setup_fixture(temp)
                def cancelled(request, _actual):
                    if phase == 'shard' or len(request['cases']) == 4:
                        os.kill(os.getpid(), signal.SIGTERM)
                    return dict(cases=len(request['cases']))
                with self.assertRaisesRegex(RuntimeError, 'cancelled'):
                    checked_supervise(exe, source, root, reference, timeout=5, validator=cancelled)
                report = json.loads((root / 'export-shards/report.json').read_text())
                self.assertEqual(report['status'], 'cancelled')
                self.assertTrue(all(r['direct_child_reaped'] for r in report['commands']))
                for name in (*mod.ARTIFACTS, 'vectors.json'):
                    self.assertFalse((root / name).exists())

    def test_existing_validator_checks_each_subset_and_full_original_order(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp)
            seen = []
            def validate(request, actual):
                names = [c['name'] for c in request['cases']]
                self.assertEqual(names, [c['name'] for c in actual['cases']])
                seen.append(names)
                return dict(cases=len(names))
            report = checked_supervise(exe, source, root, reference, timeout=5, validator=validate)
            self.assertEqual(len(seen), 5)
            self.assertEqual(seen[-1], [f'case{k}' for k in range(4)])
            self.assertEqual(report['full_check']['cases'], 4)
            self.assertEqual(len(report['shard_checks']), 4)

    def test_validator_failure_publishes_no_artifacts(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp)
            def reject(_request, _actual):
                raise RuntimeError('independent checker rejection')
            with self.assertRaisesRegex(RuntimeError, 'independent checker'):
                checked_supervise(exe, source, root, reference, timeout=5, validator=reject)
            for name in (*mod.ARTIFACTS, 'vectors.json'):
                self.assertFalse((root / name).exists())

    def test_child_failure_stops_and_reaps_others_without_publishing(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp, 'fail')
            with self.assertRaises(RuntimeError): checked_supervise(exe, source, root, reference, timeout=5, grace=.1)
            report = json.loads((root / 'export-shards/report.json').read_text())
            self.assertEqual(report['status'], 'failed')
            self.assertTrue(all(r['direct_child_reaped'] for r in report['commands']))
            self.assertTrue(any(r['exit_code'] == 9 for r in report['commands']))
            self.assertFalse((root / 'vectors.json').exists())

    def test_spawn_failure_reaps_already_started_children(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp, 'timeout')
            launch = mod.subprocess.Popen
            calls = 0
            def fail_second(*args, **kwargs):
                nonlocal calls
                calls += 1
                if calls == 2: raise OSError('injected spawn failure')
                return launch(*args, **kwargs)
            with patch.object(mod.subprocess, 'Popen', fail_second), self.assertRaises(OSError):
                checked_supervise(exe, source, root, reference, timeout=5, grace=.1)
            report = json.loads((root / 'export-shards/report.json').read_text())
            self.assertTrue(report['commands'][0]['direct_child_reaped'])
            self.assertEqual(report['commands'][1]['error'], 'OSError')
            self.assertFalse((root / 'vectors.json').exists())

    def test_timeout_kills_term_resistant_children_and_retains_logs(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp, 'timeout')
            with self.assertRaises(subprocess.TimeoutExpired):
                checked_supervise(exe, source, root, reference, timeout=.2, grace=.1)
            report = json.loads((root / 'export-shards/report.json').read_text())
            self.assertEqual(report['error'], 'TimeoutExpired')
            self.assertTrue(all(r['direct_child_reaped'] for r in report['commands']))
            self.assertTrue(any('started' in Path(r['log']).read_text() for r in report['commands']))
            self.assertFalse((root / 'vectors.json').exists())

    def test_signal_cancellation_reports_and_reaps_all_children(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp, 'cancel')
            timer = threading.Timer(.2, lambda: os.kill(os.getpid(), signal.SIGTERM))
            timer.start()
            try:
                with self.assertRaises(RuntimeError):
                    checked_supervise(exe, source, root, reference, timeout=5, grace=.1)
            finally:
                timer.cancel(); timer.join()
            report = json.loads((root / 'export-shards/report.json').read_text())
            self.assertEqual(report['status'], 'cancelled')
            self.assertTrue(all(r['direct_child_reaped'] for r in report['commands']))
            self.assertFalse((root / 'vectors.json').exists())

    def test_artifact_or_case_validation_failure_publishes_nothing(self):
        for mode in ('artifact', 'reordered'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temp:
                root, source, reference, exe = self.setup_fixture(temp, mode)
                with self.assertRaises(RuntimeError):
                    checked_supervise(exe, source, root, reference, jobs=1, timeout=5)
                self.assertFalse((root / 'vectors.json').exists())
                self.assertFalse((root / 'core.mlir').exists())
                self.assertFalse((root / 'assembly.json').exists())

    def test_existing_command_group_timeout_stops_supervisor_and_all_exporters(self):
        sys.path.insert(0, str(ROOT / 'scripts'))
        from validation_run import Commands
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp, 'timeout')
            run = Commands(ROOT, root)
            with self.assertRaises(subprocess.TimeoutExpired) as failure:
                run([sys.executable, '-B', MODULE, exe, source, root, reference,
                     '--timeout', '5', '--checker', mod.CHECKER_PATH], 'batch', timeout=.3)
            self.assertTrue(failure.exception.process_group_stopped)
            self.assertEqual(run.records[0]['error'], 'TimeoutExpired')
            self.assertIn('process group', (root / 'batch.log').read_text())
            report = json.loads((root / 'export-shards/report.json').read_text())
            self.assertEqual(report['status'], 'cancelled')
            self.assertTrue(all(r['direct_child_reaped'] for r in report['commands']))
            self.assertFalse((root / 'vectors.json').exists())

    def test_existing_output_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as temp:
            root, source, reference, exe = self.setup_fixture(temp)
            (root / 'vectors.json').write_text('preserved')
            with self.assertRaises(RuntimeError): checked_supervise(exe, source, root, reference)
            self.assertEqual((root / 'vectors.json').read_text(), 'preserved')


if __name__ == '__main__':
    unittest.main()
