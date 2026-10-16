"""Host-only correlation/gate/generation tests. No compiler/CAD subprocesses."""
import ast
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
from types import SimpleNamespace

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
from analyze import analyze_events, read_events, reconcile_native_log
import launch
import native_build


def events(mode='threads'):
    rows = [{'event': 'installed'}]
    # Last GLOBAL header belongs to4; failing error belongs to3. Order matters.
    for tid in [1, 2, 3, 4]:
        rows.append({'event': 'worker', 'thread_id': tid, 'iteration': 4,
                     'route_box_um': [20, 0, 21, 1] if tid == 3 else [tid, 0, tid + 1, 1]})
    if mode != 'control':
        r = {'event': 'DRT1231', 'thread_id': 3, 'iteration': 4, 'correlated': True,
             'target_matches': True, 'fixture': mode == 'threads'}
        if mode == 'probe':
            rows[3]['route_box_um'] = [597.6, 93.6, 648, 144]
            r['fresh_aps'] = {'source': 'fresh_global_frDesign_inside_original_error_log_call',
                'instance': 'engine.memory.storage1', 'terminal': 'A_BM[31]',
                'dbu_per_micron': 1000, 'route_box_dbu': [597600, 93600, 648000, 144000],
                'pins': [{'aps': [{'global_dbu': [611760, 144130], 'inside_route_box': False}]}],
                'generated_ap_count': 1, 'eligible_ap_count': 0, 'selected_truncated_endpoints_captured': False}
        rows.append(r)
    rows.append({'event': 'removed', 'io_ok': True})
    for row in rows:
        if "thread_id" in row:
            row.update(kernel_thread_id=row["thread_id"], raw_msg_thread_id=7, cfg_max_threads=4)
    return rows


class ObserverTest(unittest.TestCase):
    def test_simple_build_uses_absolute_staging_inclusive_cap_and_owned_runner(self):
        p = launch.ROOT / 'tools/pinwheel-physical-campaign/runner.py'
        spec = importlib.util.spec_from_file_location('observer_test_runner', p)
        runner = importlib.util.module_from_spec(spec); sys.modules[spec.name] = runner; spec.loader.exec_module(runner)
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); (root / 'runs').mkdir(); bundle = root / 'bundle'; bundle.mkdir()
            for name in ['observer.cc', 'native_build.py']: (bundle / name).write_text('frozen input')
            observed = []
            def fake(spec):
                observed.append(spec)
                return {'status': 'failed', 'exit_code': 1}
            fake_runner = SimpleNamespace(JobSpec=runner.JobSpec, run_owned_job=fake)
            args = SimpleNamespace(mode='build', name='new-build')
            with mock.patch.object(launch, 'CAMPAIGN', root), mock.patch.object(launch, 'inputs', return_value={'source': 'hash'}), mock.patch.object(launch.time, 'time', return_value=1000):
                self.assertEqual(launch.simple_job(args, bundle, {}, {'image_id': 'sha256:'+'a'*64, 'hard_stop_epoch': 5000}, fake_runner), 1)
            job = observed[0]
            self.assertEqual(job.hard_end_epoch, 1360)
            self.assertEqual((job.native_seconds, job.max_job_seconds, job.closeout_reserve_seconds), (300, 360, 45))
            self.assertEqual((job.cpus, job.memory, job.heavy_lock_path), (4, '6g', root / 'heavy.lock'))

    def test_receipt_checks_artifacts_and_requires_owned_cleanup(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); source = root / 'source'; source.write_text('source')
            artifact = root / 'output'; artifact.write_text('output')
            p = root / 'report.json'
            report = {'status': 'passed', 'inputs_unchanged': True, 'container_termination': {'status': 'absent'},
                'within_absolute_and_job_deadlines': True, 'input_sha256': {str(source): launch.sha(source)},
                'artifact_sha256': {'output': launch.sha(artifact)}}
            p.write_text(json.dumps(report)); launch.receipt(p)
            artifact.write_text('tampered')
            with self.assertRaises(AssertionError): launch.receipt(p)
            artifact.write_text('output'); report['container_termination']['status'] = 'unconfirmed'; p.write_text(json.dumps(report))
            with self.assertRaises(AssertionError): launch.receipt(p)

    def test_interleaved_four_thread_header_correlates_by_tid(self):
        self.assertEqual(analyze_events(events(), 'threads')['distinct_worker_thread_ids'], [1, 2, 3, 4])

    def test_missing_or_zero_thread_id_rejected(self):
        for value in [0, -1]:
            rows = events(); rows[1]['thread_id'] = value
            with self.assertRaises(AssertionError): analyze_events(rows, 'threads')

    def test_all_headers_on_one_thread_not_four_thread_proof(self):
        rows = events()
        for row in rows:
            if 'thread_id' in row: row['thread_id'] = 3
        with self.assertRaises(AssertionError): analyze_events(rows, 'threads')

    def test_stale_header_or_unmatched_error_rejected(self):
        for k, value in [('thread_id', 9), ('iteration', 3), ('correlated', False), ('target_matches', False)]:
            rows = events(); rows[-2][k] = value
            with self.assertRaises(AssertionError): analyze_events(rows, 'threads')

    def test_multiple_error_or_callback_failure_rejected(self):
        rows = events(); rows.insert(-1, copy.deepcopy(rows[-2]))
        with self.assertRaises(AssertionError): analyze_events(rows, 'threads')
        rows = events(); rows[-2]['capture_error'] = 'missing APs'
        with self.assertRaises(AssertionError): analyze_events(rows, 'threads')

    def test_successful_control_has_no_failure_and_four_ids(self):
        self.assertEqual(analyze_events(events('control'), 'control')['DRT1231_count'], 0)
        with self.assertRaises(AssertionError): analyze_events(events(), 'control')

    def test_fresh_global_AP_ledger_zero_eligible_is_valid(self):
        result = analyze_events(events('probe'), 'probe')
        self.assertEqual(result['fresh_AP_ledger']['eligible_ap_count'], 0)
        self.assertFalse(result['selected_truncated_endpoints_captured'])

    def test_vacuous_or_stale_AP_ledger_rejected(self):
        rows = events('probe'); rows[-2]['fresh_aps']['source'] = 'saved_ODB'
        with self.assertRaises(AssertionError): analyze_events(rows, 'probe')
        rows = events('probe'); rows[-2]['fresh_aps']['pins'][0]['aps'] = []
        with self.assertRaises(AssertionError): analyze_events(rows, 'probe')

    def test_inside_boundary_AP_cannot_be_explained_as_empty_clip(self):
        rows = events('probe'); rows[-2]['fresh_aps']['pins'][0]['aps'][0]['global_dbu'][1] = 144000
        with self.assertRaises(AssertionError): analyze_events(rows, 'probe')

    def test_ap_predicate_and_box_roundtrip_must_match(self):
        rows = events('probe'); rows[-2]['fresh_aps']['route_box_dbu'][0] += 1
        with self.assertRaises(AssertionError): analyze_events(rows, 'probe')

    def test_truncated_or_failed_sink_output_is_not_complete(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'events.jsonl'
            for rows in [events()[:-1], [*events()[:-1], {'event': 'removed', 'io_ok': False}], [*events()[:-1], {'event': 'observer_error'}, events()[-1]]]:
                p.write_text(''.join(json.dumps(r) + '\n' for r in rows))
                with self.assertRaises(AssertionError): read_events(p)

    def test_native_program_only_loads_separate_sink_and_verbose(self):
        p = launch.ROOT / 'tools/pinwheel-physical-campaign/stage.py'
        spec = importlib.util.spec_from_file_location('observer_test_stage', p)
        sys.path.insert(0, str(p.parent)); stage = importlib.util.module_from_spec(spec); spec.loader.exec_module(stage)
        for iteration, control in [(0, True), (4, False)]:
            source = launch.observer_native(stage.native_program, iteration, control)
            ast.parse(source)
            self.assertIn(f'detailed_route -droute_end_iter {iteration} -verbose 2 ', source)
            self.assertEqual(source.count('pinwheel_logger_observer_install'), 1)
            self.assertEqual(source.count('pinwheel_logger_observer_remove'), 1)
            self.assertIn("error=tcl(cmd,allow_error=True)\ntcl('pinwheel_logger_observer_remove')", source)
            self.assertNotIn('detailed_route_debug', source)
            self.assertIn('mode=os.RTLD_NOW|os.RTLD_GLOBAL', source)
            self.assertIn("if error is not None:raise RuntimeError", source)

    def test_compiler_only_compiles_sink_not_DRT_or_preservation_implementation(self):
        ref = json.loads((launch.HEADERS / 'native-05/build.json').read_text())
        cmd = native_build.command(ref, Path('/work/diagnostic'))
        self.assertEqual([v for v in cmd if v.endswith(('.cc', '.cpp'))], ['/work/diagnostic/observer.cc'])
        self.assertIn('-fvisibility=hidden', cmd)
        self.assertTrue(any('/headers/source/src/drt/src' in v for v in cmd))

    def test_callback_does_not_invoke_logger_or_mutators(self):
        source = (TOOLS / 'observer.cc').read_text()
        callback = source[source.index('  std::string freshAPs('):source.index('std::shared_ptr<Sink> installed;')]
        for forbidden in ['logger->', 'logger_->', 'updateDb(', 'setAccessPoint(', 'setPinAccess(', 'setCost(', 'route_queue(', 'getRouteConnFigs(']:
            self.assertNotIn(forbidden, callback)


class KernelIdentityTest(unittest.TestCase):
    def test_constant_native_raw_id_does_not_collapse_kernel_identity(self):
        self.assertEqual(analyze_events(events(), 'threads')['distinct_worker_thread_ids'], [1,2,3,4])
    def test_missing_kernel_identity_fails(self):
        rows=events(); del rows[1]['kernel_thread_id']
        with self.assertRaises(KeyError): analyze_events(rows,'threads')
    def test_one_kernel_id_is_not_four_thread_control(self):
        rows=events('control')
        for r in rows:
            if 'thread_id' in r: r['thread_id']=r['kernel_thread_id']=7
        with self.assertRaises(AssertionError): analyze_events(rows,'control')
    def test_native_header_ledger_is_nonvacuous_and_exact(self):
        rows=[{'event':'worker','payload':'start DR worker (BOX) ( 0 0 ) ( 1 1 )\n'}]
        log='start DR worker (BOX) ( 0 0 ) ( 1 1 )\n'
        self.assertTrue(reconcile_native_log(rows,log)['all_native_worker_headers_reconciled'])
        for bad in ['',log+log]:
            with self.assertRaises(AssertionError): reconcile_native_log(rows,bad)
    def test_kernel_syscall_and_callback_only_identity(self):
        source=(TOOLS/'observer.cc').read_text()
        self.assertIn('::syscall(SYS_gettid)',source)
        self.assertIn('headers_[kernel]',source)
        self.assertIn('headers_.find(kernel)',source)
        self.assertNotIn('headers_[msg.thread_id]',source)

if __name__ == '__main__': unittest.main()
