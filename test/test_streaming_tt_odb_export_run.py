import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_physical as P
spec = importlib.util.spec_from_file_location('odb_export_runner', P.ROOT/'scripts/run-streaming-tt-odb-export.py')
runner = importlib.util.module_from_spec(spec); spec.loader.exec_module(runner)


class ClosedODBSelection(unittest.TestCase):
    def run_fixture(self, root, *, memory=2048, mutation=None):
        root = root.resolve()
        report, state, database, _ = self.fixture(root/'physical')
        source = root/'scripts/streaming_tt_export_odb.py'; source.parent.mkdir()
        source.write_text('# Host fixture only; never executed\n')
        tools = root/'tools/physical-toolchain.json'; tools.parent.mkdir(); tools.write_text('{}')
        reference = root/'reference.json'; reference.write_text('{"modules":{}}')
        runtime = dict(image_id='sha256:'+'b'*64)
        launches = []
        def execute(argv, **options):
            if argv[:2] != ['docker', 'run']:
                self.assertEqual(argv[:3], ['docker', 'container', 'ls'])
                return SimpleNamespace(returncode=0, stdout='', stderr='')
            launches.append(argv)
            options['stdout'].write('mocked native export log\n')
            if mutation == 'timeout':
                raise runner.subprocess.TimeoutExpired(argv, options['timeout'])
            export = root/'build/streaming-physical-development/dispatch/native/export'; export.mkdir()
            for name in ('connectivity.json', 'inventory.json'): (export/name).write_text('{}\n')
            native = dict(schema='pinwheel.streaming-tt-odb-export.v1', database_sha256=P.sha(database),
                reference_sha256=P.sha(reference), source_sha256=P.sha(source), top='top', read_only_database=True,
                artifacts_sha256={name:P.sha(export/name) for name in ('connectivity.json', 'inventory.json')})
            if mutation == 'wrong-native-database': native['database_sha256'] = 'c'*64
            (export/'receipt.json').write_text(json.dumps(native))
            return SimpleNamespace(returncode=0)
        arguments = ['export', '--physical-report', str(report), '--state', str(state),
            '--reference', str(reference), '--top', 'top', '--tag', 'dispatch', '--memory-mb', str(memory)]
        with patch.object(P,'ROOT',root), patch.object(P,'committed'), \
                patch.object(P,'inspect_runtime',return_value=runtime), \
                patch.object(runner,'dependency_closure',return_value={'files':['scripts/streaming_tt_export_odb.py']}), \
                patch.object(runner,'check_environment'), patch.object(sys,'argv',arguments), \
                patch.object(runner.subprocess,'run',side_effect=execute), \
                patch.object(runner.subprocess,'check_output',return_value='a'*40+'\n'):
            code = runner.main()
        out = root/'build/streaming-physical-development/dispatch'
        return code, P.read(out/'report.json'), launches, out, database, reference

    def test_owned_dispatch_bounds_and_export_binding_remain_exact(self):
        for memory in (256, 2048):
            with self.subTest(memory=memory), tempfile.TemporaryDirectory() as directory:
                code, receipt, launches, out, database, reference = self.run_fixture(Path(directory),memory=memory)
                self.assertEqual(code, 0); self.assertTrue(receipt['passed']); self.assertEqual(len(launches), 1)
                argv = launches[0]; self.assertEqual(receipt['command'], argv)
                for flag, value in [('--name','pinwheel-odb-dispatch'), ('--memory',str(memory)+'m'),
                        ('--memory-swap',str(memory)+'m'), ('--cpus','1'), ('--network','none')]:
                    self.assertEqual(argv.count(flag), 1); self.assertEqual(argv[argv.index(flag)+1], value)
                self.assertEqual(argv[-6:], ['sha256:'+'b'*64, 'openroad', '-no_init', '-exit', '-python', '/inputs/launch.py'])
                self.assertEqual(receipt['memory'], receipt['memory_swap']); self.assertEqual(receipt['network'],'none')
                self.assertIn('--read-only',argv); self.assertEqual(argv[argv.index('--cap-drop')+1],'ALL')
                self.assertEqual(receipt['actual_odb_sha256'],P.sha(database)); self.assertEqual(receipt['reference'],str(reference))
                self.assertEqual(receipt['native_log_sha256'],P.sha(out/'native.log'))
                self.assertTrue(receipt['native_export_binding']); self.assertTrue(receipt['inputs_unchanged'])
                self.assertTrue(receipt['staged_inputs_unchanged']); self.assertTrue(receipt['runtime_unchanged'])
                self.assertEqual(receipt['container_termination']['status'],'absent')
                self.assertEqual(receipt['native_exporter_argv'], ['/inputs/export.py','--database','/inputs/actual.odb',
                    '--reference','/inputs/reference.json','--top','top','--out','/outputs/export'])

    def test_wrong_native_database_binding_still_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            code, receipt, _, _, _, _ = self.run_fixture(Path(directory),mutation='wrong-native-database')
            self.assertEqual(code,1); self.assertFalse(receipt['passed']); self.assertFalse(receipt['native_export_binding'])
            self.assertEqual(receipt['container_termination']['status'],'absent')

    def test_native_timeout_still_closes_owned_container_and_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            code, receipt, _, _, _, _ = self.run_fixture(Path(directory),mutation='timeout')
            self.assertEqual(code,1); self.assertFalse(receipt['passed']); self.assertEqual(receipt['status'],'timed_out')
            self.assertEqual(receipt['exit_code'],124); self.assertTrue(receipt['inputs_unchanged'])
            self.assertEqual(receipt['container_termination']['status'],'absent')

    def test_out_of_budget_memory_refuses_before_reading_or_creating_outputs(self):
        for value in (0, 255, 2049):
            arguments=['export','--physical-report','missing-report','--state','missing-state',
                '--reference','missing-reference','--top','top','--tag','new','--memory-mb',str(value)]
            with self.subTest(memory=value),patch.object(sys,'argv',arguments),\
                    patch.object(runner,'check_environment'),patch.object(runner,'select') as select:
                with self.assertRaisesRegex(ValueError,'Readback memory'):
                    runner.main()
                select.assert_not_called()

    def test_environment_overrides_fail_before_native_or_output(self):
        runner.check_environment({'PATH': '/usr/bin'})
        for name in ('PYTHONPATH', 'PYTHONHOME', 'PYTHONPYCACHEPREFIX', 'DYLD_INSERT_LIBRARIES',
                'LD_PRELOAD', 'OPENROAD_BIN', 'KLAYOUT_PATH', 'YOSYS_DATDIR', 'VPI_MODULE_PATH'):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'overrides'):
                runner.check_environment({name: '/injected'})

    def test_host_source_closure_includes_dynamic_cleanup(self):
        closure = runner.dependency_closure(P.ROOT, ['scripts/run-streaming-tt-odb-export.py'])
        self.assertIn('scripts/run-streaming-tt-physical.py', closure['files'])
        self.assertIn('scripts/streaming_tt_candidate.py', closure['files'])
        self.assertIn('scripts/streaming_tt_intake.py', closure['files'])

    def fixture(self, root):
        state = root/'flow/35-openroad-stamidpnr-3/state_out.json'; state.parent.mkdir(parents=True)
        odb = state.parent/'actual.odb'; odb.write_bytes(b'actual implemented graph')
        state.write_text(json.dumps(dict(odb='/work/run/35-openroad-stamidpnr-3/actual.odb')))
        report = dict(schema='pinwheel.streaming-tt-physical-run.v2', status='flow_completed', exit_code=0,
            inputs_unchanged_after_run=True, container_termination=dict(status='absent'),
            artifact_sha256={str(path.relative_to(root)): P.sha(path) for path in (state, odb)},
            states=[dict(state=str(state), state_sha256=P.sha(state), views=dict(odb=dict(path=str(odb),
                sha256=P.sha(odb), container='/work/run/35-openroad-stamidpnr-3/actual.odb')))])
        report_path = root/'report.json'; report_path.write_text(json.dumps(report))
        return report_path, state, odb, report

    def test_selects_actual_closed_odb(self):
        with tempfile.TemporaryDirectory() as directory:
            p, state, odb, _ = self.fixture(Path(directory))
            self.assertEqual(runner.select(p, state)[1], odb.resolve())

    def test_rejects_changed_actual_odb(self):
        with tempfile.TemporaryDirectory() as directory:
            p, state, odb, _ = self.fixture(Path(directory)); odb.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'authoritative'): runner.select(p, state)

    def test_rejects_unclosed_run(self):
        for status in ('running', 'interrupted', 'cleanup_unconfirmed', 'invalidated'):
            with self.subTest(status=status), tempfile.TemporaryDirectory() as directory:
                p, state, _, report = self.fixture(Path(directory)); report['status'] = status
                p.write_text(json.dumps(report))
                with self.assertRaisesRegex(ValueError, 'not closed'): runner.select(p, state)

    def test_closed_failed_producer_can_supply_diagnostic_actual_state(self):
        with tempfile.TemporaryDirectory() as directory:
            p, state, odb, report = self.fixture(Path(directory)); report.update(status='failed', exit_code=2)
            p.write_text(json.dumps(report))
            selected, actual = runner.select(p, state)
            self.assertEqual(actual, odb.resolve())
            self.assertEqual(selected['status'], 'failed')
            self.assertEqual(selected['exit_code'], 2)

    def test_failed_producer_without_actual_nonzero_exit_is_refused(self):
        for value in (0, None, True):
            with self.subTest(exit_code=value), tempfile.TemporaryDirectory() as directory:
                p, state, _, report = self.fixture(Path(directory)); report.update(status='failed', exit_code=value)
                p.write_text(json.dumps(report))
                with self.assertRaisesRegex(ValueError, 'not closed'): runner.select(p, state)


if __name__ == '__main__': unittest.main()
