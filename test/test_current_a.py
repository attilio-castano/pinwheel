"""Current-A wrapper refusals at the subprocess/report boundary.

The commands are stubbed: these controls are not new Lean or physical evidence.
"""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))


class CurrentATests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.bundle = self.root / 'bundle'
        (self.bundle / 'root').mkdir(parents=True)
        (self.bundle / 'inventory.json').write_text('{}')
        (self.bundle / 'root/lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        (self.root / 'scripts').mkdir()
        for name in ('check-current-a.py', 'retained_evidence.py', 'validation_run.py', 'process_group.py'):
            (self.root / 'scripts' / name).write_bytes((ROOT / 'scripts' / name).read_bytes())
        (self.root / 'tools').mkdir()
        for name in ('lake', 'lean'):
            (self.root / 'tools' / name).write_text('stub runtime ' + name)
        spec = importlib.util.spec_from_file_location('current_a_cli', ROOT / 'scripts/check-current-a.py')
        self.cli = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.cli)
        self.cli.ROOT = self.root
        self.cli.__file__ = str(self.root / 'scripts/check-current-a.py')

    def tearDown(self):
        self.temporary.cleanup()

    def run_replay(self, *, worker_exit=2, blockers=None, certificates=8, corrupt_wrapper=False):
        cli, fixture = self.cli, self

        class StubCommands:
            def __init__(self, root, out, records, default_timeout):
                self.records = records

            def __call__(self, command, label, reject=None):
                code = worker_exit if label == 'current-v2-assessment' else 0
                self.records.append(dict(label=label, exit_code=code, expected_failure=bool(reject)))
                if label == 'lean-version':
                    return 'Lean (version 4.33.1, test runtime)'
                if label == 'current-v2-assessment':
                    folder = fixture.bundle / 'root/build/validation' / command[-1]
                    folder.mkdir(parents=True)
                    assessment = dict(status='assessed', policy=cli.POLICY, A_accepted=False,
                                      blockers=blockers if blockers is not None else
                                      ['sram_qualification', 'timing_conditions', 'package_power'],
                                      certificates=[dict(kernel_rechecked=True)] * certificates)
                    (folder / 'report.json').write_text(json.dumps(assessment))
                    (folder / 'report.md').write_text('stub assessment')
                    if corrupt_wrapper:
                        (fixture.root / 'scripts/retained_evidence.py').write_text('late edit')
                    return '{"status": "assessed"}'
                return 'stub build'

        with patch.object(cli, 'load_bundle', return_value=dict(original_root=str(self.root / 'original'))), \
             patch.object(cli, 'compare_current_design', return_value=dict(status='identical')), \
             patch.object(cli, 'Commands', StubCommands), \
             patch.object(cli.shutil, 'which', side_effect=lambda name: str(self.root / 'tools' / name)), \
             contextlib.redirect_stdout(io.StringIO()):
            code = cli.replay(self.bundle, 'control')
        return code, json.loads((self.root / 'build/validation/control/report.json').read_text())

    def test_complete_assessed_but_blocked_result_returns_two(self):
        code, report = self.run_replay()
        self.assertEqual(code, 2)
        self.assertEqual(report['status'], 'assessed')
        self.assertFalse(report['A_accepted'])
        self.assertFalse(report['physical_evidence']['replayed_now'])
        self.assertEqual(report['fresh_kernel_certificates'], 8)

    def test_worker_exit_one_cannot_promote_a_completed_looking_report(self):
        code, report = self.run_replay(worker_exit=1)
        self.assertEqual(code, 1)
        self.assertEqual(report['status'], 'invalid_evidence')
        self.assertIn('exactly the blocked exit code 2', report['error'])

    def test_wrong_blockers_and_incomplete_certificates_refuse(self):
        code, report = self.run_replay(blockers=['package_power'])
        self.assertEqual(code, 1)
        self.assertIn('exactly three physical blockers', report['error'])

    def test_missing_fresh_certificate_checks_refuse(self):
        code, report = self.run_replay(certificates=7)
        self.assertEqual(code, 1)
        self.assertIn('Missing fresh kernel certificate', report['error'])

    def test_late_wrapper_source_edit_refuses(self):
        code, report = self.run_replay(corrupt_wrapper=True)
        self.assertEqual(code, 1)
        self.assertIn('wrapper source changed', report['error'])


if __name__ == '__main__':
    unittest.main()
