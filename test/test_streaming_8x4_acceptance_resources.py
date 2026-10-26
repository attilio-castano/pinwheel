"""Wrapper controls execute the real guard logic with no spawned Native work."""
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
SPEC = importlib.util.spec_from_file_location('streaming_8x4_resources_test',
                                            ROOT / 'scripts/streaming_8x4_acceptance_resources.py')
W = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(W)


class FakeProcess:
    pid = 987654321
    returncode = 0

    def __init__(self, *, running=False, tamper=None):
        self.running, self.tamper = running, tamper

    def poll(self):
        if self.tamper is not None:
            self.tamper.write_text('changed after admission')
        return None if self.running else 0

    def wait(self, timeout):
        return 0


class WrapperTests(unittest.TestCase):
    def fixture(self, temporary, *, kind='solver', parent=None, timeout=1):
        root = Path(temporary)
        (root / 'scripts').mkdir()
        (root / 'scripts/streaming_tt_resources.py').write_bytes((ROOT / 'scripts/streaming_tt_resources.py').read_bytes())
        seal = root / 'seal.txt'
        seal.write_text('original input')
        argv = ['--campaign-root', str(root), '--kind', kind, '--tag', 'control',
                '--timeout-seconds', str(timeout), '--input', str(seal)]
        if parent:
            parent.write_text('frozen parent')
            argv += ['--validation-parent', str(parent)]
        argv += ['--', 'never-executed']
        return W.parser().parse_args(argv), W.load_guard(root), seal

    def execute(self, args, guard, process):
        samples = dict(utc='2026-10-23T04:00:00+00:00', memory_available_percent=90, disk_free_bytes=64 * 1024**3)
        with patch.object(guard, 'observation', return_value=samples), \
             patch.object(guard, 'process_table', return_value={}), \
             patch.object(guard.shutil, 'which', return_value=None), \
             patch.object(guard.subprocess, 'Popen', return_value=process) as spawn, \
             patch.object(guard.time, 'sleep'), \
             patch.object(guard.time, 'monotonic', side_effect=itertools.chain([0, .1, 2], itertools.repeat(2.1))), \
             patch.object(guard.signal, 'signal'), patch.object(guard.signal, 'setitimer'):
            result = W.run(args, guard=guard, now='2026-10-23T04:00:00Z')
        receipt = json.loads((args.campaign_root / 'build/streaming-tt-resources/control/report.json').read_text())
        return result, receipt, spawn

    def test_positive_host_control_keeps_claim_false_and_one_root_lock(self):
        with tempfile.TemporaryDirectory() as temporary:
            args, guard, _ = self.fixture(temporary)
            guard.ROOT = Path('/unrelated-worker-runtime')
            guard.BASE = Path('/unrelated-worker-lock')
            result, receipt, spawn = self.execute(args, guard, FakeProcess())
            self.assertEqual(result, 0)
            self.assertFalse(receipt['acceptance_claim'])
            self.assertTrue(receipt['cleanup_confirmed'])
            boundary = receipt['campaign_boundary']
            self.assertEqual(boundary['shared_lease']['heavy_lock'],
                             str(args.campaign_root.resolve() / 'build/streaming-tt-resources/heavy.lock'))
            self.assertTrue(boundary['root_go_is_external_authority'])
            self.assertEqual(boundary['campaign_kind'], 'rc_experiment')
            self.assertEqual(spawn.call_count, 1)
            self.assertIn(str(Path(W.__file__).resolve()), receipt['input_sha256'])

    def test_timeout_closes_failed_not_acceptance_with_no_real_spawn(self):
        with tempfile.TemporaryDirectory() as temporary:
            args, guard, _ = self.fixture(temporary)
            result, receipt, _ = self.execute(args, guard, FakeProcess(running=True))
            self.assertEqual(result, 1)
            self.assertEqual(receipt['status'], 'stopped')
            self.assertEqual(receipt['exit_code'], 124)
            self.assertIn('Wall-time', receipt['stop_reason'])
            self.assertTrue(receipt['cleanup_confirmed'])
            self.assertEqual(receipt['owned_processes_remaining'], [])

    def test_input_tamper_invalidates_even_exit_zero(self):
        with tempfile.TemporaryDirectory() as temporary:
            args, guard, seal = self.fixture(temporary)
            result, receipt, _ = self.execute(args, guard, FakeProcess(tamper=seal))
            self.assertEqual(result, 1)
            self.assertEqual(receipt['status'], 'invalidated')
            self.assertFalse(receipt['inputs_unchanged'])
            self.assertTrue(receipt['cleanup_confirmed'])

    def test_over_cutoff_and_deadline_override_never_enter_guard(self):
        for now, changed_deadline in [('2026-10-23T05:00:35Z', None),
                                      ('2026-10-23T04:00:00Z', '2026-10-23T09:00:35Z')]:
            with tempfile.TemporaryDirectory() as temporary:
                args, guard, _ = self.fixture(temporary)
                if changed_deadline:
                    args.deadline = changed_deadline
                with patch.object(guard, 'main') as main, self.assertRaises(ValueError):
                    W.run(args, guard=guard, now=now)
                main.assert_not_called()

    def test_physical_slice_cannot_consume_protected_rc_time(self):
        with tempfile.TemporaryDirectory() as temporary:
            args, guard, _ = self.fixture(temporary, kind='cad', timeout=14400)
            args.container_name = 'pinwheel-control'
            def observe_forwarded():
                remaining = guard.admission_window('cad', W.timestamp(W.SCHEDULE['heavy_cutoff']),
                                                   W.timestamp('2026-10-23T02:30:00Z'))
                self.assertEqual(remaining, 1835)
                return 0
            with patch.object(guard, 'main', side_effect=observe_forwarded):
                self.assertEqual(W.run(args, guard=guard, now='2026-10-23T02:30:00Z'), 0)

    def test_frozen_proof_parent_required_and_four_hour_cap_preserved(self):
        with tempfile.TemporaryDirectory() as temporary:
            args, guard, _ = self.fixture(temporary, kind='lean')
            with self.assertRaisesRegex(ValueError, 'frozen parent'):
                W.run(args, guard=guard, now='2026-10-23T06:00:00Z')
            args.timeout_seconds = 14401
            with self.assertRaisesRegex(ValueError, 'four-hour'):
                W.run(args, guard=guard, now='2026-10-23T06:00:00Z')


if __name__ == '__main__':
    unittest.main()
