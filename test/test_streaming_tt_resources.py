"""Resource admission fails closed and cleanup never follows a reused PID."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('streaming_tt_resources_test', ROOT / 'scripts/streaming_tt_resources.py')
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)


class ResourceTests(unittest.TestCase):
    def test_candidate_cutoff_preserves_frozen_validation_until_hard_deadline(self):
        deadline = R.datetime.fromisoformat('2026-10-19T03:26:07+00:00')
        before = R.datetime.fromisoformat('2026-10-19T00:26:06+00:00')
        cutoff = R.datetime.fromisoformat('2026-10-19T00:26:07+00:00')
        late = R.datetime.fromisoformat('2026-10-19T02:26:07+00:00')
        self.assertGreater(R.admission_window('cad', deadline, before), 0)
        for now in (cutoff, late):
            with self.assertRaisesRegex(ValueError, 'candidate CAD'):
                R.admission_window('cad', deadline, now)
            self.assertGreater(R.admission_window('cad-validation', deadline, now), 0)
        for kind in ('cad', 'cad-validation', 'lean', 'host'):
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, 'deadline'):
                R.admission_window(kind, deadline, deadline - R.timedelta(seconds=30))

    def test_validation_requires_explicit_regular_parent_and_rejects_alias(self):
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary) / 'existing-candidate.json'
            parent.write_text('frozen existing artifact')
            result = R.validation_parent('cad-validation', parent)
            self.assertEqual(result['sha256'], R.file_hashes([parent])[str(parent.resolve())])
            with self.assertRaises(ValueError):
                R.validation_parent('cad-validation', None)
            with self.assertRaises(ValueError):
                R.validation_parent('cad', parent)
            alias = Path(temporary) / 'alias.json'
            alias.symlink_to(parent)
            with self.assertRaises(ValueError):
                R.validation_parent('cad-validation', alias)
            self.assertIsNone(R.validation_parent('lean', None))

    def test_preflight_failure_does_not_stop_any_container_or_retry_denied_observations(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            argv = ['guard', '--tag', 'fixture', '--kind', 'cad', '--timeout-seconds', '10',
                    '--container-name', 'pinwheel-user-existing', '--deadline', '2099-01-01T00:00:00+00:00',
                    '--', 'must-not-run']
            with patch.object(R, 'BASE', base), patch.object(R.sys, 'argv', argv), \
                    patch.object(R, 'observation', side_effect=ValueError('observation denied')), \
                    patch.object(R, 'process_table') as table, patch.object(R, 'docker_ids') as docker, \
                    patch.object(R.subprocess, 'Popen') as spawn:
                self.assertEqual(R.main(), 1)
            table.assert_not_called()
            docker.assert_not_called()
            spawn.assert_not_called()
            result = json.loads((base / 'fixture/report.json').read_text())
            self.assertEqual(result['cleanup_scope'], 'no_job_spawned')
            self.assertTrue(result['cleanup_confirmed'])
            self.assertFalse((base / 'cleanup-unconfirmed.json').exists())

    def sample(self, memory=85, disk=39 * 1024 ** 3):
        return dict(memory_available_percent=memory, disk_free_bytes=disk)

    def test_admission_and_emergency_floors_differ(self):
        with self.assertRaisesRegex(ValueError, 'memory'):
            R.gate(self.sample(24), admission=True)
        R.gate(self.sample(24), admission=False)
        with self.assertRaisesRegex(ValueError, 'memory'):
            R.gate(self.sample(14), admission=False)
        for percent in [-1, 101]:
            with self.subTest(percent=percent), self.assertRaises(ValueError):
                R.gate(self.sample(percent), admission=False)

    def test_disk_and_total_tree_rss_are_hard_bounds(self):
        with self.assertRaisesRegex(ValueError, 'Disk'):
            R.gate(self.sample(disk=12 * 1024 ** 3 - 1), admission=False)
        R.gate(self.sample(), admission=False, rss_kib=4096 * 1024)
        with self.assertRaisesRegex(ValueError, 'RSS'):
            R.gate(self.sample(), admission=False, rss_kib=4096 * 1024 + 1)

    def test_process_identity_keeps_birth_and_command_spaces(self):
        table = R.processes('123 12 123 4096 Sun Oct 18 11:00:00 2026 /path with space/lean\n')
        self.assertEqual(table[123]['command'], '/path with space/lean')
        self.assertEqual(table[123]['birth'], 'Sun Oct 18 11:00:00 2026')
        with self.assertRaisesRegex(ValueError, 'Malformed'):
            R.processes('123 12\n')

    def test_descendants_include_nested_separate_process_groups(self):
        table = {1: dict(ppid=0), 2: dict(ppid=1), 3: dict(ppid=2), 4: dict(ppid=9)}
        self.assertEqual(set(R.descendants(table, 1)), {1, 2, 3})

    def test_reused_pid_is_not_signaled(self):
        tracked = {123: dict(birth='old')}
        table = {123: dict(birth='new')}
        with patch.object(R, 'process_table', return_value=table), patch.object(R.os, 'kill') as kill:
            R.signal_owned(tracked, R.signal.SIGTERM)
        kill.assert_not_called()

    def test_unchanged_owned_pid_is_signaled(self):
        tracked = {123: dict(birth='same')}
        with patch.object(R, 'process_table', return_value=tracked), patch.object(R.os, 'kill') as kill:
            R.signal_owned(tracked, R.signal.SIGTERM)
        kill.assert_called_once_with(123, R.signal.SIGTERM)

    def test_async_cleanup_waits_for_observed_absence_without_signaling(self):
        tracked = {123: dict(birth='same')}
        with patch.object(R, 'process_table', side_effect=[tracked, {}]) as observe, \
                patch.object(R.time, 'sleep') as pause, patch.object(R.os, 'kill') as kill:
            self.assertEqual(R.settle_owned(tracked), {})
        self.assertEqual(observe.call_count, 2)
        pause.assert_called_once_with(.05)
        kill.assert_not_called()

    def test_cleanup_still_reports_owned_process_at_bound(self):
        tracked = {123: dict(birth='same')}
        with patch.object(R, 'process_table', return_value=tracked), \
                patch.object(R.time, 'monotonic', side_effect=[0, 6]), \
                patch.object(R.time, 'sleep') as pause:
            self.assertEqual(R.settle_owned(tracked, timeout_seconds=5), tracked)
        pause.assert_not_called()

    def test_cleanup_does_not_wait_on_reused_pid_or_hide_observation_failure(self):
        tracked = {123: dict(birth='old')}
        with patch.object(R, 'process_table', return_value={123: dict(birth='new')}), \
                patch.object(R.time, 'sleep') as pause:
            self.assertEqual(R.settle_owned(tracked), {})
        pause.assert_not_called()
        with patch.object(R, 'process_table', side_effect=ValueError('observation failed')):
            with self.assertRaisesRegex(ValueError, 'observation failed'):
                R.settle_owned(tracked)

    def test_unobservable_memory_is_rejected(self):
        with patch.object(R.sys, 'platform', 'darwin'), patch.object(R, 'command', return_value='unavailable'):
            with self.assertRaisesRegex(ValueError, 'Missing'):
                R.availability()

    def test_cad_checks_swap_cpu_network_and_memory(self):
        base = dict(Memory=6 * 1024 ** 3, MemorySwap=6 * 1024 ** 3,
                    NanoCpus=4 * 10 ** 9, NetworkMode='none')
        for key, value in [('Memory', 0), ('MemorySwap', 0), ('NanoCpus', 0), ('NetworkMode', 'default')]:
            config = dict(base, **{key: value})
            reply = json.dumps([dict(HostConfig=config, State=dict(Running=True))])
            with self.subTest(key=key), patch.object(R, 'docker_ids', return_value=['a' * 64]), \
                    patch.object(R, 'command', return_value=reply), self.assertRaises(ValueError):
                R.container_observation('pinwheel-test')
        reply = json.dumps([dict(HostConfig=base, State=dict(Running=True))])
        with patch.object(R, 'docker_ids', return_value=['a' * 64]), \
                patch.object(R, 'command', side_effect=[reply, '96.0%\n']), self.assertRaisesRegex(ValueError, 'approaching'):
            R.container_observation('pinwheel-test')
        with patch.object(R, 'docker_ids', return_value=['a' * 64]), \
                patch.object(R, 'command', side_effect=[reply, '40.0%\n']):
            self.assertEqual(R.container_observation('pinwheel-test')['memory_percent'], 40)

    def test_short_container_exit_race_is_accepted_only_after_absence_is_observed(self):
        base = dict(Memory=6 * 1024 ** 3, MemorySwap=6 * 1024 ** 3,
                    NanoCpus=4 * 10 ** 9, NetworkMode='none')
        reply = json.dumps([dict(HostConfig=base, State=dict(Running=True))])
        for failure in (ValueError('EOF'), R.subprocess.TimeoutExpired('docker stats', 10)):
            with self.subTest(failure=failure), \
                    patch.object(R, 'docker_ids', side_effect=[['a' * 64], []]), \
                    patch.object(R, 'command', side_effect=[reply, failure]):
                result = R.container_observation('pinwheel-test')
                self.assertTrue(result['removed_during_observation'])
            with patch.object(R, 'docker_ids', return_value=['a' * 64]), \
                    patch.object(R, 'command', side_effect=[reply, failure]), \
                    self.assertRaises(type(failure)):
                R.container_observation('pinwheel-test')

    def test_sequential_container_replacement_is_recorded_but_not_validated(self):
        base = dict(Memory=6 * 1024 ** 3, MemorySwap=6 * 1024 ** 3,
                    NanoCpus=4 * 10 ** 9, NetworkMode='none')
        reply = json.dumps([dict(HostConfig=base, State=dict(Running=True))])
        for phase in ('inspect', 'stats'):
            for failure in (ValueError('EOF'), R.subprocess.TimeoutExpired('docker', 10)):
                calls = [failure] if phase == 'inspect' else [reply, failure]
                with self.subTest(phase=phase, failure=failure), \
                        patch.object(R, 'docker_ids', side_effect=[['a' * 64], ['b' * 64]]), \
                        patch.object(R, 'command', side_effect=calls):
                    result = R.container_observation('pinwheel-test')
                    self.assertEqual(result['id'], 'a' * 64)
                    self.assertFalse(result['running'])
                    self.assertEqual(result['replacement_container_ids'], ['b' * 64])
                    self.assertNotIn('memory_limit_bytes', result)
                with self.subTest(phase=phase, persistent=True), \
                        patch.object(R, 'docker_ids', return_value=['a' * 64]), \
                        patch.object(R, 'command', side_effect=calls), self.assertRaises(type(failure)):
                    R.container_observation('pinwheel-test')
            with self.subTest(phase=phase, ambiguous=True), \
                    patch.object(R, 'docker_ids', side_effect=[['a' * 64], ['b' * 64, 'c' * 64]]), \
                    patch.object(R, 'command', side_effect=[ValueError('EOF')] if phase == 'inspect' else
                                 [reply, ValueError('EOF')]), self.assertRaisesRegex(ValueError, 'Ambiguous'):
                R.container_observation('pinwheel-test')

    def test_replacement_container_resource_violation_is_rejected_on_next_sample(self):
        base = dict(Memory=6 * 1024 ** 3, MemorySwap=6 * 1024 ** 3,
                    NanoCpus=4 * 10 ** 9, NetworkMode='none')
        reply = json.dumps([dict(HostConfig=base, State=dict(Running=True))])
        for phase in ('inspect', 'stats'):
            for key, value in [('Memory', 0), ('MemorySwap', 0), ('NanoCpus', 0), ('NetworkMode', 'default')]:
                invalid = json.dumps([dict(HostConfig=dict(base, **{key: value}), State=dict(Running=True))])
                calls = [ValueError('EOF'), invalid] if phase == 'inspect' else [reply, ValueError('EOF'), invalid]
                with self.subTest(phase=phase, key=key), \
                        patch.object(R, 'docker_ids', side_effect=[['a' * 64], ['b' * 64], ['b' * 64]]), \
                        patch.object(R, 'command', side_effect=calls) as command:
                    self.assertTrue(R.container_observation('pinwheel-test')['removed_during_observation'])
                    with self.assertRaises(ValueError):
                        R.container_observation('pinwheel-test')
                    self.assertEqual(command.call_args.args[0], ['docker', 'inspect', 'b' * 64])


if __name__ == '__main__':
    unittest.main()
