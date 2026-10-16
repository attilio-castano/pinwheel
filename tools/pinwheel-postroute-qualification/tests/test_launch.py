"""Host-only admission and staging tests. No Docker/CAD is executed."""
import json
from pathlib import Path
import sys
import tempfile
import shutil
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from audits import sha, write
from run import build_spec


class Launch(unittest.TestCase):
    def fixture(self, root):
        package = root / 'prepared'
        package.mkdir()
        source = root / 'frozen-source'
        source.write_text('unchanged')
        campaign = root / 'campaign.json'
        write(campaign, {'image_id': 'sha256:' + 'a' * 64,
            'hard_stop_epoch': time.time() + 8000, 'budgets_seconds': {'closeout': 3600},
            'protected_sources_sha256': {str(source): sha(source)}, 'reference_files_sha256': {}})
        (package / 'worker.py').write_text('raise RuntimeError("mock fixture must never execute")\n')
        repository = next(parent for parent in Path(__file__).resolve().parents
                          if (parent / 'tools/physical-toolchain.json').is_file())
        runner = repository / 'tools/pinwheel-physical-campaign/runner.py'
        shutil.copyfile(runner, package / 'campaign_runner.py')
        for name in ['run.py', 'audits.py']:
            shutil.copyfile(Path(__file__).resolve().parents[1] / name, package / name)
        manifest = {'schema': 'pinwheel-isolated-postroute-qualification-v1',
            'source_sha256': {str(source): sha(source), str(campaign): sha(campaign)},
            'staged_sha256': {name: sha(package / name) for name in ['worker.py', 'campaign_runner.py', 'run.py', 'audits.py']},
            'campaign_path': str(campaign), 'campaign_sha256': sha(campaign),
            'hard_stop_epoch': json.loads(campaign.read_text())['hard_stop_epoch'],
            'native_work_stop_epoch': json.loads(campaign.read_text())['hard_stop_epoch'] - 3600,
            'image_id': 'sha256:' + 'a' * 64, 'campaign_id': 'fixture',
            'heavy_lock': str(root / 'heavy.lock'), 'PDK_root': str(root)}
        write(package / 'prepared.json', manifest)
        return package / 'prepared.json', source

    def test_stage_only_has_shared_lock_and_native_cleanup_bounds(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prepared, source = self.fixture(root)
            spec = build_spec(prepared, phase='rcx-sta', output_dir=root / 'out', native_seconds=120)
            self.assertEqual(spec.native_seconds, 120)
            self.assertEqual(spec.max_job_seconds, 165)
            self.assertEqual(spec.closeout_reserve_seconds, 45)
            self.assertEqual(spec.heavy_lock_path, root / 'heavy.lock')
            self.assertEqual(spec.command, ['python3', '-B', '/work/diagnostic/worker.py'])
            self.assertFalse(spec.heavy_lock_path.exists())
            self.assertFalse((root / 'out/report.json').exists())
            self.assertEqual(source.read_text(), 'unchanged')

    def test_changed_frozen_source_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prepared, source = self.fixture(root)
            source.write_text('changed')
            with self.assertRaises(AssertionError):
                build_spec(prepared, phase='rcx-sta', output_dir=root / 'out', native_seconds=120)
            self.assertFalse((root / 'out').exists())

    def test_changed_package_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prepared, source = self.fixture(root)
            (prepared.parent / 'worker.py').write_text('wrong')
            with self.assertRaises(AssertionError):
                build_spec(prepared, phase='rcx-sta', output_dir=root / 'out', native_seconds=120)

    def test_max_all_in_and_minimum_bounds(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prepared, _ = self.fixture(root)
            for seconds, minimum in [(5400, 30), (30, 60), (0, 1)]:
                with self.assertRaises(AssertionError):
                    build_spec(prepared, phase='rcx-sta', output_dir=root / 'out',
                               native_seconds=seconds, minimum_native_seconds=minimum)

    def test_output_not_overwritten(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prepared, _ = self.fixture(root)
            out = root / 'out'
            out.mkdir()
            (out / 'report.json').write_text('retained')
            with self.assertRaises(FileExistsError):
                build_spec(prepared, phase='rcx-sta', output_dir=out, native_seconds=120)
            self.assertEqual((out / 'report.json').read_text(), 'retained')


if __name__ == '__main__':
    unittest.main()
