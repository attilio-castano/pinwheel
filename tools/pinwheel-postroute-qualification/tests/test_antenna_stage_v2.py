import json
from pathlib import Path
import shutil
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from antenna_host_v2 import job_spec, stage
from audits import sha, write


class AntennaStage(unittest.TestCase):
    def fixture(self, root):
        repository = next(p for p in Path(__file__).resolve().parents if (p / 'tools/physical-toolchain.json').is_file())
        package = root / 'prepared'
        package.mkdir()
        shutil.copyfile(repository / 'tools/pinwheel-physical-campaign/runner.py', package / 'campaign_runner.py')
        (package / 'export_native.py').write_text('raise RuntimeError("must not execute fixture CAD")\n')
        source = root / 'source'
        source.write_text('fixed')
        p = {'schema': 'pinwheel-isolated-postroute-qualification-v1',
             'source_sha256': {str(source): sha(source)},
             'staged_sha256': {n: sha(package / n) for n in ['campaign_runner.py', 'export_native.py']},
             'heavy_lock': str(root / 'heavy.lock'), 'image_id': 'sha256:' + 'a' * 64,
             'campaign_id': 'fixture', 'hard_stop_epoch': time.time()+10000,
             'native_work_stop_epoch': time.time()+6400, 'PDK_root': str(root)}
        write(package / 'prepared.json', p)
        return package / 'prepared.json'

    def test_optional_stage_and_bounds_never_launch(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prepared = self.fixture(root)
            out = stage(prepared, root / 'antenna')
            _, spec = job_spec(out, 300)
            self.assertEqual(spec.native_seconds, 300)
            self.assertEqual(spec.max_job_seconds, 345)
            self.assertEqual(spec.heavy_lock_path, root / 'heavy.lock')
            self.assertFalse(spec.heavy_lock_path.exists())
            self.assertFalse((out / 'report.json').exists())
            self.assertEqual(spec.command[-1], '/work/diagnostic/antenna_coordinator_v2.py')
            plan = json.loads((out / 'antenna-plan.json').read_text())
            self.assertTrue(plan['actual_detailed_wire_and_API_and_metadata_admission_required'])
            self.assertFalse(plan['antenna_pass_qualified'])

    def test_expensive_antenna_job_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prepared = self.fixture(root)
            out = stage(prepared, root / 'antenna')
            with self.assertRaises(AssertionError):
                job_spec(out, 1200)

    def test_changed_frozen_export_helper_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            prepared = self.fixture(root)
            (prepared.parent / 'export_native.py').write_text('different')
            with self.assertRaises(AssertionError):
                stage(prepared, root / 'antenna')


if __name__ == '__main__':
    unittest.main()
