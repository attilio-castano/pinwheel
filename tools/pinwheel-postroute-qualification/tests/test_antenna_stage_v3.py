"""No-CAD staging/admission controls, including a retained actual source replay."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
REPOSITORY = next(p for p in HERE.parents if (p / 'tools/physical-toolchain.json').is_file())
sys.path.insert(0, str(HERE))
import antenna_host_v3 as host
from audits import sha, write


class Admission(unittest.TestCase):
    def fixture(self, root):
        """Synthetic receipts exercise admission; native bodies must never run."""
        package, producer = root / 'prepared', root / 'route'
        package.mkdir(); (package / 'input').mkdir(); (producer / 'after').mkdir(parents=True)
        sentinel = root / 'protected'; sentinel.write_text('frozen RTL')
        reference = root / 'reference'; reference.write_text('frozen reference')
        image = 'sha256:' + 'a' * 64
        campaign = {'image_id': image, 'hard_stop_epoch': time.time() + 10000,
            'budgets_seconds': {'closeout': 3600}, 'single_heavy_CAD_process': True,
            'native_cpus': 4, 'native_memory': '6g',
            'protected_sources_sha256': {str(sentinel): sha(sentinel)},
            'reference_files_sha256': {str(reference): sha(reference)}}
        campaign_path = root / 'campaign.json'; write(campaign_path, campaign)
        inventory = {'nets': {'n': {'sig_type': 'SIGNAL', 'ports': ['in'], 'terminals': [['U', 'A', 'INPUT']]}},
            'instances': {'U': {'master': 'BUF', 'macro': False, 'terminals': [['A', 'n', 'INPUT']]}}}
        for staged, actual in host.AFTER_FILES.items():
            path = producer / 'after' / actual
            if staged == 'inventory.json': write(path, inventory)
            else: path.write_text('frozen ' + actual)
            shutil.copyfile(path, package / 'input' / staged)
        receipt = {'status': 'passed', 'exit_code': 0, 'inputs_unchanged': True,
            'container_termination': {'status': 'absent'}, 'within_absolute_and_job_deadlines': True,
            'controller_must_stop': False, 'image_id': image, 'campaign_id': 'test-antenna',
            'input_sha256': {str(sentinel): sha(sentinel)},
            'artifact_sha256': {str(p.relative_to(producer)): sha(p) for p in (producer / 'after').iterdir()}}
        write(producer / 'report.json', receipt)
        write(producer / 'adjudication.json', {'stage_execution_and_scope_gate_passed': True})
        native_hashes = {}
        for name in host.NATIVE_SHA256:
            (package / name).write_text('raise RuntimeError("fixture native execution is forbidden")\n')
            native_hashes[name] = sha(package / name)
        shutil.copyfile(REPOSITORY / 'tools/pinwheel-physical-campaign/runner.py', package / 'campaign_runner.py')
        sources = {str(path): sha(path) for path in [sentinel, reference, campaign_path, producer / 'report.json', producer / 'adjudication.json']}
        request = {'schema': 'pinwheel-isolated-postroute-qualification-v1', 'source_sha256': sources,
            'staged_sha256': {str(p.relative_to(package)): sha(p) for p in package.rglob('*') if p.is_file()},
            'campaign_path': str(campaign_path), 'campaign_sha256': sha(campaign_path),
            'image_id': image, 'campaign_id': 'test-antenna', 'hard_stop_epoch': campaign['hard_stop_epoch'],
            'native_work_stop_epoch': campaign['hard_stop_epoch'] - 3600,
            'heavy_lock': str(root / 'heavy.lock'), 'PDK_root': str(root),
            'route_admission': {'producer_and_scope_admitted': True, 'after_root': str(producer / 'after'),
                'route_receipt': str(producer / 'report.json'), 'route_receipt_sha256': sha(producer / 'report.json'),
                'adjudication': str(producer / 'adjudication.json'), 'adjudication_sha256': sha(producer / 'adjudication.json')}}
        write(package / 'prepared.json', request)
        return package / 'prepared.json', native_hashes

    def call_fixture(self, root):
        prepared, native_hashes = self.fixture(root)
        return prepared, patch.object(host, 'NATIVE_SHA256', native_hashes)

    def test_preserves_all_original_hashes_and_bounds_without_execution(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder).resolve(); prepared, native = self.call_fixture(root)
            original = prepared.read_bytes(); frozen = host.load(prepared)['staged_sha256']
            with native:
                out = host.stage(prepared, root / 'antenna')
                _, spec = host.job_spec(out)
            self.assertEqual(prepared.read_bytes(), original)
            self.assertTrue(all(sha(out / path) == digest for path, digest in frozen.items()))
            self.assertEqual((spec.native_seconds, spec.max_job_seconds, spec.closeout_reserve_seconds), (300, 360, 60))
            self.assertEqual((spec.cpus, spec.memory), (4, '6g'))
            self.assertEqual(spec.command, ['python3', '-B', '/work/diagnostic/antenna_coordinator_v3.py'])
            self.assertFalse(spec.heavy_lock_path.exists())
            self.assertFalse((out / 'report.json').exists())
            self.assertIsNone(host.load(out / 'antenna-expected-v3.json')['same_source_reference'])
            self.assertFalse(host.load(out / 'antenna-ready-v3.json')['physical_acceptance_claim'])

    def test_running_source_rejected_before_stage_created(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve(); prepared, native=self.call_fixture(root)
            receipt=host.load(root/'route/report.json'); receipt['status']='running';write(root/'route/report.json',receipt)
            request=host.load(prepared); request['route_admission']['route_receipt_sha256']=sha(root/'route/report.json')
            request['source_sha256'][str(root/'route/report.json')]=sha(root/'route/report.json');write(prepared,request)
            with native, self.assertRaisesRegex(ValueError, 'Producer is not completed'):
                host.stage(prepared, root/'antenna')
            self.assertFalse((root/'antenna').exists())

    def test_changed_route_artifact_rejected_before_stage_created(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();prepared,native=self.call_fixture(root)
            (root/'route/after/checkpoint.def').write_text('changed wire')
            with native, self.assertRaisesRegex(ValueError, 'Producer input/artifact changed'):
                host.stage(prepared,root/'antenna')
            self.assertFalse((root/'antenna').exists())

    def test_missing_physical_scope_gate_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();prepared,native=self.call_fixture(root)
            request=host.load(prepared);request['route_admission']['producer_and_scope_admitted']=False;write(prepared,request)
            with native, self.assertRaisesRegex(ValueError,'No actual routed source admission'):
                host.stage(prepared,root/'antenna')
            self.assertFalse((root/'antenna').exists())

    def test_changed_protected_source_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();prepared,native=self.call_fixture(root)
            (root/'protected').write_text('changed RTL')
            with native, self.assertRaises(ValueError):host.stage(prepared,root/'antenna')
            self.assertFalse((root/'antenna').exists())

    def test_unqualified_native_body_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();prepared,native=self.call_fixture(root)
            request=host.load(prepared)
            (prepared.parent/'antenna_native_v2.py').write_text('changed native body')
            request['staged_sha256']['antenna_native_v2.py']=sha(prepared.parent/'antenna_native_v2.py');write(prepared,request)
            with native, self.assertRaisesRegex(ValueError,'requires separate qualification'):
                host.stage(prepared,root/'antenna')
            self.assertFalse((root/'antenna').exists())

    def test_native_stop_mismatch_rejected_before_mkdir(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();prepared,native=self.call_fixture(root)
            request=host.load(prepared);request['native_work_stop_epoch']+=60;write(prepared,request)
            with native, self.assertRaisesRegex(ValueError,'absolute native stop'):
                host.stage(prepared,root/'antenna')
            self.assertFalse((root/'antenna').exists())

    def test_new_helpers_cannot_replace_existing_frozen_hash(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();prepared,native=self.call_fixture(root)
            name='antenna_results_v3.py';(prepared.parent/name).write_text('prior frozen helper')
            request=host.load(prepared);request['staged_sha256'][name]=sha(prepared.parent/name);write(prepared,request)
            with native, self.assertRaisesRegex(ValueError,'overwrite a prepared hash'):
                host.stage(prepared,root/'antenna')
            self.assertFalse((root/'antenna').exists())

    def test_changed_staged_coordinator_blocks_job_spec(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();prepared,native=self.call_fixture(root)
            with native:
                out=host.stage(prepared,root/'antenna')
                (out/'antenna_coordinator_v3.py').write_text('changed')
                with self.assertRaisesRegex(ValueError,'Changed staged antenna input'):host.job_spec(out)

    def test_nonexistent_checkpoint_is_not_staged(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder)
            with self.assertRaises(FileNotFoundError):host.stage(root/'nonexistent/prepared.json',root/'antenna')
            self.assertFalse((root/'antenna').exists())

    def test_different_checkpoint_reference_rejected_before_mkdir(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder).resolve();prepared,native=self.call_fixture(root)
            reference=root/'reference-job';(reference/'input').mkdir(parents=True)
            (reference/'input/checkpoint.odb').write_text('different routed checkpoint')
            inputs={}
            for name in host.NATIVE_SHA256:
                shutil.copyfile(prepared.parent/name,reference/name);inputs[str(reference/name)]=sha(reference/name)
            write(reference/'measurement.json',{'status':'measured','checker_called':True,
                'full_scope_and_DEF_TAPER_exact':True,'source_database_sha256':sha(reference/'input/checkpoint.odb')})
            receipt=host.load(root/'route/report.json');receipt['input_sha256']=inputs
            receipt['artifact_sha256']={'measurement.json':sha(reference/'measurement.json')};write(reference/'report.json',receipt)
            with native,self.assertRaisesRegex(ValueError,'same-source antenna result'):
                host.stage(prepared,root/'antenna',reference)
            self.assertFalse((root/'antenna').exists())


class ActualCompletedSource(unittest.TestCase):
    def test_new_measurement_card_does_not_inherit_C14_counts(self):
        package=REPOSITORY/'build/physical/tt-overnight-qualification-plan-01/p2-C14-v7-overlay-prepared-01'
        if not (package/'prepared.json').exists():self.skipTest('Retained qualified C14 package unavailable')
        with tempfile.TemporaryDirectory() as folder:
            out=host.stage(package/'prepared.json',Path(folder)/'antenna')
            _,spec=host.job_spec(out)
            expected=host.load(out/'antenna-expected-v3.json')
            self.assertIsNone(expected['same_source_reference'])
            self.assertNotIn('native_net_violation_count',expected)
            self.assertNotIn('semantic_violation_signature_sha256',expected)
            self.assertEqual(expected['consumed_net_count'],28948)
            self.assertEqual(expected['INPUT_contact_count'],61787)
            self.assertFalse((out/'report.json').exists())

    def test_retained_C14_replay_preserves_native_bodies_and_reference(self):
        package=REPOSITORY/'build/physical/tt-overnight-qualification-plan-01/p2-C14-v7-overlay-prepared-01'
        previous=package.with_name('p2-C14-v2-antenna-01')
        if not (package/'prepared.json').exists():self.skipTest('Retained qualified C14 package unavailable')
        with tempfile.TemporaryDirectory() as folder:
            out=host.stage(package/'prepared.json',Path(folder)/'antenna',previous)
            _,spec=host.job_spec(out)
            expected=host.load(out/'antenna-expected-v3.json')
            self.assertEqual((expected['native_net_violation_count'],expected['native_pin_violation_count']),(124,135))
            self.assertEqual(expected['semantic_violation_signature_sha256'],
                '93a282fee7b195b9e201aaf10f8b282302b8bf70d750337d0c8b589b30222229')
            self.assertTrue(all(sha(out/name)==digest for name,digest in host.NATIVE_SHA256.items()))
            self.assertEqual(spec.native_seconds,300)
            self.assertFalse((out/'report.json').exists())
            self.assertEqual(spec.heavy_lock_path,REPOSITORY/'build/physical/tt-overnight-campaign-20261015/heavy.lock')

    def test_failed_reference_is_not_promoted(self):
        package=REPOSITORY/'build/physical/tt-overnight-qualification-plan-01/p2-C14-v7-overlay-prepared-01'
        previous=package.with_name('p2-C14-v1-antenna-01')
        if not (package/'prepared.json').exists():self.skipTest('Retained qualified C14 package unavailable')
        with tempfile.TemporaryDirectory() as folder:
            out=Path(folder)/'antenna'
            with self.assertRaisesRegex(ValueError,'Producer is not completed'):host.stage(package/'prepared.json',out,previous)
            self.assertFalse(out.exists())


if __name__=='__main__':unittest.main()
