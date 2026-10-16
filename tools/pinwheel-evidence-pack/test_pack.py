"""Finite host-only custody/CAS regressions. Only temporary synthetic bytes."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import pack


class EvidencePack(unittest.TestCase):
    def test_relative_cli_paths_use_current_directory(self):
        self.assertEqual(pack.absolute('selection.json'),Path.cwd()/'selection.json')

    def fixture(self, folder):
        root=Path(folder).resolve();producer=root/'job';producer.mkdir()
        data=root/'source';data.write_bytes(b'unchanged design input\n')
        alias=root/'alias';alias.write_bytes(data.read_bytes())
        link=root/'link';link.symlink_to('source')
        (producer/'native.log').write_text('actual native diagnostic fails DRC; producer completed\n')
        anchor=root/'review.json';anchor.write_bytes(pack.encode({'source_sha256':{str(data):pack.digest(data.read_bytes())},
            'producer_status':'passed','native_DRC_passed':False,'physical_acceptance_claim':False}))
        receipt={'schema':'pinwheel-owned-campaign-job-v1','status':'passed','exit_code':0,'finished_epoch':1,
            'inputs_unchanged':True,'container_termination':{'status':'absent'},
            'within_absolute_and_job_deadlines':True,'controller_must_stop':False,
            'input_sha256':{str(p):pack.digest(p.read_bytes()) for p in [data,alias,link]},
            'artifact_sha256':{'native.log':pack.digest((producer/'native.log').read_bytes())}}
        (producer/'report.json').write_bytes(pack.encode(receipt))
        selection={'schema':'pinwheel-evidence-selection-v1','origin_root':str(root),
            'receipts':[{'path':str(producer/'report.json'),'sha256':pack.digest((producer/'report.json').read_bytes())}],
            'anchors':[{'path':str(anchor),'sha256':pack.digest(anchor.read_bytes())}],
            'external_runtime':{'image_id':'sha256:'+'a'*64,'packed':False,'remote_availability_proven':False},
            'candidate':{'checkpoint':str(data),'checkpoint_sha256':pack.digest(data.read_bytes()),
                'physical_acceptance_claim':False}}
        selected=root/'selection.json';selected.write_bytes(pack.encode(selection))
        return root,selected

    def select(self,path):return pack.digest(path.read_bytes())

    def directory_overlay(self,root,selection,*,empty=False,indirect=False):
        overlay=root/'overlay';overlay.mkdir();real=overlay/'real';real.mkdir()
        regular={}
        if not empty:
            (real/'rule').write_text('unchanged native rule')
            regular['real/rule']=pack.digest((real/'rule').read_bytes())
        link=overlay/'dir-link'
        if indirect:
            # The intermediate outside the overlay is not itself a declared
            # link. Changing it leaves dir-link's literal target unchanged.
            (root/'intermediate').symlink_to('overlay/real',target_is_directory=True)
            target='../intermediate'
        else:target='real'
        link.symlink_to(target,target_is_directory=True)
        manifest=root/'overlay.json';manifest.write_bytes(pack.encode({'overlay_PDK_root':str(overlay),
            'all_overlay_regular_files_sha256':regular,'all_overlay_symlink_targets':{'dir-link':target}}))
        chosen=pack.parse(selection.read_bytes());chosen['anchors'].append({'path':str(manifest),
            'sha256':pack.digest(manifest.read_bytes())});selection.write_bytes(pack.encode(chosen))
        return overlay,link,real

    def change_receipt(self,selection,callback):
        chosen=pack.parse(selection.read_bytes());path=Path(chosen['receipts'][0]['path'])
        record=pack.parse(path.read_bytes());callback(record);path.write_bytes(pack.encode(record))
        chosen['receipts'][0]['sha256']=pack.digest(path.read_bytes());selection.write_bytes(pack.encode(chosen))

    def test_copy_dedup_and_offline_verify_without_originals(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);out=root/'pack'
            result=pack.collect(selection,self.select(selection),out)
            index=pack.parse((out/'index.json').read_bytes());sha=pack.digest((root/'source').read_bytes())
            self.assertEqual(index['paths'][str(root/'source')]['sha256'],index['paths'][str(root/'alias')]['sha256'])
            self.assertEqual(index['paths'][str(root/'link')]['symlink_target'],'source')
            self.assertNotEqual((root/'source').stat().st_ino,(out/'objects/sha256'/sha).stat().st_ino)
            for name in ['source','alias','link','selection.json','review.json']: (root/name).unlink()
            self.assertEqual(pack.verify(out,result['seal_sha256'])['status'],'verified_pack_payloads')

    def test_input_hash_conflict_rejected_before_output(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);anchor=root/'review.json'
            anchor.write_bytes(pack.encode({'source_sha256':{str(root/'source'):'b'*64}}))
            s=pack.parse(selection.read_bytes());s['anchors'][0]['sha256']=pack.digest(anchor.read_bytes());selection.write_bytes(pack.encode(s))
            with self.assertRaisesRegex(ValueError,'hash conflict'):pack.collect(selection,self.select(selection),root/'pack')
            self.assertFalse((root/'pack').exists())

    def test_tampered_source_never_gets_a_seal(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);(root/'alias').write_text('tampered')
            with self.assertRaisesRegex(ValueError,'content hash mismatch'):pack.collect(selection,self.select(selection),root/'pack')
            self.assertFalse((root/'pack/seal.json').exists())

    def test_nonsettled_receipt_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);self.change_receipt(selection,lambda r:r.update(status='running'))
            with self.assertRaisesRegex(ValueError,'nonsettled'):pack.collect(selection,self.select(selection),root/'pack')
            self.assertFalse((root/'pack').exists())

    def test_missing_closeout_artifacts_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);self.change_receipt(selection,lambda r:r.update(artifact_sha256={}))
            with self.assertRaisesRegex(ValueError,'nonsettled'):pack.collect(selection,self.select(selection),root/'pack')

    def test_unconfirmed_container_owner_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);self.change_receipt(selection,lambda r:r.update(container_termination={'status':'unconfirmed'}))
            with self.assertRaisesRegex(ValueError,'nonsettled'):pack.collect(selection,self.select(selection),root/'pack')

    def test_failed_diagnostic_receipt_stays_failed(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);self.change_receipt(selection,lambda r:r.update(status='failed',exit_code=1))
            result=pack.collect(selection,self.select(selection),root/'pack')
            index=pack.parse((root/'pack/index.json').read_bytes())
            self.assertEqual(next(iter(index['producer_receipts'].values()))['status'],'failed')
            self.assertFalse(index['physical_acceptance_claim'])
            self.assertEqual(pack.verify(root/'pack',result['seal_sha256'])['producer_receipts'],1)

    def test_missing_object_fails_offline_verify(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);result=pack.collect(selection,self.select(selection),root/'pack')
            next((root/'pack/objects/sha256').iterdir()).unlink()
            with self.assertRaisesRegex(ValueError,'Missing/nonregular CAS object'):pack.verify(root/'pack',result['seal_sha256'])

    def test_tampered_object_fails_offline_verify(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);result=pack.collect(selection,self.select(selection),root/'pack')
            next((root/'pack/objects/sha256').iterdir()).write_text('tampered')
            with self.assertRaisesRegex(ValueError,'content hash mismatch'):pack.verify(root/'pack',result['seal_sha256'])

    def test_wrong_external_seal_digest_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);pack.collect(selection,self.select(selection),root/'pack')
            with self.assertRaisesRegex(ValueError,'Seal hash mismatch'):pack.verify(root/'pack','b'*64)

    def test_symlink_target_content_tamper_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);(root/'source').write_text('changed link payload')
            with self.assertRaises(ValueError):pack.collect(selection,self.select(selection),root/'pack')
            self.assertFalse((root/'pack/seal.json').exists())

    def test_symlink_retarget_is_separate_from_packed_bytes(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);result=pack.collect(selection,self.select(selection),root/'pack')
            (root/'link').unlink();(root/'link').symlink_to('alias')
            self.assertEqual(pack.verify(root/'pack',result['seal_sha256'])['status'],'verified_pack_payloads')
            with self.assertRaisesRegex(ValueError,'source/link identity differs'):pack.verify(root/'pack',result['seal_sha256'],origins=True)

    def test_index_only_requires_explicit_origins_and_detects_tamper(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);result=pack.collect(selection,self.select(selection),root/'index',index_only=True)
            self.assertFalse((root/'index/objects').exists())
            with self.assertRaisesRegex(ValueError,'Index-only'):pack.verify(root/'index',result['seal_sha256'])
            self.assertEqual(pack.verify(root/'index',result['seal_sha256'],origins=True)['status'],'verified_index_against_current_origins')
            (root/'alias').write_text('changed')
            with self.assertRaises(ValueError):pack.verify(root/'index',result['seal_sha256'],origins=True)

    def test_output_never_overwritten(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);pack.collect(selection,self.select(selection),root/'pack')
            before=(root/'pack/seal.json').read_bytes()
            with self.assertRaises(FileExistsError):pack.collect(selection,self.select(selection),root/'pack')
            self.assertEqual((root/'pack/seal.json').read_bytes(),before)

    def test_nested_receipt_status_and_dependency_maps_expand(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);nested=root/'nested';nested.mkdir()
            (nested/'result').write_text('fixture failed as expected')
            outer=pack.parse((root/'job/report.json').read_bytes());inner=copy.deepcopy(outer)
            inner.update(status='failed',exit_code=1,artifact_sha256={'result':pack.digest((nested/'result').read_bytes())})
            (nested/'report.json').write_bytes(pack.encode(inner))
            self.change_receipt(selection,lambda r:r['input_sha256'].update({str(nested/'report.json'):pack.digest((nested/'report.json').read_bytes())}))
            result=pack.collect(selection,self.select(selection),root/'pack')
            self.assertEqual(pack.verify(root/'pack',result['seal_sha256'])['producer_receipts'],2)

    def test_declared_overlay_symlink_and_regular_content(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);overlay=root/'overlay';overlay.mkdir()
            (overlay/'real').mkdir();(overlay/'real/rule').write_text('native rule')
            (overlay/'dir-link').symlink_to('real',target_is_directory=True)
            manifest=root/'overlay.json';manifest.write_bytes(pack.encode({'overlay_PDK_root':str(overlay),
                'all_overlay_regular_files_sha256':{'real/rule':pack.digest((overlay/'real/rule').read_bytes())},
                'all_overlay_symlink_targets':{'dir-link':'real'}}))
            selected=pack.parse(selection.read_bytes());selected['anchors'].append({'path':str(manifest),'sha256':pack.digest(manifest.read_bytes())});selection.write_bytes(pack.encode(selected))
            result=pack.collect(selection,self.select(selection),root/'pack')
            self.assertEqual(pack.verify(root/'pack',result['seal_sha256'])['status'],'verified_pack_payloads')

    def test_directory_link_retarget_rejected_in_both_origin_modes(self):
        for index_only in (False,True):
            with self.subTest(index_only=index_only),tempfile.TemporaryDirectory() as folder:
                root,selection=self.fixture(folder);overlay,link,real=self.directory_overlay(root,selection)
                result=pack.collect(selection,self.select(selection),root/'pack',index_only=index_only)
                pack.verify(root/'pack',result['seal_sha256'],origins=True)
                (overlay/'other').mkdir();link.unlink();link.symlink_to('other',target_is_directory=True)
                # The original target payload stays byte-exact.
                self.assertEqual((real/'rule').read_text(),'unchanged native rule')
                with self.assertRaisesRegex(ValueError,'Original declared overlay symlink identity differs'):
                    pack.verify(root/'pack',result['seal_sha256'],origins=True)
                if not index_only:
                    self.assertEqual(pack.verify(root/'pack',result['seal_sha256'])['status'],'verified_pack_payloads')

    def test_directory_link_missing_or_replaced_by_directory_rejected(self):
        for index_only in (False,True):
            for replacement in ('missing','directory'):
                with self.subTest(index_only=index_only,replacement=replacement),tempfile.TemporaryDirectory() as folder:
                    root,selection=self.fixture(folder);overlay,link,real=self.directory_overlay(root,selection)
                    result=pack.collect(selection,self.select(selection),root/'pack',index_only=index_only)
                    link.unlink()
                    if replacement=='directory':link.mkdir()
                    with self.assertRaisesRegex(ValueError,'Original declared overlay symlink identity differs'):
                        pack.verify(root/'pack',result['seal_sha256'],origins=True)

    def test_directory_link_resolved_path_change_with_same_literal_target_rejected(self):
        for index_only in (False,True):
            with self.subTest(index_only=index_only),tempfile.TemporaryDirectory() as folder:
                root,selection=self.fixture(folder);overlay,link,real=self.directory_overlay(root,selection,indirect=True)
                result=pack.collect(selection,self.select(selection),root/'pack',index_only=index_only)
                original_target=link.readlink();(overlay/'other').mkdir()
                (root/'intermediate').unlink();(root/'intermediate').symlink_to('overlay/other',target_is_directory=True)
                self.assertEqual(link.readlink(),original_target)
                with self.assertRaisesRegex(ValueError,'Original declared overlay symlink identity differs'):
                    pack.verify(root/'pack',result['seal_sha256'],origins=True)

    def test_directory_link_target_kind_change_with_same_text_and_path_rejected(self):
        for index_only in (False,True):
            with self.subTest(index_only=index_only),tempfile.TemporaryDirectory() as folder:
                root,selection=self.fixture(folder);overlay,link,real=self.directory_overlay(root,selection,empty=True)
                result=pack.collect(selection,self.select(selection),root/'pack',index_only=index_only)
                original_target,original_resolved=link.readlink(),link.resolve()
                real.rmdir();real.write_text('now a file, not a directory')
                self.assertEqual(link.readlink(),original_target);self.assertEqual(link.resolve(),original_resolved)
                with self.assertRaisesRegex(ValueError,'Original declared overlay symlink identity differs'):
                    pack.verify(root/'pack',result['seal_sha256'],origins=True)

    def test_duplicate_json_key_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate JSON key'):pack.parse(b'{"input_sha256":{},"input_sha256":{}}')

    def test_duplicate_native_telemetry_is_an_opaque_bound_artifact(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);p=root/'job/native-metrics.json'
            p.write_bytes(b'{"count":1,"count":2}\n')
            self.change_receipt(selection,lambda r:r['artifact_sha256'].update({'native-metrics.json':pack.digest(p.read_bytes())}))
            result=pack.collect(selection,self.select(selection),root/'pack')
            self.assertEqual(pack.verify(root/'pack',result['seal_sha256'])['status'],'verified_pack_payloads')

    def test_unknown_large_JSON_cannot_hide_dependency_maps(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);p=root/'job/extra.json'
            p.write_bytes(pack.encode({'source_sha256':{str(root/'source'):'b'*64},'padding':'x'*10000}))
            self.change_receipt(selection,lambda r:r['artifact_sha256'].update({'extra.json':pack.digest(p.read_bytes())}))
            with patch.object(pack,'JSON_LIMIT',3000),self.assertRaisesRegex(ValueError,'finite metadata bound'):
                pack.collect(selection,self.select(selection),root/'pack')
            self.assertFalse((root/'pack').exists())

    def test_resealed_wrong_blob_cannot_satisfy_original_receipt_map(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder);out=root/'pack';pack.collect(selection,self.select(selection),out)
            index=pack.parse((out/'index.json').read_bytes());wrong=b'another valid CAS object\n';sha=pack.digest(wrong)
            (out/'objects/sha256'/sha).write_bytes(wrong);index['objects'][sha]=len(wrong)
            index['paths'][str(root/'alias')].update(sha256=sha,size=len(wrong))
            raw=pack.encode(index);(out/'index.json').write_bytes(raw)
            seal=pack.parse((out/'seal.json').read_bytes());seal.update(index_sha256=pack.digest(raw),
                unique_objects=len(index['objects']),unique_content_bytes=sum(index['objects'].values()))
            raw=pack.encode(seal);(out/'seal.json').write_bytes(raw)
            with self.assertRaisesRegex(ValueError,'Dependency blob digest mismatch'):
                pack.verify(out,pack.digest(raw))

    def test_payload_plan_is_not_a_hash_seal(self):
        with tempfile.TemporaryDirectory() as folder:
            root,selection=self.fixture(folder)
            result=pack.inspect_graph(pack.source_graph(selection,self.select(selection)))
            self.assertEqual(result['status'],'stat_estimate_not_a_hash_seal')
            self.assertGreater(result['logical_bytes'],result['deduplicated_bytes_estimate'])
            self.assertFalse((root/'pack').exists())


if __name__=='__main__':unittest.main()
