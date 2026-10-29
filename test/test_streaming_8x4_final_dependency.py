"""Relocation custody and failed prerequisite controls; no Native execution."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_final_dependency as D


class DependencyTests(unittest.TestCase):
    def recovery(self, root):
        owner = root/'owner'; target = owner/'build/evidence/source.lean'; target.parent.mkdir(parents=True)
        target.write_text('theorem original : True := True.intro\n')
        row = dict(root='wt1373',kind='file',path='build/evidence/source.lean',
                   restored_relative_path='build/evidence/source.lean',sha=D.R.digest(target))
        (owner/'RESTORED-FILES-METADATA.jsonl').write_text(json.dumps(row)+'\n')
        return target, row

    def test_relocation_keeps_original_names_and_refuses_changed_or_extra_payload(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); target,row=self.recovery(root); recovery=D.Recovery(root,owners=['owner'])
            original=D.OLD/row['path']
            self.assertEqual(recovery.file(original,row['sha']),target.resolve())
            with self.assertRaisesRegex(ValueError,'Missing/unbound'):recovery.file(original,'a'*64)
            target.write_text('changed source')
            with self.assertRaisesRegex(ValueError,'bytes changed'):recovery.file(original)
            with self.assertRaisesRegex(ValueError,'membership or bytes changed'):recovery.intact()
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);self.recovery(root);recovery=D.Recovery(root,owners=['owner'])
            (root/'owner/unrecorded.olean').write_bytes(b'extra cached object')
            with self.assertRaisesRegex(ValueError,'membership or bytes changed'):recovery.intact()

    def test_equal_payload_alias_is_explicit_and_cannot_replace_an_original_owner(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary); target,row=self.recovery(root); recovery=D.Recovery(root,owners=['owner'])
            alias=str(D.OLD/'build/raw/proof/source.lean');recovery.alias(alias,target,row['sha'])
            self.assertEqual(recovery.file(alias,row['sha']),target.resolve())
            with self.assertRaisesRegex(ValueError,'Ambiguous'):recovery.alias(alias,target,row['sha'])
            with self.assertRaisesRegex(ValueError,'Ambiguous'):recovery.alias(D.OLD/row['path'],target,row['sha'])

    def test_failed_foundation_or_imported_private_object_never_becomes_dependency(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'foundation.json'
            for record in ({'schema':'pinwheel.streaming-8x4-relocated-foundation.v1','passed':False},
                dict(schema='pinwheel.streaming-8x4-relocated-foundation.v1',passed=True,qualified=False,native_executed=False,
                    historical_foundation_reused=True,current_projection_identical=True,runtime_identity_unchanged=True,
                    module_order=list(range(649)),positive_library={'path':temporary,'artifact_sha256':{D.F.CONTROL:'a'*64}})):
                path.write_text(json.dumps(record))
                with self.assertRaises(ValueError):D.foundation(path)

    def test_original_absolute_worker_inventory_is_bound_without_receipt_rewrite(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);report=root/'report.json';report.write_text('{}')
            source=root/'source.lean';source.write_text('original bytes')
            artifacts={str(D.OLD/D.WORKER/'source.lean'):D.R.digest(source)}
            D.worker_membership(root,artifacts,report)
            self.assertEqual(next(iter(artifacts)),str(D.OLD/D.WORKER/'source.lean'))
            with self.assertRaisesRegex(ValueError,'escapes'):D.worker_membership(root,{'/elsewhere/source.lean':D.R.digest(source)},report)
            source.write_text('changed')
            with self.assertRaisesRegex(ValueError,'worker changed'):D.worker_membership(root,artifacts,report)


if __name__=='__main__':unittest.main()
