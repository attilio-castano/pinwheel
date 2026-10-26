"""Native admission controls exercise real imports/objects without launching Lean."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_final_m_execute as E


class ExecuteTests(unittest.TestCase):
    def test_exact_native_limits_and_private_all_owner_audit_are_fixed(self):
        argv=E.native_argv('/pinned/lean',Path('/fresh/all/Module.lean'),Path('/fresh/all/Module.olean'))
        self.assertEqual(argv,['/pinned/lean','-M4096','-j1','-DElab.async=false','--root=/fresh/all',
            '-DwarningAsError=true','-DmaxErrors=1','-o','/fresh/all/Module.olean','/fresh/all/Module.lean'])
        texts=E.private_texts(['NOne','MTwo',E.REQUIRED])
        self.assertIn('private axiom forbiddenUnused : False',texts[E.BAD])
        self.assertTrue(texts[E.BAD].startswith('import PhysicalGRTFinalRequired\n'))
        for owner in ('NOne','MTwo',E.REQUIRED,E.BAD):self.assertIn('import '+owner,texts[E.AUDIT])
        with self.assertRaises(ValueError):E.private_texts(['NOne','NOne'])
        with self.assertRaisesRegex(ValueError,'required owner'):E.private_texts(['NOne','PhysicalGRTRequired'])

    def test_budget_uses_only_six_exact_module_names_and_reopens_selected_timeout(self):
        expected={'PhysicalStateCodec','ActualGRTClockDAGProof','PhysicalGRTOriginalProof',
            'PhysicalGRTActualProof','PhysicalGRTFinalAudit','PhysicalGRTExactPrivateAudit'}
        self.assertEqual(set(E.budget_policy()['exact_long_modules']),expected)
        for name in expected:
            self.assertEqual(E.command_timeout(name),600)
            E.verify_command_timeout(dict(module=name,timeout_seconds=600))
            with self.assertRaisesRegex(ValueError,'timeout differs'):
                E.verify_command_timeout(dict(module=name,timeout_seconds=180))
        for name in ('PhysicalCoreCells0','PhysicalGRTFinalRequired',E.BAD,'UnlistedModule',
            'PhysicalStateCodecExtra','PrefixPhysicalGRTFinalAudit','ActualGRTClockDAGProof0',
            'PhysicalGRTOriginalProofRules','PhysicalGRTActualProofSuffix'):
            self.assertEqual(E.command_timeout(name),180)
            E.verify_command_timeout(dict(module=name,timeout_seconds=180))
            with self.assertRaisesRegex(ValueError,'timeout differs'):
                E.verify_command_timeout(dict(module=name,timeout_seconds=600))
        for invalid in (True,180.0,None):
            with self.assertRaises(ValueError):E.verify_command_timeout(dict(module='UnlistedModule',timeout_seconds=invalid))
        for invalid in ('',None,'PhysicalStateCodec.py','PhysicalStateCodec Extra'):
            with self.assertRaises(ValueError):E.command_timeout(invalid)

    def test_private_import_inventory_rejects_foreign_or_missing_actual_positive_owners(self):
        owners=['NOne','MTwo',E.REQUIRED];texts=E.private_texts(owners)
        E.verify_private_import_inventory(texts,owners)
        for name in (E.BAD,E.AUDIT):
            for prefix in ('import ForeignPositive\n','public import ForeignPositive\n'):
                with self.assertRaisesRegex(ValueError,'actual manifest N\\+M'):
                    E.verify_private_import_inventory(dict(texts,**{name:prefix+texts[name]}),owners)
        with self.assertRaises(ValueError):
            E.verify_private_import_inventory(dict(texts,**{E.AUDIT:texts[E.AUDIT].replace('import MTwo\n','')}),owners)
        with self.assertRaises(ValueError):
            E.verify_private_import_inventory(dict(texts,ForeignControl='import '+E.REQUIRED+'\n'),owners)

    def test_imports_require_one_actual_object_and_bind_its_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);one=root/'one';two=root/'two';one.mkdir();two.mkdir()
            source=root/'Module.lean';source.write_text('import ActualOwner\n')
            with self.assertRaisesRegex(ValueError,'missing or multiply'):E.imports(source,[one,two])
            (one/'ActualOwner.olean').write_bytes(b'exact imported object')
            resolution=E.imports(source,[one,two]);self.assertEqual(resolution['ActualOwner']['sha256'],E.R.digest(one/'ActualOwner.olean'))
            E.verify_imports(source,[one,two],resolution)
            with self.assertRaisesRegex(ValueError,'resolution changed'):E.verify_imports(source,[one,two],{})
            (two/'ActualOwner.olean').write_bytes(b'even identical aliases are ambiguous')
            with self.assertRaisesRegex(ValueError,'missing or multiply'):E.imports(source,[one,two])
            source.write_text('import A B\n')
            with self.assertRaisesRegex(ValueError,'Unsupported'):E.imports(source,[one])

    def test_nested_report_is_an_artifact_and_cannot_hide_from_membership(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);(root/'report.json').write_text('own receipt')
            nested=root/'foreign';nested.mkdir();(nested/'report.json').write_text('unowned nested receipt')
            self.assertEqual(E.artifacts(root),{'foreign/report.json':E.R.digest(nested/'report.json')})

    def test_stage_membership_rejects_prefix_cache_and_unowned_objects(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);(root/'All.lean').write_text('source');(root/'modules.json').write_text('["All"]')
            manifest={'stages':[{'out':str(root),'modules':['All']}]}
            E.stage_membership(manifest,completed=False)
            with self.assertRaises(ValueError):E.stage_membership(manifest,completed=True)
            (root/'All.olean').write_bytes(b'fresh object');E.stage_membership(manifest,completed=True)
            with self.assertRaises(ValueError):E.stage_membership(manifest,completed=False)
            (root/'Unowned.olean').write_bytes(b'unowned cached object')
            with self.assertRaises(ValueError):E.stage_membership(manifest,completed=True)

    def test_positive_or_failed_private_receipt_never_claims_final_correspondence(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'report.json'
            for payload in ('{"schema":"pinwheel.streaming-8x4-actual-M-positive.v1","passed":true}',
                '{"schema":"pinwheel.streaming-8x4-actual-M-private.v1","passed":false}',
                '{"schema":"pinwheel.streaming-8x4-actual-M-private.v1","passed":true,"qualified":true}'):
                path.write_text(payload)
                with self.assertRaises(ValueError):E.verify_private(path)


if __name__=='__main__':unittest.main()
