"""Imported closure, resolved dynamic paths and immutable staged source tests."""
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_intake as I


class IntakeTests(unittest.TestCase):
    def test_transitive_function_import_and_literal_dynamic_dependency(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);(root/'scripts').mkdir()
            (root/'scripts/a.py').write_text('import json\nfrom b import f\ndef g():\n import c\n')
            (root/'scripts/b.py').write_text('def f(): pass\n')
            (root/'scripts/c.py').write_text('import runpy\nrunpy.run_path(str(ROOT / "scripts/d.py"))\n')
            (root/'scripts/d.py').write_text('value=1\n')
            result=I.dependency_closure(root,['scripts/a.py'])
            self.assertEqual(result['files'],['scripts/a.py','scripts/b.py','scripts/c.py','scripts/d.py'])
            self.assertIn('json',result['external_imports'])
            self.assertEqual(result['dynamic_imports'],{'scripts/c.py':['scripts/d.py']})

    def test_unknown_dynamic_import_escaping_path_and_alias_refuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);(root/'scripts').mkdir();p=root/'scripts/a.py'
            for source in ['__import__(module)','importlib.import_module(name)',
                    'runpy.run_path(path)','runpy.run_path(str(ROOT / "scripts/../outside.py"))']:
                p.write_text(source)
                with self.subTest(source=source),self.assertRaises(ValueError): I.dependency_closure(root,['scripts/a.py'])
            p.write_text('import b\n');(root/'scripts/b.py').symlink_to(p)
            with self.assertRaises(ValueError): I.dependency_closure(root,['scripts/a.py'])

    def test_snapshot_is_exact_fresh_and_readonly(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);(root/'scripts').mkdir();(root/'scripts/a.py').write_text('value=1\n')
            destination=root/'snapshot'
            I.stage_sources(root,destination,['scripts/a.py'],lambda path:path.read_bytes())
            self.assertEqual((destination/'scripts/a.py').read_bytes(),(root/'scripts/a.py').read_bytes())
            self.assertEqual((destination/'scripts/a.py').stat().st_mode & 0o222,0)
            with self.assertRaises(ValueError): I.stage_sources(root,destination,['scripts/a.py'],lambda path:path.read_bytes())

    def test_real_rc_and_completion_import_closure_is_declared(self):
        result=I.dependency_closure(ROOT,['scripts/streaming_tt_rc.py','scripts/streaming_tt_pdk.py'])
        for name in ['scripts/physical_route_intake.py','scripts/physical_checkpoint.py',
                'scripts/validation_run.py','scripts/process_group.py','scripts/streaming_tt_physical.py']:
            self.assertIn(name,result['files'])
        self.assertNotIn('scripts/streaming_tt_sta.py',result['files'])


if __name__ == '__main__': unittest.main()
