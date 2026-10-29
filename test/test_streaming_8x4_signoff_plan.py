"""HOST request preparation must preserve official check and target boundaries."""
import ast
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_signoff_plan as P

ROOT=P.P.ROOT
SUPPORT=ROOT/'build/campaigns/8x4-20261022-01/intake/support/tt-support-tools-d66cf179e7bc4d296362ab7e2e3b344dc3c4f665'
TEMPLATE=ROOT/'build/campaigns/8x4-20261022-01/intake/tt_block_8x4_pgvdd.def'


class SignoffPlan(unittest.TestCase):
    @unittest.skipUnless(SUPPORT.is_dir() and TEMPLATE.is_file(),'Campaign official support intake absent')
    def test_exact_actual_official_nine_check_inventory(self):
        lock,sources,checks=P.official_sources(SUPPORT,TEMPLATE)
        self.assertEqual(tuple(checks),P.OFFICIAL_CHECKS)
        self.assertEqual(len(checks),9)
        self.assertIn(str(SUPPORT/'tech/ihp-sg13cmos5l/def/tt_block_8x4_pgvdd.def'),sources)
        self.assertEqual(lock['tiles'],'6x4') # Historical lock remains unchanged.
        self.assertEqual(P.OMITTED,('timing','transistor LVS','antenna','CMOS5L power-pin checking'))

    def test_fixed_view_cannot_escape_its_native_mount(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();(root/'view.gds').write_bytes(b'gds')
            self.assertEqual(P.fixed_path(root,'/work/run/view.gds'),root/'view.gds')
            for value in ('/work/run/../view.gds','/work/inputs/view.gds','relative.gds'):
                with self.subTest(value=value),self.assertRaises(ValueError):P.fixed_path(root,value)

    def test_planner_declares_no_launch_implementation(self):
        source=(ROOT/'scripts/streaming_8x4_signoff_plan.py').read_text();tree=ast.parse(source)
        # Execution belongs to separately reviewed Root-owned runners. This
        # catches accidentally adding a subprocess/container convenience path.
        for node in ast.walk(tree):
            if isinstance(node,ast.Import):self.assertNotIn('subprocess',{value.name for value in node.names})
            if isinstance(node,ast.Call):
                name=node.func.id if isinstance(node.func,ast.Name) else node.func.attr if isinstance(node.func,ast.Attribute) else ''
                self.assertNotIn(name,{'Popen','check_output','run_captured','execv','system','spawnv'})


if __name__=='__main__':unittest.main()
