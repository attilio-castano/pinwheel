"""GEN04 adaptation preserves its exact mathematical generation body."""
import ast
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_final_m as M


class MTests(unittest.TestCase):
    def fixture(self):return (ROOT/'test/fixtures/streaming_8x4/GEN04-generate.py.txt').read_bytes()

    def test_all_mathematical_functions_and_complete_generation_body_are_unchanged(self):
        original=self.fixture();text,diff=M.adapted_generator(original)
        old_tree,new_tree=ast.parse(original),ast.parse(text)
        old={node.name:node for node in old_tree.body if isinstance(node,ast.FunctionDef)}
        new={node.name:node for node in new_tree.body if isinstance(node,ast.FunctionDef)}
        self.assertEqual(set(old),set(new))
        for name in old.keys()-{'physical_target','_generate'}:
            self.assertEqual(ast.dump(old[name]),ast.dump(new[name]),name)
        start='    library=load_library(cfg[\'library\']);'
        end="    F.require(R.validate_positive_stages(positive,cfg,regeneration['modules'],positive_path,parent_path=parent_path)[0]==binding,"
        exact_body=original.decode().split(start,1)[1].split(end,1)[0]
        self.assertIn(start+exact_body,text)
        self.assertIn('all6039_state_bijection=True,all24_public_endpoints=True',text)
        self.assertIn("add('required',CO.generate_required(cts_count=cts_count))",text)
        self.assertIn("add('final-audit',{'PhysicalGRTFinalAudit':audit_source(owners)})",text)
        self.assertIn('pinwheel.streaming-8x4-actual-target-M.v1',text)
        self.assertIn('immutable-GEN04/generate.py',diff)

    def test_changed_original_generator_or_adaptation_anchor_rejects(self):
        with self.assertRaisesRegex(ValueError,'original producer changed'):M.adapted_generator(self.fixture()+b'\n')
        with self.assertRaisesRegex(ValueError,'anchor changed'):M.replace_once('twice twice','twice','new')
        with self.assertRaisesRegex(ValueError,'anchor changed'):M.replace_once('absent','old','new')

    def test_prefix_or_old_schema_preparation_cannot_be_promoted(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'prepared.json'
            for payload in ('{"schema":"pinwheel.streaming-tt-actual-M-preparation.v1","passed":true}',
                '{"schema":"pinwheel.streaming-8x4-actual-M-preparation.v1","passed":false}',
                '{"schema":"pinwheel.streaming-8x4-actual-M-preparation.v1","passed":true,"qualified":false,"native_executed":true}'):
                path.write_text(payload)
                with self.assertRaises(ValueError):M.verify(path)


if __name__=='__main__':unittest.main()
