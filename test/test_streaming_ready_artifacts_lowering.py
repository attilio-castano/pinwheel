"""Metadata-only lowering boundaries; no CIRCT, Yosys or Lean execution."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_ready_artifacts as A


class LoweringInputTests(unittest.TestCase):
    def test_exact_header_copy_preserves_every_typed_body_byte(self):
        with tempfile.TemporaryDirectory() as name:
            root=Path(name);original=root/'source.mlir';lower=root/'lower.mlir'
            body=b'\n  // typed hints and original SSA\n  %v = comb.and %a, %b : i1\n}\n'
            original.write_bytes(A.LOWERING_HEADER+body)
            receipt=A.lowering_copy(original,lower)
            self.assertEqual(original.read_bytes(),A.LOWERING_HEADER+body)
            self.assertEqual(lower.read_bytes(),A.BALANCED_LOWERING_HEADER+body)
            self.assertEqual(lower.read_bytes().replace(A.BALANCED_LOWERING_HEADER,A.LOWERING_HEADER),original.read_bytes())
            self.assertEqual(receipt['original_mlir']['sha256'],hashlib.sha256(original.read_bytes()).hexdigest())
            self.assertEqual(receipt['lowering_copy']['sha256'],hashlib.sha256(lower.read_bytes()).hexdigest())
            self.assertEqual(receipt['original_hints_authority'],str(original.resolve()))
            self.assertEqual(receipt['maximum_number_of_terms_per_expression'],1)
            self.assertFalse(receipt['canonicalize'])

    def test_missing_duplicate_prepatched_or_conflicting_header_refused(self):
        with tempfile.TemporaryDirectory() as name:
            root=Path(name);original=root/'source.mlir';lower=root/'lower.mlir'
            pristine=A.LOWERING_HEADER+b'\n}\n'
            for bad in (b'',b'module {\n}\n',pristine+pristine,A.BALANCED_LOWERING_HEADER+b'\n}\n',
                        pristine+b'// maximumNumberOfTermsPerExpression=99\n',b'// prefix\n'+pristine):
                original.write_bytes(bad)
                with self.subTest(bad=bad),self.assertRaises(RuntimeError):A.lowering_copy(original,lower)
                self.assertFalse(lower.exists())

    def test_existing_or_alias_inputs_preserved_and_refused(self):
        with tempfile.TemporaryDirectory() as name:
            root=Path(name);original=root/'source.mlir';original.write_bytes(A.LOWERING_HEADER+b'\n}\n')
            alias=root/'alias';alias.symlink_to(original)
            for source,target in ((alias,root/'new'),(original,original),(original,alias)):
                with self.subTest(source=source,target=target),self.assertRaises(RuntimeError):A.lowering_copy(source,target)
            target=root/'existing';target.write_bytes(b'preserved')
            with self.assertRaises(RuntimeError):A.lowering_copy(original,target)
            self.assertEqual(target.read_bytes(),b'preserved')

    def test_component_reads_original_hints_and_freezes_copy_before_actual_argv(self):
        with tempfile.TemporaryDirectory() as name:
            root=Path(name);emitted=root/'emitted';emitted.mkdir();out=root/'component'
            for file in ('core.mlir','frontend.mlir'): (emitted/file).write_bytes(A.LOWERING_HEADER+b'\n}\n')
            for file in ('assembly.json','frontend-assembly.json'): (emitted/file).write_text('{}')
            frozen={};hints=[];calls=[]
            class Gate:
                @staticmethod
                def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
                @staticmethod
                def freeze_inputs(report,unused,paths):
                    frozen.update({str(p):Gate.digest(p) for p in paths});report['proof_input_sha256_before']=dict(frozen)
                @staticmethod
                def assert_hashes(unused,expected):
                    if any(Gate.digest(path)!=value for path,value in expected.items()):raise RuntimeError('Changed frozen input')
                @staticmethod
                def write_json(path,value):Path(path).write_text(json.dumps(value))
            backend=SimpleNamespace(read_hints=lambda path:hints.append(path) or object())
            def run(argv,label,**options):
                calls.append(argv);self.assertEqual(label,'circt-export')
                self.assertNotIn('--canonicalize',argv);self.assertEqual(argv[2:],list(A.LOWERING_PASSES))
                self.assertIn(str(argv[1]),frozen);self.assertIn(str(out/'lowering-input.json'),frozen)
                self.assertEqual(Path(argv[1]).read_bytes(),A.BALANCED_LOWERING_HEADER+b'\n}\n')
                raise RuntimeError('Stopped before any Native invocation')
            with patch.object(A.adapter,'backend',return_value=backend),patch.object(A.adapter,'check_interface'),\
                    patch.object(A.adapter.shared,'validate_graph',side_effect=lambda unused,value:value):
                with self.assertRaisesRegex(RuntimeError,'Stopped before any Native'):
                    A.component('frontend',1,emitted,out,{'circt':'/selected/circt'},run,gate=Gate())
            self.assertEqual(hints,[emitted/'frontend.mlir']);self.assertEqual(len(calls),1)
            receipt=json.loads((out/'component-report.json').read_text())
            self.assertFalse(receipt['passed']);self.assertTrue(receipt['frozen_inputs_unchanged'])
            self.assertEqual(receipt['lowering_input']['original_hints_authority'],str((emitted/'frontend.mlir').resolve()))
            self.assertEqual(set(Path(p).name for p in receipt['emitted_input_sha256_before']),
                {'core.mlir','frontend.mlir','assembly.json','frontend-assembly.json'})


if __name__=='__main__':unittest.main()
