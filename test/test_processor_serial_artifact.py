"""Fail-closed receipt and semantic rejection controls for serial artifact checks."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
sp=importlib.util.spec_from_file_location('serial_negatives',ROOT/'scripts/check-processor-serial-artifact-negatives.py')
n=importlib.util.module_from_spec(sp);sp.loader.exec_module(n)
sp=importlib.util.spec_from_file_location('serial_driver_tests',ROOT/'test/test_processor_serial_driver.py')
f=importlib.util.module_from_spec(sp);sp.loader.exec_module(f)

class ArtifactTests(unittest.TestCase):
    def bundle(self,base):
        rows=[]
        for d in n.positive.checks.MATRIX:
            dr=base/f'serial-{d}';dr.mkdir()
            for name in ('serial.mlir','serial.sv','before-pmuxtree.json','import.json','import.ys'):(dr/name).write_text('fixture')
            (dr/'interface.json').write_text(json.dumps(f.fixture(d)))
            for module in ('Design','Graphs','LocalProofs','LocalProofs000','Links','Proof','SerialTrace','Audit'):
                for suffix in ('.lean','.olean','.log'):(dr/(module+suffix)).write_text('standard axioms only')
            rows.append(dict(divisor=d,typed_registers=14,typed_outputs=13,endpoints=27,local_proof_units=1,**dict.fromkeys(n.FLAGS,True)))
        report=dict(schema=1,status='passed',source_sha256={},tool_manifest={},tool_sha256={},configurations=rows,commands=[dict(exit_code=0)],
                    artifact_sha256={str(p.relative_to(base)):n.sha(p) for p in base.rglob('*') if p.is_file()})
        receipt=base/'report.json';receipt.write_text(json.dumps(report));return receipt,report

    def test_full_positive_and_incomplete_receipts(self):
        with tempfile.TemporaryDirectory() as temp,patch.object(n.positive,'sources',return_value={}):
            receipt,report=self.bundle(Path(temp));self.assertEqual(n.verify_positive(receipt,{},{}),receipt.parent/'serial-4')
            variants=[]
            for key,value in (('schema',True),('status','running'),('source_sha256',{'wrong':'x'}),('tool_sha256',{'wrong':'x'}),('commands',[])):
                x=copy.deepcopy(report);x[key]=value;variants.append(x)
            for key,value in (('exit_code',False),('exit_code',1),('expected_failure',True),('error','timeout')):
                x=copy.deepcopy(report);x['commands'][0][key]=value;variants.append(x)
            x=copy.deepcopy(report);x['configurations'].pop();variants.append(x)
            for flag in n.FLAGS:
                x=copy.deepcopy(report);x['configurations'][0][flag]=False;variants.append(x)
            for key,value in (('endpoints',26),('typed_registers',True),('local_proof_units',0)):
                x=copy.deepcopy(report);x['configurations'][0][key]=value;variants.append(x)
            x=copy.deepcopy(report);x['artifact_sha256'].pop(next(iter(x['artifact_sha256'])));variants.append(x)
            for x in variants:
                receipt.write_text(json.dumps(x))
                with self.subTest(x=x),self.assertRaises(ValueError):n.verify_positive(receipt,{},{})
            receipt.write_text(json.dumps(report));(receipt.parent/'serial-4/Proof.lean').write_text('corruption')
            with self.assertRaises(ValueError):n.verify_positive(receipt,{},{})

    def test_paths_escape_and_alias_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp)
            for name in ('','../outside','/tmp/outside','x/../outside','x//file','./file'):
                with self.subTest(name=name),self.assertRaises(ValueError):n.contained(base,name)
            (base/'alias').symlink_to('/tmp')
            with self.assertRaises(ValueError):n.contained(base,'alias/outside')

    def test_only_semantic_lean_failures_count(self):
        self.assertEqual(n.semantic_errors('X.lean:1:2: error: unsolved goals\n'),['unsolved goals'])
        for log in ('','timeout','X.lean:1:2: error: unknown identifier\n','X.lean:1:2: error: maximum recursion depth reached\n',
                    'X.lean:1:2: error: unsolved goals\nX.lean:3:1: error: type mismatch\n'):
            with self.assertRaises(RuntimeError):n.semantic_errors(log)

    def test_slice_proof_search_preserves_statements_and_stays_within_headers(self):
        from readback_slice_proofs import prove_slice_bounds
        header = "theorem local_0 (x0 : BitVec 9) :\n    BitVec.ofBool (decide (x0.toNat < 32)) = BitVec.ofBool (decide ((x0.extractLsb' 5 4) = (0#4))) := by\n"
        body = "  all_goals first\n  | rfl\n  | grind\n"
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'LocalProofs000.lean';path.write_text(header+body+"\nend X\n")
            self.assertEqual(prove_slice_bounds(Path(temp),['LocalProofs000']),1)
            self.assertTrue(path.read_text().startswith(header));self.assertIn('have slice_bound := x0.isLt',path.read_text())
            # A malformed header must not swallow the next unrelated declaration.
            malformed="theorem local_99 (x0 : BitVec 9) broken\n"+header.replace('(x0 : BitVec 9)','(x0 : BitVec 9) (x1 : BitVec 9)')
            path.write_text(malformed+body+"\nend X\n")
            self.assertEqual(prove_slice_bounds(Path(temp),['LocalProofs000']),0)
            self.assertEqual(path.read_text(),malformed+body+"\nend X\n")

    def test_controls_have_active_independent_nonidentical_values(self):
        data=f.fixture()
        source='module processor_serial();\n'+'\n'.join([f"assign {p['name']} = '0;" for p in data['outputs']]+
            [f"always @(posedge clk) {p['name']} <= {p['name']};" for p in data['registers']])+'\nendmodule\n'
        ref=n.positive.checks.reference
        for name in n.CONTROLS:
            changed,endpoint,kind=n.mutation(source,data,name)
            self.assertNotEqual(source,changed)
            pins,state,want,bad,_=n.witness_case(name);self.assertNotEqual(want,bad)
            ports=data['outputs' if kind=='output' else 'registers'];index=next(k for k,p in enumerate(ports) if p['name']==endpoint)
            self.assertEqual((ref.output(4,pins,state) if kind=='output' else ref.step(4,pins,state))[index],want)
            if name=='invalid-selector-success':self.assertEqual(ref.output(4,pins,state)[1:3],[1,2])
            elif name=='complete-during-reset':self.assertTrue(pins['reset']);self.assertEqual(ref.output(4,pins,state)[9],0)
            else:self.assertTrue(pins['request_valid']);self.assertFalse(pins['reset'])

if __name__=='__main__':unittest.main()
