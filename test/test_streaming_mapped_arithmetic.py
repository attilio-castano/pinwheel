"""Actual arithmetic interfaces and candidate-cut refusal controls.

Synthetic gates here test interpretation/refusal, not arithmetic equivalence;
the actual five-cell FA and 39 mapped arithmetic modules are kernel evidence.
"""
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_arithmetic import arithmetic_source, generate_arithmetic
from streaming_mapped_hierarchy import FA
from streaming_mapped_liberty import PREFIX, parse_library
from test_streaming_mapped_liberty import LIBRARY, TYPES


def fixture():
    def and_gate(a, b, out):
        return dict(type=PREFIX+'and2_1',parameters={},port_directions=dict(A='input',B='input',X='output'),
            connections=dict(A=[a],B=[b],X=[out]))
    fa=dict(ports={name:dict(direction='output' if name in ('S','CO') else 'input',bits=[bit])
        for name,bit in [('A',2),('B',3),('CI',4),('S',5),('CO',6)]},
        cells=dict(sum=and_gate(2,3,5),carry=and_gate(2,4,6)),netnames={})
    word=dict(ports=dict(A=dict(direction='input',bits=[2]),B=dict(direction='input',bits=[3]),
        Y=dict(direction='output',bits=[4])),netnames=dict(carry=dict(bits=['0',5]),sum_bits=dict(bits=[4])),
        cells=dict(bit_0=dict(type=FA,parameters={},port_directions=dict(A='input',B='input',CI='input',S='output',CO='output'),
            connections=dict(A=[2],B=[3],CI=['0'],S=[4],CO=[5]))))
    return dict(modules={FA:fa,'word':word})


class ArithmeticTests(unittest.TestCase):
    def setUp(self): self.library=replace(parse_library(LIBRARY,TYPES),pinned=True)
    def generate(self,data=None,**kwargs):
        return arithmetic_source(fixture() if data is None else data,'word','$add',self.library,
            namespace='Pinwheel.Test.Word',netlist_sha256='0'*64,**kwargs)

    def test_actual_dag_and_y_are_exported_with_scalar_linkage_not_result_premises(self):
        text,meta=self.generate()
        self.assertIn('def actual (A B : BitVec 1)',text)
        self.assertIn('leaf.sum',text)
        self.assertIn('def actualSum : Expr 3',text)
        self.assertIn('theorem leaf_correct',text)
        self.assertIn('theorem linked ',text)
        self.assertIn('theorem correct ',text)
        self.assertIn('Ripple.Linked.add_correct',text)
        self.assertEqual((meta['width'],meta['actual_fa_instances']),(1,1))
        self.assertEqual(len(meta['fa_module_sha256']),64)
        self.assertNotIn('sorry',text)
        self.assertNotIn('native_decide',text)
        self.assertNotIn('axiom',text)

    def test_missing_extra_or_wrong_carry_and_sum_cut_shapes_refuse(self):
        for name,values in [('carry',[]),('carry',['0']),('carry',['0',5,6]),('sum_bits',[]),('sum_bits',[4,5])]:
            data=fixture();data['modules']['word']['netnames'][name]['bits']=values
            with self.subTest(name=name,values=values),self.assertRaises(ValueError):self.generate(data)

    def test_unknown_gate_parameter_and_changed_fa_port_refuse(self):
        for mode in ('gate','parameter','fa-port','ff'):
            data=fixture();entry=data['modules']['word']['cells']['bit_0']
            if mode=='gate':entry['type']='invented_semantics'
            elif mode=='parameter':entry['parameters']={'UNTRUSTED':'1'}
            elif mode=='fa-port':entry['connections']['CI']=[2,3]
            else:entry['type']=PREFIX+'dfrbpq_1'
            with self.subTest(mode=mode),self.assertRaises(ValueError):self.generate(data)

    def test_namespace_and_identity_cannot_inject_lean_source(self):
        for options in [dict(namespace='Bad; axiom x'),dict(fa_namespace='Bad\nName'),
                dict(fa_module='bad file'),dict(netlist_sha256='"\n')]:
            args=dict(namespace='Good',netlist_sha256='0'*64);args.update(options)
            with self.subTest(options=options),self.assertRaises(ValueError):
                arithmetic_source(fixture(),'word','$add',self.library,**args)

    def test_duplicate_json_refuses_before_proof_generation(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'mapped.json';path.write_text('{"modules":{},"modules":{}}')
            with self.assertRaisesRegex(ValueError,'Duplicate'):
                generate_arithmetic(path,self.library,'word','$add',namespace='Good')


if __name__=='__main__':unittest.main()
