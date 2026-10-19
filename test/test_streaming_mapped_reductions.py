"""Mapped reductions follow physical functions; word labels supply no behavior.

Small synthetic fixtures exercise interpretation/refusal. Actual wide words
are independently kernel-checked in the artifact campaign, not by these tests.
"""
from dataclasses import replace
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_certificate import expressions
from streaming_mapped_liberty import PREFIX, eval_boolean, parse_library
from streaming_mapped_netlist import parse_mapped
from streaming_mapped_reductions import generate_reduction, reduction_source
from test_streaming_mapped_liberty import LIBRARY, TYPES


def fixture():
    def invert(source, output):
        return dict(type=PREFIX+'inv_1',parameters={},port_directions=dict(A='input',Y='output'),
            connections=dict(A=[source],Y=[output]))
    conjunction = dict(type=PREFIX+'and2_1',parameters={},port_directions=dict(A='input',B='input',X='output'),
        connections=dict(A=[4],B=[5],X=[6]))
    return dict(modules=dict(word=dict(ports=dict(A=dict(direction='input',bits=[2,3]),
        Y=dict(direction='output',bits=[6])),netnames={},
        cells=dict(first=invert(2,4),second=invert(3,5),combine=conjunction))))


class ReductionTests(unittest.TestCase):
    def setUp(self): self.library = replace(parse_library(LIBRARY,TYPES),pinned=True)

    def generate(self,data=None,kind='$logic_not',**options):
        arguments=dict(namespace='Pinwheel.Test.Reduction',netlist_sha256='0'*64)
        arguments.update(options)
        return reduction_source(fixture() if data is None else data,'word',kind,self.library,**arguments)

    def test_physical_functions_and_output_are_explicit(self):
        data=fixture(); graph=parse_mapped(data,'word',self.library,combinational=True)
        variables,outputs=expressions(graph,('A',))
        for a in (False,True):
            for b in (False,True):
                self.assertEqual(eval_boolean(outputs['Y'][0],dict(zip(variables,(a,b)))),not(a or b))
        text,metadata=self.generate(data)
        self.assertIn('def node0 (A : BitVec 2)',text)
        self.assertIn('def actualBool (A : BitVec 2)',text)
        self.assertIn('def actual (A : BitVec 2) : BitVec 1',text)
        self.assertIn('theorem bool_correct',text)
        self.assertIn('theorem correct',text)
        self.assertIn('tree.logic_not tree_complete A',text)
        self.assertIn('all_goals ac_rfl',text)
        self.assertEqual((metadata['width'],metadata['actual_primitive_gates']),(2,3))
        self.assertEqual(len(metadata['module_sha256']),64)
        for forbidden in ('sorry','axiom','native_decide','bv_decide'):
            self.assertNotIn(forbidden,text)

    def test_wrong_expected_operator_does_not_replace_interpreted_function(self):
        original,_=self.generate(kind='$logic_not')
        wrong,_=self.generate(kind='$reduce_or')
        self.assertEqual(original.split('def tree :')[0],wrong.split('def tree :')[0])
        self.assertIn('tree.reduce_or tree_complete A',wrong)
        self.assertNotEqual(original,wrong)

    def test_changed_actual_y_is_preserved_even_when_it_invalidates_expected_logic(self):
        data=fixture();data['modules']['word']['ports']['Y']['bits']=[2]
        graph=parse_mapped(data,'word',self.library,combinational=True)
        variables,outputs=expressions(graph,('A',))
        self.assertFalse(eval_boolean(outputs['Y'][0],dict(zip(variables,(False,False)))))
        text,_=self.generate(data)
        self.assertIn('def actualBool (A : BitVec 2) : Bool := A.getLsbD 0',text)
        self.assertIn('tree.logic_not tree_complete A',text)

    def test_interface_alias_width_extra_port_and_unsupported_operator_refuse(self):
        for change in ('wide-output','extra-input','alias','clock','wrong-op'):
            data=fixture();module=data['modules']['word']
            if change=='wide-output':module['ports']['Y']['bits']=[6,6]
            elif change=='extra-input':module['ports']['B']=dict(direction='input',bits=[7,8])
            elif change=='alias':module['ports']['A']['bits']=[2,2]
            elif change=='clock':module['ports']['clk']=dict(direction='input',bits=[9])
            with self.subTest(change=change),self.assertRaises(ValueError):
                self.generate(data,kind='$add' if change=='wrong-op' else '$logic_not')

    def test_eq_operand_width_mismatch_and_unpinned_library_refuse(self):
        data=fixture();data['modules']['word']['ports']['B']=dict(direction='input',bits=[7])
        with self.assertRaises(ValueError):self.generate(data,kind='$eq')
        with self.assertRaises(ValueError):
            reduction_source(fixture(),'word','$logic_not',parse_library(LIBRARY,TYPES),
                namespace='Good',netlist_sha256='0'*64)

    def test_reduce_and_uses_all_bits_and_raw_allones_constant(self):
        data=fixture()
        data['modules']['word']['cells']['combine']['connections']=dict(A=[2],B=[3],X=[6])
        graph=parse_mapped(data,'word',self.library,combinational=True)
        variables,outputs=expressions(graph,('A',))
        for a in (False,True):
            for b in (False,True):
                self.assertEqual(eval_boolean(outputs['Y'][0],dict(zip(variables,(a,b)))),a and b)
        text,_=self.generate(data,kind='$reduce_and')
        self.assertIn('tree.reduce_and tree_complete A',text)
        self.assertIn('theorem raw_correct',text)
        self.assertIn('decide (A = 3#2)',text)

    def test_namespace_module_and_identity_source_injection_refuse(self):
        for options in (dict(namespace='Bad; arbitrary'),dict(netlist_sha256='"\n'),dict(namespace='A\nB')):
            with self.subTest(options=options),self.assertRaises(ValueError):self.generate(**options)
        with self.assertRaises(ValueError):
            reduction_source(fixture(),'word"\n','$logic_not',self.library,namespace='Good',netlist_sha256='0'*64)

    def test_duplicate_json_and_changed_artifact_refuse(self):
        import json
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'mapped.json';path.write_text('{"modules":{},"modules":{}}')
            with self.assertRaisesRegex(ValueError,'Duplicate'):
                generate_reduction(path,self.library,'word','$logic_not',namespace='Good')
            content=json.dumps(fixture()).encode();path.write_bytes(content)
            with patch.object(Path,'read_bytes',side_effect=[content,content+b' ']):
                with self.assertRaisesRegex(ValueError,'changed'):
                    generate_reduction(path,self.library,'word','$logic_not',namespace='Good')


if __name__=='__main__':unittest.main()
