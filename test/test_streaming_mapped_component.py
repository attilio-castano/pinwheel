"""Full-state boundary and physical instance refusals before kernel compilation."""
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_liberty import FF, PREFIX, parse_library
from streaming_mapped_component import generate_component,read_source_trace
import streaming_readback
from test_streaming_mapped_liberty import LIBRARY,TYPES


def fixture():
    cell=lambda kind,directions,connections,parameters={}:dict(type=kind,port_directions=directions,
        connections={pin:[value] for pin,value in connections.items()},parameters=parameters)
    ports=dict(a=dict(direction='input',bits=[2]),clk=dict(direction='input',bits=[3]),z=dict(direction='output',bits=[5]))
    nets=dict(r_state=dict(bits=[4],attributes={}))
    source=dict(modules=dict(top=dict(ports=ports,netnames=nets,cells=dict(
        state=cell('$dff',dict(CLK='input',D='input',Q='output'),dict(CLK=3,D=6,Q=4),dict(CLK_POLARITY='1',WIDTH='1')),
        inv=cell('$not',dict(A='input',Y='output'),dict(A=4,Y=5),dict(A_SIGNED='0',A_WIDTH='1',Y_WIDTH='1')),
        and_=cell('$and',dict(A='input',B='input',Y='output'),dict(A=2,B=5,Y=6),dict(A_SIGNED='0',A_WIDTH='1',B_SIGNED='0',B_WIDTH='1',Y_WIDTH='1'))))))
    mapped=deepcopy(source);m=mapped['modules']['top'];m['cells']['state']=cell(FF,dict(CLK='input',D='input',Q='output',RESET_B='input'),dict(CLK=3,D=6,Q=4,RESET_B='1'))
    for name,kind in [('inv','word_inv'),('and_','word_and')]:m['cells'][name]['type']=kind;m['cells'][name]['parameters']={}
    mapped['modules']['word_inv']=dict(ports=dict(A=dict(direction='input',bits=[2]),Y=dict(direction='output',bits=[3])),cells=dict(inv=cell(PREFIX+'inv_1',dict(A='input',Y='output'),dict(A=2,Y=3))))
    mapped['modules']['word_and']=dict(ports=dict(A=dict(direction='input',bits=[2]),B=dict(direction='input',bits=[3]),Y=dict(direction='output',bits=[4])),cells=dict(and_=cell(PREFIX+'and2_1',dict(A='input',B='input',X='output'),dict(A=2,B=3,X=4))))
    return source,mapped


class ComponentTests(unittest.TestCase):
    def setUp(self):
        self.rb=streaming_readback.backend('core',1)
        self.rb.TOP='top';self.rb.INPUTS={'a':(1,'.initialize')};self.rb.REGISTERS={'r_state':(1,'.valid')};self.rb.OUTPUTS={'z':(1,'.valid')};self.rb.FAMILIES=[]
        self.library=replace(parse_library(LIBRARY,TYPES),pinned=True)
        self.words={'word_inv':dict(module='ActualInv',namespace='Actual.Inv'),'word_and':dict(module='ActualAnd',namespace='Actual.And')}

    def generate(self,source,mapped):
        with tempfile.TemporaryDirectory() as temporary:
            a,b=Path(temporary)/'source.json',Path(temporary)/'mapped.json';a.write_text(json.dumps(source));b.write_text(json.dumps(mapped))
            traced=read_source_trace(self.rb,a);ordinary=self.rb.read_rtl(a)
            self.assertEqual(traced.nodes,ordinary.nodes)
            return generate_component(self.rb,a,b,self.library,self.words,namespace='Actual.Component',raw_module='RawProof',raw_namespace='Actual.Raw')

    def test_actual_instances_all_state_and_output_roots_are_interpreted(self):
        texts,meta=self.generate(*fixture())
        self.assertEqual((meta['source_word_instances'],meta['mapped_ff_bits'],meta['outputs']),(2,1,1))
        self.assertIn('Actual.Inv.actual',texts['MappedComponentGraph'])
        self.assertIn('Actual.And.raw_correct',texts['MappedComponentGraph'])
        self.assertIn('rw [link_cell0]',texts['MappedComponentGraph'])
        self.assertIn('theorem step_correct',texts['MappedComponentProof'])

    def test_actual_top_pin_ff_d_public_output_and_missing_instance_mutations_refuse(self):
        for kind in ('pin','d','q','clock','output','missing','unknown'):
            source,mapped=fixture();m=mapped['modules']['top']
            if kind=='pin':m['cells']['and_']['connections']['A']=[4]
            elif kind=='d':m['cells']['state']['connections']['D']=[5]
            elif kind=='q':m['netnames']['r_state']['bits']=[5]
            elif kind=='clock':m['cells']['state']['connections']['CLK']=[2]
            elif kind=='output':m['ports']['z']['bits']=[6]
            elif kind=='missing':del m['cells']['and_']
            else:m['cells']['and_']['type']='unknown'
            with self.subTest(kind=kind),self.assertRaises(ValueError):self.generate(source,mapped)

    def test_source_signedness_and_changed_state_contract_refuse(self):
        for kind in ('signed','missing-state','init'):
            source,mapped=fixture();m=source['modules']['top']
            if kind=='signed':m['cells']['and_']['parameters']['A_SIGNED']='1'
            elif kind=='missing-state':del m['netnames']['r_state']
            else:m['netnames']['r_state']['attributes']['init']='0'
            with self.subTest(kind=kind),self.assertRaises(ValueError):self.generate(source,mapped)

    def test_supplied_word_body_and_artifact_identities_must_match_actual_bytes(self):
        original=self.words
        for field in ('module_sha256','netlist_sha256'):
            self.words=deepcopy(original);self.words['word_inv'][field]='0'*64
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'Word proof belongs'):
                self.generate(*fixture())
        self.words=original

    def test_unpinned_library_is_not_a_component_certificate(self):
        self.library=replace(self.library,pinned=False)
        with self.assertRaisesRegex(ValueError,'pinned'):self.generate(*fixture())


if __name__=='__main__':unittest.main()
