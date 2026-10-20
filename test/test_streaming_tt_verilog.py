"""Narrow physical grammar normalization and exact structural binding controls."""
from copy import deepcopy
from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_verilog import flat_labels, normalize, port_shapes, structure
from streaming_mapped_liberty import parse_library
from streaming_mapped_netlist import parse_mapped
from test_streaming_mapped_liberty import LIBRARY,TYPES
from test_streaming_mapped_netlist import fixture


class PhysicalVerilogTests(unittest.TestCase):
    def test_full_public_port_shape_includes_range_direction_and_signedness(self):
        data=fixture();expected=port_shapes(data,'top')
        for key,value in [('offset',1),('upto',1),('signed',1),('direction','output')]:
            changed=deepcopy(data);changed['modules']['top']['ports']['a'][key]=value
            with self.subTest(key=key):self.assertNotEqual(expected,port_shapes(changed,'top'))

    def test_flat_semantic_aliases_cover_every_actual_ff_and_refuse_metadata_faults(self):
        library=parse_library(LIBRARY,TYPES);data=fixture();body=data['modules']['top']
        model=deepcopy(body['cells']['state']);del body['cells']['state']
        qs=list(range(100,6139))
        for index,q in enumerate(qs):
            cell=deepcopy(model);cell['connections']['Q']=[q];body['cells']['ff'+str(index)]=cell
        body['cells']['invert']['connections']['A']=[qs[0]]
        body['netnames']={'engine.frontend.r_a':dict(bits=qs[:1]),'engine.core.r_b':dict(bits=qs[1:])}
        source=dict(modules=dict(top=dict(cells=dict(engine=dict(type='package'))),
            package=dict(cells=dict(frontend=dict(type='front'),core=dict(type='core'))),
            front=dict(netnames=dict(r_a=dict(bits=[0]))),core=dict(netnames=dict(r_b=dict(bits=list(range(6038)))))))
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'source.json';path.write_text(json.dumps(source))
            candidate=dict(netlist=str(path),top='top',component_tops={'frontend':'front','core-d2':'core'},
                semantic_q_map=dict(rows=[dict(component='frontend',register='r_a',index=0)]+
                    [dict(component='core-d2',register='r_b',index=i) for i in range(6038)]))
            graph=parse_mapped(data,'top',library);labels,rows=flat_labels(candidate,data,graph,library)
            self.assertEqual(len(labels),6039);self.assertEqual(len(rows),6039)
            self.assertEqual(set(labels),graph.state_bits)
            for fault in ('missing','width','literal','duplicate','not_q','source_bit_missing'):
                changed=deepcopy(data);other=deepcopy(candidate);aliases=changed['modules']['top']['netnames']
                if fault=='missing':del aliases['engine.core.r_b']
                elif fault=='width':aliases['engine.core.r_b']['bits'].pop()
                elif fault=='literal':aliases['engine.core.r_b']['bits'][0]='1'
                elif fault=='duplicate':aliases['engine.core.r_b']['bits'][0]=qs[0]
                elif fault=='not_q':aliases['engine.core.r_b']['bits'][0]=2
                else:other['semantic_q_map']['rows'].pop()
                with self.subTest(fault=fault),self.assertRaises(ValueError):flat_labels(other,changed,graph,library)

    def test_only_internal_wire_modifier_changes_and_comments_remain_exact(self):
        before='// signed always\n/*\n wire signed [2:0] comment;\n*/\n  wire signed [31:0] ghost;\nwire [1:0] plain;\nassign plain = {ghost[0], 1\'h0};\n'
        after,report=normalize(before)
        self.assertEqual(after,before.replace('  wire signed [31:0]','  wire [31:0]'))
        self.assertEqual(report,dict(removed_internal_wire_signed=1,declaration_lines=[5]))
        self.assertEqual(normalize(after)[0],after)

    def test_signed_ports_behavioral_blocks_and_other_signed_uses_refuse(self):
        for source in ('input signed [2:0] a;','output signed [2:0] a;',
                'wire signed a;','assign x = $signed(y);','always @(posedge clk) q <= d;',
                'initial q = 0;','reg [2:0] a;','function f; endfunction','generate endgenerate'):
            with self.subTest(source=source),self.assertRaises(ValueError): normalize(source)

    def test_actual_cell_state_and_io_structures_survive_names_and_wire_renumbering(self):
        library=parse_library(LIBRARY,TYPES);source=fixture();other=deepcopy(source)
        body=other['modules']['top']
        for port in body['ports'].values():port['bits']=[b+1000 if type(b) is int else b for b in port['bits']]
        for cell in body['cells'].values():
            for pin,bits in cell['connections'].items():cell['connections'][pin]=[b+1000 if type(b) is int else b for b in bits]
        body['cells']={name+'_renamed':cell for name,cell in body['cells'].items()}
        graph=parse_mapped(source,'top',library);changed=parse_mapped(other,'top',library);pool={}
        label=('core','r_count',0)
        expected=structure(graph,{next(iter(graph.state_bits)):label},pool)
        self.assertEqual(expected,structure(changed,{next(iter(changed.state_bits)):label},pool))
        for mode in ('d','output','pin','port_shape','unused_gate','state_label'):
            value=deepcopy(source);module=value['modules']['top'];labels={next(iter(graph.state_bits)):label}
            if mode=='d':module['cells']['state']['connections']['D']=[2]
            elif mode=='output':module['ports']['z']['bits'][0]='1'
            elif mode=='pin':module['cells']['combine']['connections']['A']=['1']
            elif mode=='port_shape':module['ports']['a']['bits'].append('0')
            elif mode=='unused_gate':
                gate=deepcopy(module['cells']['combine']);gate['connections']['Y']=[2000];module['cells']['unused']=gate
            else:labels={next(iter(graph.state_bits)):('core','r_wrong',0)}
            with self.subTest(mode=mode):
                try: actual=structure(parse_mapped(value,'top',library),labels,pool)
                except ValueError:continue
                self.assertNotEqual(actual,expected)
        with self.assertRaisesRegex(ValueError,'state binding'):structure(graph,{},pool)


if __name__=='__main__':unittest.main()
