"""Static specialization boundaries and proof-premise refusal controls."""
from copy import deepcopy
from dataclasses import replace
import json
import os
from pathlib import Path
import sys
import shutil
import subprocess
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_mapped_hierarchy import binary
from streaming_mapped_liberty import PREFIX, parse_library
from streaming_tt_optimize import fixed_operands, specialized_source, mapping_script
from streaming_tt_opt_certificate import add_static_premises, generate_specialized, load_leaf, replace_once
from test_streaming_mapped_liberty import LIBRARY,TYPES


def fixture():
    ports=dict(clk=dict(direction='input',bits=[2]),a=dict(direction='input',bits=[3,4]),
        s=dict(direction='input',bits=[5]),y=dict(direction='output',bits=[6,7]))
    mux=dict(type='$mux',parameters=dict(WIDTH=binary(2)),attributes={},
        port_directions=dict(A='input',B='input',S='input',Y='output'),
        connections=dict(A=[3,4],B=['0','0'],S=[5],Y=[6,7]))
    ff=dict(type='$dff',parameters=dict(CLK_POLARITY=binary(1),WIDTH=binary(2)),attributes={},
        port_directions=dict(CLK='input',D='input',Q='output'),connections=dict(CLK=[2],D=[6,7],Q=[8,9]))
    return dict(modules=dict(top=dict(ports=ports,cells=dict(mux=mux,state=ff),
        netnames=dict(r_state=dict(bits=[8,9],attributes={})))) )


class OptimizeTests(unittest.TestCase):
    def test_specialization_keeps_exact_all_state_and_word_boundary(self):
        original=fixture();before=deepcopy(original)
        data,meta=specialized_source(original,'top')
        self.assertEqual(original,before)
        main=data['modules']['top'];raw=original['modules']['top']
        self.assertEqual(main['ports'],raw['ports'])
        self.assertEqual(main['cells']['state']['connections'],raw['cells']['state']['connections'])
        self.assertEqual(main['cells']['mux']['connections'],raw['cells']['mux']['connections'])
        name=main['cells']['mux']['type'];leaf=data['modules'][name]
        self.assertEqual(set(leaf['ports']),{'A','B','S','Y'})
        self.assertEqual(leaf['ports']['B']['bits'],[4,5])
        self.assertEqual(leaf['cells']['operator']['connections']['B'],['0','0'])
        self.assertEqual(meta['instances']['mux']['fixed_operands'],{'B':'00'})
        self.assertFalse(meta['equivalence_proved'])

    def test_only_whole_literals_specialize_and_unknowns_never_become_constants(self):
        cell=fixture()['modules']['top']['cells']['mux']
        for bits in ([3,'0'],['x','0'],['z','1'],[False,'0']):
            cell['connections']['B']=bits
            self.assertEqual(fixed_operands(cell),{})

    def test_small_comparison_bound_prevents_large_enumeration(self):
        cell=fixture()['modules']['top']['cells']['mux']
        cell['type']='$gt';cell['connections']['A']=list(range(10,19));cell['connections']['B']=['0']*9
        self.assertEqual(fixed_operands(cell),{})
        cell['connections']['A']=list(range(10,18));cell['connections']['B']=['0']*8
        self.assertEqual(fixed_operands(cell),{'B':'00000000'})

    def test_same_constant_and_shape_share_module_distinct_constants_do_not(self):
        data=fixture();cells=data['modules']['top']['cells'];cells['same']=deepcopy(cells['mux']);cells['other']=deepcopy(cells['mux']);cells['other']['connections']['B']=['1','0']
        transformed,meta=specialized_source(data,'top');cells=transformed['modules']['top']['cells']
        self.assertEqual(cells['mux']['type'],cells['same']['type'])
        self.assertNotEqual(cells['mux']['type'],cells['other']['type'])
        self.assertEqual((meta['specialized_instances'],meta['specialized_modules']),(3,2))

    def test_mapping_has_no_ff_optimization_fsm_retiming_or_resynthesis(self):
        script=mapping_script('source.json','top','/tmp/candidate','cells.lib','abc')
        self.assertIn('setattr -set keep 1 t:$dff',script)
        self.assertIn('setattr -set keep 1 w:r_*',script)
        self.assertIn('opt_expr',script)
        for forbidden in ('opt_dff','opt_clean','fsm','abc -dff','synth','retime'):
            self.assertNotIn(forbidden,script)

    def test_static_kernel_premises_attach_only_to_exact_generated_call(self):
        text='  exact Actual.Word.raw_correct A B S\n  exact Other.raw_correct A B S\n'
        output=add_static_premises({'Graph':text},{'word':dict(namespace='Actual.Word',fixed_operands={'B':'00'})})['Graph']
        self.assertIn('Actual.Word.raw_correct A B S (by rfl)',output)
        self.assertIn('Other.raw_correct A B S\n',output)
        self.assertEqual(output.count('(by rfl)'),1)

    def test_proof_seam_must_be_exactly_once(self):
        for text in ('none','seam seam'):
            with self.assertRaises(ValueError):replace_once(text,'seam','replacement')

    def test_empty_cone_requires_actual_direct_output_no_guessed_driver(self):
        library=replace(parse_library(LIBRARY,TYPES),pinned=True)
        body=dict(ports=dict(A=dict(direction='input',bits=[2]),B=dict(direction='input',bits=[3]),
            Y=dict(direction='output',bits=['1'])),cells={})
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'mapped.json';path.write_text(json.dumps(dict(modules=dict(leaf=body))))
            graph=load_leaf(path,'leaf',library);self.assertEqual(graph.outputs,{'Y':('1',)})
            for kind in ('driver','unknown','alias','blackbox'):
                bad=deepcopy(body)
                if kind=='driver':bad['ports']['Y']['bits']=[99]
                elif kind=='unknown':bad['ports']['Y']['bits']=['x']
                elif kind=='alias':bad['ports']['B']['bits']=[2]
                else:bad['attributes']={'blackbox':'1'}
                path.write_text(json.dumps(dict(modules=dict(leaf=bad))))
                with self.subTest(kind=kind),self.assertRaises(ValueError):load_leaf(path,'leaf',library)

    def test_real_kernel_refuses_wrong_constant_output_and_static_wiring_premise(self):
        root=Path(__file__).resolve().parents[1]
        library_path=root/'.lake/build/lib/lean'
        lean=shutil.which('lean')
        if not lean or not (library_path/'Pinwheel/Hardware/StreamingMapped/Word.olean').is_file():
            self.skipTest('Native Lean mapped Boolean support is unavailable')
        library=replace(parse_library(LIBRARY,TYPES),pinned=True)
        cell=lambda kind,con:dict(type=PREFIX+kind,parameters={},
            port_directions={pin:'output' if pin in ('Y','X') else 'input' for pin in con},
            connections={pin:[wire] for pin,wire in con.items()})
        body=dict(ports=dict(A=dict(direction='input',bits=[2]),B=dict(direction='input',bits=[3]),
            S=dict(direction='input',bits=[4]),Y=dict(direction='output',bits=[6])),
            cells=dict(inv=cell('inv_1',dict(A=4,Y=5)),and_=cell('and2_1',dict(A=2,B=5,X=6))))
        with tempfile.TemporaryDirectory() as directory:
            directory=Path(directory);path=directory/'mapped.json'
            env=dict(os.environ,LEAN_PATH=str(directory)+':'+str(library_path))
            def check(name,desc,changed=None,extra=''):
                path.write_text(json.dumps(dict(modules=dict(leaf=changed or body))))
                source=generate_specialized(path,library,'leaf',desc,namespace='Actual.'+name)+extra
                source_path=directory/(name+'.lean');source_path.write_text(source)
                return subprocess.run([lean,'--root='+str(directory),'-DwarningAsError=true',str(source_path)],
                    text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=env,timeout=30)
            desc=dict(kind='$mux',fixed_operands={'B':'0'})
            valid=check('Good',desc)
            self.assertEqual(valid.returncode,0,valid.stdout)
            wrong_constant=check('WrongConstant',dict(kind='$mux',fixed_operands={'B':'1'}))
            self.assertNotEqual(wrong_constant.returncode,0)
            wrong=deepcopy(body);wrong['ports']['Y']['bits']=[2]
            self.assertNotEqual(check('WrongOutput',desc,wrong).returncode,0)
            extra='\nexample (A : BitVec 1) (S : BitVec 1) : Actual.WrongPremise.actual A 1#1 S = (if S = 1#1 then 1#1 else A) := by\n  exact Actual.WrongPremise.raw_correct A 1#1 S (by rfl)\n'
            self.assertNotEqual(check('WrongPremise',desc,extra=extra).returncode,0)


if __name__=='__main__':unittest.main()
