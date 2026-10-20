"""Physical clock/state boundaries and actual-function refusal controls."""
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_tt_certificate import (clock_cones,clock_source,parse_graph,read_json,read_library,
    read_corners,data_model,canonical_model,contract_model)
from streaming_mapped_liberty import PREFIX, FF
from test_streaming_mapped_liberty import INV, AND, DFF

BUF = '''cell(sg13cmos5l_buf_4){pin(A){direction:"input";}
pin(X){direction:"output";function:"A";}}'''
TIE = '''cell(sg13cmos5l_tiehi){pin(L_HI){direction:"output";function:"1";}}'''
LIB = 'library(test){' + INV + AND + DFF + BUF + TIE + '}'
TYPES = {PREFIX + name for name in ('inv_1', 'and2_1', 'buf_4', 'tiehi', 'dfrbpq_1')}


def cell(kind, connections, output):
    return dict(type=PREFIX+kind, parameters={}, connections={key:[value] for key,value in connections.items()},
        port_directions={key:'output' if key==output else 'input' for key in connections})


def fixture():
    return dict(modules=dict(top=dict(ports=dict(clk=dict(direction='input',bits=[2]),
        data=dict(direction='input',bits=[3]),result=dict(direction='output',bits=[4])),
        netnames={},cells=dict(
            ff=cell('dfrbpq_1',dict(CLK=7,D=3,Q=4,RESET_B=8),'Q'),
            clockInvert1=cell('inv_1',dict(A=2,Y=5),'Y'),
            clockBuffer=cell('buf_4',dict(A=5,X=6),'X'),
            clockInvert2=cell('inv_1',dict(A=6,Y=7),'Y'),
            resetTie=cell('tiehi',dict(L_HI=8),'L_HI')))))


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.temporary=tempfile.TemporaryDirectory();self.addCleanup(self.temporary.cleanup)
        self.root=Path(self.temporary.name);self.libpath=self.root/'cells.lib';self.libpath.write_text(LIB)
        self.library=read_library(self.libpath,TYPES,expected_sha256=sha256(LIB.encode()).hexdigest())

    def test_actual_resized_buffer_tie_and_two_inversions_preserve_positive_clock(self):
        graph=parse_graph(fixture(),'top',self.library);roots=clock_cones(graph)
        self.assertEqual((len(graph.flipflops),len(graph.gates)),(1,4))
        self.assertEqual(len(roots),1)
        text,metadata=clock_source(graph,namespace='Pinwheel.Test.PhysicalClock',netlist_sha256='a'*64)
        self.assertIn('.inv (.var',text);self.assertIn('PositiveClock clock0',text)
        self.assertEqual(metadata['ff_clocks'],1)

    def test_clock_data_gating_negative_edge_constant_and_reset_changes_refuse(self):
        for mode in ('negative','constant','data-clock','gated','reset-active','reset-data','clock-data'):
            data=fixture();cells=data['modules']['top']['cells'];ff=cells['ff']['connections']
            if mode=='negative':ff['CLK']=[6]
            elif mode=='constant':ff['CLK']=['1']
            elif mode=='data-clock':ff['CLK']=[3]
            elif mode=='gated':
                cells['gate']=cell('and2_1',dict(A=7,B=3,X=9),'X');ff['CLK']=[9]
            elif mode=='reset-active':ff['RESET_B']=['0']
            elif mode=='reset-data':ff['RESET_B']=[3]
            else:ff['D']=[7]
            with self.subTest(mode=mode),self.assertRaises(ValueError):
                clock_cones(parse_graph(data,'top',self.library))

    def test_actual_ff_sequential_functions_and_library_bytes_are_not_supplied_by_names(self):
        for old,new in [('clocked_on:"CLK"','clocked_on:"!CLK"'),
                ('next_state:"D"','next_state:"!D"'),('function:"IQ"','function:"IQN"')]:
            changed=LIB.replace(old,new);self.libpath.write_text(changed)
            with self.subTest(new=new),self.assertRaises(ValueError):
                read_library(self.libpath,TYPES,expected_sha256=sha256(changed.encode()).hexdigest())
        self.libpath.write_text(LIB)
        with self.assertRaisesRegex(ValueError,'pin'):
            read_library(self.libpath,TYPES,expected_sha256='0'*64)

    def test_three_actual_corner_functions_must_agree(self):
        corners={}
        for name in ('slow','typ','fast'):
            path=self.root/(name+'.lib');path.write_text(LIB)
            corners[name]=dict(path=str(path),sha256=sha256(LIB.encode()).hexdigest())
        _,receipt=read_corners(corners,TYPES)
        self.assertTrue(receipt['all_corner_functions_equal'])
        changed=LIB.replace('function:"(A*B)"','function:"!(A*B)"')
        self.assertNotEqual(changed,LIB)
        Path(corners['fast']['path']).write_text(changed)
        corners['fast']['sha256']=sha256(changed.encode()).hexdigest()
        with self.assertRaisesRegex(ValueError,'across corners'):read_corners(corners,TYPES)

    def test_passive_antenna_load_is_retained_and_cannot_hide_a_float(self):
        text=LIB[:-1]+'cell(sg13cmos5l_antennanp){pin(A){direction:"input";}}}'
        self.libpath.write_text(text)
        lib=read_library(self.libpath,TYPES|{PREFIX+'antennanp'},expected_sha256=sha256(text.encode()).hexdigest())
        data=fixture();data['modules']['top']['cells']['load']=cell('antennanp',dict(A=3),None)
        graph=parse_graph(data,'top',lib)
        self.assertEqual(len(graph.passive_loads),1)
        self.assertEqual(graph.counts[PREFIX+'antennanp'],1)
        data['modules']['top']['cells']['load']['connections']['A']=[99]
        with self.assertRaisesRegex(ValueError,'passive-load'):parse_graph(data,'top',lib)

    def test_only_functionally_matching_buffers_and_all_data_roots_contract(self):
        reference=data_model(parse_graph(fixture(),'top',self.library))
        canonical=canonical_model(reference)
        buffered=fixture();cells=buffered['modules']['top']['cells']
        cells['dataBuffer']=cell('buf_4',dict(A=3,X=9),'X');cells['ff']['connections']['D']=[9]
        plan=contract_model(data_model(parse_graph(buffered,'top',self.library)),canonical)
        self.assertEqual(plan['full_state_bits'],1)
        for mode in ('data','output'):
            changed=deepcopy(buffered)
            if mode=='data':changed['modules']['top']['cells']['ff']['connections']['D']=[4]
            else:changed['modules']['top']['ports']['result']['bits']=[3]
            with self.subTest(mode=mode),self.assertRaises(ValueError):
                contract_model(data_model(parse_graph(changed,'top',self.library)),canonical)

    def test_state_pairing_is_checked_by_functions_and_outputs(self):
        data=fixture();module=data['modules']['top'];cells=module['cells']
        cells['invertData']=cell('inv_1',dict(A=3,Y=9),'Y')
        cells['ff2']=cell('dfrbpq_1',dict(CLK=7,D=9,Q=11,RESET_B=8),'Q')
        module['ports']['result']['bits']=[4,11]
        graph=parse_graph(data,'top',self.library);names=[ff.name for ff in graph.flipflops]
        labels={names[0]:'first',names[1]:'second'}
        reference=canonical_model(data_model(graph,state_labels=labels))
        with self.assertRaisesRegex(ValueError,'D function|public output'):
            contract_model(data_model(graph,state_labels={names[0]:'second',names[1]:'first'}),reference)

    def test_unknown_state_missing_driver_duplicate_json_and_inout_are_not_hidden(self):
        for mode in ('unknown','q-alias','undriven','inout','cycle'):
            data=fixture();module=data['modules']['top']
            if mode=='unknown':module['cells']['ff']['type']='invented_ff'
            elif mode=='q-alias':module['cells']['clone']=deepcopy(module['cells']['ff'])
            elif mode=='undriven':module['cells']['ff']['connections']['D']=[99]
            elif mode=='inout':module['ports']['data']['direction']='inout'
            else:module['cells']['clockBuffer']['connections']['A']=[6]
            with self.subTest(mode=mode),self.assertRaises(ValueError):parse_graph(data,'top',self.library)
        path=self.root/'bad.json';path.write_text('{"modules":{},"modules":{}}')
        with self.assertRaisesRegex(ValueError,'Duplicate'):read_json(path)

    def test_native_clock_truth_proof_rejects_a_single_inversion(self):
        lake=shutil.which('lake')
        if lake is None:self.skipTest('Native Lean unavailable')
        project=Path(__file__).resolve().parents[1]
        dependency=project/'.lake/build/lib/lean/Pinwheel/Hardware/StreamingPhysical/Clock.olean'
        if not dependency.exists():self.skipTest('New physical Clock library is not built in this environment')
        good,_=clock_source(parse_graph(fixture(),'top',self.library),
            namespace='Pinwheel.Test.PhysicalClock',netlist_sha256='a'*64)
        bad=good.replace('.inv (.var ⟨0, by decide⟩)', '.var ⟨0, by decide⟩',1)
        self.assertNotEqual(good,bad)
        for name,text,expected in [('Good',good,0),('Bad',bad,1)]:
            path=self.root/(name+'.lean');path.write_text(text)
            result=subprocess.run([lake,'env','lean','--root='+str(self.root),'-DwarningAsError=true',str(path)],
                cwd=project,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
            self.assertEqual(result.returncode,expected,result.stdout)
            if expected:self.assertIn('error',result.stdout)


if __name__=='__main__':unittest.main()
