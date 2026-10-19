"""Actual FF-pin mutation, selected native corpus and failed-receipt refusals."""
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch,Mock

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_mapped_liberty import FF,PREFIX,parse_library
from streaming_mapped_simulation import cell_models,sampler_mutation,check_uart_cases,run_uart_cases
from test_streaming_mapped_liberty import LIBRARY,TYPES


def receipt():
    cases=[]
    for q in (4,12,128):
        for byte in (0,255,0x96,0x69):cases.append(dict(kind='valid',quarter_cycles=q,payload=byte))
        cases.extend([dict(kind='false-start',quarter_cycles=q,payload=0x96),dict(kind='bad-stop',quarter_cycles=q,payload=0x69)])
        if q==4:cases.extend([dict(kind='sampling-center',quarter_cycles=q,payload=0),dict(kind='sampling-off-center',quarter_cycles=q,payload=0)])
        cases.append(dict(kind='held-high',quarter_cycles=q,payload=0))
    cases.append(dict(kind='sampler-ff-pin',quarter_cycles=4,payload=0,oracle_rejected=True,
        mutation=dict(changed_ff_pins=1,pin='D',before=[4],after=[2]),observation=dict(terminal_delta=-1)))
    for case in cases:case.update(passed=True,starts=1,tx_accepted=0,expected_terminal_delta=-1 if case['kind']=='sampler-ff-pin' else 0)
    runs=[dict(name=name,native_exit_code=0,physical_edges=10,trace=dict(edges=10,bytes=200,sha256='a'*64)) for name in ('unchanged','sampler-ff-pin')]
    return dict(schema='pinwheel.streaming-mapped-uart-wire.v1',passed=True,depth=2,cases=cases,native_runs=runs,physical_edges=20)


def circuit():
    def ff(q,d):return dict(type=FF,parameters={},port_directions=dict(CLK='input',D='input',Q='output',RESET_B='input'),connections=dict(CLK=[3],D=[d],Q=[q],RESET_B=['1']))
    return dict(modules=dict(core=dict(ports=dict(clk=dict(direction='input',bits=[3])),netnames=dict(
        r_stage1=dict(bits=[4,5]),r_stage2=dict(bits=[6,7])),cells=dict(first0=ff(4,2),first1=ff(5,9),second0=ff(6,4),second1=ff(7,5)))))


class SimulationTests(unittest.TestCase):
    def setUp(self):self.library=replace(parse_library(LIBRARY,TYPES),pinned=True)

    def test_cell_models_use_actual_pinned_boolean_and_sequential_functions(self):
        text=cell_models(self.library,{PREFIX+'inv_1',FF})
        self.assertIn('assign Y = (~A);',text)
        self.assertIn('posedge CLK or negedge RESET_B',text)
        self.assertIn("if (!RESET_B) Q <= 1'b0; else Q <= D;",text)
        self.assertNotIn('#',text)
        for library,used in [(replace(self.library,pinned=False),{FF}),(self.library,{'unknown'}),(self.library,set())]:
            with self.assertRaises(ValueError):cell_models(library,used)

    def test_sampler_changes_one_actual_D_pin_and_preserves_original_and_other_state(self):
        before=circuit();after,meta=sampler_mutation(before,'core',self.library)
        self.assertEqual(before,circuit())
        changes=[]
        for name,cell in before['modules']['core']['cells'].items():
            if cell!=after['modules']['core']['cells'][name]:changes.append(name)
        self.assertEqual(changes,['second0']);self.assertEqual(meta['changed_ff_pins'],1)
        self.assertEqual(meta['before'],[4]);self.assertEqual(meta['after'],[2])
        self.assertEqual(after['modules']['core']['cells']['second1'],before['modules']['core']['cells']['second1'])

    def test_vacuous_unknown_clock_reset_and_duplicate_Q_mutations_refuse(self):
        for mode in ('vacuous','clock','reset','duplicate','unknown'):
            data=circuit();m=data['modules']['core']
            if mode=='vacuous':m['cells']['second0']['connections']['D']=[2]
            elif mode=='clock':m['cells']['second0']['connections']['CLK']=[2]
            elif mode=='reset':m['cells']['second0']['connections']['RESET_B']=['0']
            elif mode=='duplicate':m['cells']['duplicate']=deepcopy(m['cells']['second0'])
            else:del m['netnames']['r_stage2']
            with self.subTest(mode=mode),self.assertRaises(ValueError):sampler_mutation(data,'core',self.library)

    def test_exact_selected_corpus_and_two_successful_native_runs_are_required(self):
        check_uart_cases(receipt())
        for mode in ('missing','duplicate','wrong-byte','wrong-q','wrong-owner','crash','missing-run','trace','edges','mutant-timing','no-mutation','bool-depth','error'):
            result=receipt()
            if mode=='missing':result['cases'].pop()
            elif mode=='duplicate':result['cases'][1]=deepcopy(result['cases'][0])
            elif mode=='wrong-byte':result['cases'][0]['payload']=1
            elif mode=='wrong-q':result['cases'][0]['quarter_cycles']=8
            elif mode=='wrong-owner':result['cases'][0]['starts']=2
            elif mode=='crash':result['native_runs'][1]['native_exit_code']=1
            elif mode=='missing-run':result['native_runs'].pop()
            elif mode=='trace':result['native_runs'][0]['trace']['bytes']=199
            elif mode=='edges':result['physical_edges']=19
            elif mode=='mutant-timing':result['cases'][-1]['observation']['terminal_delta']=0
            elif mode=='no-mutation':result['cases'][-1]['mutation']['after']=[4]
            elif mode=='bool-depth':result['depth']=True
            else:result['error']='late failed closeout'
            with self.subTest(mode=mode),self.assertRaises(ValueError):check_uart_cases(result)

    def test_invalid_depth_and_mutation_refuse_before_creating_output(self):
        import tempfile
        with tempfile.TemporaryDirectory() as temporary:
            output=Path(temporary)/'unused'
            for depth,mutation in [(True,{}),(8,{}),(2,dict(changed_ff_pins=1,pin='D',before=[2],after=[2]))]:
                with self.assertRaises(ValueError):run_uart_cases('unused','unused',output,depth=depth,mutant='unused',mutation=mutation)
                self.assertFalse(output.exists())

    def test_late_checker_failure_saves_a_failed_receipt(self):
        import json,tempfile
        class Native:
            def __init__(self,*args,**kwargs):self.process=SimpleNamespace(returncode=0);self.cycle=1
            def __enter__(self):return self
            def __exit__(self,*args):pass
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);exe=root/'native';mutant=root/'mutant';exe.write_bytes(b'candidate');mutant.write_bytes(b'mutant')
            recording=SimpleNamespace(trace=SimpleNamespace(close=lambda:dict(edges=1,bytes=20,sha256='a'*64)))
            host=SimpleNamespace(initialize=lambda:None,load=lambda image:object())
            with patch('streaming_rtl.QuadRTL',Native),patch('streaming_transport.QuadTransport',return_value=object()),\
                patch('streaming_ready_transport.ReadyHost',return_value=host),\
                patch('streaming_uart_compile.uart_image',return_value=object()),\
                patch('streaming_uart_wire_cases.Recording',return_value=recording),\
                patch('streaming_uart_wire_cases.receive_frame',return_value={}),\
                patch('streaming_uart_wire_cases.opcode_counts',return_value={}),\
                patch('streaming_mapped_simulation.check_uart_cases',side_effect=ValueError('late validation failure')):
                with self.assertRaisesRegex(ValueError,'late validation failure'):
                    run_uart_cases('selected-vvp',exe,root/'report',depth=2,mutant=mutant,
                        mutation=dict(changed_ff_pins=1,pin='D',before=[4],after=[2]))
            result=json.loads((root/'report/report.json').read_text())
            self.assertFalse(result['passed']);self.assertIn('late validation failure',result['error'])


if __name__=='__main__':unittest.main()
