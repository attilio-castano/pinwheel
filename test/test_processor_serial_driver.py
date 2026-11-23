import copy
import importlib.util
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import serial_oracle as o
sp=importlib.util.spec_from_file_location('serial_checks',ROOT/'scripts/check-processor-serial.py')
c=importlib.util.module_from_spec(sp);sp.loader.exec_module(c)

def fixture(d=4):
    data=dict(schema=1,clock='clk',module='processor_serial',divisor=d,counter_width=o.widths(d)[9],roles={},register_roles={},
              response_codes=dict(read=0,stored=1,register_hole=2,direction=3,tx_busy=4,rx_empty=5),device_codes=dict(gpio=0,timer=1,uart=2,invalid=3),**c.BOUNDARIES)
    for group,roles,ws in (('inputs',o.INPUT_ROLES,o.INPUT_WIDTHS),('outputs',o.OUTPUT_ROLES,o.OUTPUT_WIDTHS),('registers',o.REGISTER_ROLES,o.widths(d))):
        data[group]=[]
        for k,(role,w) in enumerate(zip(roles,ws,strict=True)):
            name=role if group=='inputs' else ('r_' if group=='registers' else '')+f'state_{k}'
            p=dict(index=k,name=name,width=w)
            if group=='registers':p['reference']=name
            data[group].append(p);data['register_roles' if group=='registers' else 'roles'][role]=name
    return data

def trace(rows):
    return ''.join(','.join(map(str,row))+'\n' for row in rows)+'SERIAL_DONE\nfixture: $finish called at 123 (1ns)\n'

class DriverTests(unittest.TestCase):
    def setUp(self):
        self.data=fixture();s,rows=o.stimulus(4);self.s=s;self.rows=rows[:3]
        self.frames,_,_=o.oracle(4,s,self.rows);self.want=c.expected(self.frames,True)

    def test_all_complete_descriptors(self):
        for d in c.MATRIX:c.validate_descriptor(fixture(d),d)

    def test_descriptor_omissions_aliasing_types_and_timing(self):
        bad=[]
        for group in ('inputs','outputs','registers'):
            x=fixture();x[group].pop();bad.append(x)
        x=fixture();x['roles']['tx_complete']='state_8';bad.append(x)
        x=fixture();x['registers'][0]['reference']='other';bad.append(x)
        x=fixture();x['registers'][9]['width']=5;bad.append(x)
        x=fixture();x['outputs'][0]['index']=False;bad.append(x)
        x=fixture();x['schema']=True;bad.append(x)
        x=fixture();x['divisor']=6;bad.append(x)
        x=fixture();x['counter_width']=True;bad.append(x)
        x=fixture();x['response_codes']['read']=False;bad.append(x)
        x=fixture();x['frontend_boundary']='wire proven';bad.append(x)
        for x in bad:
            with self.subTest(x=x),self.assertRaises(ValueError):c.validate_descriptor(x,4)

    def test_complete_trace_and_exact_concrete_witness(self):
        self.assertEqual(c.check_trace(trace(self.want),self.want,self.data),9)
        changed=self.want.copy();changed[0]=(*changed[0][:2],1,*changed[0][3:])
        with self.assertRaises(c.ConcreteMismatch) as ex:c.check_trace(trace(changed),self.want,self.data)
        self.assertEqual(ex.exception.witness,dict(observation='PRE',cycle=0,signal='state_0',expected=0,actual=1))

    def test_malformed_unknown_truncated_late_failure_never_semantic(self):
        good=trace(self.want)
        bad=[trace(self.want[:-1]),trace(self.want+[self.want[-1]]),trace(list(reversed(self.want))),good.replace('SERIAL_DONE',''),
             good.replace('SERIAL_DONE','SERIAL_DONE\nSERIAL_DONE'),good+'warning\n',good.replace('PRE,0,0','PRE,0,x',1),
             good.replace('PRE,0,0','PRE,0,2',1),good.replace('PRE,0,0','PRE,0,٠',1),good+'PRE,3,0\n',
             good+'fixture: $finish called at 124 (1ns)\n']
        changed=self.want.copy();changed[0]=(*changed[0][:2],1,*changed[0][3:])
        bad.append(trace(changed).replace('SERIAL_DONE','REG,99,x\nSERIAL_DONE'))
        for x in bad:
            with self.subTest(x=x),self.assertRaises(c.TraceError):c.check_trace(x,self.want,self.data)

    def test_frames_exact_types_and_complete_state(self):
        c.validate_frames(4,self.rows,self.frames)
        for field in ('pre','post','registers'):
            x=copy.deepcopy(self.frames);x[0][field].pop()
            with self.assertRaises(ValueError):c.validate_frames(4,self.rows,x)
        x=copy.deepcopy(self.frames);x[0]['input']['reset']=1
        with self.assertRaises(ValueError):c.validate_frames(4,self.rows,x)

    def test_synth_reset_and_no_force_raw_full_force(self):
        seg=[dict(startup=self.s,rows=self.rows)]
        raw=c.testbench(self.data,seg,True);syn=c.testbench(self.data,seg,False)
        self.assertEqual(raw.count('force dut.'),14);self.assertNotIn('force dut.',syn);self.assertNotIn('REG,',syn)
        for ss in ([],seg+seg,[dict(startup=self.s,rows=[o.row()])]):
            with self.assertRaises(ValueError):c.testbench(self.data,ss,False)
        two=c.testbench(self.data,o.raw_segments(4)[:2],True)
        self.assertEqual(two.count('force dut.'),28);self.assertEqual(two.count('"PRE,0,'),1);self.assertIn('"PRE,3,',two)

    def test_actual_mutations_are_single_endpoint_changes(self):
        text='module processor_serial();\n'+'\n'.join([f"assign {p['name']} = '0;" for p in self.data['outputs']]+
             [f"always @(posedge clk) {p['name']} <= {p['name']};" for p in self.data['registers']])+'\nendmodule\n'
        mutants=list(c.mutations(text,self.data));self.assertEqual(len(mutants),12)
        self.assertEqual(len({n for n,_ in mutants}),12)
        for _,value in mutants:
            self.assertNotEqual(value,text);self.assertNotIn('&&',value)
            self.assertEqual(sum(a!=b for a,b in zip(value.splitlines(),text.splitlines(),strict=True)),1)
        with self.assertRaises(ValueError):list(c.mutations('',self.data))

if __name__=='__main__':unittest.main()
