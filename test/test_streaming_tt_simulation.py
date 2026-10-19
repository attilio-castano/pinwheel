"""Refusal and actual-clock tests for the separate physical simulator lane."""
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_simulation as physical
from streaming_mapped_liberty import Cell,Library


def library():
    return Library('0'*64,{
        'sg13cmos5l_buf_8':Cell('sg13cmos5l_buf_8',dict(A='input',X='output'),'X','A',('variable','A')),
        'sg13cmos5l_tiehi':Cell('sg13cmos5l_tiehi',dict(L_HI='output'),'L_HI','1',('constant',True)),
        'sg13cmos5l_dfrbpq_1':Cell('sg13cmos5l_dfrbpq_1',dict(Q='output',CLK='input',D='input',RESET_B='input'),
            'Q','IQ',('variable','IQ'),True,('IQ','IQN'),('variable','CLK'),('variable','D'),('not',('variable','RESET_B')))},True)


def fixture():
    ports={};wire=2
    for name,(direction,width) in physical.PORTS.items():
        ports[name]=dict(direction=direction,bits=list(range(wire,wire+width)));wire+=width
    cells={};lib=library()
    def cell(name,kind,connections):
        cells[name]=dict(type=kind,parameters={},port_directions=lib.cells[kind].directions,
            connections={pin:[value] for pin,value in connections.items()})
    cell('cts/root','sg13cmos5l_buf_8',dict(A=ports['clk']['bits'][0],X=100))
    cell('cts/leaf','sg13cmos5l_buf_8',dict(A=100,X=101))
    cell('tie','sg13cmos5l_tiehi',dict(L_HI=102))
    cell('first','sg13cmos5l_dfrbpq_1',dict(Q=103,CLK=100,D=ports['ui_in']['bits'][0],RESET_B=102))
    cell('second','sg13cmos5l_dfrbpq_1',dict(Q=104,CLK=101,D=103,RESET_B=102))
    for name,port in ports.items():
        if port['direction']=='output':port['bits']=['0']*len(port['bits'])
    ports['uo_out']['bits'][0]=104
    return dict(modules={physical.TOP:dict(ports=ports,cells=cells,netnames={})})


def binding(document):
    body=document['modules'][physical.TOP]
    return {stage:dict(component='core-d2',register='r_'+stage,index=0,cell=name,
        q=body['cells'][name]['connections']['Q'][0],d=body['cells'][name]['connections']['D'][0],
        clock=body['cells'][name]['connections']['CLK'][0],reset_b=body['cells'][name]['connections']['RESET_B'][0])
        for stage,name in [('stage1','first'),('stage2','second')]}


def export_fixture(root):
    doc=fixture();body=doc['modules'][physical.TOP]
    # Native OpenDB ports name real nets, rather than JSON constant aliases.
    at=200
    for port in body['ports'].values():
        if port['direction']=='output':
            port['bits']=list(range(at,at+len(port['bits'])));at+=len(port['bits'])
    body['ports']['uo_out']['bits'][0]=104
    wires={wire for port in body['ports'].values() for wire in port['bits']}
    wires.update(wire for cell in body['cells'].values() for bits in cell['connections'].values() for wire in bits)
    nets={'n'+str(wire):dict(wire=wire,signal_type='SIGNAL') for wire in wires}
    body['netnames']={name:dict(bits=[value['wire']],hide_name=0,attributes={}) for name,value in nets.items()}
    instances={name:dict(master=cell['type'],master_type='CORE',terminals={pin:dict(
        direction=cell['port_directions'][pin].upper(),signal_type='SIGNAL',net='n'+str(bits[0]))
        for pin,bits in cell['connections'].items()}) for name,cell in body['cells'].items()}
    instances['tap']=dict(master='power_only',master_type='CORE_WELLTAP',terminals={
        'VDD':dict(direction='INOUT',signal_type='POWER',net=None)})
    terms={}
    for name,port in body['ports'].items():
        for index,wire in enumerate(port['bits']):
            key=name if len(port['bits'])==1 else name+'['+str(index)+']'
            terms[key]=dict(port=name,index=index,direction=port['direction'],net='n'+str(wire))
    from collections import Counter
    inventory=dict(schema='pinwheel.streaming-tt-odb-inventory.v1',top=physical.TOP,nets=nets,
        public_bterms=terms,instances=instances,physical_only_instances={'tap':'power_only'},
        unconnected_signal_outputs={},signal_model_instances=len(body['cells']),
        instance_counts=dict(sorted(Counter(item['master'] for item in instances.values()).items())))
    directory=root/'export';directory.mkdir()
    database=root/'database.odb';database.write_bytes(b'actual native database bytes')
    reference=root/'reference.json';reference.write_text(json.dumps(doc))
    def save():
        for name,value in [('connectivity.json',doc),('inventory.json',inventory)]:
            (directory/name).write_text(json.dumps(value,sort_keys=True))
        receipt=dict(schema='pinwheel.streaming-tt-odb-export.v1',read_only_database=True,top=physical.TOP,
            source_sha256='7'*64,database_sha256=physical.digest(database),reference_sha256=physical.digest(reference),
            artifacts_sha256={name:physical.digest(directory/name) for name in ('connectivity.json','inventory.json')})
        (directory/'receipt.json').write_text(json.dumps(receipt))
        return dict(directory=directory,receipt_sha256=physical.digest(directory/'receipt.json'),
            database=database,reference=reference,exporter_sha256='7'*64)
    return doc,inventory,save


class PhysicalSimulationTests(unittest.TestCase):
    def test_exact_three_pins_required_before_read(self):
        for value in ({},dict(x=dict(path='missing',sha256='0'*64)),dict(x='bad',y='bad',z='bad')):
            with self.assertRaises(ValueError):physical.libraries(value,{'sg13cmos5l_buf_8'})

    def test_preserves_all_cells_and_clock_depth(self):
        text,meta=physical.structural_verilog(fixture(),library(),expected_ff=2)
        self.assertEqual(len(meta['instances']),5)
        self.assertFalse(meta['clock_contraction'])
        self.assertIn('sg13cmos5l_buf_8 \\cts/root (.A(',text)
        self.assertIn('.CLK(w100)',text);self.assertIn('.CLK(w101)',text)
        self.assertEqual(len(meta['actual_ff_clock_pins']),2)

    def test_all_three_actual_corner_functions_must_agree(self):
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'corner';path.write_text('selected library bytes')
            corners={str(index):dict(path=str(path),sha256=pin) for index,pin in enumerate(physical.CORNERS_SHA256)}
            first=library();different=deepcopy(first.cells)
            old=different['sg13cmos5l_buf_8']
            different[old.name]=Cell(old.name,old.directions,old.output,'!A',('not',('variable','A')))
            with patch.object(physical,'read_library',side_effect=[first,first,Library('0'*64,different,True)]):
                with self.assertRaises(ValueError):physical.libraries(corners,first.cells)

    def test_ff_inventory_and_bool_refusal(self):
        for value in (True,1,3):
            with self.assertRaises(ValueError):physical.structural_verilog(fixture(),library(),expected_ff=value)

    def test_unknown_cell_pin_and_functional_x_refused(self):
        original=fixture()
        for change in ('cell','pin','x','cycle','clock'):
            doc=deepcopy(original);cells=doc['modules'][physical.TOP]['cells']
            if change=='cell':cells['tie']['type']='unknown'
            elif change=='pin':cells['first']['connections'].pop('RESET_B')
            elif change=='x':cells['first']['connections']['D']=['x']
            elif change=='cycle':cells['cts/root']['connections']['A']=[101]
            else:cells['cts/root']['connections']['A']=[103]
            with self.assertRaises(ValueError):physical.structural_verilog(doc,library(),expected_ff=2)

    def test_changed_edge_or_extra_state_refused(self):
        lib=library();bad=deepcopy(lib.cells)
        old=bad['sg13cmos5l_dfrbpq_1']
        bad[old.name]=Cell(old.name,old.directions,old.output,old.function_text,old.function,True,
            old.state_names,('not',('variable','CLK')),old.next_state,old.clear)
        with self.assertRaises(ValueError):physical.cell_models(Library('0'*64,bad,True),bad)

    def test_sampler_binding_actual_pins_and_only_d_change(self):
        doc=fixture();links=binding(doc);mutant,record=physical.sampler_mutation(doc,library(),links)
        self.assertEqual(record['changed_ff_pins'],1)
        expected=deepcopy(doc);expected['modules'][physical.TOP]['cells']['second']['connections']['D']=doc['modules'][physical.TOP]['cells']['first']['connections']['D']
        self.assertEqual(mutant,expected)
        links['stage2']['clock']=100
        with self.assertRaises(ValueError):physical.sampler_mutation(doc,library(),links)

    def test_final_component_symlink_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'input').write_text('value');(root/'alias').symlink_to(root/'input')
            with self.assertRaises(ValueError):physical.regular(root/'alias')

    def test_actual_export_partition_ports_and_every_pin(self):
        with tempfile.TemporaryDirectory() as temp:
            doc,inventory,save=export_fixture(Path(temp));args=save()
            _,_,identity=physical.verify_export(**args)
            self.assertEqual(identity['functional_instances'],5);self.assertEqual(identity['power_only_instances'],1)
            inventory['instances']['first']['terminals']['D']['net']='n104'
            with self.assertRaises(ValueError):physical.verify_export(**save())

    def test_export_native_receipt_and_public_net_refusals(self):
        with tempfile.TemporaryDirectory() as temp:
            doc,inventory,save=export_fixture(Path(temp));args=save()
            with self.assertRaises(ValueError):physical.verify_export(**dict(args,receipt_sha256='0'*64))
            with self.assertRaises(ValueError):physical.verify_export(**dict(args,exporter_sha256='0'*64))
            inventory['public_bterms']['clk']['net']='n104'
            with self.assertRaises(ValueError):physical.verify_export(**save())

    def test_power_only_may_not_hide_functional_terminal(self):
        with tempfile.TemporaryDirectory() as temp:
            doc,inventory,save=export_fixture(Path(temp))
            inventory['instances']['tap']['terminals']['VDD']['signal_type']='SIGNAL'
            with self.assertRaises(ValueError):physical.verify_export(**save())

    def test_native_real_clock_tree_nonblocking_pipeline(self):
        iverilog=ROOT/'build/tools/oss-cad-suite/bin/iverilog';vvp=ROOT/'build/tools/oss-cad-suite/bin/vvp'
        if not iverilog.is_file() or not vvp.is_file():self.skipTest('Pinned Icarus unavailable')
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);design,_=physical.structural_verilog(fixture(),library(),expected_ff=2)
            (root/'dut.sv').write_text(design);(root/'cells.sv').write_text(physical.cell_models(library(),library().cells))
            (root/'tb.sv').write_text('''module tb;
reg clk=0;reg[7:0] ui=0;wire[7:0] uo,io,oe;
tt_um_pinwheel_streaming_ready_d2 dut(.ui_in(ui),.uo_out(uo),.uio_in(8'b0),.uio_out(io),.uio_oe(oe),.ena(1'b1),.clk(clk),.rst_n(1'b1));
initial begin
#2;clk=1;#2;clk=0;#2;clk=1;#2;clk=0;
if(uo[0]!==0)$fatal(1,"cold pipeline");
ui=1;#2;clk=1;#2;clk=0;if(uo[0]!==0)$fatal(1,"clock depth raced");
#2;clk=1;#2;clk=0;if(uo[0]!==1)$fatal(1,"physical clock tree absent");
$display("PHYSICAL_CLOCK_PIPELINE_PASS");$finish;end
endmodule
''')
            executable=root/'test.vvp'
            compiled=subprocess.run([str(iverilog),'-g2012','-s','tb','-o',str(executable),
                str(root/'dut.sv'),str(root/'cells.sv'),str(root/'tb.sv')],capture_output=True,text=True,timeout=30)
            self.assertEqual(compiled.returncode,0,compiled.stdout+compiled.stderr)
            native=subprocess.run([str(vvp),str(executable)],capture_output=True,text=True,timeout=30)
            self.assertEqual(native.returncode,0,native.stdout+native.stderr)
            self.assertIn('PHYSICAL_CLOCK_PIPELINE_PASS',native.stdout)


if __name__=='__main__':unittest.main()
