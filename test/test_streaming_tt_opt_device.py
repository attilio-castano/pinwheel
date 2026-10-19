"""Whole-device import binding, actual pad cut and semantic Q-map controls."""
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_mapped_liberty import FF,PREFIX,parse_library
from streaming_mapped_wrapper import ENGINE,PADS
from streaming_mapped_device import JOIN_THEOREMS
from streaming_mapped_uart_timing import THEOREMS
from streaming_tt_opt_device import (TOP,PACKAGE,SESSION,NAMESPACE,generate,cut_outer,
    semantic_q_map,required_source,run_worker,ordered_raw_sources,library_preflight_source)
from test_streaming_mapped_liberty import LIBRARY,TYPES


def candidate_fixture():
    """Actual6039 physical FFs, two components and resolved outer pad gates."""
    ports={};at=2
    for pin,(direction,width) in PADS.items():
        if direction=='input':ports[pin]=dict(direction=direction,bits=list(range(at,at+width)));at+=width
    engine={}
    for pin,(_,width) in ENGINE.items():
        if pin=='clk':engine[pin]=ports['clk']['bits']
        elif pin=='initialize':engine[pin]=[at];at+=1
        elif pin=='csn':engine[pin]=ports['ui_in']['bits'][:1]
        elif pin=='sck':engine[pin]=ports['ui_in']['bits'][1:2]
        elif pin=='mosi':engine[pin]=[ports['ui_in']['bits'][i] for i in (2,5,6,7)]
        elif pin=='raw_inputs':engine[pin]=ports['ui_in']['bits'][3:5]
        else:engine[pin]=list(range(at,at+width));at+=width
    cells={}
    def gate(name,kind,connections):
        cells[name]=dict(type=PREFIX+kind,parameters={},port_directions={pin:'output' if pin in ('X','Y') else 'input' for pin in connections},connections={pin:[bit] for pin,bit in connections.items()})
    active=at;at+=1;gate('active','and2_1',dict(A=ports['ena']['bits'][0],B=ports['rst_n']['bits'][0],X=active))
    gate('cold','inv_1',dict(A=active,Y=engine['initialize'][0]))
    for pin,source in [('uo_out',engine['miso']+engine['ready']+engine['busy']),('uio_out',engine['levels']),('uio_oe',engine['enabled'])]:
        bits=[]
        for i,wire in enumerate(source):gate(pin+str(i),'and2_1',dict(A=active,B=wire,X=at));bits.append(at);at+=1
        ports[pin]=dict(direction='output',bits=bits+['0']*(8-len(bits)))
    cells['engine']=dict(type=PACKAGE,parameters={},port_directions={p:d for p,(d,_) in ENGINE.items()},connections=engine)
    package_ports={};at=2
    for pin,(direction,width) in ENGINE.items():package_ports[pin]=dict(direction=direction,bits=list(range(at,at+width)));at+=width
    child_cells={};modules={TOP:dict(ports=ports,cells=cells,netnames={})};inventories={}
    for label,name,count,outs in [('frontend','frontend',1403,('miso','ready')),('core-d2','core',4636,('busy','levels','enabled'))]:
        cports=dict(clk=dict(direction='input',bits=[2]));connections=dict(clk=package_ports['clk']['bits']);qbits=list(range(10,10+count));position=0
        for pin in outs:
            width=ENGINE[pin][1];cports[pin]=dict(direction='output',bits=qbits[position:position+width]);position+=width;connections[pin]=package_ports[pin]['bits']
        ff={f'ff{i}':dict(type=FF,parameters={},port_directions=dict(CLK='input',D='input',Q='output',RESET_B='input'),connections=dict(CLK=[2],D=[q],Q=[q],RESET_B=['1'])) for i,q in enumerate(qbits)}
        modules[name]=dict(ports=cports,cells=ff,netnames=dict(r_state=dict(bits=qbits,attributes={})))
        child_cells[name]=dict(type=name,parameters={},port_directions={p:v['direction'] for p,v in cports.items()},connections=connections)
        inventories[label]=dict(registers=[dict(register='r_state',index=i,source_q=q,mapped_q=q,mapped_d=q,mapped_cell=json.dumps(['ff'+str(i)],separators=(',',':'))) for i,q in enumerate(qbits)])
    modules[PACKAGE]=dict(ports=package_ports,cells=child_cells,netnames={})
    return dict(modules=modules),inventories


class DeviceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.library=replace(parse_library(LIBRARY,TYPES),pinned=True)

    def test_factory_carries_all25_apis_with_only_optimized_actual_imports(self):
        texts=generate();self.assertEqual(list(texts),[SESSION,'StreamingOptimizedUARTTimingD2'])
        source='\n'.join(texts.values())
        for name in (*JOIN_THEOREMS,*THEOREMS):self.assertEqual(len(re.findall(r'(?m)^theorem '+name+r'\b',source)),1)
        for name in ('OptimizedFrontendProof','OptimizedCoreD2Proof','StreamingOptimizedPackageD2','StreamingOptimizedTinyD2'):
            self.assertIn('import '+name,source)
        for forbidden in ('import MappedFrontend','import MappedCore','StreamingMappedPackageD2','StreamingMappedTinyD2','sorry','native_decide','bv_decide'):
            self.assertNotIn(forbidden,source)
        self.assertIn('example (s : Package.State 1)',required_source())
        self.assertIn(NAMESPACE+'.physical_step_correct s i',required_source())

    def test_actual_outer_cut_retains_pin_functions_and_direct_clock(self):
        candidate,_=candidate_fixture();before=deepcopy(candidate)
        cut,graph,boundary=cut_outer(candidate,self.library)
        self.assertEqual(candidate,before);self.assertEqual(boundary['engine_instance'],'engine')
        self.assertNotIn('clk',cut['modules'][TOP]['ports'])
        self.assertEqual(graph.outputs['engine_boundary_mosi'],tuple(candidate['modules'][TOP]['ports']['ui_in']['bits'][i] for i in (2,5,6,7)))

    def test_outer_clock_unknown_gate_duplicate_engine_and_bad_abi_refuse(self):
        for kind in ('clock','unknown','duplicate','abi'):
            candidate,_=candidate_fixture();body=candidate['modules'][TOP]
            if kind=='clock':body['cells']['engine']['connections']['clk']=body['ports']['ena']['bits']
            elif kind=='unknown':body['cells']['active']['type']='unknown_cell'
            elif kind=='duplicate':body['cells']['second']=deepcopy(body['cells']['engine'])
            else:body['cells']['engine']['connections']['mosi']=[1,2,3]
            with self.subTest(kind=kind),self.assertRaises(ValueError):cut_outer(candidate,self.library)

    def test_q_map_independently_covers_every_actual6039_ff(self):
        candidate,inventory=candidate_fixture();result=semantic_q_map(candidate,self.library,inventory)
        self.assertEqual(result['physical_ff_bits'],6039);self.assertEqual(len(result['rows']),6039)
        self.assertEqual(len({row['candidate_q'] for row in result['rows']}),6039)

    def test_q_map_relabel_alias_q_d_and_missing_field_refuse(self):
        for kind in ('label','alias','q','d','missing'):
            candidate,inventory=candidate_fixture();rows=inventory['frontend']['registers']
            if kind=='label':rows[0]['index']=1
            elif kind=='alias':rows[0]=deepcopy(rows[1])
            elif kind=='q':rows[0]['mapped_q']=99
            elif kind=='d':rows[0]['mapped_d']=99
            else:rows.pop()
            with self.subTest(kind=kind),self.assertRaises(ValueError):semantic_q_map(candidate,self.library,inventory)

    def test_exact_source_producer_identities_refuse_before_output_creation(self):
        with tempfile.TemporaryDirectory() as directory:
            out=Path(directory)/'never-created'
            with self.assertRaises(ValueError):run_worker(dict(source_commit='HEAD',producer_commit='HEAD'),out)
            self.assertFalse(out.exists())

    def test_aliased_input_is_refused_before_output_or_source_read(self):
        with tempfile.TemporaryDirectory() as directory:
            directory=Path(directory);original=directory/'actual';original.write_text('not a source')
            alias=directory/'alias';alias.symlink_to(original)
            component=dict(raw_json=str(original),sv=str(original),raw_sources={'Proof':str(original)})
            config=dict(source_commit='a'*40,producer_commit='a'*40,library=str(alias),tools={},
                components={'frontend':component,'core-d2':component},
                device={'2':dict(tiny=str(original),package=str(original))})
            out=directory/'never-created'
            with self.assertRaisesRegex(ValueError,'Regular staged input required'):run_worker(config,out)
            self.assertFalse(out.exists())

    def test_actual_factory_library_preflight_includes_warm_reset_and_every_direct_import(self):
        source=library_preflight_source()
        self.assertIn('import Pinwheel.Hardware.StreamingReady.WarmReset\n',source)
        for text in generate().values():
            for name in re.findall(r'(?m)^import (Pinwheel\.[A-Za-z0-9_.]+)\s*$',text):
                self.assertIn('import '+name+'\n',source)
        self.assertNotIn('import OptimizedCore',source)

    def test_raw_module_order_comes_from_actual_imports_and_cycles_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            directory=Path(directory);sources={}
            for name,text in [('A','import C\n'),('B',''),('C','import B\n')]:
                path=directory/(name+'.lean');path.write_text(text);sources[name]=str(path)
            self.assertEqual(list(ordered_raw_sources(sources)),['B','C','A'])
            (directory/'B.lean').write_text('import A\n')
            with self.assertRaisesRegex(ValueError,'Cyclic'):ordered_raw_sources(sources)


if __name__=='__main__':unittest.main()
