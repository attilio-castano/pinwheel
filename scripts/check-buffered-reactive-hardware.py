#!/usr/bin/env python3
"""Reactive counted programs through typed reference, circuit, emitted RTL and saved gates.

This opt-in reactive parallel target has no paired SRAM/serial
package integration, routed timing or physical qualification.
"""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import sys
import time

from buffered_engine import (BufferedEngine, BufferedInstruction, BufferedProgram,
    BufferedBlock, BufferedSequence, BufferedRepeat)
from buffered_hardware import (BufferedHardwareWaitTimeout, encode_instruction, pack_wire_bits)
from buffered_counted_hardware import compact_spi, compact_jtag
from buffered_reactive_hardware import BufferedReactiveHardwareHost, lower_reactive
from buffered_i2c import buffered_i2c_read, register_read_tx
from buffered_i2c_peer import BufferedI2CReadPeer
import importlib.util
_spec=importlib.util.spec_from_file_location('buffered_reactive_reference_gate',Path(__file__).with_name('check-buffered-reactive.py'))
reference_gate=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(reference_gate)
from buffered_reactive_hardware_rtl import BufferedReactiveRTL, COMMAND_FIELDS, replay_vectors
from buffered_hardware_synthesis import CAD, compile_rtl, stage_pdk, synthesize
from buffered_peers import BufferedSPIPeer, BufferedJTAGPeer
from jtag_peers import TAP
from pad_io import PadDrive
from pinwheel_buffers import TransferError, TransferSlot
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
CIRCT = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
TARGET = 'pinwheel-buffered-reactive32-v1'
BRIDGE = ROOT / 'physical/buffered_reactive_host_bridge.sv'
STORAGE = dict(tx=[('r_tx_data', 32)], rx=[('r_rx_data', 32)],
    instructions=[(f'r_word{k}', 144, 0, 64) for k in range(64)],
    controls=[(f'r_word{k}', 144, 64, 24) for k in range(64)],
    branches=[(f'r_word{k}', 144, 88, 56) for k in range(64)],
    written_mask=[('r_written', 64)])
STATE_WIDTHS = dict(valid=1, busy=1, retained=1, pending=1, rejected=1, mode=2,
    pc=8, remaining=8, levels=3, enabled=3, tx_consumed=6, rx_length=6, rx_data=32,
    read_valid=1, read_bit=1, generation=16, transfer=16, exhausted=1, stage1=2, stage2=2, virtual_pc=10, env0=3, env1=3, phase=3, wait_left=8, scratch=16)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def compile_reactive(run, out, source, label):
    return compile_rtl(run, out, source, label, bridge=BRIDGE,
                       testbench='buffered_reactive_host_bridge')


def loop_control(depth, *, outer_start=0, outer_count=1, inner_start=0,
                 inner_count=1, outer_end=False, inner_end=False):
    """Independent bit packing; do not reuse the host's control encoder."""
    return (depth | (outer_start << 2) | ((outer_count-1) << 8) |
            (inner_start << 11) | ((inner_count-1) << 17) |
            (int(outer_end) << 20) | (int(inner_end) << 21))


def check_export(request, exported):
    require(type(exported) is dict and set(exported) == {'schema', 'cases'},
            'Wrong exported hardware vector envelope')
    require(exported.get('schema') == 'pinwheel-buffered-reactive-hardware-vectors-v1',
            'Wrong exported hardware vector schema')
    actual = exported.get('cases')
    require(type(actual) is list and len(actual) == len(request['cases']),
            'Truncated hardware command cases')
    edges = checks = 0
    for expected, case in zip(request['cases'], actual, strict=True):
        require(type(case) is dict and set(case) == {'name', 'vectors'} and
                type(case['name']) is str and type(case['vectors']) is list,
                'Wrong exported hardware case schema')
        require(case['name'] == expected['name'], 'Changed hardware command case identity')
        require(len(case['vectors']) == len(expected['vectors']), 'Truncated hardware command edges')
        for given, vector in zip(expected['vectors'], case['vectors'], strict=True):
            require(type(vector) is dict and set(vector) == {'command', 'raw_inputs', 'state'},
                    'Wrong exported hardware edge schema')
            command, raw, state = vector['command'], vector['raw_inputs'], vector['state']
            require(type(command) is dict and set(command) <= set(COMMAND_FIELDS) and
                    all(type(value) is int and 0 <= value < 2**COMMAND_FIELDS[key]
                        for key, value in command.items()),
                    'Wrong exported command field type or width')
            require(type(raw) is int and 0 <= raw < 4, 'Wrong exported raw input type or width')
            require(type(state) is dict and set(state) == set(STATE_WIDTHS) and
                    all(type(value) is int and 0 <= value < 2**STATE_WIDTHS[key]
                        for key, value in state.items()),
                    'Wrong exported public state field type or width')
            require(vector['command'] == given['command'] and
                    vector['raw_inputs'] == given['raw_inputs'], 'Changed hardware input transcript')
        for check in expected['checks']:
            state = case['vectors'][check['edge']]['state']
            require(all(state.get(key) == value for key, value in check['state'].items()),
                    f'Independent command expectation differs: {case["name"]}/{check}')
            checks += 1
        edges += len(case['vectors'])
    return dict(cases=len(actual), edges=edges, independent_state_checks=checks,
                raw_input_histories=sum(case['name'].startswith('nested-sampler-history-')
                                        for case in actual))


def stored_row(code, pc, base=0):
    """Derive physical leaf placement from source geometry, not encoded controls."""
    if type(code) is BufferedBlock:
        return base+pc
    if type(code) is BufferedSequence:
        offset=0
        for part in code.parts:
            if pc < part.span: return stored_row(part,pc,base+offset)
            pc-=part.span
            offset+=part.words
        raise RuntimeError('Source PC exceeds sequence geometry')
    if type(code) is BufferedRepeat:
        return stored_row(code.body,pc%code.body.span,base)
    raise RuntimeError('Unknown counted source node')


def spi_cases(full):
    cases=[]
    for lane in range(4):
        for value in (range(256) if full else (0,1,0x96,255)):
            tx,rx=bytearray(b'\x96\xa5\x3c\xc3'),bytearray(b'\xa6\x9b\x42\xe1')
            tx[lane],rx[lane]=value,value^255
            cases.append((4,4,1,bytes(tx),bytes(rx)))
    cases += [(n,half,tco,b'\x96\xa5\x3c\xc3'[:n],b'\xa6\x9b\x42\xe1'[:n])
              for n,half,tco in ((1,3,0),(2,7,1),(4,256,1))]
    return cases


def jtag_cases(full):
    cases=[]
    widths=(1,7,13,17,32) if full else (17,)
    for width in widths:
        mask=(1<<width)-1
        patterns=((0,mask),(mask,0),(0x96a53cc3&mask,0xa69b42e1&mask)) if full else ((0x165ac&mask,0x0a653&mask),)
        for state in TAP:
            for tx,rx in patterns: cases.append((width,4,1,state,tx,rx))
    if not full:
        cases += [(width,4,1,'pause_ir',0x96a53cc3&((1<<width)-1),0xa69b42e1&((1<<width)-1))
                  for width in (1,32)]
    cases += [(17,half,tco,'pause_ir',0x165ac,0x0a653) for half,tco in ((3,0),(7,1))]
    return cases



def model_program(case):
    definition=case['program']
    return BufferedProgram((), schedule=reference_gate.decode_schedule(definition['schedule']),
        idle_levels=definition['idle_levels'],idle_enabled=definition['idle_enabled'],
        declared_tx_bits=case['tx_demand'],declared_rx_bits=case['rx_demand'],
        max_rx_bits=case['rx_max'])


def model_state(program,state):
    """Project typed generic model state; row placement uses source geometry."""
    stopped=state['control']=='stopped'
    phase={'active':1,'waiting':2,'checked':3,'qualifying':4}.get(state['control'])
    if stopped: phase={'ready':0,'complete':5,'timeout':6,'fault':7}[state['stop_reason']]
    expected=dict(mode=2 if phase==5 else 3 if phase in (6,7) else 1,
        phase=phase,remaining=state['remaining'] or 0,wait_left=state['wait_left'] or 0,
        scratch=sum(int(bit)<<k for k,bit in enumerate(state['samples'])),
        virtual_pc=0 if stopped else state['pc'],levels=state['levels'],enabled=state['enabled'],
        tx_consumed=state['tx_consumed_bits'],rx_length=len(state['rx_bits']),
        rx_data=sum(int(bit)<<k for k,bit in enumerate(state['rx_bits'])),
        stage1=state['sampler_first'],stage2=state['sampler_second'],
        busy=int(not stopped),retained=int(stopped),valid=1,generation=1,transfer=1)
    if stopped: expected.update(pc=0,env0=0,env1=0)
    else:
        _,environment=program.locate(state['pc'])
        expected.update(pc=stored_row(program.schedule,state['pc']),
                        env0=environment[0],env1=environment[1])
    return expected


def command_cases(model_vectors):
    cases=[]
    def fixture(name):
        vectors,checks=[],[]
        def edge(raw=3,expect=None,**command):
            vectors.append(dict(command=command,raw_inputs=raw))
            if expect is not None: checks.append(dict(edge=len(vectors)-1,state=expect))
        edge(initialize=1,expect=dict(mode=0,phase=0,stage1=0,stage2=0,scratch=0))
        cases.append(dict(name=name,vectors=vectors,checks=checks))
        return edge
    def load(edge,image):
        for address,(word,control,branch) in enumerate(zip(image.words,image.controls,image.branches,strict=True)):
            edge(command=1,address=address,word=word,control=control,branch=branch)
        edge(command=2,count=len(image.words),virtual_span=image.virtual_span,
             idle_levels=image.idle_levels,idle_enabled=image.idle_enabled,
             expect=dict(valid=1,generation=1,pending=0,rejected=0))
    # Actual typed source snapshots include entry priority, all held phases,
    # branches, loop geometry and all I2C cleanup paths, not reconstructed DUT state.
    for case in model_vectors['cases']:
        program=model_program(case)
        reference_gate.bind_i2c_factory(case,program)
        image=lower_reactive(program)
        edge=fixture('typed-'+case['name'])
        load(edge,image)
        edge();edge() # Establish the typed reference constructor's sampler3/3 relation.
        edge(command=3,expected_generation=1,tx_data=pack_wire_bits(tuple(case['tx_bits'])),
             tx_length=len(case['tx_bits']),rx_capacity=case['rx_limit'],
             expect=model_state(program,case['initial_state']))
        first=second=3
        retained_edges=0
        for raw,state in zip(case['incoming'],case['states'],strict=True):
            first,second=raw,first
            expected=model_state(program,state)
            expected.update(stage1=first,stage2=second)
            edge(raw=raw,expect=expected)
            if state['control']=='stopped': retained_edges+=1
            if retained_edges==4: break
    # Independent reference fixtures restore nonzero destination environments and
    # expose a retained prefix larger than the declared successful payload.
    for target in (3,11,19,23):
        code=BufferedSequence((BufferedBlock((BufferedInstruction('checked',finish=target),)),
            BufferedRepeat(3,BufferedRepeat(4,BufferedBlock((
                BufferedInstruction('drive',append_input=0),
                BufferedInstruction('checked',terminal_capture=(1,0),finish=(0,25,None)))))),
            BufferedBlock((BufferedInstruction('halt'),))))
        program=BufferedProgram((),schedule=code,declared_tx_bits=0,declared_rx_bits=0,max_rx_bits=16)
        slot=TransferSlot(tx_capacity_bits=32,rx_capacity_bits=32)
        identity=slot.begin(program.key,(),16)
        model=BufferedEngine(slot,identity,program)
        edge=fixture(f'reference-branch-loop-environment-{target}');load(edge,lower_reactive(program));edge();edge()
        def snapshot():
            return dict(control='stopped' if model.done else model.mode,
                stop_reason='complete' if model.mode=='completed' else model.mode if model.done else None,
                remaining=model.remaining,wait_left=model.wait_left,samples=list(model.samples),pc=model.pc,
                levels=model.levels,enabled=model.enabled,tx_consumed_bits=slot._tx_consumed,rx_bits=list(slot._rx),
                sampler_first=model._first,sampler_second=model._second)
        edge(command=3,expected_generation=1,rx_capacity=16,expect=model_state(program,snapshot()))
        first=3
        for cycle in range(32):
            raw=(cycle%4) if cycle<8 else 3
            model.step(raw)
            expected=model_state(program,snapshot());expected.update(stage1=raw,stage2=first);first=raw
            edge(raw=raw,expect=expected)
    # Independent raw owner and canonical-word failures.
    edge=fixture('coverage-and-retained-owner')
    edge(command=2,count=1,virtual_span=1,expect=dict(rejected=1,valid=0))
    edge(command=1,address=0,word=3)
    for count,span in ((0,1),(65,1),(1,0),(1,1025)):
        edge(command=2,count=count,virtual_span=span,expect=dict(rejected=1,valid=0))
    edge(command=2,count=1,virtual_span=1,expect=dict(valid=1,generation=1))
    edge(command=3,expected_generation=0,expect=dict(rejected=1,transfer=0))
    edge(command=3,expected_generation=1,tx_length=33,expect=dict(rejected=1,transfer=0))
    edge(command=3,expected_generation=1,expect=dict(mode=2,phase=5,retained=1,transfer=1))
    for command in (1,2,3):
        edge(command=command,word=4,count=1,virtual_span=1,expected_generation=1,
             expect=dict(rejected=1,retained=1,phase=5,generation=1,transfer=1))
    edge(command=4,expected_generation=1,expected_transfer=2,expect=dict(rejected=1,retained=1))
    edge(command=4,expected_generation=1,expected_transfer=1,
         expect=dict(rejected=0,retained=0,phase=0,scratch=0))
    for label,word,control,branch in (
        ('word-reserved',1<<63,0,0),('append-invalid',3<<22,0,0),
        ('capture-disabled-nonzero',2<<29,0,0),('terminal-extra',3|(1<<29),0,0),
        ('control-reserved',0,1<<23,0),('branch-reserved',6,0,1<<55),
        ('branch-invalid-kind',6,0,3),('nonchecked-branch',0,0,1)):
        edge=fixture('canonical-'+label)
        edge(command=1,address=0,word=word,control=control,branch=branch)
        edge(command=2,count=1,virtual_span=1,idle_levels=4,idle_enabled=7)
        edge(command=3,expected_generation=1,tx_length=1,rx_capacity=1,
             expect=dict(mode=3,phase=7,retained=1,scratch=0,tx_consumed=0,rx_length=0,levels=4,enabled=7))
    edge=fixture('wait-last-budget-readiness-priority')
    edge(command=1,address=0,word=5|(1<<46))
    edge(command=1,address=1,word=3)
    edge(command=2,count=2,virtual_span=2,idle_levels=4,idle_enabled=7)
    edge(command=3,expected_generation=1,expect=dict(mode=1,phase=2,remaining=0))
    edge(expect=dict(mode=2,phase=5,levels=4,enabled=7,retained=1))
    edge=fixture('first-entry-second-input-selected')
    edge(raw=2,command=1,address=0,word=2<<22)
    edge(raw=2,command=1,address=1,word=3)
    edge(raw=2,command=2,count=2,virtual_span=2)
    edge(raw=0,command=3,expected_generation=1,rx_capacity=1,
         expect=dict(mode=1,phase=1,rx_length=1,rx_data=1,stage1=0,stage2=2))
    edge(raw=0,expect=dict(mode=2,phase=5,rx_length=1,rx_data=1,retained=1))
    edge(read_index=0,expect=dict(read_valid=1,read_bit=1))
    # Input0 append over every possible three-edge input history.
    for history in range(64):
        edge=fixture(f'nested-sampler-history-{history}')
        word=(1<<22) # DRIVE input0 append, zero output profile, duration1.
        control=loop_control(2,outer_count=2,inner_count=3,outer_end=True,inner_end=True)
        edge(command=1,address=0,word=word,control=control)
        edge(command=1,address=1,word=3)
        edge(command=2,count=2,virtual_span=7)
        edge();edge()
        raw=[(history>>(2*k))&3 for k in range(3)]+[0,2,1]
        sampled=[3,3]+raw[:-2]
        for virtual,pads in enumerate(raw):
            cmd=dict(command=3,expected_generation=1,rx_capacity=6) if virtual==0 else {}
            edge(raw=pads,**cmd,expect=dict(pc=0,virtual_pc=virtual,env0=virtual%3,
                env1=virtual//3,rx_length=virtual+1))
        edge(expect=dict(mode=2,phase=5,rx_length=6,rx_data=sum((n&1)<<k for k,n in enumerate(sampled))))
    return dict(schema='pinwheel-buffered-reactive-hardware-input-v1',cases=cases)


class ReferenceTransport:
    """Derive sampler FIFO from resolved preclock wires, independent of the DUT."""
    def __init__(self,rtl):
        self.rtl,self.program=rtl,None
        self.engine=None
        self.first=self.second=0
        self.compared_edges=self.starts=self.fetch_checks=self.sampler_checks=0
    def edge(self,**command):
        old_first,old_second=self.first,self.second
        actual=self.rtl.edge(**command)
        reset=command.get('initialize') or command.get('command')==7
        self.first,self.second=(0,0) if reset else (actual.edge_inputs,old_first)
        require((actual.stage1,actual.stage2)==(self.first,self.second),
                'Reactive sampler differs from independent resolved-wire FIFO')
        self.sampler_checks+=1
        if reset: self.engine=None
        elif command.get('command')==3 and not actual.rejected:
            require(self.program is not None,'Reference requires canonical source')
            bits=tuple(bool(command['tx_data']&(1<<k)) for k in range(command['tx_length']))
            slot=TransferSlot(tx_capacity_bits=32,rx_capacity_bits=32)
            identity=slot.begin(self.program.key,bits,command['rx_capacity'])
            self.engine=BufferedEngine(slot,identity,self.program,
                initial_first_sample=old_first,initial_second_sample=old_second)
            self.engine._first,self.engine._second=self.first,self.second
            self.starts+=1
        elif self.engine is not None:
            self.engine.step(actual.edge_inputs)
        if self.engine is not None and command.get('command')!=4:
            model=self.engine
            phase={'active':1,'waiting':2,'checked':3,'qualifying':4,'completed':5,'timeout':6,'fault':7}[model.mode]
            expected=dict(mode=2 if phase==5 else 3 if model.done else 1,phase=phase,
                virtual_pc=model.pc,remaining=model.remaining,wait_left=model.wait_left,
                scratch=sum(int(bit)<<k for k,bit in enumerate(model.samples)),
                levels=model.levels,enabled=model.enabled,tx_consumed=model.slot._tx_consumed,
                rx_length=len(model.slot._rx),rx_data=sum(int(bit)<<k for k,bit in enumerate(model.slot._rx)))
            if model.done: expected.update(pc=0,env0=0,env1=0)
            else:
                _,environment=self.program.locate(model.pc)
                expected.update(pc=stored_row(self.program.schedule,model.pc),env0=environment[0],env1=environment[1])
                self.fetch_checks+=1
            require(all(getattr(actual,key)==value for key,value in expected.items()),
                    'Reactive circuit differs from source execution/lookup: '+repr(expected)+' observed '+repr(actual))
            self.compared_edges+=1
        if command.get('command')==4 and not actual.rejected: self.engine=None
        return actual


def i2c_cases(full):
    cases=[]
    base=dict(address=0x53,register=0xa6,reply=b'\x96\xa5\x55\x3c',phase_cycles=4,wait_cycles=32)
    if full:
        for lane in range(4):
            for value in range(256):
                reply=bytearray(base['reply']);reply[lane]=value
                cases.append(dict(base,reply=bytes(reply)))
    else: cases.append(base)
    cases += [dict(base,reply=base['reply'][:n]) for n in (1,2)]
    cases += [dict(base,address=address,register=register) for address,register in ((0,0),(127,255))]
    cases += [dict(base,ack_bits=tuple(int(k==stage) for k in range(3))) for stage in range(3)]
    cases += [dict(base,phase_cycles=h,wait_cycles=w,stretch_cycles=s)
              for h,w,s in ((3,32,0),(4,32,1),(4,32,15),(7,32,28),(4,32,30),(4,32,31),(4,4,2),(4,4,3))]
    cases += [dict(base,initially_stuck=True),dict(base,never_after_bits=37),dict(base,stop_sda_stuck=True)]
    return cases


def wire_gate(executable,full=False):
    results,images=[],[]
    with BufferedReactiveRTL(CAD/'vvp',executable) as rtl:
        reference=ReferenceTransport(rtl);host=BufferedReactiveHardwareHost(reference)
        host.initialize()
        loaded,configuration,uploads=None,None,0
        fixtures=[('spi',(n,half),dict(n=n,half=half,tco=tco,tx=tx,rx=rx))
                  for n,half,tco,tx,rx in spi_cases(full)]
        fixtures += [('jtag',(n,half),dict(n=n,half=half,tco=tco,state=state,tx=tx,rx=rx))
                     for n,half,tco,state,tx,rx in jtag_cases(full)]
        fixtures += [('i2c',(len(c['reply']),c['phase_cycles'],c['wait_cycles']),c) for c in i2c_cases(full)]
        for protocol,config,c in fixtures:
            if configuration!=(protocol,config):
                reference.program=(compact_spi(*config) if protocol=='spi' else compact_jtag(*config)
                    if protocol=='jtag' else buffered_i2c_read(*config))
                loaded=host.load(reference.program);uploads+=len(loaded.image.words)
                images.append(dict(protocol=protocol,configuration=list(config),image_key=loaded.image.key,**loaded.image.storage()))
                configuration=protocol,config
            if protocol=='spi':
                peer=BufferedSPIPeer(c['tx'],c['rx'],c['half'],c['tco']);outgoing,reply=c['tx'],c['rx'];outcome='complete'
            elif protocol=='jtag':
                peer=BufferedJTAGPeer(c['tx'],c['rx'],c['n'],c['half'],c['tco'],initial_state=c['state'])
                outgoing=c['tx'].to_bytes((c['n']+7)//8,'little');reply=c['rx'].to_bytes((c['n']+7)//8,'little');outcome='complete'
            else:
                args={k:v for k,v in c.items() if k!='wait_cycles'}
                peer=BufferedI2CReadPeer(**args)
                outgoing,reply=register_read_tx(c['address'],c['register']),c['reply']
                timeout=(c.get('initially_stuck') or c.get('never_after_bits') is not None or c.get('stop_sda_stuck') or
                         c.get('stretch_cycles',0)>c['wait_cycles']-2)
                outcome='timeout' if timeout else 'fault' if any(c.get('ack_bits',())) else 'complete'
            rtl.device=peer;pending=loaded.submit(tx=outgoing)
            try: pending.wait(timeout_cycles=0)
            except BufferedHardwareWaitTimeout as error: require(error.pending is pending,'Host timeout lost owner')
            else: raise RuntimeError('Zero host wait completed wire transfer')
            pending.wait(timeout_cycles=200_000)
            first=pending.read()
            require(first.outcome==outcome and first.payload==(reply if outcome=='complete' else None),
                    'Reactive retained result differs from independent peer')
            require(first==pending.read(),'Reactive retained result changed on repeat read')
            record=(peer.check(first.raw_rx_bits,timeout=outcome=='timeout') if protocol=='i2c' else peer.check(first.raw_rx_bits))
            results.append(dict(record,outcome=outcome,tx_consumed_bits=first.tx_consumed_bits,
                                rx_valid_bits=first.rx_valid_bits))
            before=host.edges
            try: loaded.submit(tx=outgoing)
            except TransferError: pass
            else: raise RuntimeError('Host overwrote retained reactive result')
            require(host.edges==before,'Ownership rejection emitted edge')
            pending.release();rtl.device=None
        require(sum(r['command']['command']==1 for r in rtl.records)==uploads,'Transfers reuploaded program storage')
        return dict(cases=len(results),spi_cases=len(spi_cases(full)),jtag_cases=len(jtag_cases(full)),
            i2c_cases=len(i2c_cases(full)),starts=reference.starts,reference_edges=reference.compared_edges,
            fetch_environment_checks=reference.fetch_checks,independent_sampler_checks=reference.sampler_checks,
            circuit_edges=rtl.cycle,uploaded_program_rows=uploads,uploaded_program_bits=uploads*144,
            program_images=images,indexed_reads_retained_twice=True,host_wait_timeout_recovered=True,
            cases_sha256=hashlib.sha256(json.dumps(results,sort_keys=True).encode()).hexdigest(),
            i2c_failures=[r for r in results if r.get('protocol')=='i2c-register-read' and r['outcome']!='complete'])
def replay_gate(executable, exported):
    edges = 0
    for case in exported['cases']:
        with BufferedReactiveRTL(CAD / 'vvp', executable) as rtl:
            edges += replay_vectors(rtl, case['vectors'])['edges']
    return dict(cases=len(exported['cases']), edges=edges, public_state_fields=26)


def execution_mutants(run,out,exported,labels=None):
    """Re-emit narrow circuit equation corruptions; preserve typed expectations."""
    original=(ROOT/'Pinwheel/Hardware/Buffered/Reactive.lean').read_text()
    branch_start=original.index('def branchBit : E 1 :=')
    branch_end=original.index('def finish : E 2 :=',branch_start)
    old_scratch=original[:branch_start]+'''def branchBit : E 1 := Execution.readTree 4
  (fun k => .slice k.toNat 1 (by omega) (.reg .scratch)) branchSample
'''+original[branch_end:]
    guard_start=original.index('def checkedReady : E 1 :=')
    guard_end=original.index('def waitReady : E 1 :=',guard_start)
    guard=original[:guard_start]+'def checkedReady : E 1 := .lit 1\n'+original[guard_end:]
    priority_anchor='(both (isPhase 2) (both (.inv waitReady) (.zero (.reg .remaining))))'
    require(original.count(priority_anchor)==1,'Missing WAIT timeout priority mutation anchor')
    priority=original.replace(priority_anchor,'(both (isPhase 2) (.zero (.reg .remaining)))')
    results={}
    for label,changed in (('old-scratch-branch',old_scratch),('disabled-guard',guard),('timeout-priority',priority)):
        if labels is not None and label not in labels: continue
        require(changed!=original,'Execution mutation did not alter circuit')
        namespace='Pinwheel.CI.BufferedReactive'+''.join(part.title() for part in label.split('-'))
        changed=changed.replace('namespace Pinwheel.Hardware.Buffered.Reactive\n','namespace '+namespace+'\n')
        changed=changed.replace('end Pinwheel.Hardware.Buffered.Reactive\n','end '+namespace+'\n')
        changed=changed.replace('MemoEmit.moduleText','Pinwheel.Hardware.Buffered.MemoEmit.moduleText')
        changed+='''\ndef main (args : List String) : IO Unit := do
  let text ← match '''+namespace+'''.moduleText with
    | .ok text => pure text
    | .error error => throw (IO.userError error)
  IO.FS.writeFile (args.headD "negative.mlir") text
'''
        source=out/(label+'-negative.lean');source.write_text(changed)
        mlir=out/(label+'-negative.mlir')
        run(['lake','env','lean','-DwarningAsError=true','--run',source,mlir],label+'-negative-emit')
        sv=run([CIRCT,mlir,'--canonicalize','--lower-seq-to-sv','--lower-hw-to-sv',
            '--hw-legalize-modules','--export-verilog','-o','/dev/null'],label+'-negative-circt')
        target=out/(label+'-negative.sv');target.write_text(sv)
        executable=compile_reactive(run,out,target,label+'-negative')
        try: replay_gate(executable,exported)
        except RuntimeError as error:
            require('Reactive buffered RTL public state mismatch' in str(error),
                    label+' negative failed outside represented state')
        else: raise RuntimeError(label+' circuit mutation was accepted')
        results[label]='rejected for public execution state mismatch'
    return results

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--pdk-root', type=Path)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/buffered-reactive-hardware', args.tag)
    run = Commands(ROOT, out, default_timeout=1800)
    started = time.monotonic()
    report = dict(schema='pinwheel-buffered-reactive-hardware-results-v1', target=TARGET,
                  status='running', commands=run.records)
    try:
        pdk = stage_pdk(pdk_root=args.pdk_root)
        sources = [ROOT / name for name in ('Pinwheel.lean', 'lean-toolchain',
                    'lakefile.toml', 'lake-manifest.json', 'tools/technology-library.json',
                    'tools/hardware-toolchain.json', 'physical/buffered_reactive_host_bridge.sv')]
        sources += sorted((ROOT / 'Pinwheel').rglob('*.lean'))
        sources += sorted((ROOT / 'test').glob('*.lean')) + sorted((ROOT / 'test').glob('test_*.py'))
        sources += sorted((ROOT / 'scripts').glob('*.py'))
        sources += [CIRCT, *[CAD / name for name in ('yosys', 'yosys-abc', 'iverilog', 'vvp')],
                    *[CAD.parent / 'libexec' / name for name in
                      ('yosys', 'yosys-abc', 'iverilog', 'vvp', 'ivl', 'ivlpp', 'realpath')],
                    Path(pdk['library']), *map(Path, pdk['models']),
                    ROOT / 'build/tools/oss-cad-suite/share/yosys/simcells.v']
        source_hashes = {str(path.relative_to(ROOT)): sha(path) for path in sources}
        report['source_sha256'] = source_hashes
        version = run(['lake', 'env', 'lean', '--version'], 'lean-version').strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        require(bool(re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version)),
                'Lean version differs from its repository pin')
        report['lean'] = version
        report['tools'] = {
            'circt': run([CIRCT, '--version'], 'circt-version').strip(),
            'yosys': run([CAD / 'yosys', '-V'], 'yosys-version').strip(),
            'iverilog': run([CAD / 'iverilog', '-V'], 'iverilog-version').strip(),
        }
        run(['lake', 'build'], 'build')
        audit = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'test/ProofAudit.lean'], 'axioms')
        counts = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', audit)
        require(counts is not None, 'Missing whole-library axiom audit')
        report['audit'] = dict(declarations=int(counts[1]), theorems=int(counts[2]))
        audit_text = (ROOT / 'test/ProofAudit.lean').read_text().removesuffix('#audit_pinwheel\n')
        mutant = out / 'RejectAxiom.lean'
        mutant.write_text(audit_text + 'axiom Pinwheel.CI.untrusted : False\n#audit_pinwheel\n')
        run(['lake', 'env', 'lean', mutant], 'axiom-negative',
            reject='Unapproved axioms in Pinwheel.CI.untrusted')
        lean = ['lake', 'env', 'lean', '-DwarningAsError=true', '--run']
        run([*lean, 'test/BufferedReactiveHardware.lean'], 'lean-hardware')
        run([*lean, 'test/BufferedHardware.lean'], 'lean-linear-baseline')
        run([*lean, 'test/Buffered.lean'], 'lean-reference')
        model_text = run([*lean, 'test/BufferedExport.lean'], 'typed-model-export')
        model_vectors = json.loads(model_text)
        report['typed_model'] = reference_gate.differential(model_vectors)
        (out / 'model-vectors.json').write_text(json.dumps(model_vectors,indent=2)+'\n')
        request = command_cases(model_vectors)
        (out / 'input.json').write_text(json.dumps(request, indent=2) + '\n')
        run([*lean, 'test/BufferedReactiveHardwareExport.lean', out / 'input.json', out], 'emit-vectors')
        exported = json.loads((out / 'vectors.json').read_text())
        report['command_expectations'] = check_export(request, exported)
        assembly = json.loads((out / 'assembly.json').read_text())
        report['declared_register_bits'] = sum(slot['width'] for slot in assembly['registers'])
        sv = run([CIRCT, out / 'core.mlir', '--canonicalize', '--lower-seq-to-sv',
                  '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog',
                  '-o', '/dev/null'], 'circt-export')
        (out / 'core.sv').write_text(sv)
        executable = compile_reactive(run, out, out / 'core.sv', 'emitted')
        report['emitted_control'] = replay_gate(executable, exported)
        report['emitted_wire'] = wire_gate(executable, full=True)
        changed = sv.replace('r_stage2[0]', 'r_stage1[0]').replace('r_stage2[1]', 'r_stage1[1]')
        require(changed != sv, 'Missing emitted RX sampler negative-control anchor')
        (out / 'capture-negative.sv').write_text(changed)
        negative = compile_reactive(run, out, out / 'capture-negative.sv', 'capture-negative')
        try:
            replay_gate(negative, exported)
        except RuntimeError as error:
            require('Reactive buffered RTL public state mismatch' in str(error),
                    'Capture negative failed outside its represented execution state')
        else:
            raise RuntimeError('One-stage RX capture mutant was accepted')
        report['capture_negative_rejected'] = True
        changed = sv.replace('r_stage2[1]', 'r_stage2[0]')
        require(changed != sv, 'Missing emitted input-selection negative-control anchor')
        (out / 'input-selection-negative.sv').write_text(changed)
        negative = compile_reactive(run, out, out / 'input-selection-negative.sv', 'input-selection-negative')
        try:
            replay_gate(negative, exported)
        except RuntimeError as error:
            require('Reactive buffered RTL public state mismatch' in str(error),
                    'Input-selection negative failed outside represented execution state')
        else:
            raise RuntimeError('Hardwired first-input RX mutant was accepted')
        report['input_selection_negative_rejected'] = True
        changed = sv.replace('r_current_control[21]', "1'h0")
        require(changed != sv, 'Missing emitted inner-rollover negative-control anchor')
        (out / 'rollover-negative.sv').write_text(changed)
        negative = compile_reactive(run, out, out / 'rollover-negative.sv', 'rollover-negative')
        try:
            replay_gate(negative, exported)
        except RuntimeError as error:
            require('Reactive buffered RTL public state mismatch' in str(error),
                    'Rollover negative failed outside represented execution state')
        else:
            raise RuntimeError('Disabled inner rollover mutant was accepted')
        report['rollover_negative_rejected'] = True
        branch_mutant=deepcopy(exported)
        chosen=next(c for c in branch_mutant['cases'] if c['name']=='reference-branch-loop-environment-19')
        uploaded=next(v for v in chosen['vectors'] if v['command'].get('command')==1 and v['command'].get('address')==0)
        uploaded['command']['branch'] &= ~(7 << 24) # erase absolute destination outer index2
        (out / 'endpoint-negative.json').write_text(json.dumps(branch_mutant,indent=2)+'\n')
        try:
            replay_gate(executable,branch_mutant)
        except RuntimeError as error:
            require('Reactive buffered RTL public state mismatch' in str(error),'Endpoint negative failed outside represented state')
        else: raise RuntimeError('Erased absolute destination loop environment was accepted')
        report['endpoint_environment_negative_rejected']=True
        report['reactive_execution_negatives']=execution_mutants(run,out,exported)

        report['synthesis'] = synthesize(run, out, out / 'core.sv', pdk_root=args.pdk_root,
            top='pinwheel_buffered_reactive', storage=STORAGE, bridge=BRIDGE,
            testbench='buffered_reactive_host_bridge')
        for variant, artifact in report['synthesis']['variants'].items():
            gate = Path(artifact['executable'])
            artifact['control_replay'] = replay_gate(gate, exported)
            artifact['wire_replay'] = wire_gate(gate)
        report['python'] = {}
        for label, optimization in (('python', []), ('python-optimized', ['-O'])):
            output = run([sys.executable, *optimization, '-B', '-m', 'unittest', 'discover',
                          '-s', 'test', '-p', 'test_*.py'], label)
            totals = re.search(r'Ran (\d+) tests', output)
            require(totals is not None, 'Missing Python regression count')
            skips = re.search(r'skipped=(\d+)', output)
            report['python'][label] = dict(total=int(totals[1]),
                skipped=int(skips[1]) if skips else 0)
        preservation_path = ROOT / 'build/buffered-reactive-hardware/baseline-preservation.json'
        if not preservation_path.exists():
            manifest = json.loads((ROOT / 'physical/experiments/buffered-reactive-hardware-results.json').read_text())
            record = manifest['preservation']
            data = (json.dumps({key: record[key] for key in ('base', 'prior_sha256')}, indent=2)+'\n').encode()
            require(hashlib.sha256(data).hexdigest() == record['baseline_map_sha256'],
                    'Tracked predecessor map digest differs')
            preservation_path.write_bytes(data)
        preservation = json.loads(preservation_path.read_text())
        for name, digest in preservation['prior_sha256'].items():
            require(sha(ROOT / name) == digest, 'Prior hardware/physical artifact changed: ' + name)
        report['preservation'] = dict(base=preservation['base'],
            previous_files=len(preservation['prior_sha256']), unchanged=True,
            baseline_map_sha256=sha(ROOT / 'build/buffered-reactive-hardware/baseline-preservation.json'))
        for name, digest in source_hashes.items():
            require(sha(ROOT / name) == digest, 'Source changed during hardware validation: ' + name)
        report.update(status='passed', inputs_unchanged=True,
            elapsed_seconds=round(time.monotonic()-started, 3),
            boundary='Opt-in reloadable reactive counted parallel hardware target, actual typed reference '
                     'and circuit snapshots, SPI/JTAG/I2C wire traces, saved generic/typical CMOS5L '
                     'state-cut equivalence and retained indexed ownership. No universal initialized '
                     'compiler/package refinement, SRAM, serial package, physical routing or timing qualification.')
        report['artifact_sha256'] = {str(path.relative_to(out)): sha(path)
            for path in out.rglob('*') if path.is_file() and path.name != 'report.json'}
    except BaseException as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Buffered reactive hardware gate passed: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
