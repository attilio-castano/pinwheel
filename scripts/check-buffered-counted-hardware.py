#!/usr/bin/env python3
"""Compact counted timed programs through typed circuit, emitted RTL and saved gates.

This opt-in counted parallel target has no reactive execution, paired SRAM/serial
package integration, routed timing or physical qualification.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import time

from buffered_engine import (BufferedEngine, BufferedInstruction, BufferedProgram,
    BufferedBlock, BufferedSequence, BufferedRepeat)
from buffered_hardware import (BufferedHardwareWaitTimeout, encode_instruction, pack_wire_bits)
from buffered_counted_hardware import (BufferedCountedHardwareHost, lower_counted,
    compact_spi, compact_jtag)
from buffered_counted_hardware_rtl import BufferedCountedRTL, COMMAND_FIELDS, replay_vectors
from buffered_hardware_synthesis import CAD, compile_rtl, stage_pdk, synthesize
from buffered_peers import BufferedSPIPeer, BufferedJTAGPeer
from jtag_peers import TAP
from pad_io import PadDrive
from pinwheel_buffers import TransferError, TransferSlot
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
CIRCT = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
TARGET = 'pinwheel-buffered-counted32-v1'
BRIDGE = ROOT / 'test/buffered_counted_hardware_tb.sv'
STORAGE = dict(tx=[('r_tx_data', 32)], rx=[('r_rx_data', 32)],
    timed_words=[(f'r_word{k}', 56, 0, 32) for k in range(64)],
    controls=[(f'r_word{k}', 56, 32, 24) for k in range(64)],
    written_mask=[('r_written', 64)])
STATE_WIDTHS = dict(valid=1, busy=1, retained=1, pending=1, rejected=1, mode=2,
    pc=8, remaining=8, levels=3, enabled=3, tx_consumed=6, rx_length=6, rx_data=32,
    read_valid=1, read_bit=1, generation=16, transfer=16, exhausted=1, stage1=2, stage2=2, virtual_pc=10, env0=3, env1=3)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def compile_counted(run, out, source, label):
    return compile_rtl(run, out, source, label, bridge=BRIDGE,
                       testbench='buffered_counted_hardware_tb')


def loop_control(depth, *, outer_start=0, outer_count=1, inner_start=0,
                 inner_count=1, outer_end=False, inner_end=False):
    """Independent bit packing; do not reuse the host's control encoder."""
    return (depth | (outer_start << 2) | ((outer_count-1) << 8) |
            (inner_start << 11) | ((inner_count-1) << 17) |
            (int(outer_end) << 20) | (int(inner_end) << 21))


def command_cases():
    """Directed loop/ownership expectations and every three-edge raw history."""
    cases = []

    def case():
        vectors, checks = [], []
        def edge(raw=3, expect=None, **command):
            vectors.append(dict(command=command, raw_inputs=raw))
            if expect is not None:
                checks.append(dict(edge=len(vectors)-1, state=expect))
        def load(words, controls=None, span=None, idle=4):
            controls = [0]*len(words) if controls is None else controls
            for address, (word, control) in enumerate(zip(words, controls, strict=True)):
                edge(command=1, address=address, word=word, control=control)
            edge(command=2, count=len(words), virtual_span=len(words) if span is None else span,
                 idle_levels=idle, idle_enabled=7,
                 expect=dict(valid=1, pending=0, rejected=0))
        edge(initialize=1, expect=dict(generation=0, transfer=0, retained=0, busy=0,
                                      pc=0, virtual_pc=0, env0=0, env1=0))
        return edge, load, vectors, checks

    def finish(name, vs, cs):
        cases.append(dict(name=name, vectors=vs, checks=cs))

    e, load, vs, cs = case()
    e(command=2, count=1, virtual_span=1, expect=dict(rejected=1, valid=0, generation=0))
    e(command=1, address=0, word=3)
    for count, span in ((0,1),(2,2),(65,65),(127,127),(1,0),(1,1025),(1,2047)):
        e(command=2, count=count, virtual_span=span,
          expect=dict(rejected=1, valid=0, generation=0))
    e(command=2, count=1, virtual_span=1024, idle_levels=4, idle_enabled=7,
      expect=dict(rejected=0, valid=1, generation=1))
    e(command=3, expected_generation=0, expect=dict(rejected=1, transfer=0))
    for tx, rx in ((33,0),(0,33),(63,63)):
        e(command=3, expected_generation=1, tx_length=tx, rx_capacity=rx,
          expect=dict(rejected=1, transfer=0))
    e(command=3, expected_generation=1,
      expect=dict(rejected=0, mode=2, retained=1, transfer=1, pc=0, virtual_pc=0))
    for command in (1,2,3):
        e(command=command, expected_generation=1, count=1, virtual_span=1, word=4,
          expect=dict(rejected=1, mode=2, retained=1, generation=1, transfer=1))
    for generation, transfer in ((1,2),(0,1)):
        e(command=4, expected_generation=generation, expected_transfer=transfer,
          expect=dict(rejected=1, retained=1))
    e(command=4, expected_generation=1, expected_transfer=1,
      expect=dict(rejected=0, retained=0, mode=0))
    finish('coverage-count-span-and-ownership',vs,cs)

    shift = encode_instruction(BufferedInstruction('shift',append_input=0,shift_pin=0))
    drive = encode_instruction(BufferedInstruction('drive',append_input=0))
    keep = encode_instruction(BufferedInstruction('keep',append_input=0))
    nested = loop_control(2,outer_count=2,inner_count=3,outer_end=True,inner_end=True)
    invalid_controls = [3, 1<<22, 1<<2,
        loop_control(1,inner_start=1), loop_control(1,inner_end=True),
        loop_control(2,outer_end=True), loop_control(1,outer_start=1),
        loop_control(2,inner_start=1)]
    failures = [
        ('underflow-in-second-iteration',[shift,3],[nested,0],7,1,6,1,1),
        ('overflow-after-loop-tx',[shift,3],[nested,0],7,6,1,2,1),
        ('underflow-zero-tx',[shift,3],[nested,0],7,0,1,0,0),
        ('underflow-before-overflow',[shift,3],[nested,0],7,0,0,0,0),
        ('malformed-word-before-effects',[shift|(1<<24),3],[nested,0],7,6,6,0,0),
        ('malformed-word-retains-prefix',[shift,shift|(1<<24),3],[0,0,0],3,2,2,1,1),
        ('virtual-span-fault-before-effects',[shift,shift,3],[0,0,0],1,2,2,1,1),
        ('physical-falloff-before-effects',[shift],[0],2,2,2,1,1),
        ('terminal-control-must-zero',[3],[nested],1,0,0,0,0),
        ('explicit-fault',[4],[0],1,0,0,0,0),
    ]
    failures += [(f'control-corruption-{n}',[shift,3],[control,0],2,1,1,0,0)
                 for n,control in enumerate(invalid_controls)]
    for name,words,controls,span,tx,rx,consumed,appended in failures:
        e,load,vs,cs=case()
        load(words,controls,span)
        e(command=3,expected_generation=1,tx_data=63,tx_length=tx,rx_capacity=rx)
        for _ in range(8): e()
        e(expect=dict(mode=3,retained=1,levels=4,enabled=7,pc=0,virtual_pc=0,
                      env0=0,env1=0,tx_consumed=consumed,rx_length=appended))
        for index in range(appended):
            e(read_index=index,expect=dict(read_valid=1,read_bit=1))
        e(command=4,expected_generation=1,expected_transfer=1,
          expect=dict(retained=0,tx_consumed=0,rx_length=0))
        finish(name,vs,cs)

    for duration in (1,2,256):
        e,load,vs,cs=case()
        word=encode_instruction(BufferedInstruction('shift',duration,append_input=0,shift_pin=0))
        ctrl=loop_control(2,outer_count=2,inner_count=2,outer_end=True,inner_end=True)
        load([word,3],[ctrl,0],5)
        for entry in range(4):
            command=dict(command=3,expected_generation=1,tx_data=15,tx_length=4,rx_capacity=4) if entry==0 else {}
            e(**command,expect=dict(mode=1,pc=0,virtual_pc=entry,
                env0=entry%2,env1=entry//2,remaining=duration-1,
                tx_consumed=entry+1,rx_length=entry+1))
            # Check representative held edges; duration256 is still a full trace.
            for remaining in range(duration-2,-1,-1):
                e(expect=dict(pc=0,virtual_pc=entry,env0=entry%2,env1=entry//2,
                    remaining=remaining,tx_consumed=entry+1,rx_length=entry+1)
                    if remaining in (duration-2,0) else None)
        e(expect=dict(mode=2,retained=1,pc=0,virtual_pc=0,env0=0,env1=0,
                      tx_consumed=4,rx_length=4))
        finish(f'nested-rollover-duration-{duration}',vs,cs)

    e,load,vs,cs=case()
    load([shift,shift,3],[loop_control(1,outer_count=2,outer_end=True),
        loop_control(1,outer_start=1,outer_count=3,outer_end=True),0],6)
    for virtual,(row,index) in enumerate(((0,0),(0,1),(1,0),(1,1),(1,2))):
        command=dict(command=3,expected_generation=1,tx_data=31,tx_length=5,rx_capacity=5) if virtual==0 else {}
        e(**command,expect=dict(pc=row,virtual_pc=virtual,env0=index,env1=0,
            tx_consumed=virtual+1,rx_length=virtual+1))
    e(expect=dict(mode=2,retained=1,tx_consumed=5,rx_length=5))
    finish('adjacent-loops-reset-indices',vs,cs)

    e,load,vs,cs=case()
    load([shift,keep,3],[loop_control(2,outer_count=2,inner_count=2,inner_end=True),
         loop_control(1,outer_count=2,outer_end=True),0],7)
    positions=((0,0,0),(0,1,0),(1,0,0),(0,0,1),(0,1,1),(1,1,0))
    consumed=0
    for virtual,(row,env0,env1) in enumerate(positions):
        consumed+=row==0
        command=dict(command=3,expected_generation=1,tx_data=15,tx_length=4,rx_capacity=6) if virtual==0 else {}
        e(**command,expect=dict(pc=row,virtual_pc=virtual,env0=env0,env1=env1,
            tx_consumed=consumed,rx_length=virtual+1))
    e(expect=dict(mode=2,retained=1,tx_consumed=4,rx_length=6))
    finish('inner-loop-then-outer-tail',vs,cs)

    e,load,vs,cs=case()
    load([encode_instruction(BufferedInstruction('drive')),3],
        [loop_control(2,outer_count=8,inner_count=8,outer_end=True,inner_end=True),0],65)
    for virtual in range(64):
        command=dict(command=3,expected_generation=1) if virtual==0 else {}
        e(**command,expect=dict(pc=0,virtual_pc=virtual,env0=virtual%8,env1=virtual//8,busy=1))
    e(expect=dict(mode=2,retained=1,pc=0,virtual_pc=0))
    finish('full-eight-by-eight-rollover',vs,cs)

    e,load,vs,cs=case()
    load([shift]+[encode_instruction(BufferedInstruction('drive'))]*63,span=65)
    e(command=3,expected_generation=1,tx_data=3,tx_length=2,rx_capacity=2,
      expect=dict(pc=0,busy=1,tx_consumed=1,rx_length=1))
    for _ in range(63): e()
    e(expect=dict(mode=3,retained=1,pc=0,virtual_pc=0,tx_consumed=1,rx_length=1))
    finish('dispatch-past-physical-row63',vs,cs)

    e,load,vs,cs=case()
    controls=[loop_control(2,outer_start=row,outer_count=8,inner_start=row,
        inner_count=8,outer_end=True,inner_end=True) for row in range(16)]
    load([encode_instruction(BufferedInstruction('drive'))]*16+[shift],controls+[0],1024)
    for virtual in range(1024):
        command=dict(command=3,expected_generation=1,tx_data=1,tx_length=1,rx_capacity=1) if virtual==0 else {}
        e(**command,expect=dict(pc=virtual//64,virtual_pc=virtual,
            env0=virtual%8,env1=(virtual//8)%8,tx_consumed=0,rx_length=0)
            if virtual in (0,1022,1023) else None)
    e(expect=dict(mode=3,retained=1,pc=0,virtual_pc=0,env0=0,env1=0,
                  tx_consumed=0,rx_length=0))
    finish('virtual-position1023-fault-before-next-effects',vs,cs)

    e,load,vs,cs=case()
    load([shift,shift,keep,3],[loop_control(1,outer_count=2),
        loop_control(1,outer_count=1),loop_control(1,outer_count=2,outer_end=True),0],7)
    e(command=3,expected_generation=1,tx_data=7,tx_length=3,rx_capacity=5)
    for _ in range(4): e()
    e(expect=dict(mode=3,retained=1,tx_consumed=3,rx_length=4,
        pc=0,virtual_pc=0,env0=0,env1=0))
    finish('carried-index-exceeds-destination-bound',vs,cs)

    e,load,vs,cs=case()
    load([encode_instruction(BufferedInstruction('drive')),shift,3],
         [0,loop_control(2,outer_start=1,inner_start=0),0],3)
    e(command=3,expected_generation=1,tx_data=1,tx_length=1,rx_capacity=1)
    e(expect=dict(mode=3,retained=1,tx_consumed=0,rx_length=0))
    finish('outer-start-after-inner-start',vs,cs)

    e,load,vs,cs=case()
    load([encode_instruction(BufferedInstruction('shift',256,shift_pin=0)),3],
        [loop_control(1,outer_count=2,outer_end=True),0],3)
    e(command=3,expected_generation=1,tx_data=3,tx_length=2,
      expect=dict(mode=1,remaining=255,tx_consumed=1,transfer=1))
    for command in (1,2,3,4):
        e(command=command,expected_generation=1,expected_transfer=1,count=2,virtual_span=3,
          expect=dict(rejected=1,busy=1,generation=1,transfer=1,tx_consumed=1))
    e(command=7,expect=dict(mode=0,retained=0,valid=0,generation=2,transfer=1,
         tx_consumed=0,rx_length=0,pc=0,virtual_pc=0,env0=0,env1=0))
    load([3])
    e(command=3,expected_generation=1,expect=dict(rejected=1,transfer=1))
    e(command=3,expected_generation=3,expect=dict(mode=2,retained=1,transfer=2))
    e(command=4,expected_generation=1,expected_transfer=1,expect=dict(rejected=1,retained=1))
    e(command=4,expected_generation=3,expected_transfer=2,expect=dict(rejected=0,retained=0))
    finish('busy-warm-reset-loop-state',vs,cs)

    e,load,vs,cs=case()
    e(raw=0,command=1,address=0,word=drive)
    e(raw=0,command=1,address=1,word=3)
    e(raw=0,command=2,count=2,virtual_span=2,idle_levels=4,idle_enabled=7)
    e(raw=3,command=3,expected_generation=1,rx_capacity=1,
      expect=dict(mode=1,rx_length=1,rx_data=0))
    e(expect=dict(mode=2,rx_length=1,rx_data=0,retained=1))
    finish('first-entry-primed-low',vs,cs)

    e,load,vs,cs=case()
    second = encode_instruction(BufferedInstruction('drive',append_input=1))
    e(raw=2,command=1,address=0,word=second)
    e(raw=2,command=1,address=1,word=3)
    e(raw=2,command=2,count=2,virtual_span=2,idle_levels=4,idle_enabled=7)
    e(raw=0,command=3,expected_generation=1,rx_capacity=1,
      expect=dict(mode=1,rx_length=1,rx_data=1))
    e(expect=dict(mode=2,rx_length=1,rx_data=1,retained=1))
    e(read_index=0,expect=dict(read_valid=1,read_bit=1))
    finish('first-entry-second-input-selected',vs,cs)

    for history in range(64):
        e,load,vs,cs=case()
        load([drive,3],[nested,0],7)
        raw=[(history>>(2*k))&3 for k in range(3)]+[0,2,1]
        sampled=[3,3]+raw[:-2]
        bits=[pads&1 for pads in sampled]
        for virtual,pads in enumerate(raw):
            command=dict(command=3,expected_generation=1,rx_capacity=6) if virtual==0 else {}
            e(raw=pads,**command,expect=dict(pc=0,virtual_pc=virtual,env0=virtual%3,
                env1=virtual//3,rx_length=virtual+1))
        e(expect=dict(mode=2,retained=1,rx_length=6,
            rx_data=sum(bit<<k for k,bit in enumerate(bits))))
        for index,bit in enumerate(bits): e(read_index=index,expect=dict(read_valid=1,read_bit=bit))
        e(read_index=6,expect=dict(read_valid=0,read_bit=0))
        e(command=4,expected_generation=1,expected_transfer=1)
        finish(f'nested-sampler-history-{history}',vs,cs)
    return dict(schema='pinwheel-buffered-counted-input-v1',cases=cases)


def check_export(request, exported):
    require(type(exported) is dict and set(exported) == {'schema', 'cases'},
            'Wrong exported hardware vector envelope')
    require(exported.get('schema') == 'pinwheel-buffered-counted-vectors-v1',
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


class ReferenceTransport:
    """Compare every active edge and the selected leaf/environment to the reference."""
    def __init__(self, rtl):
        self.rtl,self.program=rtl,None
        self.engine=None
        self.compared_edges=self.starts=self.fetch_checks=0

    def edge(self, **command):
        actual=self.rtl.edge(**command)
        if command.get('initialize') or command.get('command')==7:
            self.engine=None
        elif command.get('command')==3 and not actual.rejected:
            require(self.program is not None,'Reference requires the canonical counted source')
            bits=tuple(bool(command['tx_data']&(1<<k)) for k in range(command['tx_length']))
            slot=TransferSlot(tx_capacity_bits=32,rx_capacity_bits=32)
            identity=slot.begin(self.program.key,bits,command['rx_capacity'])
            self.engine=BufferedEngine(slot,identity,self.program)
            require(self.program.fetch(0).append_input is None,
                    'START sampler binding requires a first leaf without RX')
            self.engine._first,self.engine._second=actual.stage1,actual.stage2
            self.starts+=1
        elif self.engine is not None and not self.engine.done:
            self.engine.step(actual.stage1)
        if self.engine is not None and command.get('command')!=4:
            model=self.engine
            expected=dict(mode=2 if model.mode=='completed' else 3 if model.done else 1,
                virtual_pc=model.pc,remaining=model.remaining,levels=model.levels,
                enabled=model.enabled,tx_consumed=model.slot._tx_consumed,
                rx_length=len(model.slot._rx),
                rx_data=sum(int(bit)<<k for k,bit in enumerate(model.slot._rx)))
            if model.done:
                expected.update(pc=0,env0=0,env1=0)
            else:
                _,environment=self.program.locate(model.pc)
                expected.update(pc=stored_row(self.program.schedule,model.pc),
                                env0=environment[0],env1=environment[1])
                self.fetch_checks+=1
            require(all(getattr(actual,key)==value for key,value in expected.items()),
                    'Counted circuit differs from source execution/lookup: '+repr(expected))
            if not model.done:
                require((actual.stage1,actual.stage2)==(model._first,model._second),
                        'Counted circuit sampler age differs from reference')
            self.compared_edges+=1
        if command.get('command')==4 and not actual.rejected:
            self.engine=None
        return actual


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


def wire_gate(executable, full=False):
    results,images=[],[]
    with BufferedCountedRTL(CAD/'vvp',executable) as rtl:
        reference=ReferenceTransport(rtl)
        host=BufferedCountedHardwareHost(reference)
        host.initialize()
        loaded,configuration,uploads=None,None,0
        fixtures=[('spi',n,half,tco,None,tx,rx) for n,half,tco,tx,rx in spi_cases(full)]
        fixtures += [('jtag',n,half,tco,state,tx,rx) for n,half,tco,state,tx,rx in jtag_cases(full)]
        for protocol,n,half,tco,state,tx,rx in fixtures:
            selected=protocol,n,half
            if configuration!=selected:
                reference.program=compact_spi(n,half) if protocol=='spi' else compact_jtag(n,half)
                loaded=host.load(reference.program)
                uploads+=len(loaded.image.words)
                images.append(dict(protocol=protocol,length=n,half_cycles=half,
                    image_key=loaded.image.key,**loaded.image.storage()))
                configuration=selected
            if protocol=='spi':
                peer=BufferedSPIPeer(tx,rx,half,tco)
                outgoing,reply=tx,rx
            else:
                peer=BufferedJTAGPeer(tx,rx,n,half,tco,initial_state=state)
                outgoing=tx.to_bytes((n+7)//8,'little')
                reply=rx.to_bytes((n+7)//8,'little')
            rtl.device=peer
            pending=loaded.submit(tx=outgoing)
            try:
                pending.wait(timeout_cycles=0)
            except BufferedHardwareWaitTimeout as error:
                require(error.pending is pending,'Host wait timeout lost counted owner')
            else:
                raise RuntimeError('Zero host wait unexpectedly completed a wire transfer')
            pending.wait(timeout_cycles=loaded.image.execution_edges+2)
            first=pending.read()
            require(first.payload==reply and first.outcome=='complete',
                    'Counted indexed RX differs from independent peer')
            require(first==pending.read(),'Counted retained result changed on repeat read')
            require(rtl.snapshot.retained==1,'Counted indexed read released ownership')
            results.append(peer.check(first.raw_rx_bits))
            before=host.edges
            try:
                loaded.submit(tx=outgoing)
            except TransferError:
                pass
            else:
                raise RuntimeError('Host overwrote a retained counted result')
            require(host.edges==before,'Host ownership rejection emitted a hardware edge')
            pending.release()
            rtl.device=None
            require(rtl.snapshot.retained==0,'Matching counted release failed')
        require(sum(record['command']['command']==1 for record in rtl.records)==uploads,
                'Repeated counted transfers reuploaded program storage')
        return dict(cases=len(results),spi_cases=len(spi_cases(full)),
            jtag_cases=len(jtag_cases(full)),starts=reference.starts,
            reference_edges=reference.compared_edges,fetch_environment_checks=reference.fetch_checks,
            circuit_edges=rtl.cycle,uploaded_program_rows=uploads,
            uploaded_program_bits=uploads*56,program_images=images,
            indexed_reads_retained_twice=True,host_wait_timeout_recovered=True,
            cases_sha256=hashlib.sha256(json.dumps(results,sort_keys=True).encode()).hexdigest())


def replay_gate(executable, exported):
    edges = 0
    for case in exported['cases']:
        with BufferedCountedRTL(CAD / 'vvp', executable) as rtl:
            edges += replay_vectors(rtl, case['vectors'])['edges']
    return dict(cases=len(exported['cases']), edges=edges, public_state_fields=23)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--pdk-root', type=Path)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/buffered-counted-hardware', args.tag)
    run = Commands(ROOT, out, default_timeout=1800)
    started = time.monotonic()
    report = dict(schema='pinwheel-buffered-counted-results-v1', target=TARGET,
                  status='running', commands=run.records)
    try:
        pdk = stage_pdk(pdk_root=args.pdk_root)
        sources = [ROOT / name for name in ('Pinwheel.lean', 'lean-toolchain',
                    'lakefile.toml', 'lake-manifest.json', 'tools/technology-library.json',
                    'tools/hardware-toolchain.json', 'test/buffered_counted_hardware_tb.sv')]
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
        run([*lean, 'test/BufferedCountedHardware.lean'], 'lean-hardware')
        run([*lean, 'test/BufferedHardware.lean'], 'lean-linear-baseline')
        run([*lean, 'test/Buffered.lean'], 'lean-reference')
        request = command_cases()
        (out / 'input.json').write_text(json.dumps(request, indent=2) + '\n')
        run([*lean, 'test/BufferedCountedHardwareExport.lean', out / 'input.json', out], 'emit-vectors')
        exported = json.loads((out / 'vectors.json').read_text())
        report['command_expectations'] = check_export(request, exported)
        assembly = json.loads((out / 'assembly.json').read_text())
        report['declared_register_bits'] = sum(slot['width'] for slot in assembly['registers'])
        sv = run([CIRCT, out / 'core.mlir', '--canonicalize', '--lower-seq-to-sv',
                  '--lower-hw-to-sv', '--hw-legalize-modules', '--export-verilog',
                  '-o', '/dev/null'], 'circt-export')
        (out / 'core.sv').write_text(sv)
        executable = compile_counted(run, out, out / 'core.sv', 'emitted')
        report['emitted_control'] = replay_gate(executable, exported)
        report['emitted_wire'] = wire_gate(executable, full=True)
        changed = sv.replace('r_stage2[0]', 'r_stage1[0]').replace('r_stage2[1]', 'r_stage1[1]')
        require(changed != sv, 'Missing emitted RX sampler negative-control anchor')
        (out / 'capture-negative.sv').write_text(changed)
        negative = compile_counted(run, out, out / 'capture-negative.sv', 'capture-negative')
        try:
            replay_gate(negative, exported)
        except RuntimeError as error:
            require('Counted buffered RTL public state mismatch' in str(error),
                    'Capture negative failed outside its represented execution state')
        else:
            raise RuntimeError('One-stage RX capture mutant was accepted')
        report['capture_negative_rejected'] = True
        changed = sv.replace('r_stage2[1]', 'r_stage2[0]')
        require(changed != sv, 'Missing emitted input-selection negative-control anchor')
        (out / 'input-selection-negative.sv').write_text(changed)
        negative = compile_counted(run, out, out / 'input-selection-negative.sv', 'input-selection-negative')
        try:
            replay_gate(negative, exported)
        except RuntimeError as error:
            require('Counted buffered RTL public state mismatch' in str(error),
                    'Input-selection negative failed outside represented execution state')
        else:
            raise RuntimeError('Hardwired first-input RX mutant was accepted')
        report['input_selection_negative_rejected'] = True
        changed = sv.replace('r_current_control[21]', "1'h0")
        require(changed != sv, 'Missing emitted inner-rollover negative-control anchor')
        (out / 'rollover-negative.sv').write_text(changed)
        negative = compile_counted(run, out, out / 'rollover-negative.sv', 'rollover-negative')
        try:
            replay_gate(negative, exported)
        except RuntimeError as error:
            require('Counted buffered RTL public state mismatch' in str(error),
                    'Rollover negative failed outside represented execution state')
        else:
            raise RuntimeError('Disabled inner rollover mutant was accepted')
        report['rollover_negative_rejected'] = True
        report['synthesis'] = synthesize(run, out, out / 'core.sv', pdk_root=args.pdk_root,
            top='pinwheel_buffered_counted', storage=STORAGE, bridge=BRIDGE,
            testbench='buffered_counted_hardware_tb')
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
        preservation_path = ROOT / 'build/buffered-counted-hardware/baseline-preservation.json'
        if not preservation_path.exists():
            manifest = json.loads((ROOT / 'physical/experiments/buffered-counted-hardware-results.json').read_text())
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
            baseline_map_sha256=sha(ROOT / 'build/buffered-counted-hardware/baseline-preservation.json'))
        for name, digest in source_hashes.items():
            require(sha(ROOT / name) == digest, 'Source changed during hardware validation: ' + name)
        report.update(status='passed', inputs_unchanged=True,
            elapsed_seconds=round(time.monotonic()-started, 3),
            boundary='Opt-in reloadable counted timed parallel hardware target, finite directed Lean/RTL '
                     'and reference SPI/JTAG traces, saved generic/typical CMOS5L state-cut equivalence '
                     'and indexed result ownership. No reactive hardware, paired SRAM, '
                     'serial package, reset reconnection, physical pads, routing or timing qualification.')
        report['artifact_sha256'] = {str(path.relative_to(out)): sha(path)
            for path in out.rglob('*') if path.is_file() and path.name != 'report.json'}
    except BaseException as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Buffered counted gate passed: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
