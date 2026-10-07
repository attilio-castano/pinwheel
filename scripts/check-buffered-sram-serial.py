#!/usr/bin/env python3
"""Accept the versioned serial frontend and complete two-macro digital package.

Checks actual serial pins, independently reconstructed delivery edges, all
frozen status fields, saved optimized-source frontend mappings and independent
SPI/JTAG/I2C peers. Electrical/CDC/routed package qualification is separate.
"""
import argparse
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import time

from buffered_engine import BufferedBlock, BufferedInstruction, BufferedProgram
from buffered_hardware import BufferedHardwareTransportError, BufferedHardwareWaitTimeout
from buffered_hardware_synthesis import CAD, stage_pdk, synthesize
from buffered_i2c import buffered_i2c_read, register_read_tx
from buffered_i2c_peer import BufferedI2CReadPeer
from buffered_peers import BufferedJTAGPeer, BufferedSPIPeer
from buffered_reactive_hardware import compact_jtag, compact_spi
from buffered_sram_serial import (BufferedSramSerialHost, BufferedSramSerialTransport,
    SerialProtocolError, decode_response, encode_request)
from buffered_sram_serial_reference import FIELDS, WireSchedule, check_trace
from buffered_sram_serial_binding import binding_readback, read_complete_binding
from buffered_sram_serial_mapping import prove_frontend_mapping
from buffered_sram_serial_rtl import BufferedSramSerialRTL
from buffered_sram_hardware import lower_sram
from buffered_shared_branches import lower_shared_branches
from pinwheel_buffers import TransferError
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
CIRCT = ROOT / 'build/tools/firtool-1.159.0/bin/circt-opt'
FRONT = 'pinwheel_buffered_sram_serial_frontend'
TOP = 'pinwheel_buffered_shared_branches_sram_serial'
WRAPPER = ROOT / 'physical/buffered_sram_serial_wrapper.sv'
BRIDGE = ROOT / 'physical/buffered_sram_serial_host_bridge.sv'
MEMORY = ROOT / 'physical/buffered_sram_memory.sv'
VIEWS = ROOT / 'build/storage/macros'
MACRO = 'RM_IHPSG13_1P_64x64_c2_bm_bist'


def require(condition, reason):
    if not condition:
        raise RuntimeError(reason)


def load_sram_gate():
    spec = importlib.util.spec_from_file_location('accepted_sram_gate', ROOT / 'scripts/check-buffered-sram.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def predecessor():
    manifest = ROOT / 'physical/experiments/buffered-sram-results.json'
    accepted = json.loads(manifest.read_text())
    receipt = accepted['reports']['hardware']
    report_path = ROOT / receipt['path']
    report = json.loads(report_path.read_text())
    require(sha(report_path) == receipt['sha256'] and report['status'] == 'passed' and
            not report['smoke'], 'Changed or incomplete accepted SRAM predecessor')
    for name, digest in accepted['accepted_artifact_sha256'].items():
        require(sha(ROOT / name) == digest, 'Changed predecessor artifact: ' + name)
    # New default imports/gate suites are intentional; the accepted execution,
    # source admission and macro wrapper bytes themselves remain frozen.
    critical = ['Pinwheel/Hardware/Buffered/Sram.lean',
        'Pinwheel/Hardware/Buffered/SramModel.lean', 'Pinwheel/Hardware/Buffered/SramProofs.lean',
        'Pinwheel/Hardware/Buffered/SramCandidates.lean',
        'Pinwheel/Hardware/Buffered/Reactive.lean', 'Pinwheel/Hardware/Buffered/SharedBranches.lean',
        'Pinwheel/Hardware/Buffered/MemoBind.lean', 'Pinwheel/Hardware/Buffered/MemoEval.lean',
        'scripts/buffered_sram_hardware.py', 'scripts/buffered_shared_branches.py',
        'scripts/buffered_hardware.py', 'scripts/buffered_reactive_hardware.py',
        'test/BufferedSramExport.lean', 'physical/buffered_sram_memory.sv',
        'physical/buffered_sram_wrapper.sv']
    for name in critical:
        require(sha(ROOT / name) == accepted['frozen_source_sha256'][name],
                'Changed accepted execution/admission source: ' + name)
    return report_path.parent, dict(manifest_sha256=sha(manifest),
        hardware_report_sha256=sha(report_path), critical_source_files=len(critical),
        accepted_artifact_files=len(accepted['accepted_artifact_sha256']))


def request_samples(packet, length=160, varied=False):
    samples = [dict(csn=1, sck=0, mosi=0), dict(csn=0, sck=0, mosi=0)]
    for index in range(length):
        bit = (packet >> (159-index)) & 1 if index < 160 else (index & 1)
        samples += [dict(csn=0, sck=0, mosi=bit)] * (1 + index % 3 if varied else 1)
        samples += [dict(csn=0, sck=1, mosi=bit)] * (2 + index % 2 if varied else 1)
    return samples + [dict(csn=1, sck=0, mosi=0)] * 3


def read_samples(length=192):
    samples = [dict(csn=0, sck=0, mosi=1)]
    for index in range(length):
        samples += [dict(csn=0, sck=0, mosi=index&1), dict(csn=0, sck=1, mosi=index&1)]
    return samples + [dict(csn=1, sck=0, mosi=0)]


def frontend_input():
    cases = []
    def add(name, samples):
        all_samples = [dict(initialize=1, csn=1, sck=0, mosi=0)] + samples
        vectors = []
        for index, sample in enumerate(all_samples):
            status = {name: (index*104729 + k*7919 + 23) % (1 << width)
                      for k, (name, width) in enumerate(FIELDS)}
            pins = dict(initialize=0, raw_inputs=index % 4)
            pins.update(sample)
            vectors.append(dict(pins=pins, status=status))
        cases.append(dict(name=name, vectors=vectors))
    valid = [(0, dict(read_index=31)), (1, dict(address=63, word=(1<<64)-1,
        control=(1<<24)-1, branch=15)), (2, dict(count=64, virtual_span=1024,
        idle_levels=5, idle_enabled=7)), (3, dict(tx_data=0x96a53cc3,
        tx_length=32, rx_capacity=32, expected_generation=65535)),
        (4, dict(expected_generation=23, expected_transfer=41)),
        (6, dict(address=15, branch=(1<<56)-1)), (7, {}), (8, {})]
    for op, fields in valid:
        packet = encode_request(100+op, command=0 if op==8 else op, initialize=int(op==8), **fields)
        add('operation-'+str(op), request_samples(packet, varied=True)+read_samples())
    for version in range(16):
        packet = ((0xA700 | version << 4) << 144) | (version << 128)
        add('version-'+str(version), request_samples(packet)+read_samples())
    for op in (5, 9, 10, 11, 12, 13, 14, 15):
        packet = ((0xA710|op) << 144) | (op << 128)
        add('unsupported-'+str(op), request_samples(packet)+read_samples())
    for op, used in ((0,5),(1,98),(2,24),(3,60),(4,32),(6,60),(7,0),(8,0)):
        for bit in sorted({used,127}):
            packet = ((0xA710|op)<<144) | (77<<128) | (1<<bit)
            add(f'reserved-{op}-{bit}', request_samples(packet)+read_samples())
    packet = encode_request(0x1234, command=7)
    for length in (0,1,15,16,31,32,127,159,161,192,193,320):
        add('length-'+str(length), request_samples(packet,length)+read_samples())
    for length in (1,37,191,193,250):
        add('read-retention-'+str(length),request_samples(packet)+read_samples(length)+read_samples())
    add('request-backpressure',request_samples(packet)+request_samples(encode_request(5,initialize=1))+
        read_samples()+request_samples(encode_request(6,command=7))+read_samples())
    add('high-clock-assertion', [dict(csn=1,sck=0,mosi=0),dict(csn=0,sck=1,mosi=1)]*3+
        [dict(csn=1,sck=0,mosi=0)]+request_samples(packet)+read_samples())
    add('reset-partial-request',request_samples(packet,37)[:-3]+[
        dict(initialize=1,csn=0,sck=1,mosi=1),dict(csn=1,sck=0,mosi=0)]+
        request_samples(packet)+read_samples())
    add('reset-held-response',request_samples(packet)+[
        dict(initialize=1,csn=1,sck=0,mosi=0)]+request_samples(packet)+read_samples())
    return dict(schema='pinwheel-buffered-sram-serial-input-v1', cases=cases)


def native_exporter(run, out, source, label, library):
    c = out / (label+'.c')
    executable = out / label
    run(['lake','env','lean','-DwarningAsError=true','-c',c,source],label+'-c')
    run(['lake','env','leanc','-O3','-o',executable,c,library],label+'-link')
    return executable


def frontend_tb(out, assembly, vectors):
    inputs, outputs, registers = (assembly[key] for key in ('inputs','outputs','registers'))
    columns = [('in_'+p['name'],p['width']) for p in inputs]
    columns += [('pre_'+p['name'],p['width']) for p in outputs]
    columns += [('post_'+p['name'],p['width']) for p in outputs]
    columns += [('state_'+p['name'],p['width']) for p in registers]
    rows = []
    for case in vectors['cases']:
        for vector in case['vectors']:
            input_values = {**vector['pins'], **{'status_'+k:v for k,v in vector['status'].items()}}
            rows.append(' '.join(format(v,'x') for v in [
                *[input_values[p['name']] for p in inputs],
                *[vector['pre_outputs'][p['name']] for p in outputs],
                *[vector['post_outputs'][p['name']] for p in outputs],
                *[vector['post_registers'][p['name']] for p in registers]]))
    fixture = out / 'frontend-fixture.txt'; fixture.write_text('\n'.join(rows)+'\n')
    declarations = '\n'.join(f'reg [{w-1}:0] {name};' for name,w in columns)
    declarations += '\n'+'\n'.join(f'wire [{p["width"]-1}:0] {p["name"]};' for p in outputs)
    ports = ', '.join(['.clk(clk)']+[f'.{p["name"]}(in_{p["name"]})' for p in inputs]+
                     [f'.{p["name"]}({p["name"]})' for p in outputs])
    gated = {'core_initialize','core_command','core_raw_inputs','miso','ready'}
    pre = '\n'.join(f'if ({"1" if p["name"] in gated else "!in_initialize"}) '
        f'if ({p["name"]} !== pre_{p["name"]}) $fatal(1,"Frontend pre mismatch {p["name"]} row %0d",n);' for p in outputs)
    post = '\n'.join(f'if ({p["name"]} !== post_{p["name"]}) $fatal(1,"Frontend post mismatch {p["name"]} row %0d",n);' for p in outputs)
    states = '\n'.join(f'if (dut.{p["name"]} !== state_{p["name"]}) $fatal(1,"Frontend state mismatch {p["name"]} row %0d",n);' for p in registers)
    # RTL registers start unknown. Every case begins with physical POR; only
    # POR-gated outputs are compared before that first initialized edge.
    tb = out / 'frontend-fixture.sv'
    tb.write_text(f'''module buffered_sram_serial_frontend_tb;
reg clk=0;
{declarations}
{FRONT} dut({ports});
integer fd,n=0,code;
initial begin
fd=$fopen("{fixture}","r");
if(!fd) $fatal(1,"Missing frontend fixture");
while(!$feof(fd)) begin
code=$fscanf(fd,"{' '.join(['%h']*len(columns))}\\n",{','.join(name for name,_ in columns)});
if(code != {len(columns)}) $fatal(1,"Malformed frontend fixture");
clk=0; #10;
{pre}
clk=1; #10; clk=0;
{post}
{states}
n=n+1;
end
$display("Frontend finite replay %0d edges",n);
$finish;
end
endmodule
''')
    resets = sum(bool(v['pins'].get('initialize')) for c in vectors['cases'] for v in c['vectors'])
    return tb, dict(cases=len(vectors['cases']), edges=len(rows),
        pre_output_checks=(len(rows)-resets)*len(outputs)+resets*len(gated),
        post_output_checks=len(rows)*len(outputs),
        register_checks=len(rows)*len(registers))


def compile_package(run,out,front,controller,label,models,wrapper=WRAPPER,bridge=BRIDGE,cells=()):
    executable=out/(label+'.vvp')
    run([CAD/'iverilog','-g2012','-DFUNCTIONAL','-s','buffered_sram_serial_host_bridge',
         '-o',executable,front,controller,wrapper,MEMORY,bridge,*models,*cells],label+'-compile')
    return executable


def raw_request(backend,packet,length=160,varied=False):
    for pins in request_samples(packet,length,varied):
        backend.tick(**pins)


def raw_response(backend,length=192):
    word=0
    backend.tick(csn=0,sck=0,mosi=0)
    for _ in range(length):
        backend.tick(csn=0,sck=0,mosi=0)
        observed=backend.tick(csn=0,sck=1,mosi=1)
        word=(word<<1)|observed['miso']
    final=backend.tick(csn=1,sck=0,mosi=0)
    return word,final


def trace_sink(records,annotations,schedule):
    def append(record):
        annotations.append(schedule.step(record['pins']))
        records.append(record)
    return append


def wire_cases(executable, *, bounded=False):
    records,annotations,results=[],[],[]
    with BufferedSramSerialRTL(CAD/'vvp',executable,record_limit=0,
            record_sink=trace_sink(records,annotations,WireSchedule())) as rtl:
        transport=BufferedSramSerialTransport(rtl)
        host=BufferedSramSerialHost(transport); host.initialize()
        fixtures=[]
        for half,tco in ((4,1),(3,0),(7,1))[:1 if bounded else 3]:
            program=compact_spi(4,half)
            for tx,rx in ((b'\x96\xa5\x3c\xc3',b'\xa6\x9b\x42\xe1'),
                    (bytes(4),b'\xff'*4),(b'\xff'*4,bytes(4)))[:1 if bounded else 3]:
                fixtures.append(('spi',(4,half),program,BufferedSPIPeer(tx,rx,half,tco),tx,rx,'complete'))
        for width,state in ((17,'pause_ir'),(1,'test_logic_reset'),(32,'shift_dr'))[:1 if bounded else 3]:
            mask=(1<<width)-1; tx,rx=0x96a53cc3&mask,0xa69b42e1&mask
            fixtures.append(('jtag',(width,4),compact_jtag(width,4),
                BufferedJTAGPeer(tx,rx,width,4,1,initial_state=state),
                tx.to_bytes((width+7)//8,'little'),rx.to_bytes((width+7)//8,'little'),'complete'))
        base=dict(address=0x53,register=0xa6,reply=b'\x96\xa5\x55\x3c',phase_cycles=4)
        i2c=[({},32,'complete'),({'stretch_cycles':15},32,'complete')]
        i2c += [(dict(ack_bits=tuple(int(k==stage) for k in range(3))),32,'fault') for stage in range(3)]
        i2c += [(dict(initially_stuck=True),32,'timeout'),(dict(never_after_bits=37),32,'timeout'),
                (dict(stop_sda_stuck=True),32,'timeout'),(dict(stretch_cycles=31),32,'timeout')]
        for overrides,wait,outcome in i2c[:1 if bounded else len(i2c)]:
            case=dict(base,**overrides)
            fixtures.append(('i2c',(4,4,wait),buffered_i2c_read(4,4,wait),
                BufferedI2CReadPeer(**case),register_read_tx(base['address'],base['register']),base['reply'],outcome))
        configuration=loaded=None
        zero_timeout=0
        images=[]
        for protocol,config,program,peer,tx,rx,outcome in fixtures:
            if configuration != (protocol,config):
                loaded=host.load(program); configuration=(protocol,config)
                images.append(dict(protocol=protocol,configuration=list(config),image_key=loaded.image.key,
                                   **loaded.image.storage()))
            rtl.device=peer; pending=loaded.submit(tx=tx)
            try: pending.wait(timeout_polls=0)
            except BufferedHardwareWaitTimeout as error:
                require(error.pending is pending,'Serial wait timeout lost owner'); zero_timeout+=1
            pending.wait(timeout_polls=2000)
            result=pending.read()
            require(result.outcome==outcome and result.payload==(rx if outcome=='complete' else None),
                    'Serial retained result differs from independent wire peer')
            require(result==pending.read(),'Serial repeat read changed retained result')
            checked=(peer.check(result.raw_rx_bits,timeout=outcome=='timeout')
                     if protocol=='i2c' else peer.check(result.raw_rx_bits))
            before=rtl.cycle
            try: loaded.submit(tx=tx)
            except TransferError: pass
            else: raise RuntimeError('Serial host overwrote retained owner')
            require(rtl.cycle==before,'Local owner rejection emitted physical clocks')
            results.append(dict(checked,outcome=outcome,rx_valid_bits=result.rx_valid_bits,
                                tx_consumed_bits=result.tx_consumed_bits))
            pending.release(); rtl.device=None
        report=dict(cases=len(results),spi_cases=sum(p=='spi' for p,*_ in fixtures),
            jtag_cases=sum(p=='jtag' for p,*_ in fixtures),i2c_cases=sum(p=='i2c' for p,*_ in fixtures),
            physical_edges=rtl.cycle,requests=transport.requests,responses=transport.responses,
            program_images=images,zero_poll_timeouts=zero_timeout,results_retained_twice=True,
            peer_results=results)
    return records,annotations,report


def protocol_cases(executable):
    records,annotations=[],[]
    with BufferedSramSerialRTL(CAD/'vvp',executable,record_limit=0,
            record_sink=trace_sink(records,annotations,WireSchedule())) as rtl:
        host=BufferedSramSerialHost(BufferedSramSerialTransport(rtl));host.initialize()
        loaded=host.load(compact_spi(1))
        generation=host._generation
        before=rtl.cycle
        try:host.load(lower_shared_branches(compact_spi(1)))
        except ValueError:pass
        else:raise RuntimeError('Serial host admitted the wrong image target')
        damaged=lower_sram(compact_spi(1))
        object.__setattr__(damaged,'words',(damaged.words[0]^8,)+damaged.words[1:])
        try:host.load(damaged)
        except ValueError:pass
        else:raise RuntimeError('Serial host admitted a tampered source image')
        require(rtl.cycle==before,'Image rejection emitted physical clocks')
        errors=[]
        for name,packet,length,code in [
            ('short',encode_request(31,command=7),159,1),
            ('overlong',encode_request(32,command=7),193,1),
            ('wrong-version',(0xA720<<144)|(33<<128),160,2),
            ('unknown-op',(0xA715<<144)|(34<<128),160,3),
            ('reserved',(0xA711<<144)|(35<<128)|(1<<98),160,3)]:
            raw_request(rtl,packet,length,varied=True)
            word,final=raw_response(rtl)
            _,observed,status=decode_response(word)
            require(observed==code and status['valid'] and status['generation']==generation and not final['ready'],
                    'Malformed serial frame affected committed image: '+name)
            errors.append(name)
        # A held receipt is retried from the first bit, and a would-be START
        # cannot cross that backpressure boundary.
        raw_request(rtl,encode_request(36,command=0))
        original,_=raw_response(rtl,37)
        require(rtl.snapshot.ready,'Partial serial read consumed held receipt')
        raw_request(rtl,encode_request(37,command=3,tx_data=0x96,tx_length=8,
            rx_capacity=8,expected_generation=generation))
        require(rtl.snapshot.ready,'Request while ready consumed held receipt')
        _,final=raw_response(rtl,193)
        require(final['ready'],'Overlong serial read consumed held receipt')
        word,final=raw_response(rtl)
        sequence,code,status=decode_response(word)
        require(sequence==36 and code==0 and status['transfer']==0 and not final['ready'],
                'Held receipt changed or delivered a backpressured START')
        require(original==word>>(192-37),'Partial read did not preserve response prefix')
        # Wrong owner release, busy/retained raw commands, and retained restart.
        peer=BufferedSPIPeer(b'\x96',b'\xa6',4,1);rtl.device=peer
        pending=loaded.submit(tx=b'\x96');pending.wait(timeout_polls=10);first=pending.read()
        require(first.payload==b'\xa6','Protocol lifecycle SPI result differs')
        peer.check(first.raw_rx_bits);rtl.device=None
        for fields in (dict(command=1,address=0,word=0,control=0,branch=0),
                dict(command=6,address=0,branch=0),dict(command=2,count=1,virtual_span=1),
                dict(command=3,expected_generation=generation),dict(command=4,
                expected_generation=generation,expected_transfer=pending.identity.transfer+1)):
            rejected=host.transport.edge(**fields)
            require(rejected['rejected'] and rejected['retained'] and rejected['transfer']==pending.identity.transfer,
                    'Raw serial command stole retained owner')
        require(first==pending.read(),'Rejected raw serial commands changed retained result')
        pending.release()
        rtl.device=BufferedSPIPeer(b'\x3c',b'\x42',4,1)
        second=loaded.run(tx=b'\x3c',timeout_polls=10)
        require(second.identity.transfer==2 and second.payload==b'\x42','Serial release/restart failed')
        rtl.device.check(second.raw_rx_bits);rtl.device=None
        warm=host.reset()
        require(not warm['valid'] and warm['generation']==min(65535,generation+1) and warm['transfer']==2,
                'Serial warm reset failed to advance generation and retain transfer counter')
        try: loaded.submit(tx=b'\x96')
        except TransferError: pass
        else: raise RuntimeError('Serial warm reset left stale loaded handle usable')
        # Cold reset during a partial request cancels the parser as well.
        for pins in request_samples(encode_request(40,command=7),37)[:-3]:rtl.tick(**pins)
        host.initialize()
        require(host.status()['generation']==0 and host.status()['transfer']==0,
                'Physical serial reset failed to clear core counters')
        # A slow transfer proves timeout ownership while framing continues.
        slow=host.load(compact_spi(4,256))
        rtl.device=BufferedSPIPeer(b'\x96\xa5\x3c\xc3',b'\xa6\x9b\x42\xe1',256,1)
        pending=slow.submit(tx=b'\x96\xa5\x3c\xc3')
        try:pending.wait(timeout_polls=0)
        except BufferedHardwareWaitTimeout as error:require(error.pending is pending,'Slow serial timeout lost owner')
        else:raise RuntimeError('Slow serial transfer did not exercise wait timeout')
        for fields in (dict(command=1,address=0,word=0,control=0,branch=0),
                       dict(command=6,address=0,branch=0),dict(command=2,count=1,virtual_span=1)):
            rejected=host.transport.edge(**fields)
            require(rejected['rejected'] and rejected['busy'],'Raw serial load was accepted while busy')
        pending.wait(timeout_polls=100);result=pending.read()
        require(result.payload==b'\xa6\x9b\x42\xe1','Slow serial transfer result differs')
        rtl.device.check(result.raw_rx_bits);pending.release();rtl.device=None
        # No protocol peer is attached while deliberately cancelling a program.
        # This source uses the ordinary CHECKED branch to remain active.
        loop=BufferedProgram((),schedule=BufferedBlock((BufferedInstruction('checked',finish=0),)),
            idle_levels=0,idle_enabled=0,declared_tx_bits=0,declared_rx_bits=0,max_rx_bits=0)
        halt=BufferedProgram((BufferedInstruction('halt'),),idle_enabled=0)
        reset_checks=[]
        for cold,retained in ((False,False),(False,True),(True,False),(True,True)):
            owned=host.load(halt if retained else loop)
            pending=owned.submit(tx=b'')
            before=host.status()
            require(bool(before['retained'])==retained and bool(before['busy'])!=retained,
                    'Reset witness did not establish intended owned state')
            after=host.initialize() if cold else host.reset()
            require(not after['valid'] and not after['busy'] and not after['retained'],
                    'Serial reset failed to cancel owned state')
            require((after['generation'],after['transfer'])==((0,0) if cold else
                    (min(65535,before['generation']+1),before['transfer'])),
                    'Serial reset identity counter mismatch')
            for stale in (lambda:owned.submit(tx=b''),pending.read):
                try:stale()
                except TransferError:pass
                else:raise RuntimeError('Serial reset left stale owner/image handle usable')
            reset_checks.append(dict(cold=cold,retained=retained))
        # The full-address predecessor and a short replacement have different
        # terminal words. COMMIT leaves the old SRAM tail physically untouched.
        full=BufferedProgram((),schedule=BufferedBlock((BufferedInstruction('checked',finish=63),)+
            (BufferedInstruction('keep',duration=1),)*62+(BufferedInstruction('fault'),)),idle_enabled=0,
            declared_tx_bits=0,declared_rx_bits=0,max_rx_bits=0)
        full_loaded=host.load(full)
        require(len(full_loaded.image.words)==64 and full_loaded.image.branch_table[0]!=0,
                'Full-address nonzero dictionary fixture missing')
        full_result=full_loaded.run(tx=b'',timeout_polls=10)
        require(full_result.outcome=='fault','Full-address fixture did not execute old tail')
        short=host.load(halt)
        require(short.run(tx=b'',timeout_polls=10).outcome=='complete',
                'Short serial replacement executed stale SRAM tail')
        # COMMIT must acknowledge missing row/dictionary coverage as core
        # rejection, even though every serial frame itself is well formed.
        host.reset()
        halt_word=lower_sram(halt).words[0]
        # The hardware COMMIT contract initializes all sixteen dictionary
        # entries, including entries not referenced by the resident rows.
        for address in (0, *range(2,16)):
            host.transport.edge(command=6,address=address,branch=0)
        incomplete=[]
        for stage in range(3):
            status=host.transport.edge(command=2,count=2,virtual_span=2)
            require(status['rejected'] and not status['valid'] and status['pending'],
                    'Serial COMMIT admitted incomplete upload coverage')
            incomplete.append(stage)
            if stage==0:host.transport.edge(command=1,address=0,word=halt_word,control=0,branch=0)
            elif stage==1:host.transport.edge(command=1,address=1,word=halt_word,control=0,branch=1)
        host.transport.edge(command=6,address=1,branch=0)
        committed=host.transport.edge(command=2,count=2,virtual_span=2)
        require(not committed['rejected'] and committed['valid'] and not committed['pending'],
                'Serial COMMIT rejected complete row/dictionary coverage')
        # Physical POR can also cancel a held unread serial receipt.
        raw_request(rtl,encode_request(41,command=0))
        require(rtl.snapshot.ready,'Held reset fixture lacks a receipt')
        host.initialize()
        # Lose the host observation after an actual START was delivered. The
        # public endpoint remains live so only reading its held receipt recovers.
        class LoseStartReceipt:
            armed=True
            operation=3
            @property
            def cycle(self):return rtl.cycle
            def cold_reset(self):return rtl.cold_reset()
            def tick(self,**pins):
                value=rtl.tick(**pins)
                event=annotations[-1]['captured']
                if self.armed and event is not None and event['delivery_edge'] is not None and \
                        annotations[event['delivery_edge']]['command'].get('command')==self.operation:
                    self.armed=False
                    raise TimeoutError('Injected loss after actual serial command receipt publication')
                return value
        lossy=LoseStartReceipt()
        recovered_host=BufferedSramSerialHost(BufferedSramSerialTransport(lossy))
        recovered_host.initialize(); recovered_loaded=recovered_host.load(compact_spi(1))
        rtl.device=BufferedSPIPeer(b'\x96',b'\xa6',4,1)
        starts_before=sum(a['delivered'] and a['command'].get('command')==3 for a in annotations)
        try:recovered_loaded.submit(tx=b'\x96')
        except BufferedHardwareTransportError as error:recovered_pending=error.pending
        else:raise RuntimeError('Lost serial START receipt was not surfaced')
        recovered_pending.recover();recovered_pending.wait(timeout_polls=10)
        recovered_result=recovered_pending.read()
        require(recovered_result.payload==b'\xa6','Recovered serial START lost its retained result')
        rtl.device.check(recovered_result.raw_rx_bits)
        rtl.device=None
        starts_after=sum(a['delivered'] and a['command'].get('command')==3 for a in annotations)
        require(starts_after-starts_before==1,'Serial receipt recovery duplicated START')
        releases_before=sum(a['delivered'] and a['command'].get('command')==4 for a in annotations)
        lossy.operation=4;lossy.armed=True
        try:recovered_pending.release()
        except BufferedHardwareTransportError as error:
            require(error.pending is recovered_pending,'Lost RELEASE receipt lost its local owner')
        else:raise RuntimeError('Lost serial RELEASE receipt was not surfaced')
        released=recovered_pending.recover()
        require(not released['retained'] and recovered_host._pending is None,
                'Recovered RELEASE left a stale local owner')
        releases_after=sum(a['delivered'] and a['command'].get('command')==4 for a in annotations)
        require(releases_after-releases_before==1,'Serial receipt recovery duplicated RELEASE')
        rtl.device=BufferedSPIPeer(b'\x3c',b'\x42',4,1)
        restarted=recovered_loaded.run(tx=b'\x3c',timeout_polls=10)
        require(restarted.payload==b'\x42','Recovered RELEASE prevented resident-image reuse')
        rtl.device.check(restarted.raw_rx_bits);rtl.device=None
        report=dict(physical_edges=rtl.cycle,malformed_frames=errors,
            partial_overlong_read_retention=True,request_backpressure=True,
            retained_raw_rejections=5,busy_upload_rejections=3,
            retained_restart=True,warm_generation_invalidated=True,warm_transfer_preserved=True,
            partial_physical_reset=True,
            slow_wait_timeout_owner_recovered=True,reset_owned_states=reset_checks,
            full_address_short_replacement=True,wrong_image_before_io=True,
            incomplete_upload_commit_rejections=len(incomplete),
            tampered_image_before_io=True,held_receipt_physical_reset=True,
            actual_start_receipt_loss_recovered=True,start_delivery_count_on_recovery=1,
            actual_release_receipt_loss_recovered=True,release_delivery_count_on_recovery=1,
            release_recovery_resident_restart=True)
    return records,annotations,report


def trace_oracle(run,out,exporter,records,annotations,label):
    target=out/label; target.mkdir()
    (target/'pins.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in records))
    (target/'schedule.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in annotations))
    vectors=[dict(command=a['command'],raw_inputs=r['observation']['edge_inputs'])
             for r,a in zip(records,annotations,strict=True)]
    request=dict(schema='pinwheel-buffered-shared-branches-input-v1',cases=[dict(name=label,vectors=vectors)])
    path=target/'input.json';path.write_text(json.dumps(request,separators=(',',':'))+'\n')
    run([exporter,path,target/'oracle'],'oracle-'+label,timeout=1200)
    actual=json.loads((target/'oracle/vectors.json').read_text())['cases'][0]['vectors']
    report=check_trace(records,annotations,actual)
    (target/'check.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def poison_bridge(out,seed):
    text=BRIDGE.read_text()
    anchor='  pinwheel_buffered_shared_branches_sram_serial dut (.*);'
    require(text.count(anchor)==1,'Missing serial macro fixture insertion anchor')
    statements=['  // Test fixture varies initial arrays/Q, never expected outputs.',
                '  integer poison_index;', '  initial begin']
    for k in range(2):
        core=f'dut.memory.storage{k}.i_SRAM_1P_behavioral_bm_bist'
        value=(0x96A53CC36A5AC33C ^ seed*0x1111111111111111 ^ k*0xffffffffffffffff)&((1<<64)-1)
        statements += [f"    {core}.dr_r = 64'h{value:016x};",
            '    for(poison_index=0;poison_index<64;poison_index=poison_index+1)',
            f"      {core}.memory[poison_index] = 64'h{value:016x} ^ poison_index;"]
    statements.append('  end')
    path=out/f'poison-bridge-{seed}.sv'
    path.write_text(text.replace(anchor,anchor+'\n'+'\n'.join(statements)))
    return path


def binding_negatives(out):
    saved=json.loads((out/'emitted-binding.json').read_text())
    controls={}
    for name in ('status_transfer','core_read_index','raw_inputs'):
        mutant=deepcopy(saved)
        bits=mutant['modules'][TOP]['netnames'][name]['bits']
        bits[0]='0' if bits[0]!='0' else '1'
        path=out/(name+'-binding-negative.json')
        path.write_text(json.dumps(mutant,indent=2)+'\n')
        try:binding_readback(mutant)
        except RuntimeError as error:
            require('Changed transparent serial' in str(error),'Unexpected binding negative reason')
            controls[name]=str(error)
        else:raise RuntimeError('Incorrect serial binding admitted: '+name)
    return controls


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--tag',default='local')
    args=parser.parse_args()
    out=fresh_directory(ROOT/'build/buffered-sram-serial',args.tag)
    run=Commands(ROOT,out)
    report=dict(schema='pinwheel-buffered-sram-serial-hardware-v1',status='running',
                smoke=False,commands=run.records)
    started=time.monotonic()
    sources=sorted((ROOT/'Pinwheel').rglob('*.lean'))+sorted((ROOT/'test').glob('*.lean'))
    sources += sorted((ROOT/'scripts').glob('*.py'))+sorted((ROOT/'test').glob('test_*.py'))
    sources += [ROOT/p for p in ['Pinwheel.lean','lean-toolchain','lakefile.toml','lake-manifest.json',
        'physical/buffered_sram_serial_wrapper.sv','physical/buffered_sram_serial_host_bridge.sv',
        'physical/buffered_sram_memory.sv','tools/storage-macros.json','tools/technology-library.json']]
    try:
        directory,report['predecessor']=predecessor()
        models=[VIEWS/(MACRO+'.v'),VIEWS/'RM_IHPSG13_1P_core_behavioral_bm_bist.v']
        lock=json.loads((ROOT/'tools/storage-macros.json').read_text())
        for p in [*models,VIEWS/(MACRO+'_typ_1p20V_25C.lib')]:
            key=('lib/' if p.suffix=='.lib' else 'verilog/')+p.name
            require(sha(p)==lock['files_sha256'][key],'Changed pinned serial package macro: '+str(p))
        pdk=stage_pdk()
        report['pdk']=pdk
        sources += [*models,VIEWS/(MACRO+'_typ_1p20V_25C.lib'),CIRCT,
            *[CAD/n for n in ('yosys','yosys-abc','iverilog','vvp')],
            Path(pdk['library']),*[Path(n) for n in pdk['models']],
            ROOT/'build/tools/oss-cad-suite/share/yosys/simcells.v']
        source_hashes={str(p.relative_to(ROOT)):sha(p) for p in sources}
        report['source_sha256']=source_hashes
        run(['lake','build','Pinwheel:static'],'native-library',timeout=900)
        library=out/'libpinwheel_Pinwheel.a';library.write_bytes((ROOT/'.lake/build/lib/libpinwheel_Pinwheel.a').read_bytes())
        frontend=native_exporter(run,out,'test/BufferedSramSerialExport.lean','frontend-export',library)
        oracle=native_exporter(run,out,'test/BufferedSramExport.lean','controller-oracle',library)
        request=frontend_input();path=out/'frontend-input.json';path.write_text(json.dumps(request,separators=(',',':'))+'\n')
        run([frontend,path,out/'frontend'],'frontend-export',timeout=600)
        vectors=json.loads((out/'frontend/vectors.json').read_text())
        assembly=json.loads((out/'frontend/assembly.json').read_text())
        small=dict(request,cases=request['cases'][:1]);parity=out/'parity-input.json';parity.write_text(json.dumps(small)+'\n')
        run(['lake','env','lean','-DwarningAsError=true','--run','test/BufferedSramSerialExport.lean',parity,out/'interpreted'],'frontend-interpreted-parity',timeout=600)
        run([frontend,parity,out/'native-parity'],'frontend-native-parity')
        for name in ('frontend.mlir','assembly.json','vectors.json'):
            require((out/'interpreted'/name).read_bytes()==(out/'native-parity'/name).read_bytes(),
                    'Serial native/interpreted export parity failed: '+name)
        report['native_parity']=dict(cases=1,edges=len(small['cases'][0]['vectors']))
        rtl=run([CIRCT,out/'frontend/frontend.mlir','--canonicalize','--lower-seq-to-sv',
            '--lower-hw-to-sv','--hw-legalize-modules','--export-verilog','-o','/dev/null'],'frontend-lower')
        source=out/'frontend.sv';source.write_text(rtl)
        tb,report['frontend_replay']=frontend_tb(out,assembly,vectors)
        sim=out/'frontend.vvp'
        run([CAD/'iverilog','-g2012','-s','buffered_sram_serial_frontend_tb','-o',sim,source,tb],'frontend-compile')
        run([CAD/'vvp',sim],'frontend-replay')
        controller=directory/'core.sv'
        report['binding']=read_complete_binding(run,out,source,controller,'emitted')
        report['binding_negative_controls']=binding_negatives(out)
        complete=compile_package(run,out,source,controller,'emitted-package',models)
        records,annotations,report['wire_peers']=wire_cases(complete)
        report['wire_oracle']=trace_oracle(run,out,oracle,records,annotations,'emitted-wire')
        records,annotations,report['protocol_lifecycle']=protocol_cases(complete)
        report['protocol_oracle']=trace_oracle(run,out,oracle,records,annotations,'protocol-lifecycle')
        report['poison_replays']={}
        for seed in (1,7):
            label='poison-'+str(seed)
            executable=compile_package(run,out,source,controller,label,models,
                bridge=poison_bridge(out,seed))
            records,annotations,peers=wire_cases(executable,bounded=True)
            report['poison_replays'][str(seed)]=dict(peers=peers,
                oracle=trace_oracle(run,out,oracle,records,annotations,label))
        report['mapping']=synthesize(run,out,source,description=assembly,equivalence=False,
            top=FRONT,storage={'frontend_anchor':[('r_ready',1)]},
            bridge=tb,testbench='buffered_sram_serial_frontend_tb')
        report['mapped_packages']={}
        for variant in ('generic','typical'):
            saved=report['mapping']['variants'][variant]
            data=json.loads((out/variant/'readback.json').read_text())
            saved['equivalence']=prove_frontend_mapping(run,out,variant,assembly,data,Path(pdk['library']))
            run([CAD/'vvp',saved['executable']],'frontend-'+variant+'-finite-replay')
            mapped_front=Path(saved['netlist_verilog'])
            mapped_controller=directory/variant/'netlist.v'
            bound=read_complete_binding(run,out,mapped_front,mapped_controller,'mapped-'+variant,
                Path(pdk['library']) if variant=='typical' else None)
            cells=([ROOT/'build/tools/oss-cad-suite/share/yosys/simcells.v'] if variant=='generic'
                   else [Path(n) for n in pdk['models']])
            label='mapped-'+variant
            executable=compile_package(run,out,mapped_front,mapped_controller,label,models,cells=cells)
            records,annotations,peers=wire_cases(executable,bounded=True)
            report['mapped_packages'][variant]=dict(binding=bound,peers=peers,
                oracle=trace_oracle(run,out,oracle,records,annotations,label))
        run([sys.executable,'-B','-m','unittest','discover','-s','test','-p','test_*.py'],'python',timeout=600)
        run([sys.executable,'-O','-B','-m','unittest','discover','-s','test','-p','test_*.py'],'python-optimized',timeout=600)
        for path,digest in source_hashes.items():
            require(sha(ROOT/path)==digest,'Source changed during serial acceptance: '+path)
        report.update(status='passed',elapsed_seconds=round(time.monotonic()-started,3),
            inputs_unchanged=True,artifact_sha256={str(p.relative_to(out)):sha(p)
                for p in sorted(out.rglob('*')) if p.is_file() and p!=out/'report.json'},
            boundary='Versioned atomic sampled serial frontend, frozen per-command receipts, one-owner retained results, '
                'finite complete two-macro command and independent protocol pin replays, '
                'saved frontend mapping equality over the optimized physical-state quotient. '
                'No electrical serial timing, CDC, macro qualification, routed timing, package power or complete initialized package refinement.')
    except BaseException as error:
        report.update(status='failed',error=repr(error),elapsed_seconds=round(time.monotonic()-started,3))
        raise
    finally:
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Buffered SRAM serial gate passed: '+str(out/'report.json'),flush=True)


if __name__=='__main__':
    main()
