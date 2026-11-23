#!/usr/bin/env python3
"""Fresh complete-state digital serial RTL replay, synthesis and semantic controls."""
from __future__ import annotations
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import time
import serial_oracle as reference

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('serial_cad',ROOT/'scripts/check-round-robin-circuit.py')
rr = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(rr)
MATRIX = (4,6,10,32)
LEAN_ROOTS = ('test/ProcessorSerialEmit.lean','test/ProcessorSerialReplay.lean','test/ProcessorSerialCircuit.lean')
BOUNDARIES = {
 'startup':'arbitrary fourteen physical registers; logical correspondence requires UART bounds and TX ownership until reset',
 'reset_behavior':'synchronous reset clears all fourteen registers; TX is high and other outputs zero during reset',
 'operation_behavior':'always-ready atomic request/response edge; invalid device faults without CPU effect; accepted TX write bypasses on the same edge',
 'frontend_boundary':'RX is already synchronous; exact digital 8N1 timing only, without analog, CDC or baud-tolerance qualification',
}


def source_hashes():
    pending,paths=[ROOT/name for name in LEAN_ROOTS],set()
    while pending:
        path=pending.pop()
        if path in paths: continue
        paths.add(path)
        for line in path.read_text().splitlines():
            if match:=re.match(r'^import\s+(.+)$',line):
                for module in match[1].split('--',1)[0].split():
                    if module=='Pinwheel' or module.startswith(('Pinwheel.','test.')):
                        pending.append(ROOT/(module.replace('.','/')+'.lean'))
    paths.update(ROOT/name for name in ('scripts/check-processor-serial.py','scripts/serial_oracle.py',
        'scripts/check-round-robin-circuit.py','scripts/validation_run.py','scripts/process_group.py',
        'test/test_serial_oracle.py','test/test_processor_serial_driver.py','lakefile.toml','lake-manifest.json',
        'lean-toolchain','tools/hardware-toolchain.json'))
    return {str(p.relative_to(ROOT)):rr.sha(p) for p in sorted(paths)}


def validate_descriptor(data,d):
    ws=reference.widths(d)
    if type(data.get('schema')) is not int or data['schema']!=1 or data.get('clock')!='clk' or data.get('module')!='processor_serial' or \
       type(data.get('divisor')) is not int or data['divisor']!=d or type(data.get('counter_width')) is not int or data['counter_width']!=ws[9]:
        raise ValueError('Wrong serial schema/module/timing')
    names={'clk'}
    for group,widths,roles in (('inputs',reference.INPUT_WIDTHS,reference.INPUT_ROLES),('outputs',reference.OUTPUT_WIDTHS,reference.OUTPUT_ROLES),('registers',ws,reference.REGISTER_ROLES)):
        if type(data.get(group)) is not list or len(data[group])!=len(widths): raise ValueError('Incomplete '+group)
        for k,(p,w) in enumerate(zip(data[group],widths,strict=True)):
            expected_name=roles[k] if group=='inputs' else ('r_' if group=='registers' else '')+f'state_{k}'
            if type(p) is not dict or p.get('name')!=expected_name or p['name'] in names or type(p.get('width')) is not int or p['width']!=w or type(p.get('index')) is not int or p['index']!=k:
                raise ValueError('Invalid signal label/width/order')
            if group=='registers' and p.get('reference')!=p['name']: raise ValueError('Changed raw reference')
            names.add(p['name'])
    for key,groups in (('roles',(('inputs',reference.INPUT_ROLES),('outputs',reference.OUTPUT_ROLES))),('register_roles',(('registers',reference.REGISTER_ROLES),))):
        expected={role:p['name'] for group,roles in groups for role,p in zip(roles,data[group],strict=True)}
        if data.get(key)!=expected: raise ValueError('Incomplete or aliased roles')
    for key,expected in (('response_codes',dict(read=0,stored=1,register_hole=2,direction=3,tx_busy=4,rx_empty=5)),('device_codes',dict(gpio=0,timer=1,uart=2,invalid=3))):
        codes=data.get(key)
        if type(codes) is not dict or codes!=expected or any(type(v) is not int for v in codes.values()): raise ValueError('Changed encoding')
    if any(data.get(k)!=v for k,v in BOUNDARIES.items()): raise ValueError('Changed scope boundary')
    return data


def validate_frames(d,rows,frames):
    if type(frames) is not list or len(frames)!=len(rows): raise ValueError('Incomplete frames')
    for k,(i,f) in enumerate(zip(rows,frames,strict=True)):
        reference.validate_row(i)
        if type(f) is not dict or set(f)!={'cycle','input','pre','post','registers'} or type(f['cycle']) is not int or f['cycle']!=k or json.dumps(f['input'],sort_keys=True)!=json.dumps(i,sort_keys=True): raise ValueError('Changed input or frame order')
        for key,ws in (('pre',reference.OUTPUT_WIDTHS),('post',reference.OUTPUT_WIDTHS),('registers',reference.widths(d))):
            if type(f[key]) is not list or len(f[key])!=len(ws) or any(type(v) is not int or not 0<=v<1<<w for v,w in zip(f[key],ws,strict=True)): raise ValueError('Incomplete/out-of-width '+key)


def initialization_evidence(rows):
    if not rows: raise ValueError('Empty serial replay')
    for i in rows: reference.validate_row(i)
    if not rows[0]['reset']: raise ValueError('Synthesized replay requires synchronous reset first')
    return dict(synthesized_registers_forced=False,all_registers_initialized_by_reset=True,pre_reset_outputs='all reset masked, TX high')


def testbench(data,segments,registers):
    d=data['divisor']
    if not segments: raise ValueError('Empty segments')
    if not registers:
        if len(segments)!=1: raise ValueError('Synthesized replay cannot force raw segments')
        initialization_evidence(segments[0]['rows'])
    lines=['`timescale 1ns/1ps','module tb;','reg clk = 0;']; con=['.clk(clk)']
    for group,kind in (('inputs','reg'),('outputs','wire')):
        for p in data[group]:
            lines.append(f"{kind} [{p['width']-1}:0] {p['name']}"+(' = 0;' if kind=='reg' else ';'))
            con.append(f".{p['name']}({p['name']})")
    lines += [f"{data['module']} dut({', '.join(con)});",'initial begin']
    outputs=', '.join(p['name'] for p in data['outputs'])
    refs=', '.join('dut.'+p['reference'] for p in data['registers'])
    cycle=0
    for segment in segments:
        s=reference.restore(d,segment['startup'])
        if registers:
            lines += [f"force dut.{p['reference']} = {p['width']}'h{v:x};" for p,v in zip(data['registers'],s,strict=True)]
            lines += ['#1;']+[f"release dut.{p['reference']};" for p in data['registers']]
        for i in segment['rows']:
            reference.validate_row(i)
            lines += [f"{p['name']} = {p['width']}'h{int(i[role]):x};" for p,role in zip(data['inputs'],reference.INPUT_ROLES,strict=True)]
            lines += ['#1;',f'$display("PRE,{cycle}{",%0d"*13}", {outputs});','clk = 1; #1;',f'$display("POST,{cycle}{",%0d"*13}", {outputs});']
            if registers: lines += [f'$display("REG,{cycle}{",%0d"*14}", {refs});']
            lines += ['clk = 0; #1;']; cycle+=1
    return '\n'.join(lines+['$display("SERIAL_DONE"); $finish;','end','endmodule',''])


def expected(frames, registers):
    result = []
    for frame in frames:
        result += [("PRE", frame["cycle"], *frame["pre"]), ("POST", frame["cycle"], *frame["post"])]
        if registers:
            result.append(("REG", frame["cycle"], *frame["registers"]))
    return result


class TraceError(AssertionError):
    """Malformed/unknown/incomplete output is never a semantic negative."""


class ConcreteMismatch(AssertionError):
    def __init__(self, witness):
        self.witness = witness
        super().__init__("Concrete SERIAL value mismatch: " + json.dumps(witness, sort_keys=True))


def check_trace(text, want, data):
    observations, done, finish = [], 0, 0
    for line in text.splitlines():
        if line == "SERIAL_DONE":
            done += 1
        elif line.startswith(("PRE,", "POST,", "REG,")):
            fields = line.split(",")
            if done or len(fields) < 3 or any(not v.isascii() or not v.isdecimal() for v in fields[1:]):
                raise TraceError("Unknown or out-of-order SERIAL observation")
            observations.append((fields[0], *map(int, fields[1:])))
        elif re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)", line):
            finish += 1
            if done != 1 or finish > 1:
                raise TraceError("Misplaced or duplicate simulator finish")
        elif line.strip():
            raise TraceError("Unexpected simulation output: " + line)
    if done != 1 or len(observations) != len(want):
        raise TraceError("Incomplete SERIAL observations/completion")
    for actual, target in zip(observations, want, strict=True):
        ports = data["registers" if actual[0] == "REG" else "outputs"]
        if actual[:2] != target[:2] or len(actual) != len(target) or len(actual) != len(ports)+2 or \
                any(v >= 1 << p["width"] for v, p in zip(actual[2:], ports, strict=True)):
            raise TraceError("Changed observation shape, edge order, or signal width")
    for actual, target in zip(observations, want, strict=True):
        ports = data["registers" if actual[0] == "REG" else "outputs"]
        for index, (v, w) in enumerate(zip(actual[2:], target[2:], strict=True)):
            if v != w:
                raise ConcreteMismatch({"observation": actual[0], "cycle": actual[1], "signal": ports[index]["name"],
                                        "expected": w, "actual": v})
    return len(observations)


def mutations(text,data):
    p,r=data['roles'],data['register_roles']
    start=f"(~{p['reset']} & {p['request_valid']} & ({p['device']} == 2'd2) & ({p['word']} == 6'd1) & {p['write']} & ~{r['held_tx_active']})"
    clear=f"(~{p['reset']} & {p['request_valid']} & ({p['device']} == 2'd2) & ({p['word']} == 6'd3) & {p['write']})"
    for name,reg,fn in (
        ('lose-tx-bypass',r['tx_active'],lambda v:f"{start} ? 1'b0 : ({v})"),
        ('duplicate-frame',r['held_tx_active'],lambda v:f"(~{p['reset']} & {p['tx_complete']}) ? 1'b1 : ({v})"),
        ('keep-completed-tx',r['tx_active'],lambda v:f"(~{p['reset']} & {p['tx_complete']}) ? 1'b1 : ({v})"),
        ('drop-rx-refill',r['held_rx_data'],lambda v:f"(~{p['reset']} & {r['held_rx_valid']} & {p['rx_valid']}) ? {r['held_rx_data']} : ({v})"),
        ('overwrite-full-rx',r['held_rx_data'],lambda v:f"(~{p['reset']} & {p['rx_valid']}) ? {p['rx_data']} : ({v})"),
        ('clear-new-framing',r['framing'],lambda v:f"{clear} ? 1'b0 : ({v})"),
        ('ignore-tx-reset',r['tx_byte'],lambda v:f"{p['reset']} ? {r['tx_byte']} : ({v})"),
        ('freeze-timer',r['timer'],lambda v:f"{p['reset']} ? 32'd0 : {r['timer']}"),
    ):
        changed,n=re.subn(r'(\b'+re.escape(reg)+r'\s*<=\s*)([^;]+);',lambda m:m[1]+fn(m[2].strip())+';',text)
        if n!=1 or changed==text: raise ValueError('Expected one actual register assignment for '+name)
        yield name,changed
    for name,role,fn in (
        ('invalid-selector-success','response_code',lambda v:f"(~{p['reset']} & {p['request_valid']} & ({p['device']} == 2'd3)) ? 3'd0 : ({v})"),
        ('complete-during-reset','tx_complete',lambda v:f"({p['reset']} & {r['tx_active']}) ? 1'b1 : ({v})"),
        ('reverse-first-bit','tx',lambda v:f"(~{p['reset']} & {r['tx_active']} & ({r['tx_count']} == {data['counter_width']}'d{data['divisor']})) ? {r['tx_byte']}[7] : ({v})"),
        ('corrupt-arrival','rx_data',lambda v:f"{p['rx_valid']} ? (({v}) ^ 8'h80) : ({v})"),
    ):
        changed,n=re.subn(r'(\bassign\s+'+re.escape(p[role])+r'\s*=\s*)([^;]+);',lambda m:m[1]+fn(m[2].strip())+';',text)
        if n!=1 or changed==text: raise ValueError('Expected one actual output assignment for '+name)
        yield name,changed


def configuration(run,tools,out,d):
    directory=out/f'serial-{d}'; directory.mkdir()
    run(['lake','env','lean','-DwarningAsError=true','--run','test/ProcessorSerialEmit.lean',str(d),directory],f'd{d}-emit')
    data=validate_descriptor(json.loads((directory/'interface.json').read_text()),d)
    startup,rows=reference.stimulus(d)
    initialization=initialization_evidence(rows)
    segments=[dict(startup=startup,rows=rows)]
    frames,events,ledger=reference.oracle(d,startup,rows,owned=True)
    if any(ledger.get(key,0)<=0 for key in ('reads','stores','faults','invalid_selectors','tx_completions','rx_consumed','rx_refills','rx_dropped','framing_errors','tx_cancelled')): raise AssertionError('Incomplete event coverage')
    raw=reference.raw_segments(d)
    raw_frames,raw_events,raw_rows,raw_before=[],[],[],[]
    for segment in raw:
        fs,es,_=reference.oracle(d,segment['startup'],segment['rows'])
        for k,(f,e) in enumerate(zip(fs,es,strict=True)):
            cycle=len(raw_frames)
            raw_frames.append({**f,'cycle':cycle}); raw_events.append({**e,'cycle':cycle})
            raw_rows.append(f['input']); raw_before.append(segment['startup'] if k==0 else fs[k-1]['registers'])
    for label,ss,fs,items in (('',segments,frames,rows),('raw-',raw,raw_frames,raw_rows)):
        validate_frames(d,items,fs)
        (directory/(label+'segments.json')).write_text(json.dumps(ss,indent=2)+'\n')
        (directory/(label+'expected.json')).write_text(json.dumps(fs,indent=2)+'\n')
        target=directory/(label+'lean.jsonl')
        run(['lake','env','lean','-DwarningAsError=true','--run','test/ProcessorSerialReplay.lean',str(d),directory/(label+'segments.json'),target],f'd{d}-{label}lean',timeout=900)
        actual=[json.loads(line) for line in target.read_text().splitlines()]
        validate_frames(d,items,actual)
        if actual!=fs:
            mismatch=next(dict(expected=x,actual=y) for x,y in zip(fs,actual,strict=True) if x!=y)
            raise AssertionError('Lean disagrees with numeric oracle: '+json.dumps(mismatch))
    for filename,value in (('startup.json',startup),('events.json',events),('ledger.json',ledger),('raw-events.json',raw_events)):
        (directory/filename).write_text(json.dumps(value,indent=2)+'\n')
    (directory/'stimulus.jsonl').write_text(''.join(json.dumps(i)+'\n' for i in rows))
    rtl=directory/'serial.sv'
    rtl.write_text(run([tools['circt'],directory/'serial.mlir','--canonicalize','--lower-seq-to-sv','--lower-hw-to-sv','--hw-legalize-modules','--export-verilog','-o','/dev/null'],f'd{d}-lower'))
    def simulate(source,stage,registers,*,negative=False,raw_campaign=False):
        ss,fs,items,es=(raw,raw_frames,raw_rows,raw_events) if raw_campaign else (segments,frames,rows,events)
        tb,exe=directory/(stage+'-tb.sv'),directory/(stage+'.vvp')
        tb.write_text(testbench(data,ss,registers))
        run([tools['iverilog'],'-g2012','-s','tb','-o',exe,source,tb],f'd{d}-{stage}-compile')
        trace=run([tools['vvp'],exe],f'd{d}-{stage}-simulate')
        (directory/(stage+'-trace.txt')).write_text(trace)
        try: check_trace(trace,expected(fs,registers),data)
        except ConcreteMismatch as error:
            if not negative: raise
            k=error.witness['cycle']
            before=raw_before[k] if raw_campaign else startup if k==0 else frames[k-1]['registers']
            return {**error.witness,'campaign':'raw' if raw_campaign else 'reset','input':items[k],
                    'before_registers':before,'expected_post_registers':fs[k]['registers'],'event':es[k]}
        if negative: raise AssertionError('Accepted actual RTL mutant '+stage)
    simulate(rtl,'rtl',True); simulate(rtl,'raw',True,raw_campaign=True)
    netlist,netjson,script=directory/'synth.v',directory/'synth.json',directory/'synth.ys'
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {data['module']}\nsynth -top {data['module']}\ncheck -assert\nwrite_json {rr.yosys_quote(netjson)}\nwrite_verilog -noattr {rr.yosys_quote(netlist)}\n")
    run([tools['yosys'],'-Q','-T','-s',script],f'd{d}-synthesize'); simulate(netlist,'synth',False)
    controls=[]
    for name,changed in mutations(rtl.read_text(),data):
        source=directory/(name+'.sv'); source.write_text(changed)
        controls.append(dict(mutation=name,witness=simulate(source,name,True,negative=True)))
    modules=json.loads(netjson.read_text())['modules']
    if set(modules)!={data['module']} or modules[data['module']].get('memories'): raise AssertionError('Unexpected netlist hierarchy/memory')
    cells=Counter(c['type'] for c in modules[data['module']]['cells'].values())
    return dict(divisor=d,edges_per_form=len(frames),additional_raw_edges=len(raw_frames),raw_startup_images=len(raw),
                typed_registers=14,typed_outputs=13,initialization=initialization,ledger=ledger,generic_cells=sum(cells.values()),
                cell_types=dict(cells),rtl_mutations_rejected=controls,artifact_certificate='not_run')


def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--tag',required=True)
    args=p.parse_args(); out=rr.fresh_directory(ROOT/'build/processor-serial',args.tag)
    report=dict(schema=1,status='running',commands=[],configurations=[],boundary='All binary raw-state circuit behavior and reset-driven owned digital serial histories. No analog/CDC/baud tolerance or imported RTL certificate is inferred from finite replay.')
    run,started=rr.Commands(out,report['commands']),time.monotonic()
    try:
        report['source_sha256']=source_hashes()
        manifest,tools,paths=rr.selected_tools(); report['tool_manifest']=manifest; report['tool_sha256']=rr.tool_hashes(paths)
        run(['lake','build','Pinwheel.Hardware.Processor.SerialCircuitProofs','Pinwheel.Hardware.Emit'],'build',timeout=900)
        run(['python3','test/test_serial_oracle.py'],'oracle-tests'); run(['python3','test/test_processor_serial_driver.py'],'driver-tests')
        for d in MATRIX: report['configurations'].append(configuration(run,tools,out,d))
        if source_hashes()!=report['source_sha256'] or rr.tool_hashes(paths)!=report['tool_sha256']: raise RuntimeError('Sources or tools changed during validation')
        report['status']='passed'
    except BaseException as error:
        report['status'],report['error']='failed',f'{type(error).__name__}: {error}'; raise
    finally:
        report['seconds']=round(time.monotonic()-started,3)
        report['artifact_sha256']={str(p.relative_to(out)):rr.sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__': main()
