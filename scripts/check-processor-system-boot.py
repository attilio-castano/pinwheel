#!/usr/bin/env python3
"""Emitted RTL boot from an explicitly forced 60-register startup image.

This campaign is deliberately not synthesized boot: reset does not initialize
RAM. Every input, pre/post output and post-edge register is checked. The oracle
frames come from the independently composed Lean system model/staged-circuit
test, with an additional numeric firmware/effect ledger checked here.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import time

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("system_boot_cad", ROOT / "scripts/check-round-robin-circuit.py")
rr = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(rr)
INPUT_NAMES = ["reset", "gpio_input", "tx_complete", "rx_valid", "rx_data", "framing_error"]
INPUT_WIDTHS = [1, 32, 1, 1, 8, 1]
CORE_INPUT_NAMES = ["reset", "fetch_ready", "fetch_response_valid", "fetch_response_fault", "fetch_response_data",
    "data_service_valid", "data_service_atomic", "data_service_fault", "data_service_data",
    "data_response_valid", "data_response_fault", "data_response_data"]
CORE_INPUT_WIDTHS = [1, 1, 1, 1, 32, 1, 1, 2, 32, 1, 2, 32]
CORE_OUTPUT_ROLES = ["cancel", "fetch_valid", "fetch_address", "fetch_response_ready", "data_valid", "data_write",
    "data_address", "data_size", "data_signed", "data_store_data", "data_response_ready", "retire_valid", "retire_pc",
    "retire_instruction", "retire_next_pc", "retire_write_enable", "retire_write_rd", "retire_write_data", "trap_valid",
    "trap_pc", "trap_instruction_valid", "trap_instruction", "trap_cause", "trap_address", "terminal_valid", "terminal_pc",
    "terminal_instruction_valid", "terminal_instruction", "terminal_cause", "terminal_address"]
CORE_OUTPUT_WIDTHS = [1,1,32,1,1,1,32,2,1,32,1,1,32,32,32,1,5,32,1,32,1,32,4,32,1,32,1,32,4,32]
CORE_REGISTER_WIDTHS = [32]*31 + [3,32,32,4,32,1]
RAM_INPUT_NAMES = ["reset", "request_valid", "write", "signed_load", "size", "address", "offset", "data", "response_ready"]
RAM_INPUT_WIDTHS = [1,1,1,1,2,2,2,32,1]
RAM_OUTPUT_NAMES = ["request_ready", "response_valid", "response_code", "response_data"]
RAM_OUTPUT_WIDTHS = [1,1,2,32]
RAM_REGISTER_WIDTHS = [32]*5 + [1,1,2,2,2,32,1]
MMIO_INPUT_NAMES = ["reset", "request_valid", "device", "write", "word", "data", "gpio_input", "tx_complete",
                    "rx_valid", "rx_data", "framing_error"]
MMIO_INPUT_WIDTHS = [1,1,2,1,6,32,32,1,1,8,1]
MMIO_OUTPUT_ROLES = ["request_ready", "response_valid", "response_code", "response_data", "gpio_output", "tx_active", "tx_data"]
MMIO_OUTPUT_WIDTHS = [1,1,3,32,32,1,8]
MMIO_REGISTER_NAMES = ["r_gpio", "r_timer", "r_tx_active", "r_tx_data", "r_rx_valid", "r_rx_data", "r_overrun", "r_framing"]
MMIO_REGISTER_WIDTHS = [32,32,1,8,1,8,1,1]
FETCH_NAMES, FETCH_WIDTHS = ["r_fetch_valid", "r_fetch_fault", "r_fetch_data"], [1,1,32]
OUTPUT_WIDTHS = CORE_OUTPUT_WIDTHS + MMIO_OUTPUT_WIDTHS
REGISTER_WIDTHS = CORE_REGISTER_WIDTHS + RAM_REGISTER_WIDTHS + MMIO_REGISTER_WIDTHS + FETCH_WIDTHS
BOUNDARY = ("Emitted RTL only; all 60 startup registers are explicitly forced once, including a nonzero RAM image and Q. "
            "The first synchronous reset preserves RAM/Q. No synthesized boot, memory initialization coverage, "
            "imported-RTL certificate, physical UART, or independent Python ISA implementation is claimed.")


def source_hashes():
    pending = [ROOT / p for p in ("test/ProcessorSystemEmit.lean", "test/ProcessorSystemCircuit.lean",
                                 "test/ProcessorSystemExport.lean")]
    paths = set()
    while pending:
        path = pending.pop()
        if path in paths:
            continue
        paths.add(path)
        for line in path.read_text().splitlines():
            if match := re.match(r"^import\s+(.+)$", line):
                for module in match[1].split("--", 1)[0].split():
                    if module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    paths.update(ROOT / p for p in ("scripts/check-processor-system-boot.py", "test/test_processor_system_boot.py",
        "scripts/check-round-robin-circuit.py", "scripts/validation_run.py", "scripts/process_group.py",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain", "tools/hardware-toolchain.json"))
    return {str(p.relative_to(ROOT)): rr.sha(p) for p in sorted(paths)}


def iword(imm, rs1, funct, rd, opcode):
    return ((imm % 4096) << 20) + (rs1 << 15) + (funct << 12) + (rd << 7) + opcode


def sword(imm, rs1, rs2, funct):
    return ((imm // 32) << 25) + (rs2 << 20) + (rs1 << 15) + (funct << 12) + ((imm % 32) << 7) + 0x23


PROGRAM = [0x000100b7, iword(128,0,0,2,0x13), sword(1,1,2,0), iword(1,1,0,3,3), iword(1,1,4,4,3),
           iword(4,1,2,0,3), 0x400002b7, sword(4,5,3,2), iword(4,5,2,6,3), iword(256,5,0,7,0x13),
           iword(0,7,2,8,3), 15, 0x00100073]


def checked_rows(rows, names, widths, *, registers=False):
    if type(rows) is not list or len(rows) != len(names):
        raise ValueError("Incomplete typed endpoint enumeration")
    for index, (row, name, width) in enumerate(zip(rows, names, widths, strict=True)):
        if type(row) is not dict or type(row.get("index")) is not int or row["index"] != index or \
                row.get("name") != name or type(row.get("width")) is not int or row["width"] != width:
            raise ValueError("Changed typed endpoint name/index/width")
        if registers and row.get("reference") != name:
            raise ValueError("Leaf register reference is not its declared register")


def validate_descriptor(data):
    if type(data) is not dict: raise ValueError("Descriptor must be an object")
    constants = {"schema":1, "module":"processor_system", "clock":"clk", "rom_word_width":5, "ram_word_width":2,
        "ram_base":0x10000, "gpio_base":0x40000000, "timer_base":0x40000100, "uart_base":0x40000200,
        "top_verilog":"top.sv", "latency_added":0, "reset_synchronous":True}
    for key, value in constants.items():
        if type(data.get(key)) is not type(value) or data[key] != value:
            raise ValueError("Changed boot descriptor field: " + key)
    image = data.get("rom_words")
    if type(image) is not list or any(type(v) is not int for v in image) or image != PROGRAM+[0]*19:
        raise ValueError("ROM image differs from the explicit firmware")
    checked_rows(data.get("inputs"), INPUT_NAMES, INPUT_WIDTHS)
    checked_rows(data.get("outputs"), [f"state_{k}" for k in range(37)], OUTPUT_WIDTHS)
    checked_rows(data.get("registers"), [f"r_state_{k}" for k in range(60)], REGISTER_WIDTHS)
    roles = {x:x for x in INPUT_NAMES}
    roles.update({"core_"+r:f"state_{k}" for k,r in enumerate(CORE_OUTPUT_ROLES)})
    roles.update({"mmio_"+r:f"state_{30+k}" for k,r in enumerate(MMIO_OUTPUT_ROLES)})
    if data.get("roles") != roles:
        raise ValueError("Semantic roles do not match complete typed port order")
    specs = [
        ("core", CORE_INPUT_NAMES, CORE_INPUT_WIDTHS, CORE_OUTPUT_WIDTHS, [f"r_state_{k}" for k in range(37)], CORE_REGISTER_WIDTHS),
        ("ram", RAM_INPUT_NAMES, RAM_INPUT_WIDTHS, RAM_OUTPUT_WIDTHS, [f"r_state_{k}" for k in range(12)], RAM_REGISTER_WIDTHS),
        ("mmio", MMIO_INPUT_NAMES, MMIO_INPUT_WIDTHS, MMIO_OUTPUT_WIDTHS, MMIO_REGISTER_NAMES, MMIO_REGISTER_WIDTHS),
        ("bus", [f"state_{k}" for k in range(47)], INPUT_WIDTHS+CORE_OUTPUT_WIDTHS+RAM_OUTPUT_WIDTHS+MMIO_OUTPUT_WIDTHS,
         CORE_INPUT_WIDTHS+RAM_INPUT_WIDTHS+MMIO_INPUT_WIDTHS, FETCH_NAMES, FETCH_WIDTHS)]
    leaves = data.get("leaf_interfaces")
    if type(leaves) is not list or len(leaves) != 4:
        raise ValueError("Incomplete component hierarchy")
    refs, index = [], 0
    for leaf, (name, ins, iw, ow, regs, rw) in zip(leaves, specs, strict=True):
        if type(leaf) is not dict or leaf.get("module") != "processor_system_"+name or leaf.get("mlir") != name+".mlir" or leaf.get("clock") != "clk":
            raise ValueError("Changed leaf identity/path/clock")
        checked_rows(leaf.get("inputs"), ins, iw)
        checked_rows(leaf.get("registers"), regs, rw, registers=True)
        checked_rows(leaf.get("outputs"), [f"out_state_{k}" for k in range(len(ow)+len(rw))], ow+rw)
        taps = {r:f"out_state_{len(ow)+k}" for k,r in enumerate(regs)}
        if leaf.get("state_taps") != taps:
            raise ValueError("Incomplete or permuted raw-state taps")
        for reg in regs:
            ref = name+"."+reg
            row = data["registers"][index]
            if row.get("reference") != ref or row.get("flat_reference") != row["name"] or row.get("tap") != row["name"]:
                raise ValueError("Changed flat-to-hierarchical register correspondence")
            refs.append(ref); index += 1
    if data.get("hierarchical_registers") != refs or data.get("register_map") != {f"r_state_{k}":r for k,r in enumerate(refs)}:
        raise ValueError("Register map must be a complete ordered bijection")
    return data


def validate_topology(data, text):
    """Exact named connections, not merely equal-width or driver checks."""
    validate_descriptor(data)
    if not text.splitlines(): raise ValueError("Missing wiring top")
    header = re.fullmatch(r"module processor_system\((.+)\);", text.splitlines()[0])
    expected_header = ["input wire clk"] + [f"input wire [{p['width']-1}:0] {p['name']}" for p in data["inputs"]] + \
        [f"output wire [{p['width']-1}:0] {p['name']}" for p in data["outputs"]]
    if not header or header[1].split(", ") != expected_header:
        raise ValueError("Changed top-level interface")
    wires = {}
    instances = {}
    for line in text.splitlines()[1:]:
        if line == "endmodule":
            continue
        if match := re.fullmatch(r"wire \[([0-9]+):0\] ([A-Za-z0-9_]+);", line):
            if match[2] in wires: raise ValueError("Duplicate internal net")
            wires[match[2]] = int(match[1])+1
        elif match := re.fullmatch(r"processor_system_(core|ram|mmio|bus) (core|ram|mmio|bus)\((.+)\);", line):
            name = match[1]
            if name != match[2] or name in instances: raise ValueError("Changed instance identity")
            pairs = re.findall(r"\.([A-Za-z0-9_]+)\(([A-Za-z0-9_]+)\)", match[3])
            if ", ".join(f".{p}({w})" for p,w in pairs) != match[3] or len(dict(pairs)) != len(pairs):
                raise ValueError("Malformed or duplicated named connection")
            instances[name] = dict(pairs)
        else:
            raise ValueError("Unexpected logic/text in wiring-only top")
    if text.splitlines()[-1] != "endmodule" or text.count("endmodule") != 1 or set(instances) != {"core","ram","mmio","bus"}:
        raise ValueError("Incomplete hierarchy")
    wanted_wires = {r["tap"]:r["width"] for r in data["registers"]}
    for prefix, names, widths in (("core_input_",CORE_INPUT_NAMES,CORE_INPUT_WIDTHS),
        ("ram_input_",RAM_INPUT_NAMES,RAM_INPUT_WIDTHS),("mmio_input_",MMIO_INPUT_NAMES,MMIO_INPUT_WIDTHS),
        ("ram_output_",RAM_OUTPUT_NAMES,RAM_OUTPUT_WIDTHS)):
        wanted_wires.update(zip((prefix+n for n in names), widths, strict=True))
    if wires != wanted_wires: raise ValueError("Changed internal net declarations")
    internal_inputs = ["core_input_"+n for n in CORE_INPUT_NAMES]+["ram_input_"+n for n in RAM_INPUT_NAMES]+["mmio_input_"+n for n in MMIO_INPUT_NAMES]
    bus_inputs = INPUT_NAMES+[f"state_{k}" for k in range(30)]+["ram_output_"+n for n in RAM_OUTPUT_NAMES]+[f"state_{k}" for k in range(30,37)]
    specs = [("core",["core_input_"+n for n in CORE_INPUT_NAMES],[f"state_{k}" for k in range(30)],0,37),
             ("ram",["ram_input_"+n for n in RAM_INPUT_NAMES],["ram_output_"+n for n in RAM_OUTPUT_NAMES],37,12),
             ("mmio",["mmio_input_"+n for n in MMIO_INPUT_NAMES],[f"state_{k}" for k in range(30,37)],49,8),
             ("bus",bus_inputs,internal_inputs,57,3)]
    for leaf,(name,ins,outs,offset,count) in zip(data["leaf_interfaces"],specs,strict=True):
        wanted = {"clk":"clk"}
        wanted.update(zip((p["name"] for p in leaf["inputs"]),ins,strict=True))
        wanted.update(zip((p["name"] for p in leaf["outputs"]),outs+[f"r_state_{k}" for k in range(offset,offset+count)],strict=True))
        if instances[name] != wanted: raise ValueError("Changed typed connection in " + name)
    return {"inputs":6,"outputs":37,"registers":60,"instances":4,"exact_typed_connections":True}


def numbers(values, widths):
    return type(values) is list and len(values) == len(widths) and all(
        type(v) is int and 0 <= v < 1 << w for v,w in zip(values,widths,strict=True))


def validate_frames(data, frames, startup, ledger):
    validate_descriptor(data)
    if not numbers(startup,REGISTER_WIDTHS): raise ValueError("Invalid complete startup register image")
    expected_start = [0]*60
    expected_start[37:42] = [0x11223344+k for k in range(4)]+[0x87654321]
    if startup != expected_start: raise ValueError("Changed explicit nonzero RAM/Q startup image")
    if type(frames) is not list or len(frames) != 52: raise ValueError("Incomplete firmware frame sequence")
    for cycle,frame in enumerate(frames):
        if type(frame) is not dict or set(frame) != {"cycle","input","pre","post","registers"} or \
                type(frame["cycle"]) is not int or frame["cycle"] != cycle:
            raise ValueError("Malformed frame identity/order")
        for field,widths in (("input",INPUT_WIDTHS),("pre",OUTPUT_WIDTHS),("post",OUTPUT_WIDTHS),("registers",REGISTER_WIDTHS)):
            if not numbers(frame[field],widths): raise ValueError("Incomplete or out-of-width frame " + field)
        if frame["input"] != [int(cycle==0),0xdecafbad,0,0,0,0]: raise ValueError("Changed firmware stimulus")
    if frames[0]["registers"][37:42] != startup[37:42]: raise ValueError("Reset did not preserve initial RAM/Q")
    retired = [f["pre"] for f in frames if f["pre"][11]]
    if [r[13] for r in retired] != PROGRAM[:-1] or [r[12] for r in retired] != list(range(0,48,4)) or \
            [r[14] for r in retired] != list(range(4,52,4)):
        raise ValueError("Firmware retirement instruction/PC sequence differs")
    traps = [f["pre"] for f in frames if f["pre"][18]]
    if len(traps)!=1 or traps[0][19:23] != [48,1,0x00100073,4]: raise ValueError("Wrong terminal breakpoint event")
    previous, writes = startup, 0
    for frame in frames:
        current = frame["registers"]
        if current[37] != previous[37]:
            writes += 1
            if not frame["pre"][11] or frame["pre"][13] != PROGRAM[2]: raise ValueError("RAM effect without store retirement")
        if current[38:41] != startup[38:41]: raise ValueError("Firmware changed an untouched RAM word")
        previous = current
    final = frames[-1]["registers"]
    timer_rows = [f for f in frames if f["pre"][11] and f["pre"][12]==40]
    if len(timer_rows)!=1: raise ValueError("Missing timer load occurrence")
    timer_cycle=timer_rows[0]["cycle"]
    timer_value=frames[timer_cycle-1]["registers"][50]
    expected_ledger={"edges":52,"retired_words":PROGRAM[:-1],"ram_commits":1,"timer_read":timer_value,
                     "terminal_pc":48,"ram_word0":0x11228044,"gpio_output":0xffffff80}
    if type(ledger) is not dict or ledger != expected_ledger or any(type(ledger.get(k)) is not int
            for k in expected_ledger if k != "retired_words") or not numbers(ledger.get("retired_words"),[32]*12) or writes != 1:
        raise ValueError("Effect ledger differs from complete frame reconstruction")
    if [final[k] for k in (2,3,5,7,32,37,49)] != [0xffffff80,128,0xffffff80,timer_value,48,0x11228044,0xffffff80] or \
            frames[-1]["post"][24:29] != [1,48,1,0x00100073,4]:
        raise ValueError("Wrong final architectural/memory/device result")
    return expected_ledger


def testbench(data, startup, frames):
    lines,connections=["`timescale 1ns/1ps","module tb;","reg clk = 0;"],[".clk(clk)"]
    for group,kind in (("inputs","reg"),("outputs","wire")):
        for p in data[group]:
            lines.append(f"{kind} [{p['width']-1}:0] {p['name']}{' = 0' if kind=='reg' else ''};")
            connections.append(f".{p['name']}({p['name']})")
    lines += [f"{data['module']} dut({', '.join(connections)});","initial begin"]
    lines += [f"force dut.{p['reference']} = {p['width']}'h{v:x};" for p,v in zip(data["registers"],startup,strict=True)]
    lines += ["#1;"]+[f"release dut.{p['reference']};" for p in data["registers"]]
    def display(kind,cycle,group):
        args=", ".join(("dut."+p["reference"] if group=="registers" else p["name"]) for p in data[group])
        return f'$display("{kind},{cycle}{",%b"*len(data[group])}", {args});'
    for f in frames:
        for p,v in zip(data["inputs"],f["input"],strict=True): lines.append(f"{p['name']} = {p['width']}'h{v:x};")
        lines += ["#1;",display("IN",f["cycle"],"inputs"),display("PRE",f["cycle"],"outputs"),"clk = 1; #1;",
                  display("POST",f["cycle"],"outputs"),display("REG",f["cycle"],"registers"),"clk = 0; #1;"]
    return "\n".join(lines+['$display("SYSTEM_DONE"); $finish;',"end","endmodule",""])


def expected(frames):
    return [(kind,f["cycle"],*f[field]) for f in frames for kind,field in (("IN","input"),("PRE","pre"),("POST","post"),("REG","registers"))]


class TraceError(AssertionError):
    """A malformed/unknown/incomplete trace never establishes a semantic fault."""


class ConcreteMismatch(AssertionError):
    def __init__(self,witness,observations):
        self.witness,self.observations=witness,observations
        super().__init__("Concrete boot value mismatch: "+json.dumps(witness,sort_keys=True))


def check_trace(text,want,data):
    observations=[];done=finish=0
    for line in text.splitlines():
        if line=="SYSTEM_DONE":
            if done or finish: raise TraceError("Duplicate/misplaced completion")
            done+=1
        elif line.startswith(("IN,","PRE,","POST,","REG,")):
            fields=line.split(",");kind=fields[0]
            ports=data["inputs" if kind=="IN" else "registers" if kind=="REG" else "outputs"]
            if done or finish or len(fields)!=len(ports)+2 or not re.fullmatch(r"0|[1-9][0-9]*",fields[1]):
                raise TraceError("Malformed observation order/shape")
            if any(len(bits)!=p["width"] or re.fullmatch(r"[01]+",bits) is None for bits,p in zip(fields[2:],ports,strict=True)):
                raise TraceError("Unknown, missing or out-of-width binary value")
            observations.append((kind,int(fields[1]),*(int(bits,2) for bits in fields[2:])))
        elif re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)",line):
            finish+=1
            if done!=1 or finish!=1: raise TraceError("Misplaced simulator finish")
        elif line.strip(): raise TraceError("Unexpected simulator output")
    if done!=1 or finish!=1 or len(observations)!=len(want): raise TraceError("Incomplete trace/completion")
    for actual,target in zip(observations,want,strict=True):
        if actual[:2]!=target[:2] or len(actual)!=len(target): raise TraceError("Changed endpoint/edge order")
    # Only after the entire trace is valid may a concrete mismatch be reported.
    for actual,target in zip(observations,want,strict=True):
        ports=data["inputs" if actual[0]=="IN" else "registers" if actual[0]=="REG" else "outputs"]
        for index,(a,e) in enumerate(zip(actual[2:],target[2:],strict=True)):
            if a!=e:
                raise ConcreteMismatch({"observation":actual[0],"cycle":actual[1],"index":index,
                    "signal":ports[index]["name"],"reference":ports[index].get("reference",ports[index]["name"]),
                    "width":ports[index]["width"],"expected":e,"actual":a},observations)
    return len(observations)


def mutate_assignment(text,register,transform,*,output=False):
    pattern=(r"(\bassign\s+"+re.escape(register)+r"\s*=\s*)([^;]+);" if output else
             r"(\b"+re.escape(register)+r"\s*<=\s*)([^;]+);")
    changed,count=re.subn(pattern,lambda m:m[1]+transform(m[2].strip())+";",text)
    if count!=1 or changed==text: raise ValueError("Expected exactly one actual RTL endpoint assignment")
    return changed


def mutations(sources,data):
    core,ram,mmio,_=data["leaf_interfaces"]
    cp=lambda n:core["outputs"][n]["name"]
    cr=core["registers"][1]["reference"]
    guard=f"(~reset & {cp(15)} & ({cp(16)} == 5'd2))"
    yield "corrupt-active-x2","core",mutate_assignment(sources["core"],cr,lambda rhs:f"{guard} ? (({rhs}) ^ 32'd1) : ({rhs})")
    yield "corrupt-retired-pc","core",mutate_assignment(sources["core"],cp(12),
        lambda rhs:f"{cp(11)} ? (({rhs}) ^ 32'd4) : ({rhs})",output=True)
    word,pending,write=(ram["registers"][k]["reference"] for k in (0,11,5))
    guard=f"(~reset & {pending} & {write} & response_ready)"
    yield "drop-ram-store","ram",mutate_assignment(sources["ram"],word,lambda rhs:f"{guard} ? {word} : ({rhs})")
    gpio=mmio["registers"][0]["reference"]
    guard="(~reset & request_valid & (device == 2'd0) & write & (word == 6'd1))"
    yield "drop-gpio-store","mmio",mutate_assignment(sources["mmio"],gpio,lambda rhs:f"{guard} ? {gpio} : ({rhs})")


def semantic_witness(name,error,startup):
    w=error.witness;cycle=w["cycle"];rows={(r[0],r[1]):list(r[2:]) for r in error.observations}
    pre=rows["PRE",cycle];input_values=rows["IN",cycle]
    old=startup if cycle==0 else rows["REG",cycle-1]
    if name=="corrupt-active-x2":
        conditions={"reset":input_values[0],"retire_write_enable":pre[15],"retire_write_rd":pre[16]}
        active=w["observation"]=="REG" and w["index"]==1 and list(conditions.values())==[0,1,2]
    elif name=="corrupt-retired-pc":
        observed=rows[w["observation"],cycle]
        conditions={"retire_valid":observed[11]}
        active=w["observation"] in ("PRE","POST") and w["index"]==12 and observed[11]==1
    elif name=="drop-ram-store":
        conditions={"reset":input_values[0],"pending":old[48],"write":old[42],"response_ready":pre[10]}
        active=w["observation"]=="REG" and w["index"]==37 and list(conditions.values())==[0,1,1,1]
    elif name=="drop-gpio-store":
        conditions={"reset":input_values[0],"data_valid":pre[4],"data_write":pre[5],"data_address":pre[6]}
        active=w["observation"]=="POST" and w["index"]==34 and list(conditions.values())==[0,1,1,0x40000004]
    else: raise ValueError("Unknown mutation")
    if not active: raise AssertionError("Mismatch is not the intended active semantic fault")
    return {**w,"active_conditions":conditions,"complete_binary_trace":True,"input":input_values}


def configuration(run,tools,out):
    bundle=out/"system"
    run(["lake","env","lean","-DwarningAsError=true","--run","test/ProcessorSystemEmit.lean",bundle],"emit")
    run(["lake","env","lean","-DwarningAsError=true","--run","test/ProcessorSystemCircuit.lean",bundle],"lean-model-replay")
    data=validate_descriptor(json.loads((bundle/"interface.json").read_text()))
    topology=validate_topology(data,(bundle/"top.sv").read_text())
    frames=json.loads((bundle/"expected.json").read_text());startup=json.loads((bundle/"startup.json").read_text())
    ledger=validate_frames(data,frames,startup,json.loads((bundle/"ledger.json").read_text()))
    rtl={}
    for leaf in data["leaf_interfaces"]:
        name=Path(leaf["mlir"]).stem;path=bundle/(name+".sv")
        path.write_text(run([tools["circt"],bundle/leaf["mlir"],"--canonicalize","--lower-seq-to-sv","--lower-hw-to-sv",
            "--hw-legalize-modules","--export-verilog","-o","/dev/null"],"lower-"+name))
        rtl[name]=path
    tb=bundle/"tb.sv";tb.write_text(testbench(data,startup,frames));want=expected(frames)
    def simulate(label,paths,directory):
        exe=directory/"sim.vvp"
        run([tools["iverilog"],"-g2012","-s","tb","-o",exe,*paths,bundle/"top.sv",tb],label+"-compile")
        trace=run([tools["vvp"],exe],label+"-simulate")
        (directory/"trace.txt").write_text(trace)
        return trace
    trace=simulate("emitted",list(rtl.values()),bundle)
    checked=check_trace(trace,want,data)
    negatives=[]
    sources={name:path.read_text() for name,path in rtl.items()}
    for name,leaf,changed in mutations(sources,data):
        directory=out/name;directory.mkdir();mutant=directory/(leaf+".sv");mutant.write_text(changed)
        paths=[mutant if key==leaf else value for key,value in rtl.items()]
        trace=simulate(name,paths,directory)
        try:check_trace(trace,want,data)
        except ConcreteMismatch as error:
            witness=semantic_witness(name,error,startup)
            (directory/"witness.json").write_text(json.dumps(witness,indent=2)+"\n")
            negatives.append({"name":name,"leaf":leaf,"semantic_rejection":True,"witness":witness,
                "source_sha256":rr.sha(rtl[leaf]),"mutated_sha256":rr.sha(mutant)})
        else:raise AssertionError("Actual RTL fault was not detected: "+name)
    return {"edges":len(frames),"observations":checked,"all_registers_forced_at_startup":True,
            "forced_register_count":60,"synthesized":False,"topology":topology,"ledger":ledger,"negative_controls":negatives}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--tag",required=True);args=parser.parse_args()
    out=rr.fresh_directory(ROOT/"build/processor-system-boot",args.tag)
    report={"schema":1,"status":"running","boundary":BOUNDARY,"commands":[]};started=time.monotonic()
    run=rr.Commands(out,report["commands"])
    try:
        report["source_sha256"]=source_hashes();manifest,tools,paths=rr.selected_tools()
        report["tool_manifest"],report["tool_sha256"]=manifest,rr.tool_hashes(paths)
        run(["lake","build","Pinwheel.Hardware.Processor.SystemExportProofs","Pinwheel.Hardware.FastEmit:dynlib"],"build",900)
        run(["python3","test/test_processor_system_boot.py"],"portable-tests")
        audit=run(["lake","env","lean","-DwarningAsError=true","--run","test/ProcessorSystemExport.lean"],"staged-audit",900)
        if "standard axioms only" not in audit:raise AssertionError("Missing system export audit")
        report["configuration"]=configuration(run,tools,out)
        if source_hashes()!=report["source_sha256"] or rr.tool_hashes(paths)!=report["tool_sha256"]:
            raise RuntimeError("Owning source/tool closure changed during boot validation")
        report["status"]="passed"
    except BaseException as error:
        report["status"],report["error"]="failed",f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"]=round(time.monotonic()-started,3)
        report["artifact_sha256"]={str(p.relative_to(out)):rr.sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out/"report.json").write_text(json.dumps(report,indent=2)+"\n")


if __name__=="__main__":main()
