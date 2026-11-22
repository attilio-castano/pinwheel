#!/usr/bin/env python3
"""Cold reset/load/run replay of emitted and synthesized processor RTL.

No register is forced or initialized by the testbench. All external pins must be
binary; raw RAM/Q/metadata observations are compared once the supplied clocked
history defines them. The knownness schedule is fixed before simulation.
"""
from __future__ import annotations
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import time

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location("processor_boot",ROOT/"scripts/check-processor-system-boot.py")
boot=importlib.util.module_from_spec(spec);spec.loader.exec_module(boot)
rr=boot.rr
INPUT_WIDTHS=boot.INPUT_WIDTHS+[1,1,2,32]
OUTPUT_WIDTHS=boot.OUTPUT_WIDTHS+[1,1]
INPUT_NAMES=[f"in_state_{k}" for k in range(10)]
OUTPUT_NAMES=[f"state_{k}" for k in range(39)]
LOADER_INPUT_WIDTHS=boot.RAM_INPUT_WIDTHS+[1,1,2,32]
LOADER_OUTPUT_WIDTHS=boot.RAM_OUTPUT_WIDTHS+[1]
BOUNDARY=("Cold emitted and generic synthesized RTL boot with synchronous reset and four accepted loader writes; "
          "no testbench force, deposit, initialization attribute, RAM image preload, or synthesized raw-register assumption. "
          "All external outputs are binary and checked. Raw emitted registers are checked only after reset or an explicit "
          "accepted write/read/capture defines them; earlier RAM/Q/inactive metadata may be X. "
          "Firmware/model replay is finite evidence, not imported-RTL certification or independent Python ISA execution.")


def source_hashes():
    pending=[ROOT/p for p in ("test/ProcessorLoadableSystemEmit.lean","test/ProcessorLoadableSystemExport.lean",
                             "test/ProcessorLoadableSystemCircuit.lean")]
    paths=set()
    while pending:
        path=pending.pop()
        if path in paths:continue
        paths.add(path)
        for line in path.read_text().splitlines():
            if m:=re.match(r"^import\s+(.+)$",line):
                for module in m[1].split("--",1)[0].split():
                    if module.startswith(("Pinwheel.","test.")):
                        pending.append(ROOT/(module.replace(".","/")+".lean"))
    paths.update(ROOT/p for p in ("scripts/check-processor-loadable-system-boot.py","test/test_processor_loadable_system_boot.py",
        "scripts/check-processor-system-boot.py","test/test_processor_system_boot.py","scripts/check-round-robin-circuit.py",
        "scripts/process_group.py","scripts/validation_run.py","lakefile.toml","lake-manifest.json","lean-toolchain",
        "tools/hardware-toolchain.json"))
    return {str(p.relative_to(ROOT)):rr.sha(p) for p in sorted(paths)}


def leaf_shapes():
    return [
        ("core",boot.CORE_INPUT_NAMES,boot.CORE_INPUT_WIDTHS,boot.CORE_OUTPUT_WIDTHS,
         [f"r_state_{k}" for k in range(37)],boot.CORE_REGISTER_WIDTHS),
        ("ram",[f"state_{k}" for k in range(13)],LOADER_INPUT_WIDTHS,LOADER_OUTPUT_WIDTHS,
         [f"r_state_{k}" for k in range(12)],boot.RAM_REGISTER_WIDTHS),
        ("mmio",boot.MMIO_INPUT_NAMES,boot.MMIO_INPUT_WIDTHS,boot.MMIO_OUTPUT_WIDTHS,
         boot.MMIO_REGISTER_NAMES,boot.MMIO_REGISTER_WIDTHS),
        ("bus",[f"state_{k}" for k in range(52)],INPUT_WIDTHS+boot.CORE_OUTPUT_WIDTHS+LOADER_OUTPUT_WIDTHS+boot.MMIO_OUTPUT_WIDTHS,
         boot.CORE_INPUT_WIDTHS+LOADER_INPUT_WIDTHS+boot.MMIO_INPUT_WIDTHS+[1,1],boot.FETCH_NAMES,boot.FETCH_WIDTHS)]


def validate_descriptor(data):
    if type(data) is not dict:raise ValueError("Missing descriptor object")
    constants={"schema":1,"module":"processor_loadable_system","clock":"clk","rom_word_width":5,"ram_word_width":2,
        "ram_base":0x10000,"gpio_base":0x40000000,"timer_base":0x40000100,"uart_base":0x40000200,
        "top_verilog":"top.sv","latency_added":0,"reset_synchronous":True}
    for k,v in constants.items():
        if type(data.get(k)) is not type(v) or data[k]!=v:raise ValueError("Changed descriptor "+k)
    if not boot.numbers(data.get("rom_words"),[32]*32) or data["rom_words"]!=boot.PROGRAM+[0]*19:
        raise ValueError("Changed immutable ROM image")
    boot.checked_rows(data.get("inputs"),INPUT_NAMES,INPUT_WIDTHS)
    boot.checked_rows(data.get("outputs"),OUTPUT_NAMES,OUTPUT_WIDTHS)
    boot.checked_rows(data.get("registers"),[f"r_state_{k}" for k in range(60)],boot.REGISTER_WIDTHS)
    roles={n:INPUT_NAMES[k] for k,n in enumerate(boot.INPUT_NAMES+["loader_mode","loader_valid","loader_address","loader_data"])}
    roles.update({"core_"+n:OUTPUT_NAMES[k] for k,n in enumerate(boot.CORE_OUTPUT_ROLES)})
    roles.update({"mmio_"+n:OUTPUT_NAMES[k+30] for k,n in enumerate(boot.MMIO_OUTPUT_ROLES)})
    roles.update(loader_ready="state_37",running="state_38")
    if data.get("roles")!=roles:raise ValueError("Incomplete/permuted semantic roles")
    leaves=data.get("leaf_interfaces")
    if type(leaves) is not list or len(leaves)!=4:raise ValueError("Incomplete four-leaf topology")
    refs=[]
    for leaf,(name,ins,iw,ow,regs,rw) in zip(leaves,leaf_shapes(),strict=True):
        if type(leaf) is not dict or leaf.get("module")!="processor_loadable_system_"+name or leaf.get("mlir")!=name+".mlir" or leaf.get("clock")!="clk":
            raise ValueError("Changed leaf identity")
        boot.checked_rows(leaf.get("inputs"),ins,iw)
        boot.checked_rows(leaf.get("outputs"),[f"out_state_{k}" for k in range(len(ow)+len(rw))],ow+rw)
        boot.checked_rows(leaf.get("registers"),regs,rw,registers=True)
        if leaf.get("state_taps")!={r:f"out_state_{len(ow)+k}" for k,r in enumerate(regs)}:
            raise ValueError("Incomplete/permuted raw state taps")
        refs += [name+"."+r for r in regs]
    for p,ref in zip(data["registers"],refs,strict=True):
        if p.get("reference")!=ref or p.get("flat_reference")!=p["name"] or p.get("tap")!=p["name"]:
            raise ValueError("Changed register correspondence")
    if data.get("hierarchical_registers")!=refs or data.get("register_map")!={f"r_state_{k}":r for k,r in enumerate(refs)}:
        raise ValueError("Register correspondence is not a complete ordered bijection")
    return data


def topology_expected(data):
    wires={p["name"]:p["width"] for p in data["registers"]}
    core=["core_input_"+n for n in boot.CORE_INPUT_NAMES]
    ram=["ram_input_state_"+str(k) for k in range(13)]
    mmio=["mmio_input_"+n for n in boot.MMIO_INPUT_NAMES]
    ramout=["ram_output_state_"+str(k) for k in range(5)]
    for names,widths in ((core,boot.CORE_INPUT_WIDTHS),(ram,LOADER_INPUT_WIDTHS),(mmio,boot.MMIO_INPUT_WIDTHS),(ramout,LOADER_OUTPUT_WIDTHS)):
        wires.update(zip(names,widths,strict=True))
    configs=[("core",core,OUTPUT_NAMES[:30],0,37),("ram",ram,ramout,37,12),
        ("mmio",mmio,OUTPUT_NAMES[30:37],49,8),
        ("bus",INPUT_NAMES+OUTPUT_NAMES[:30]+ramout+OUTPUT_NAMES[30:37],core+ram+mmio+OUTPUT_NAMES[37:],57,3)]
    instances={}
    for leaf,(name,ins,outs,start,count) in zip(data["leaf_interfaces"],configs,strict=True):
        ports={"clk":"clk"}
        ports.update(zip([p["name"] for p in leaf["inputs"]],ins,strict=True))
        ports.update(zip([p["name"] for p in leaf["outputs"]],outs+[f"r_state_{k}" for k in range(start,start+count)],strict=True))
        instances[name]=ports
    return wires,instances


def validate_topology(data,text):
    validate_descriptor(data)
    lines=text.splitlines()
    header=["input wire clk"]+[f"input wire [{p['width']-1}:0] {p['name']}" for p in data["inputs"]]
    header += [f"output wire [{p['width']-1}:0] {p['name']}" for p in data["outputs"]]
    if not lines or lines[0]!="module processor_loadable_system("+", ".join(header)+");" or lines[-1]!="endmodule":
        raise ValueError("Changed external typed topology")
    wires={};instances={}
    for line in lines[1:-1]:
        if m:=re.fullmatch(r"wire \[([0-9]+):0\] ([A-Za-z0-9_]+);",line):
            if m[2] in wires:raise ValueError("Duplicate net")
            wires[m[2]]=int(m[1])+1
        elif m:=re.fullmatch(r"processor_loadable_system_(core|ram|mmio|bus) (core|ram|mmio|bus)\((.+)\);",line):
            if m[1]!=m[2] or m[1] in instances:raise ValueError("Changed instance identity")
            pairs=re.findall(r"\.([A-Za-z0-9_]+)\(([A-Za-z0-9_]+)\)",m[3])
            if len(dict(pairs))!=len(pairs) or ", ".join(f".{p}({n})" for p,n in pairs)!=m[3]:
                raise ValueError("Malformed named connections")
            instances[m[1]]=dict(pairs)
        else:raise ValueError("Unexpected logic in wiring-only top")
    if (wires,instances)!=topology_expected(data):raise ValueError("Changed typed wiring (including equal-width aliases)")
    return {"inputs":10,"outputs":39,"registers":60,"leaves":4,"exact_typed_connections":True}


def initialization(frames):
    """Derive definedness from the fixed expected history, never mutant values."""
    known=[False]*60;result=[];loaded=set();first_capture=None;accepted=[]
    if not frames or frames[0]["input"][0]!=1:raise ValueError("Cold replay must start with synchronous reset")
    for f in frames:
        cycle=f["cycle"];i=f["input"];pre=f["pre"]
        reset,mode,valid,address,data=i[0],i[6],i[7],i[8],i[9]
        if reset or mode:
            for k in [*range(37),48,*range(49,60)]:known[k]=True
        if mode and not reset and valid:
            known[37+address]=True;loaded.add(address);accepted.append({"cycle":cycle,"address":address,"data":data})
        if not reset and not mode:
            if loaded!={0,1,2,3}:raise ValueError("Processor ran before all words were loaded")
            if pre[4] and 0x10000<=pre[6]<0x10010:
                if cycle==0 or not known[48]:raise ValueError("Unknown RAM pending state at request")
                pending=frames[cycle-1]["registers"][48]
                if not pending:
                    for k in range(42,48):known[k]=True
                    size,offset=pre[7],pre[6]%4
                    legal=size==0 or size==1 and offset in (0,2) or size==2 and offset==0
                    if legal:
                        word=(pre[6]-0x10000)//4
                        if not known[37+word]:raise ValueError("Read captured an uninitialized word")
                        known[41]=True
                    if first_capture is None:first_capture=cycle
        result.append(known.copy())
    if not all(known):raise ValueError("Firmware never defined every raw register")
    return result,{"startup_forced_registers":0,"loader_writes":accepted,"loaded_words":sorted(loaded),
                   "first_metadata_capture_cycle":first_capture,"defined_register_observations":sum(map(sum,result)),
                   "unconstrained_register_observations":len(result)*60-sum(map(sum,result))}


def validate_frames(data,frames,startup,ledger):
    validate_descriptor(data)
    if not boot.numbers(startup,boot.REGISTER_WIDTHS):raise ValueError("Malformed conceptual startup")
    if type(frames) is not list or not 50<=len(frames)<=100:raise ValueError("Missing bounded boot trace")
    for cycle,f in enumerate(frames):
        if type(f) is not dict or set(f)!={"cycle","input","pre","post","registers"} or type(f["cycle"]) is not int or f["cycle"]!=cycle:
            raise ValueError("Changed frame identity/order")
        for field,widths in (("input",INPUT_WIDTHS),("pre",OUTPUT_WIDTHS),("post",OUTPUT_WIDTHS),("registers",boot.REGISTER_WIDTHS)):
            if not boot.numbers(f[field],widths):raise ValueError("Invalid frame "+field)
        i=f["input"]
        if i[1:6]!=[0xdecafbad,0,0,0,0]:raise ValueError("Changed GPIO/frontend traffic")
        if [i[0],i[6],i[7]]!=[int(cycle in (0,7)),int(cycle<8),int(cycle in (0,2,3,4,5,7))]:
            raise ValueError("Changed reset/loader ownership schedule")
        if 2<=cycle<=5 and i[8:10]!=[cycle-2,0x11223344+cycle-2]:raise ValueError("Changed loader image")
        if i[0] or i[6]:
            if f["pre"][1:37]!=[0]*36 or f["post"][1:37]!=[0]*36:
                raise ValueError("Core/device activity during loader/reset ownership")
        status=[int(i[6] and not i[0]),int(not i[6] and not i[0])]
        if f["pre"][37:]!=status or f["post"][37:]!=status:raise ValueError("Changed loader/running status")
    masks,coverage=initialization(frames)
    old=startup;stores=0
    for f in frames:
        i=f["input"];new=f["registers"]
        if i[0] or i[6]:
            for a in range(4):
                value=i[9] if not i[0] and i[6] and i[7] and i[8]==a else old[37+a]
                if new[37+a]!=value:raise ValueError("Loader/reset RAM effect differs")
            if new[41:48]!=old[41:48]:raise ValueError("Loader/reset altered Q/inactive metadata")
        elif new[37]!=old[37]:
            stores+=1
            if not f["pre"][11] or f["pre"][13]!=boot.PROGRAM[2]:raise ValueError("RAM write without matching store retirement")
        old=new
    retired=[f["pre"] for f in frames if f["pre"][11]]
    if [r[13] for r in retired]!=boot.PROGRAM[:-1] or [r[12] for r in retired]!=list(range(0,48,4)) or [r[14] for r in retired]!=list(range(4,52,4)):
        raise ValueError("Wrong retirement words/PCs")
    traps=[f["pre"] for f in frames if f["pre"][18]]
    if len(traps)!=1 or traps[0][19:23]!=[48,1,0x00100073,4]:raise ValueError("Wrong breakpoint completion")
    reads=[f for f in frames if f["pre"][11] and f["pre"][12]==40]
    if len(reads)!=1:raise ValueError("Wrong timer read occurrences")
    timer=frames[reads[0]["cycle"]-1]["registers"][50];final=frames[-1]["registers"]
    if stores!=1 or [final[k] for k in (2,3,5,7,32,37,49)]!=[0xffffff80,128,0xffffff80,timer,48,0x11228044,0xffffff80] or final[38:41]!=[0x11223345,0x11223346,0x11223347]:
        raise ValueError("Wrong final CPU/RAM/device state")
    if frames[-1]["post"][24:29]!=[1,48,1,0x00100073,4]:raise ValueError("Missing persistent terminal result")
    if type(ledger) is not dict:raise ValueError("Missing model effect ledger")
    reconstructed={"edges":len(frames),"retired_words":boot.PROGRAM[:-1],"ram_commits":stores,
        "timer_read":timer,"terminal_pc":48,"ram_word0":0x11228044,"gpio_output":0xffffff80,
        "loader_writes":len(coverage["loader_writes"]),"external_resets":sum(f["input"][0] for f in frames)}
    if set(ledger)!=set(reconstructed):raise ValueError("Incomplete/extra model ledger fields")
    for k,v in reconstructed.items():
        if type(ledger.get(k)) is not type(v) or ledger[k]!=v:raise ValueError("Model ledger differs at "+k)
    if not boot.numbers(ledger["retired_words"],[32]*12):raise ValueError("Noninteger retirement word in ledger")
    return masks,coverage,reconstructed


def expected(frames,masks,registers):
    result=[]
    for f,known in zip(frames,masks,strict=True):
        result += [(kind,f["cycle"],*f[field]) for kind,field in (("IN","input"),("PRE","pre"),("POST","post"))]
        if registers:result.append(("REG",f["cycle"],*(v if k else None for v,k in zip(f["registers"],known,strict=True))))
    return result


def check_trace(text,want,data):
    observations=[];done=finish=0
    for line in text.splitlines():
        if line=="LOADABLE_DONE":
            if done or finish:raise boot.TraceError("Duplicate/misplaced completion")
            done=1
        elif line.startswith(("IN,","PRE,","POST,","REG,")):
            fields=line.split(",");kind=fields[0]
            ports=data["inputs" if kind=="IN" else "registers" if kind=="REG" else "outputs"]
            n=len(observations)
            if done or finish or n>=len(want) or len(fields)!=len(ports)+2 or not re.fullmatch(r"0|[1-9][0-9]*",fields[1]) or (kind,int(fields[1]))!=want[n][:2]:
                raise boot.TraceError("Malformed/missing/extra/out-of-order observation")
            values=[]
            for token,p,target in zip(fields[2:],ports,want[n][2:],strict=True):
                if len(token)!=p["width"] or not re.fullmatch(r"[01x]+" if target is None else r"[01]+",token):
                    raise boot.TraceError("Unknown defined endpoint or malformed raw observation")
                if target is None and kind!="REG":raise boot.TraceError("External endpoint cannot be unconstrained")
                values.append(None if "x" in token else int(token,2))
            observations.append((kind,int(fields[1]),*values))
        elif re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)",line):
            finish+=1
            if done!=1 or finish!=1:raise boot.TraceError("Misplaced finish")
        elif line.strip():raise boot.TraceError("Unexpected simulator diagnostic")
    if done!=1 or finish!=1 or len(observations)!=len(want):raise boot.TraceError("Incomplete replay")
    for actual,target in zip(observations,want,strict=True):
        ports=data["inputs" if actual[0]=="IN" else "registers" if actual[0]=="REG" else "outputs"]
        for index,(a,e) in enumerate(zip(actual[2:],target[2:],strict=True)):
            if e is not None and a!=e:
                p=ports[index]
                raise boot.ConcreteMismatch({"observation":actual[0],"cycle":actual[1],"index":index,
                    "signal":p["name"],"reference":p.get("reference",p["name"]),"width":p["width"],"expected":e,"actual":a},observations)
    return len(observations)


def testbench(data,frames,registers):
    lines=["`timescale 1ns/1ps","module tb;","reg clk = 0;"];connections=[".clk(clk)"]
    for field,kind in (("inputs","reg"),("outputs","wire")):
        for p in data[field]:
            lines.append(f"{kind} [{p['width']-1}:0] {p['name']}{' = 0' if kind=='reg' else ''};")
            connections.append(f".{p['name']}({p['name']})")
    lines += [f"{data['module']} dut({', '.join(connections)});","initial begin"]
    def display(kind,cycle,field):
        args=", ".join("dut."+p["reference"] if field=="registers" else p["name"] for p in data[field])
        return f'$display("{kind},{cycle}{",%b"*len(data[field])}", {args});'
    for f in frames:
        for p,v in zip(data["inputs"],f["input"],strict=True):lines.append(f"{p['name']} = {p['width']}'h{v:x};")
        lines += ["#1;",display("IN",f["cycle"],"inputs"),display("PRE",f["cycle"],"outputs"),"clk = 1; #1;",
                  display("POST",f["cycle"],"outputs")]
        if registers:lines.append(display("REG",f["cycle"],"registers"))
        lines += ["clk = 0; #1;"]
    return "\n".join(lines+['$display("LOADABLE_DONE"); $finish;',"end","endmodule",""])


def mutations(sources,data):
    core,ram,mmio,_=data["leaf_interfaces"]
    cr=core["registers"][1]["reference"]
    yield "corrupt-active-x2","core",boot.mutate_assignment(sources["core"],cr,
        lambda rhs:f"(~reset & out_state_15 & (out_state_16 == 5'd2)) ? (({rhs}) ^ 32'd1) : ({rhs})")
    yield "corrupt-retired-pc","core",boot.mutate_assignment(sources["core"],"out_state_12",
        lambda rhs:f"out_state_11 ? (({rhs}) ^ 32'd4) : ({rhs})",output=True)
    word,pending,write=(ram["registers"][k]["reference"] for k in (0,11,5))
    yield "drop-ram-store","ram",boot.mutate_assignment(sources["ram"],word,
        lambda rhs:f"(~state_0 & ~state_9 & {pending} & {write} & state_8) ? {word} : ({rhs})")
    yield "drop-gpio-store","mmio",boot.mutate_assignment(sources["mmio"],mmio["registers"][0]["reference"],
        lambda rhs:f"(~reset & request_valid & (device == 2'd0) & write & (word == 6'd1)) ? r_gpio : ({rhs})")
    yield "corrupt-loader-word","ram",boot.mutate_assignment(sources["ram"],word,
        lambda rhs:f"(~state_0 & state_9 & state_10 & (state_11 == 2'd0)) ? (({rhs}) ^ 32'd1) : ({rhs})")
    yield "suppress-retired-write","core",boot.mutate_assignment(sources["core"],"out_state_15",
        lambda rhs:f"({rhs}) & ~out_state_11",output=True)
    yield "redirect-retired-write","core",boot.mutate_assignment(sources["core"],"out_state_16",
        lambda rhs:f"(out_state_11 & out_state_15) ? (({rhs}) ^ 5'd1) : ({rhs})",output=True)


def semantic_witness(name,error,startup):
    if name in ("suppress-retired-write", "redirect-retired-write"):
        w = error.witness
        rows = {(r[0], r[1]): r[2:] for r in error.observations}
        if w["observation"] not in ("PRE", "POST"):
            raise AssertionError("Expected a retirement output mismatch")
        outputs = rows[w["observation"], w["cycle"]]
        inputs = rows["IN", w["cycle"]]
        suppress = name == "suppress-retired-write"
        enabled = w["expected"] if suppress else outputs[15]
        rd = outputs[16] if suppress else w["expected"]
        if (inputs[0] or inputs[6] or outputs[11] != 1 or enabled != 1 or rd == 0
                or w["index"] != (15 if suppress else 16)
                or w["actual"] != (0 if suppress else rd ^ 1)):
            raise AssertionError("Mismatch lacks an active architectural writeback")
        return {**w, "input": list(inputs), "complete_binary_defined_trace": True,
                "uninitialized_raw_fields_scoped": True,
                "active_conditions": {"retire_valid": 1, "expected_write_enable": enabled,
                                      "expected_destination": rd}}
    if name!="corrupt-loader-word":
        witness=boot.semantic_witness(name,error,startup)
        witness.pop("complete_binary_trace")
        return {**witness,"complete_binary_defined_trace":True,"uninitialized_raw_fields_scoped":True}
    w=error.witness;rows={(r[0],r[1]):list(r[2:]) for r in error.observations};i=rows["IN",w["cycle"]]
    if w["observation"]!="REG" or w["index"]!=37 or [i[k] for k in (0,6,7,8)]!=[0,1,1,0]:
        raise AssertionError("Loader mismatch lacks active accepted-word event")
    return {**w,"input":i,"active_conditions":{"reset":0,"mode":1,"valid":1,"address":0},"complete_binary_defined_trace":True}


def check_no_initialization(graph):
    modules=graph.get("modules")
    if type(modules) is not dict or not modules:raise ValueError("Missing RTL modules")
    for module in modules.values():
        if any("init" in net.get("attributes",{}) for net in module.get("netnames",{}).values()):
            raise ValueError("DUT initialization attribute violates cold-start scope")
        if any(c.get("type","").startswith(("$meminit","$initstate")) for c in module.get("cells",{}).values()):
            raise ValueError("DUT initialization cell violates cold-start scope")


def configuration(run,tools,out):
    directory=out/"system"
    run(["lake","env","lean","-DwarningAsError=true","--run","test/ProcessorLoadableSystemEmit.lean",directory],"emit")
    run(["lake","env","lean","-DwarningAsError=true","--run","test/ProcessorLoadableSystemCircuit.lean",directory],"model-replay")
    data=validate_descriptor(json.loads((directory/"interface.json").read_text()))
    topology=validate_topology(data,(directory/"top.sv").read_text())
    frames=json.loads((directory/"expected.json").read_text());startup=json.loads((directory/"startup.json").read_text())
    masks,coverage,ledger=validate_frames(data,frames,startup,json.loads((directory/"ledger.json").read_text()))
    (directory/"known-registers.json").write_text(json.dumps(masks,indent=2)+"\n")
    (directory/"initialization.json").write_text(json.dumps(coverage,indent=2)+"\n")
    rtl={}
    for leaf in data["leaf_interfaces"]:
        name=Path(leaf["mlir"]).stem;path=directory/(name+".sv")
        path.write_text(run([tools["circt"],directory/leaf["mlir"],"--canonicalize","--lower-seq-to-sv","--lower-hw-to-sv",
            "--hw-legalize-modules","--export-verilog","-o","/dev/null"],"lower-"+name));rtl[name]=path
    def simulate(label,paths,registers,target):
        tb=target/"tb.sv";exe=target/"sim.vvp";tb.write_text(testbench(data,frames,registers))
        run([tools["iverilog"],"-g2012","-s","tb","-o",exe,*paths,tb],label+"-compile")
        text=run([tools["vvp"],exe],label+"-simulate");(target/"trace.txt").write_text(text)
        return text
    wanted=expected(frames,masks,True)
    positive=simulate("emitted",[*rtl.values(),directory/"top.sv"],True,directory)
    checked=check_trace(positive,wanted,data)
    netlist=directory/"synth.v";netjson=directory/"synth.json";script=directory/"synth.ys";rawjson=directory/"before-synth.json"
    script.write_text("read_verilog -sv "+" ".join(rr.yosys_quote(p) for p in [*rtl.values(),directory/"top.sv"])+"\n"+
        f"hierarchy -check -top {data['module']}\nproc\nwrite_json {rr.yosys_quote(rawjson)}\n"+
        f"synth -top {data['module']} -flatten\ncheck -assert\n"+
        f"write_json {rr.yosys_quote(netjson)}\nwrite_verilog -noattr {rr.yosys_quote(netlist)}\n")
    run([tools["yosys"],"-Q","-T","-s",script],"synthesize",900)
    check_no_initialization(json.loads(rawjson.read_text()))
    check_no_initialization(json.loads(netjson.read_text()))
    synthdir=out/"synthesized";synthdir.mkdir()
    synth=simulate("synthesized",[netlist],False,synthdir)
    synth_checked=check_trace(synth,expected(frames,masks,False),data)
    modules=json.loads(netjson.read_text())["modules"]
    if set(modules)!={data["module"]} or modules[data["module"]].get("memories"):raise ValueError("Unexpected synthesized hierarchy/memory")
    cells=Counter(c["type"] for c in modules[data["module"]]["cells"].values())
    negatives=[];sources={n:p.read_text() for n,p in rtl.items()}
    for name,leaf,changed in mutations(sources,data):
        target=out/name;target.mkdir();mutant=target/(leaf+".sv");mutant.write_text(changed)
        paths=[mutant if n==leaf else p for n,p in rtl.items()]+[directory/"top.sv"]
        trace=simulate(name,paths,True,target)
        try:check_trace(trace,wanted,data)
        except boot.ConcreteMismatch as error:
            witness=semantic_witness(name,error,startup)
            (target/"witness.json").write_text(json.dumps(witness,indent=2)+"\n")
            negatives.append({"name":name,"leaf":leaf,"semantic_rejection":True,"witness":witness,
                "source_sha256":rr.sha(rtl[leaf]),"mutated_sha256":rr.sha(mutant)})
        else:raise AssertionError("Actual RTL fault survived: "+name)
    return {"edges_per_form":len(frames),"emitted_observations":checked,"synthesized_observations":synth_checked,
        "topology":topology,"initialization":coverage,"ledger":ledger,"generic_cells":sum(cells.values()),
        "cell_types":dict(cells),"negative_controls":negatives,"synthesized_startup_forcing":False}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--tag",required=True);args=parser.parse_args()
    out=rr.fresh_directory(ROOT/"build/processor-loadable-system-boot",args.tag)
    report={"schema":1,"status":"running","boundary":BOUNDARY,"commands":[]};start=time.monotonic()
    run=rr.Commands(out,report["commands"])
    try:
        report["source_sha256"]=source_hashes();manifest,tools,paths=rr.selected_tools()
        report["tool_manifest"],report["tool_sha256"]=manifest,rr.tool_hashes(paths)
        run(["lake","build","Pinwheel.Hardware.Processor.Examples.ByteProgram",
             "Pinwheel.Hardware.Processor.LoadableSystemExportProofs",
             "Pinwheel.Hardware.Processor.LoadableSystemProofs","Pinwheel.Hardware.FastEmit:dynlib"],"build",900)
        run(["python3","test/test_processor_loadable_system_boot.py"],"portable-tests")
        audit=run(["lake","env","lean","-DwarningAsError=true","--run","test/ProcessorLoadableSystemExport.lean"],"export-audit")
        if "standard axioms only" not in audit:raise ValueError("Missing standard-only export audit")
        report["configuration"]=configuration(run,tools,out)
        if source_hashes()!=report["source_sha256"] or rr.tool_hashes(paths)!=report["tool_sha256"]:
            raise RuntimeError("Owning sources or selected CAD tools changed during replay")
        report["status"]="passed"
    except BaseException as error:
        report["status"],report["error"]="failed",f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"]=round(time.monotonic()-start,3)
        report["artifact_sha256"]={str(p.relative_to(out)):rr.sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out/"report.json").write_text(json.dumps(report,indent=2)+"\n")


if __name__=="__main__":main()
