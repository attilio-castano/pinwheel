#!/usr/bin/env python3
"""Pinned Sail architectural differential gate. No assembler is required.

Each case uses a fresh upstream process and a raw ELF32 image. The debugger
sets/reads integer registers and reads bytes; instruction execution is the
unaltered upstream model. Its debugger's PC setter updates next_pc rather than
the current fetch PC, so it is deliberately never used. Native Sail's debugger
binds a transient local test port; processes are closed after each one-step case.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import socket
import struct
import subprocess
import sys
import tarfile
import time
import urllib.request

from isa_reference_cases import campaign, KINDS, EXCLUSIONS

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / "build/isa-reference/dependencies"
MANIFEST = ROOT / "tools/isa_reference.json"
ADAPTER = ROOT / "test/ISAReferenceTrace.lean"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def source_paths():
    found = {Path(__file__).resolve(), ROOT / "scripts/isa_reference_cases.py", MANIFEST,
             ROOT / "test/isa_reference_test.py", ADAPTER, ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"}
    todo = [ADAPTER]
    while todo:
        path = todo.pop()
        for module in re.findall(r"^import\s+(Pinwheel\.[\w.]+)\s*$", path.read_text(), re.M):
            dependency = ROOT / (module.replace(".", "/") + ".lean")
            if dependency not in found:
                found.add(dependency)
                todo.append(dependency)
    return sorted(found)


def source_hashes():
    return {str(p.relative_to(ROOT)): sha(p) for p in source_paths()}


def command(argv, directory, records, *, timeout=120):
    index = len(records)
    start = time.monotonic()
    result = subprocess.run([str(v) for v in argv], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    log = directory / f"command-{index:03d}.log"
    log.write_text(result.stdout)
    records.append(dict(argv=[str(v) for v in argv], exit_code=result.returncode,
                        seconds=time.monotonic()-start, log=str(log.relative_to(directory))))
    if result.returncode:
        raise RuntimeError(f"Command failed: {argv}; see {log}")
    return result.stdout


def dependencies(fetch):
    pin = json.loads(MANIFEST.read_text())
    if f"{platform.system()}-{platform.machine()}" != pin["native_platform"]:
        raise RuntimeError("This pinned binary gate currently supports Darwin arm64 only")
    CACHE.mkdir(parents=True, exist_ok=True)
    for name in ("archive", "source"):
        entry = pin[name]
        archive = CACHE / entry["filename"]
        if not archive.exists():
            if not fetch:
                raise RuntimeError(f"Missing {archive}; use --fetch for the authorized isolated download")
            with urllib.request.urlopen(entry["url"], timeout=60) as response:
                data = response.read()
            if hashlib.sha256(data).hexdigest() != entry["sha256"]:
                raise RuntimeError("Downloaded archive does not match immutable pin")
            archive.write_bytes(data)
        if sha(archive) != entry["sha256"]:
            raise RuntimeError(f"Mismatched dependency archive: {archive}")
        with tarfile.open(archive) as tar:
            members = tar.getmembers()
            for member in members:
                parts = Path(member.name).parts
                if not parts or parts[0] != entry["root"] or ".." in parts or member.issym() or member.islnk():
                    raise RuntimeError("Unsafe upstream archive member")
            if not (CACHE / entry["root"]).exists():
                tar.extractall(CACHE, filter="data")
            # Check extracted bytes against the archive, not just a cached receipt.
            for member in members:
                if member.isfile():
                    actual = CACHE / member.name
                    if not actual.is_file() or actual.read_bytes() != tar.extractfile(member).read():
                        raise RuntimeError(f"Changed extracted dependency: {actual}")
    binary = CACHE / pin["archive"]["root"] / "bin/sail_riscv_sim"
    return pin, binary


def configuration(default_text):
    # Upstream's JSON template has full-line // comments, no string URL values.
    data = json.loads(re.sub(r"//[^\n]*", "", default_text))
    def disable(value):
        if isinstance(value, dict):
            for key, item in value.items():
                if key == "supported": value[key] = False
                elif key == "support_level": value[key] = "Disabled"
                else: disable(item)
        elif isinstance(value, list):
            for item in value: disable(item)
    disable(data["extensions"])
    data["base"]["xlen"] = 32
    data["base"]["E"] = False
    data["base"]["mstatus"]["fs_legal_states"] = "ExtContext_Off"
    data["base"]["mstatus"]["vs_legal_states"] = "ExtContext_Off"
    data["base"]["hpmevent_width_bits"] = 32
    memory = data["memory"]
    memory["physaddr_bits"] = 32
    memory["pmp"]["count"] = memory["pmp"]["usable_count"] = 0
    memory["misaligned"]["exceptions"]["load_store"] = {"Some": "AlignmentException"}
    data["platform"]["clint"]["supported"] = False
    data["platform"]["simple_interrupt_generator"]["supported"] = False
    ram = copy.deepcopy(memory["regions"][-1])
    ram["base"]["value"] = "0x10000"
    ram["size"]["value"] = "0x1000"
    ram["attributes"]["executable"] = False
    rom = copy.deepcopy(ram)
    rom["base"]["value"] = "0x0"
    rom["attributes"].update(executable=True, writable=False, mem_type="IOMemory")
    for region in (rom, ram):
        region["attributes"].update(atomic_support="AMONone", misaligned_atomicity_granule_size_exp=0,
            vector_misaligned_atomicity_granule_size_exp=0, reservability="RsrvNone",
            supports_cbo_zero=False, supports_pte_read=False, supports_pte_write=False)
    memory["regions"] = [rom, ram]
    return data


def rom_bytes(case):
    result = bytearray(4096)
    struct.pack_into("<I", result, case["pc"], case["word"])
    return bytes(result)


def elf(case):
    rom = rom_bytes(case)
    ram = bytes(case["ram"])
    header = b"\x7fELF" + bytes([1, 1, 1, 0]) + bytes(8)
    header += struct.pack("<HHIIIIIHHHHHH", 2, 243, 1, case["pc"], 52, 0, 0, 52, 32, 2, 0, 0, 0)
    segments = struct.pack("<IIIIIIII", 1, 116, 0, 0, len(rom), len(rom), 5, 4)
    segments += struct.pack("<IIIIIIII", 1, 116+len(rom), 65536, 65536, len(ram), len(ram), 6, 4)
    return header + segments + rom + ram


class RSP:
    def __init__(self, sock):
        self.sock = sock
        self.sock.settimeout(5)
        self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.transcript = []
        self.ack = True

    def exact(self, count):
        result = b""
        while len(result) < count:
            data = self.sock.recv(count-len(result))
            if not data: raise RuntimeError("Truncated debugger response")
            result += data
        return result

    def call(self, request):
        data = request.encode("ascii")
        self.sock.sendall(b"$"+data+b"#"+f"{sum(data)%256:02x}".encode())
        first = self.exact(1)
        if self.ack:
            if first != b"+": raise RuntimeError("Missing debugger acknowledgement")
            first = self.exact(1)
        if first != b"$": raise RuntimeError("Malformed debugger response framing")
        response = b""
        while True:
            byte = self.exact(1)
            if byte == b"#": break
            response += byte
            if len(response) > 40000: raise RuntimeError("Oversized debugger response")
        checksum = self.exact(2)
        if not re.fullmatch(rb"[0-9a-fA-F]{2}", checksum) or int(checksum, 16) != sum(response)%256:
            raise RuntimeError("Debugger checksum mismatch")
        if self.ack: self.sock.sendall(b"+")
        result = response.decode("ascii")
        self.transcript.append(dict(request=request, response=result))
        return result

    def ok(self, request):
        result = self.call(request)
        if result != "OK": raise RuntimeError(f"Debugger rejected {request}: {result}")

    def bytes(self, request, count):
        response = self.call(request)
        if not re.fullmatch(r"[0-9a-fA-F]{"+str(count*2)+r"}", response):
            raise RuntimeError("Incomplete/nonhex debugger state")
        return bytes.fromhex(response)

    def registers(self):
        return list(struct.unpack("<33I", self.bytes("g", 33*4)))


def parse_trace(text, case):
    instructions = re.findall(r"^\[(\d+)\] \[M\]: 0x([0-9a-fA-F]+) \(0x([0-9a-fA-F]+)\) (.+)$", text, re.M)
    if len(instructions) != 1:
        raise RuntimeError(f"Expected one executed instruction, got {len(instructions)}")
    number, pc, word, assembly = instructions[0]
    if int(number) != 0 or int(pc,16) != case["pc"] or int(word,16) != case["word"]:
        raise RuntimeError("Upstream executed a different instruction/PC")
    csrs = {}
    for name, _, value in re.findall(r"^CSR (\w+) \(0x([0-9a-fA-F]+)\) <- 0x([0-9a-fA-F]+)$",text,re.M):
        csrs.setdefault(name,[]).append(int(value,16))
    exceptions = re.findall(r"^handling exc#(.+) at priv M \| tval=0x([0-9a-fA-F]+) \|.*$",text,re.M)
    if len(exceptions) > 1 or len(csrs.get("mcause",[])) != len(exceptions):
        raise RuntimeError("Ambiguous/missing upstream exception evidence")
    trap = None
    if exceptions:
        for name in ("mcause","mepc","mtval"):
            if len(csrs.get(name,[])) != 1: raise RuntimeError("Incomplete machine trap observation")
        if csrs["mepc"][0] != case["pc"] or csrs["mtval"][0] != int(exceptions[0][1],16):
            raise RuntimeError("Inconsistent upstream exception address evidence")
        cause = csrs["mcause"][0]
        if cause not in (0,2,3,4,5,6,7,11): raise RuntimeError("Unexpected upstream exception class")
        trap = dict(cause=cause, target=csrs["mtval"][0] if cause in (0,4,5,6,7) else None)
    if any(token in text for token in ("Error:", "FAILURE", "Cannot execute", "internal error")):
        raise RuntimeError("Upstream model failed")
    return dict(trap=trap, csr=csrs, assembly=assembly)


def sail_case(binary, config, case, directory):
    directory.mkdir()
    image = directory / "case.elf"
    image.write_bytes(elf(case))
    reservation = socket.socket()
    reservation.bind(("127.0.0.1",0))
    port = reservation.getsockname()[1]
    reservation.close()
    argv = [str(binary),"--config",str(config),"--trace-instr","--trace-exception","--trace-csr",
            "--trace-step","--gdb-server-port",str(port),str(image)]
    logpath = directory / "sail.log"
    start = time.monotonic()
    sock = None
    with logpath.open("w") as log:
        proc = subprocess.Popen(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        try:
            deadline = time.monotonic()+10
            while time.monotonic() < deadline:
                if proc.poll() is not None: raise RuntimeError(f"Sail exited before debugger connection: {logpath}")
                try:
                    sock = socket.create_connection(("127.0.0.1",port),timeout=.1)
                    break
                except OSError: time.sleep(.005)
            if sock is None: raise RuntimeError("Sail debugger startup timeout")
            rsp = RSP(sock)
            if rsp.call("?") != "S05": raise RuntimeError("Unexpected initial debugger stop")
            rsp.ok("QStartNoAckMode")
            rsp.ack = False
            for index,value in enumerate(case["registers"]):
                # Pinned upstream requests.cpp parses P values as numeric hex,
                # unlike target-byte-order g responses. Read back every value.
                rsp.ok(f"P{index:x}={value:08x}")
            before = rsp.registers()
            if before != case["registers"]+[case["pc"]]:
                raise RuntimeError(f"Upstream initial architectural state differs: {before} != {case['registers']+[case['pc']]}")
            if rsp.bytes("m10000,1000",4096) != bytes(case["ram"]) or rsp.bytes("m0,1000",4096) != rom_bytes(case):
                raise RuntimeError("Upstream initial bytes differ from supplied ELF")
            if rsp.call("s") != "S05": raise RuntimeError("Unexpected debugger single-step result")
            after = rsp.registers()
            ram = list(rsp.bytes("m10000,1000",4096))
            if rsp.bytes("m0,1000",4096) != rom_bytes(case):
                raise RuntimeError("Upstream changed read-only program bytes")
            rsp.ok("D")
            sock.close();sock=None
            exit_code = proc.wait(timeout=5)
            if exit_code != 0: raise RuntimeError(f"Upstream process failed: {exit_code}")
        finally:
            if 'rsp' in locals(): write_json(directory/"rsp.json",rsp.transcript)
            if sock is not None: sock.close()
            if proc.poll() is None:
                proc.terminate()
                proc.wait(timeout=5)
    details = parse_trace(logpath.read_text(),case)
    normalized_pc = case["pc"] if details["trap"] is not None else after[32]
    frame = dict(id=case["id"],word=case["word"],pc=normalized_pc,registers=after[:32],ram=ram,trap=details["trap"])
    write_json(directory/"rsp.json",rsp.transcript)
    write_json(directory/"observation.json",dict(**frame,upstream_pc=after[32],details=details))
    write_json(directory/"command.json",dict(argv=argv,exit_code=exit_code,seconds=time.monotonic()-start))
    return frame


def compare(local, reference):
    required = {"id","word","pc","registers","ram","trap"}
    if type(local) is not dict or type(reference) is not dict or not required <= local.keys() or set(reference) != required:
        raise RuntimeError("Incomplete architectural frame")
    for frame in (local,reference):
        if type(frame["id"]) is not int or frame["id"] < 0:
            raise RuntimeError("Malformed architectural case identifier")
        for name in ("word","pc"):
            if type(frame[name]) is not int or not 0 <= frame[name] < 2**32:
                raise RuntimeError("Malformed architectural " + name)
        trap = frame["trap"]
        if trap is not None:
            if type(trap) is not dict or set(trap) != {"cause","target"} or \
                    type(trap["cause"]) is not int or trap["cause"] not in (0,2,3,4,5,6,7,11):
                raise RuntimeError("Malformed architectural trap")
            if trap["cause"] in (0,4,5,6,7):
                if type(trap["target"]) is not int or not 0 <= trap["target"] < 2**32:
                    raise RuntimeError("Malformed architectural trap address")
            elif trap["target"] is not None:
                raise RuntimeError("Unexpected architectural trap address")
        for name,count,limit in (("registers",32,2**32),("ram",4096,256)):
            if not isinstance(frame[name],list) or len(frame[name]) != count or any(type(v) is not int or not 0 <= v < limit for v in frame[name]):
                raise RuntimeError("Malformed complete architectural state")
    for key in sorted(required):
        if local[key] != reference[key]:
            if key in ("registers","ram"):
                index = next(i for i,(x,y) in enumerate(zip(local[key],reference[key])) if x!=y)
                raise AssertionError(f"{key}[{index}]: local={local[key][index]}, upstream={reference[key][index]}")
            raise AssertionError(f"{key}: local={local[key]}, upstream={reference[key]}")


def mutation_controls(binary, config, cases, local, directory):
    controls=[]
    selectors=[("wrong_lui_immediate",lambda c:c["kind"]=="lui" and ((c["word"]>>7)&31)!=0,
                lambda c:c["word"]^4096),
               ("store_word_instead_of_byte",lambda c:c["kind"]=="sb" and c["feature"]=="boundaries_overlap_x0",
                lambda c:c["word"]|(2<<12)),
               ("drop_faulting_x0_load",lambda c:c["kind"]=="lw" and c["feature"]=="data_fault_priority_x0" and c["registers"][1]==0x11000,
                lambda c:0x13)]
    for name,select,mutate in selectors:
        index=next(k for k,c in enumerate(cases) if select(c))
        case=copy.deepcopy(cases[index]);case["word"]=mutate(case)
        observed=sail_case(binary,config,case,directory/name)
        # The raw instruction mismatch is intentional and independently checked
        # against the mutated ELF. Require a further architectural value mismatch.
        observed["word"]=local[index]["word"]
        try: compare(local[index],observed)
        except AssertionError as failure:
            controls.append(dict(name=name,case_id=case["id"],original_word=cases[index]["word"],
                                 changed_word=case["word"],semantic_witness=str(failure)))
        else: raise RuntimeError(f"Undetected actual ELF mutation {name}")
    return controls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag",required=True)
    parser.add_argument("--fetch",action="store_true")
    parser.add_argument("--limit",type=int,help="Smoke only: receipt explicitly records incomplete coverage")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-zA-Z0-9_-]+",args.tag): raise RuntimeError("Unsafe evidence tag")
    if args.limit is not None and args.limit < 1: raise RuntimeError("Positive smoke limit required")
    directory = ROOT / "build/isa-reference" / args.tag
    directory.mkdir(parents=True,exist_ok=False)
    sources = source_hashes()
    records = []
    report = dict(status="running",sources=sources,commands=records,exclusions=EXCLUSIONS)
    try:
        pin,binary = dependencies(args.fetch)
        write_json(directory/"pin.json",pin)
        report["upstream_pin"] = pin
        report["upstream_binary"] = dict(path=str(binary),sha256=sha(binary))
        report["host"] = dict(system=platform.platform(),machine=platform.machine(),python=sys.version)
        report["build_info"] = command([binary,"--build-info"],directory,records)
        report["native_linkage"] = command(["/usr/bin/otool","-L",binary],directory,records)
        report["runtime_boundary"] = "Official release binary; libc++/libSystem provided by macOS dyld cache. Host identity recorded, OS image not qualified."
        template = command([binary,"--rv32","--print-default-config"],directory,records)
        (directory/"default-rv32.json").write_text(template)
        config = directory/"config.json"
        write_json(config,configuration(template))
        command([binary,"--config",config,"--validate-config"],directory,records)
        isa = command([binary,"--config",config,"--print-isa-string"],directory,records).strip()
        if isa != "rv32i_zvl32b_zvl64b_zvl128b_zvl256b": raise RuntimeError(f"Unexpected pinned model ISA: {isa}")
        report["sail_isa_string"] = isa
        report["vector_marker_note"] = "Sail reports fixed VLEN markers even with vector support_level Disabled and all extension supported flags false; no vector execution is accepted/tested."
        command(["lake","build","Pinwheel.Hardware.Processor.RV32I.Semantics","Pinwheel.Hardware.Processor.AddressMap"],directory,records)
        lean = Path(command(["lake","env","which","lean"],directory,records).strip()).resolve()
        lake = Path(command(["lake","env","which","lake"],directory,records).strip()).resolve()
        toolpaths={binary,lean,lake,Path(shutil.which("lake")).resolve(),Path(sys.executable).resolve(),Path("/usr/bin/otool")}
        toolpaths.update((lean.parent.parent/"lib/lean").glob("*.dylib"))
        report["tools"] = {str(p):sha(p) for p in sorted(toolpaths)}
        report["lean_version"] = command([lean,"--version"],directory,records).strip()
        command([sys.executable,ROOT/"test/isa_reference_test.py"],directory,records)
        # Record the compiled project inputs as well as their transitive sources.
        build_inputs={}
        for path in source_paths():
            if path.suffix==".lean" and "Pinwheel" in path.parts:
                base=ROOT/".lake/build/lib/lean"/path.relative_to(ROOT).with_suffix("")
                for extension in (".olean",".olean.private",".olean.server",".ir"):
                    artifact=Path(str(base)+extension)
                    if artifact.exists(): build_inputs[str(artifact.relative_to(ROOT))]=sha(artifact)
        report["project_build_inputs"]=build_inputs
        report["direct_lean_dependencies"]=command(["lake","env","lean","--deps",ADAPTER],directory,records).splitlines()
        # Standard library/imported interpreter inputs are release-pinned and hashed.
        report["lean_distribution_inputs"]={str(p):sha(p) for p in sorted((lean.parent.parent/"lib/lean").rglob("*"))
            if p.is_file() and (p.name.endswith((".olean",".olean.private",".olean.server",".ir")))}
        cases = campaign()
        if args.limit is not None: cases=cases[:args.limit]
        stimulus = directory/"cases.jsonl"
        stimulus.write_text("".join(json.dumps(c,separators=(",",":"))+"\n" for c in cases))
        localpath=directory/"local.jsonl"
        command(["lake","env","lean","-DwarningAsError=true","--run",ADAPTER,stimulus,localpath],directory,records)
        local=[json.loads(line) for line in localpath.read_text().splitlines()]
        if len(local)!=len(cases): raise RuntimeError("Incomplete local trace")
        reference=[]
        for case,frame in zip(cases,local):
            if frame["id"]!=case["id"] or frame["word"]!=case["word"]: raise RuntimeError("Local trace reordered or changed raw instruction")
            result=sail_case(binary,config,case,directory/f"case-{case['id']:04d}")
            compare(frame,result)
            reference.append(result)
            if len(reference)%40==0: print(f"Sail differential: {len(reference)}/{len(cases)} cases passed",flush=True)
        (directory/"reference.jsonl").write_text("".join(json.dumps(r,separators=(",",":"))+"\n" for r in reference))
        report["cases"]=len(cases)
        report["kind_counts"]={kind:sum(c["kind"]==kind for c in cases) for kind in KINDS}
        report["feature_counts"]={key:sum(c["feature"]==key for c in cases) for key in sorted({c["feature"] for c in cases})}
        report["full_matrix"] = args.limit is None
        if args.limit is None and any(v==0 for v in report["kind_counts"].values()): raise RuntimeError("Missing base instruction kind")
        if args.limit is None:
            report["actual_elf_mutations"]=mutation_controls(binary,config,cases,local,directory)
        report["comparison"]="Every integer register, normalized architectural PC/trap cause+address, every RAM byte and unchanged ROM; upstream instruction word/PC/initial state independently checked."
        report["eei_adapter"]="ROM [0,4096), RAM [65536,69632), little endian, pre-translation fatal alignment priority; Sail machine traps normalize to terminal outcomes at mepc. FENCE acknowledged serially; MMIO excluded explicitly."
        if source_hashes()!=sources: raise RuntimeError("Sources changed during campaign")
        for path,digest in report["tools"].items():
            if sha(path)!=digest: raise RuntimeError("Tool changed during campaign")
        for path,digest in report["project_build_inputs"].items():
            if sha(ROOT/path)!=digest: raise RuntimeError("Project compiled input changed during campaign")
        for path,digest in report["lean_distribution_inputs"].items():
            if sha(path)!=digest: raise RuntimeError("Lean distribution input changed during campaign")
        dependencies(False)
        report["status"]="passed"
    except Exception as error:
        report["status"]="failed"
        report["error"]=f"{type(error).__name__}: {error}"
        raise
    finally:
        report["artifacts"]={str(p.relative_to(directory)):sha(p) for p in sorted(directory.rglob("*")) if p.is_file() and p.name!="report.json"}
        write_json(directory/"report.json",report)
    print(f"PASS {report['cases']} pinned Sail comparisons; report {directory/'report.json'}")


if __name__ == "__main__":
    main()
