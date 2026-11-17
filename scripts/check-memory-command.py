#!/usr/bin/env python3
"""Replay command RAM against an independent array oracle before/after synthesis.

Emitted RTL starts from explicit arbitrary words/Q and exposes every state word.
Synthesized RTL starts uninitialized; full writes and one read establish its
observable state before comparison. This is simulation, not artifact proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import random
import re
import time

from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("memory_tools", ROOT / "scripts/check-round-robin-circuit.py")
rr = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(rr)
CONFIGS = [(1, 1), (1, 8), (2, 8), (3, 17)]


def sources():
    pending = [ROOT / path for path in ("test/MemoryCommandEmit.lean", "test/MemoryCommandReplay.lean",
               "test/MemoryCommandFlops.lean", "test/MemoryCommandContracts.lean")]
    found = set()
    while pending:
        path = pending.pop()
        if path in found:
            continue
        found.add(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for module in match[1].split("--", 1)[0].split():
                    if module == "Pinwheel" or module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    found.update(ROOT / name for name in ("scripts/check-memory-command.py",
        "scripts/check-round-robin-circuit.py", "scripts/validation_run.py", "scripts/process_group.py",
        "lakefile.toml", "lean-toolchain", "lake-manifest.json", "tools/hardware-toolchain.json"))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(found)}


def validate_descriptor(data, a, w):
    if any(data.get(key) != value for key, value in
           (("schema", 1), ("address_width", a), ("data_width", w), ("depth", 1 << a), ("clock", "clk"))):
        raise ValueError("Wrong command memory configuration")
    if not rr.IDENTIFIER.fullmatch(data.get("module", "")):
        raise ValueError("Invalid module name")
    all_names = {"clk"}
    for kind in ("inputs", "registers", "outputs"):
        for port in data[kind]:
            if not rr.IDENTIFIER.fullmatch(port["name"]) or port["name"] in all_names:
                raise ValueError("Duplicate or invalid signal name")
            if type(port["width"]) is not int or port["width"] <= 0:
                raise ValueError("Invalid signal width")
            all_names.add(port["name"])
    roles, regs = data["roles"], data["register_roles"]
    expected = {roles["enable"]: 1, roles["write"]: 1, roles["address"]: a, roles["data"]: w}
    if len(expected) != 4 or len(data["inputs"]) != 4 or {p["name"]: p["width"] for p in data["inputs"]} != expected:
        raise ValueError("Incomplete memory input role map")
    if data["outputs"] != [{"name": roles["q"], "width": w}]:
        raise ValueError("Wrong output role map")
    register_order = regs["words"] + [regs["q"]]
    if len(regs["words"]) != 1 << a or len(set(register_order)) != (1 << a) + 1:
        raise ValueError("Incomplete register role map")
    if register_order != [p["name"] for p in data["registers"]] or any(
            p["reference"] != p["name"] or p["width"] != w for p in data["registers"]):
        raise ValueError("Changed typed memory state order")


def stimulus(a, w):
    rng = random.Random(0x4D454D + a * 100 + w)
    depth, limit = 1 << a, 1 << w
    startup = [rng.randrange(limit) for _ in range(depth + 1)]
    rows = []

    def add(enable, write, address, data=0):
        rows.append(dict(enable=enable, write=write, address=address, data=data))

    # Establish all state without assuming a hardware power-up value. Emitted
    # RTL is additionally checked throughout this prefix against arbitrary Q.
    for address in range(depth):
        add(True, True, address, startup[address])
    add(True, False, 0)
    for address in range(depth):
        add(False, True, address, limit - 1)
        add(True, False, address, rng.randrange(limit))
        add(False, False, address, rng.randrange(limit))
        add(True, True, address, (startup[address] + 1) % limit)
        add(True, False, address)
        add(True, False, (address + 1) % depth)
    for _ in range(320):
        add(bool(rng.randrange(2)), bool(rng.randrange(2)), rng.randrange(depth), rng.randrange(limit))
    for address in range(depth):
        add(True, False, address)
    return startup, rows


def oracle(startup, rows):
    words, q, frames = startup[:-1].copy(), startup[-1], []
    for cycle, row in enumerate(rows):
        before = q
        if row["enable"]:
            if row["write"]:
                words[row["address"]] = row["data"]
            else:
                q = words[row["address"]]
        frames.append(dict(cycle=cycle, input=row, pre=before, post=q, registers=words.copy() + [q]))
    return frames


def observations(frames, registers, depth):
    result = []
    for frame in frames:
        cycle = frame["cycle"]
        if registers or cycle > depth:
            result.append(("PRE", cycle, frame["pre"]))
        if registers or cycle >= depth:
            result.append(("POST", cycle, frame["post"]))
        if registers:
            result.append(("REG", cycle, *frame["registers"]))
    return result


def testbench(data, startup, rows, registers):
    declarations, connections = ["reg clk = 0;"], [".clk(clk)"]
    for kind, direction in (("inputs", "reg"), ("outputs", "wire")):
        for p in data[kind]:
            declarations.append(f"{direction} [{p['width']-1}:0] {p['name']}{' = 0' if direction == 'reg' else ''};")
            connections.append(f".{p['name']}({p['name']})")
    body = []
    if registers:
        for p, value in zip(data["registers"], startup, strict=True):
            body.append(f"force dut.{p['reference']} = {p['width']}'h{value:x};")
        body.append("#1;")
        body.extend(f"release dut.{p['reference']};" for p in data["registers"])
    roles, depth = data["roles"], data["depth"]
    widths = {p["name"]: p["width"] for p in data["inputs"]}
    for cycle, row in enumerate(rows):
        for role in ("enable", "write", "address", "data"):
            name = roles[role]
            body.append(f"{name} = {widths[name]}'h{int(row[role]):x};")
        body.append("#1;")
        if registers or cycle > depth:
            body.append(f'$display("PRE,{cycle},%0d", {roles["q"]});')
        body.append("clk = 1; #1;")
        if registers or cycle >= depth:
            body.append(f'$display("POST,{cycle},%0d", {roles["q"]});')
        if registers:
            args = ", ".join("dut." + p["reference"] for p in data["registers"])
            body.append(f'$display("REG,{cycle}{",%0d" * len(startup)}", {args});')
        body.append("clk = 0; #1;")
    body.append('$display("MEMORY_DONE"); $finish;')
    return "\n".join(["`timescale 1ns/1ps", "module tb;", *declarations,
        f"{data['module']} dut({', '.join(connections)});", "initial begin", *body, "end", "endmodule", ""])


def check_trace(text, expected):
    rows, done = [], 0
    for line in text.splitlines():
        if line == "MEMORY_DONE":
            done += 1
        elif line.startswith(("PRE,", "POST,", "REG,")):
            fields = line.split(",")
            if done or any(not x.isdecimal() for x in fields[1:]):
                raise AssertionError("Unknown or out-of-order memory observation")
            rows.append((fields[0], *map(int, fields[1:])))
        elif line.strip() and not re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)", line):
            raise AssertionError(f"Unexpected simulation output: {line}")
    if done != 1 or rows != expected:
        mismatch = next(((a, b) for a, b in zip(expected, rows) if a != b), None)
        raise AssertionError(f"Memory trace mismatch: {mismatch}; rows {len(rows)}/{len(expected)}, completions {done}")


def mutations(text, data):
    enable, write = data["roles"]["enable"], data["roles"]["write"]
    q = data["register_roles"]["q"]
    replacements = {
        "ignore-enable": (enable + " &", "1'b1 &"),
        "read-on-write": (enable + " & ~" + write, enable),
        "clear-held-q": (": " + q + ";", ": '0;")}
    for name, (old, new) in replacements.items():
        if old not in text:
            raise ValueError(f"Mutation no longer matches emitted RTL: {name}")
        yield name, text.replace(old, new)


def configuration(run, tools, out, a, w):
    directory = out / f"memory-{a}-{w}"
    directory.mkdir()
    label = directory.name
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryCommandEmit.lean", a, w, directory], label + "-emit")
    data = json.loads((directory / "interface.json").read_text())
    validate_descriptor(data, a, w)
    startup, rows = stimulus(a, w)
    frames = oracle(startup, rows)
    for filename, value in (("startup.json", startup), ("expected.json", frames)):
        (directory / filename).write_text(json.dumps(value, indent=2) + "\n")
    (directory / "stimulus.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryCommandReplay.lean", a, w,
         directory / "stimulus.jsonl", directory / "startup.json", directory / "lean.jsonl"], label + "-lean")
    actual = [json.loads(line) for line in (directory / "lean.jsonl").read_text().splitlines()]
    if actual != frames:
        raise AssertionError("Lean structural memory trace differs from independent oracle")
    rtl = directory / "memory.sv"
    rtl.write_text(run([tools["circt"], directory / "memory.mlir", "--canonicalize", "--lower-seq-to-sv",
        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label + "-lower"))

    def simulate(source, stage, registers, negative=False):
        tb, executable = directory / (stage + "-tb.sv"), directory / (stage + ".vvp")
        tb.write_text(testbench(data, startup, rows, registers))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], label + "-" + stage + "-compile")
        trace = run([tools["vvp"], executable], label + "-" + stage + "-simulate")
        (directory / (stage + "-trace.txt")).write_text(trace)
        try:
            check_trace(trace, observations(frames, registers, data["depth"]))
        except AssertionError as error:
            if negative:
                return str(error)
            raise
        if negative:
            raise AssertionError("Mutated RTL was accepted: " + stage)

    simulate(rtl, "rtl", True)
    netlist, netjson = directory / "synth.v", directory / "synth.json"
    script = directory / "synth.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
        f"hierarchy -check -top {data['module']}\nsynth -top {data['module']}\ncheck -assert\n"
        f"write_verilog -noattr {rr.yosys_quote(netlist)}\nwrite_json {rr.yosys_quote(netjson)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], label + "-synth")
    simulate(netlist, "synth", False)
    controls = []
    for name, changed in mutations(rtl.read_text(), data):
        path = directory / (name + ".sv")
        path.write_text(changed)
        controls.append({"mutation": name, "rejection": simulate(path, name, True, negative=True)})
    module = json.loads(netjson.read_text())["modules"][data["module"]]
    cells = Counter(cell["type"] for cell in module["cells"].values())
    return {"configuration": [a, w], "edges": len(rows), "arbitrary_startup": startup,
        "synthesized_checked_edges": len(rows) - data["depth"], "generic_cells": sum(cells.values()),
        "cell_types": dict(cells), "rtl_mutations_rejected": controls,
        "artifact_certificate": "not_run"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-command", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Independent oracle/Lean/emitted RTL replay checks every register and Q; synthesized Q "
        "is checked after full writes and one read establish state. No power-up or reset assumption, "
        "artifact certificate, macro equivalence, or physical timing claim."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.CommandFlopsProofs", "Pinwheel.Hardware.Emit"], "build")
        run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryCommandFlops.lean"], "independent-lean-tests")
        run(["lake", "env", "lean", "-DwarningAsError=true", "test/MemoryCommandContracts.lean"], "axiom-audit")
        for a, w in CONFIGS:
            report["configurations"].append(configuration(run, tools, out, a, w))
        if report["source_sha256"] != sources() or report["tool_sha256"] != rr.tool_hashes(paths):
            raise RuntimeError("Owning sources/tools changed during validation")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
