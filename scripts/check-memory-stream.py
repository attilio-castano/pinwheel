#!/usr/bin/env python3
"""Check a backpressured command RAM against independent state/event accounting."""
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
SPEC = importlib.util.spec_from_file_location("memory_command", ROOT / "scripts/check-memory-command.py")
command = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(command)
rr = command.rr


def sources():
    result = command.sources()
    pending = [ROOT / path for path in ("test/MemoryStreamEmit.lean", "test/MemoryStreamReplay.lean",
        "test/MemoryStreamModel.lean", "test/MemoryStreamFlops.lean", "test/MemoryStreamContracts.lean")]
    while pending:
        path = pending.pop()
        key = str(path.relative_to(ROOT))
        if key in result:
            continue
        result[key] = sha(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for module in match[1].split("--", 1)[0].split():
                    if module == "Pinwheel" or module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    result["scripts/check-memory-stream.py"] = sha(Path(__file__))
    return dict(sorted(result.items()))


def validate_descriptor(data, a, w):
    if any(data.get(key) != value for key, value in (("schema", 1), ("address_width", a),
            ("data_width", w), ("depth", 1 << a), ("clock", "clk"))):
        raise ValueError("Wrong stream memory configuration")
    if not rr.IDENTIFIER.fullmatch(data.get("module", "")):
        raise ValueError("Invalid module")
    roles, regs = data["roles"], data["register_roles"]
    names = {"clk"}
    for group in ("inputs", "outputs", "registers"):
        for port in data[group]:
            if not rr.IDENTIFIER.fullmatch(port["name"]) or port["name"] in names or \
                    type(port["width"]) is not int or port["width"] <= 0:
                raise ValueError("Invalid or duplicate signal")
            names.add(port["name"])
    for group, ordered in (("inputs", [("reset", 1), ("valid", 1), ("write", 1), ("address", a), ("data", w), ("ready", 1)]),
                           ("outputs", [("in_ready", 1), ("out_valid", 1), ("out_data", w)])):
        if data[group] != [{"name": roles[role], "width": width} for role, width in ordered]:
            raise ValueError("Changed typed external role order")
    expected = regs["words"] + [regs["q"], regs["pending"]]
    if len(regs["words"]) != 1 << a or len(set(expected)) != (1 << a) + 2:
        raise ValueError("Incomplete stream memory state")
    if [p["name"] for p in data["registers"]] != expected or any(
            p["reference"] != p["name"] or p["width"] != (1 if p["name"] == regs["pending"] else w)
            for p in data["registers"]):
        raise ValueError("Changed typed register binding")


def stimulus(a, w):
    rng = random.Random(0x535452 + 100 * a + w)
    depth, limit = 1 << a, 1 << w
    startup = [rng.randrange(limit) for _ in range(depth + 1)] + [1]
    startup[0] = limit - 1
    rows = []

    def add(reset=False, valid=False, write=False, address=0, data=0, ready=False):
        rows.append(dict(reset=reset, valid=valid, write=write, address=address, data=data, ready=ready))

    # Mask the arbitrary pending bit before use; reset must not clear words/Q.
    add(reset=True, valid=True, write=True, data=0, ready=True)
    for address in range(depth):
        add(valid=True, write=True, address=address, data=startup[address], ready=True)
    add(valid=True, address=0)
    for address in range(depth):
        add(valid=True, write=True, address=address, data=0)
        add(valid=True, address=(address + 1) % depth)
        add(valid=True, address=address, ready=True)
        add(valid=True, write=True, address=address, data=(startup[address] + 1) % limit, ready=True)
        add(valid=True, address=address)
        add(reset=True, valid=True, write=True, address=address, data=0, ready=True)
        add(valid=True, address=address, ready=True)
        add(ready=True)
    for cycle in range(360):
        add(reset=cycle % 59 == 17, valid=bool(rng.randrange(2)), write=bool(rng.randrange(2)),
            address=rng.randrange(depth), data=rng.randrange(limit), ready=bool(rng.randrange(2)))
    add(ready=True)
    for address in range(depth):
        add(valid=True, address=address, ready=True)
    add(ready=True)
    return startup, rows


def oracle(startup, rows):
    words, q, pending = startup[:-2].copy(), startup[-2], bool(startup[-1])
    reads, responses = ([q] if pending else []), []
    frames, events = [], []

    def output(row):
        if row["reset"]:
            return [0, 0, 0]
        return [int(not pending or row["ready"]), int(pending), q if pending else 0]

    for cycle, row in enumerate(rows):
        before = output(row)
        accepted, emitted = bool(before[0] and row["valid"]), bool(before[1] and row["ready"])
        sample = words[row["address"]] if accepted and not row["write"] else None
        delivery = q if emitted else None
        if row["reset"]:
            pending, reads, responses = False, [], []
        else:
            if emitted:
                responses.append(q)
            if before[0]:
                pending = bool(accepted and not row["write"])
            if accepted:
                if row["write"]:
                    words[row["address"]] = row["data"]
                else:
                    q = sample
                    reads.append(sample)
        if reads != responses + ([q] if pending else []):
            raise AssertionError("Independent read snapshot ledger lost order or ownership")
        frames.append(dict(cycle=cycle, input=row, pre=before, post=output(row),
                           registers=words.copy() + [q, int(pending)]))
        events.append(dict(cycle=cycle, accepted=accepted, emitted=emitted, read_snapshot=sample,
                           delivered=delivery, read_history=reads.copy(), response_history=responses.copy()))
    return frames, events


def testbench(data, startup, rows, registers):
    lines, connections = ["`timescale 1ns/1ps", "module tb;", "reg clk = 0;"], [".clk(clk)"]
    for group, kind in (("inputs", "reg"), ("outputs", "wire")):
        for p in data[group]:
            lines.append(f"{kind} [{p['width']-1}:0] {p['name']}{' = 0' if kind == 'reg' else ''};")
            connections.append(f".{p['name']}({p['name']})")
    lines += [f"{data['module']} dut({', '.join(connections)});", "initial begin"]
    if registers:
        lines += [f"force dut.{p['reference']} = {p['width']}'h{x:x};" for p, x in zip(data["registers"], startup, strict=True)]
        lines += ["#1;"] + [f"release dut.{p['reference']};" for p in data["registers"]]
    outputs = ", ".join(p["name"] for p in data["outputs"])
    regargs = ", ".join("dut." + p["reference"] for p in data["registers"])
    widths = {p["name"]: p["width"] for p in data["inputs"]}
    for cycle, row in enumerate(rows):
        for role in ("reset", "valid", "write", "address", "data", "ready"):
            name = data["roles"][role]
            lines.append(f"{name} = {widths[name]}'h{int(row[role]):x};")
        lines += ["#1;", f'$display("PRE,{cycle},%0d,%0d,%0d", {outputs});', "clk = 1; #1;",
                  f'$display("POST,{cycle},%0d,%0d,%0d", {outputs});']
        if registers:
            lines.append(f'$display("REG,{cycle}{",%0d" * len(startup)}", {regargs});')
        lines += ["clk = 0; #1;"]
    return "\n".join(lines + ['$display("MEMORY_DONE"); $finish;', "end", "endmodule", ""])


def expected_observations(frames, registers):
    result = []
    for frame in frames:
        result.extend((("PRE", frame["cycle"], *frame["pre"]), ("POST", frame["cycle"], *frame["post"])))
        if registers:
            result.append(("REG", frame["cycle"], *frame["registers"]))
    return result


def mutations(text, data):
    header = text.index(");") + 2
    tail, count = re.subn(r"\b" + re.escape(data["roles"]["ready"]) + r"\b", "1'b1", text[header:])
    if not count:
        raise ValueError("Cannot identify response-ready uses")
    yield "ignore-response-stall", text[:header] + tail
    for name, register, replacement in (
            ("drop-pending", data["register_roles"]["pending"], lambda m: m[1] + "1'b0;"),
            ("clear-word-on-reset", data["register_roles"]["words"][0],
             lambda m: m[1] + data["roles"]["reset"] + " ? '0 : (" + m[2].strip() + ");")):
        pattern = r"(\b" + re.escape(register) + r"\s*<=\s*)([^;]+);"
        changed, count = re.subn(pattern, replacement, text)
        if count != 1 or changed == text:
            raise ValueError("Mutation no longer identifies one state update")
        yield name, changed


def configuration(run, tools, out, a, w):
    directory = out / f"memory-{a}-{w}"
    directory.mkdir()
    label = directory.name
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryStreamEmit.lean", a, w, directory], label + "-emit")
    data = json.loads((directory / "interface.json").read_text())
    validate_descriptor(data, a, w)
    startup, rows = stimulus(a, w)
    frames, events = oracle(startup, rows)
    for filename, value in (("startup.json", startup), ("expected.json", frames), ("events.json", events)):
        (directory / filename).write_text(json.dumps(value, indent=2) + "\n")
    (directory / "stimulus.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryStreamReplay.lean", a, w,
        directory / "stimulus.jsonl", directory / "startup.json", directory / "lean.jsonl"], label + "-lean")
    actual = [json.loads(line) for line in (directory / "lean.jsonl").read_text().splitlines()]
    if actual != frames:
        raise AssertionError("Structural stream memory differs from independent oracle")
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
            command.check_trace(trace, expected_observations(frames, registers))
        except AssertionError as error:
            if negative:
                return str(error)
            raise
        if negative:
            raise AssertionError("Accepted actual stream-memory mutation: " + stage)

    simulate(rtl, "rtl", True)
    netlist, netjson, script = directory / "synth.v", directory / "synth.json", directory / "synth.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {data['module']}\n"
        f"synth -top {data['module']}\ncheck -assert\nwrite_verilog -noattr {rr.yosys_quote(netlist)}\n"
        f"write_json {rr.yosys_quote(netjson)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], label + "-synth")
    simulate(netlist, "synth", False)
    controls = []
    for name, changed in mutations(rtl.read_text(), data):
        source = directory / (name + ".sv")
        source.write_text(changed)
        controls.append(dict(mutation=name, rejection=simulate(source, name, True, negative=True)))
    module = json.loads(netjson.read_text())["modules"][data["module"]]
    cells = Counter(cell["type"] for cell in module["cells"].values())
    return {"configuration": [a, w], "edges": len(rows), "generic_cells": sum(cells.values()),
        "cell_types": dict(cells), "rtl_mutations_rejected": controls, "artifact_certificate": "not_run",
        "read_snapshots": sum(event["read_snapshot"] is not None for event in events),
        "delivered_responses": sum(event["emitted"] for event in events)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-stream", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Independent state/read-snapshot oracle, Lean, emitted RTL all-register replay, "
        "and synthesized external observations. Reset preserves memory/Q; synthesized words are established "
        "by full writes before reads. No power-up assumption, artifact certificate, or physical timing claim."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.StreamFlopsProofs", "Pinwheel.Hardware.Emit"], "build")
        for name in ("MemoryStreamModel", "MemoryStreamFlops"):
            run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/" + name + ".lean"], name)
        run(["lake", "env", "lean", "-DwarningAsError=true", "test/MemoryStreamContracts.lean"], "axiom-audit")
        for a, w in command.CONFIGS:
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
