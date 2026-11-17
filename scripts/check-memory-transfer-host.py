#!/usr/bin/env python3
"""Validate host loading, transfer, abort and readback against an array oracle."""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import time

import transfer_host_oracle as reference
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("host_controller_checks", ROOT / "scripts/check-memory-transfer.py")
controller = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(controller)
rr, memory = controller.rr, controller.memory
MATRIX = [(1, 1, 1), (2, 8, 8), (3, 8, 4), (2, 4, 17)]


def source_hashes():
    result = controller.source_hashes()
    paths = {ROOT / p for p in ("scripts/check-memory-transfer-host.py", "scripts/transfer_host_oracle.py",
                               "test/test_transfer_host_validation.py")}
    pending = [ROOT / p for p in ("test/MemoryTransferHostEmit.lean", "test/MemoryTransferHostReplay.lean",
        "test/MemoryTransferHostCircuit.lean", "Pinwheel/Hardware/Memory/TransferHostCircuitProofs.lean")]
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
    result.update({str(path.relative_to(ROOT)): sha(path) for path in paths})
    return dict(sorted(result.items()))


def widths(a, wi, wo):
    return ([1, 1, a, a, a+1, 1, 1, a, wi, 1, 1, 1, a, wo, 1],
            [1, 1, 1, 1, 1, 1, wi, 1, 1, wo],
            [2, a, a, a+1, a+1, 1, 1] + [wi]*((1 << a)+1) + [1] + [wo]*((1 << a)+1) + [1])


def validate_descriptor(data, a, wi, wo):
    for key, value in (("schema", 1), ("address_width", a), ("input_width", wi),
                       ("output_width", wo), ("clock", "clk"), ("transform", "invert_resize")):
        if data.get(key) != value:
            raise ValueError("Wrong host descriptor field: " + key)
    if not rr.IDENTIFIER.fullmatch(data.get("module", "")):
        raise ValueError("Invalid host module name")
    names = {"clk"}
    for group, expected in zip(("inputs", "outputs", "registers"), widths(a, wi, wo), strict=True):
        if not isinstance(data.get(group), list) or len(data[group]) != len(expected):
            raise ValueError("Incomplete typed host " + group)
        for p, width in zip(data[group], expected, strict=True):
            name = p.get("name")
            if not isinstance(name, str) or not rr.IDENTIFIER.fullmatch(name) or name in names or \
                    type(p.get("width")) is not int or p["width"] != width:
                raise ValueError("Invalid typed host signal")
            if group == "registers" and p.get("reference") != name:
                raise ValueError("Register reference must name its declared register")
            names.add(name)
    for group, roles in (("inputs", reference.INPUT_ROLES), ("outputs", reference.OUTPUT_ROLES)):
        for p, role in zip(data[group], roles, strict=True):
            if data["roles"].get(role) != p["name"]:
                raise ValueError("Wrong host port role/order: " + role)
    roles, depth = data["register_roles"], 1 << a
    expected_names = [roles[k] for k in reference.CONTROL_ROLES]
    for prefix in ("source", "destination"):
        words = roles[prefix+"_words"]
        if not isinstance(words, list) or len(words) != depth:
            raise ValueError("Incomplete memory word enumeration")
        expected_names += words + [roles[prefix+"_q"], roles[prefix+"_pending"]]
    if expected_names != [p["name"] for p in data["registers"]]:
        raise ValueError("Register roles do not enumerate every word/Q/pending exactly once in typed order")


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
    for cycle, row in enumerate(rows):
        for role, p in zip(reference.INPUT_ROLES, data["inputs"], strict=True):
            lines.append(f"{p['name']} = {p['width']}'h{row[role]:x};")
        lines += ["#1;", f'$display("PRE,{cycle}{",%0d" * len(data["outputs"])}", {outputs});', "clk = 1; #1;",
                  f'$display("POST,{cycle}{",%0d" * len(data["outputs"])}", {outputs});']
        if registers:
            lines.append(f'$display("REG,{cycle}{",%0d" * len(startup)}", {regargs});')
        lines += ["clk = 0; #1;"]
    return "\n".join(lines + ['$display("MEMORY_DONE"); $finish;', "end", "endmodule", ""])


def mutations(text, data):
    header = text.index(");")+2
    for name, role, replacement in (("disable-start", "start_valid", "1'b0"),
                                    ("ignore-host-stall", "source_resp_ready", "1'b1")):
        changed, count = re.subn(r"\b" + re.escape(data["roles"][role]) + r"\b", replacement, text[header:])
        if count == 0:
            raise ValueError("No signal use for " + name)
        yield name, text[:header]+changed
    output = data["roles"]["destination_resp_data"]
    valid = data["roles"]["destination_resp_valid"]
    changed, count = re.subn(r"(\bassign\s+" + re.escape(output) + r"\s*=\s*)([^;]+);",
        lambda m: m[1]+valid+" ? ~("+m[2].strip()+") : ("+m[2].strip()+");", text)
    if count != 1:
        raise ValueError("Expected one host response data assignment")
    yield "invert-active-readback", changed
    for name, reg, expression in (
            ("erase-progress", data["register_roles"]["index"], lambda value: "'0"),
            ("clear-word-on-reset", data["register_roles"]["destination_words"][0],
             lambda value: data["roles"]["reset"]+" ? '0 : ("+value+")"),
            ("host-write-while-busy", data["register_roles"]["source_words"][0],
             lambda value: data["roles"]["busy"]+" && "+data["roles"]["source_req_valid"]+" && "+
             data["roles"]["source_req_write"]+" ? "+data["roles"]["source_req_data"]+" : ("+value+")")):
        pattern = r"(\b"+re.escape(reg)+r"\s*<=\s*)([^;]+);"
        changed, count = re.subn(pattern, lambda m: m[1]+expression(m[2].strip())+";", text)
        if count != 1 or changed == text:
            raise ValueError("Expected one register update for " + name)
        yield name, changed


def configuration(run, tools, out, a, wi, wo):
    directory = out / f"host-{a}-{wi}-{wo}"
    directory.mkdir()
    label = directory.name
    run(controller.lean_command(out, "--run", "test/MemoryTransferHostEmit.lean", a, wi, wo, directory), label+"-emit")
    data = json.loads((directory / "interface.json").read_text())
    validate_descriptor(data, a, wi, wo)
    startup, rows, coverage = reference.stimulus(a, wi, wo)
    frames, events, ledger = reference.oracle(a, wi, wo, startup, rows)
    for filename, value in (("startup.json", startup), ("expected.json", frames),
                            ("events.json", events), ("ledger.json", ledger)):
        (directory / filename).write_text(json.dumps(value, indent=2)+"\n")
    (directory / "stimulus.jsonl").write_text("".join(json.dumps(row)+"\n" for row in rows))
    run(controller.lean_command(out, "--run", "test/MemoryTransferHostReplay.lean", a, wi, wo,
        directory / "stimulus.jsonl", directory / "startup.json", directory / "lean.jsonl"), label+"-lean")
    actual = [json.loads(line) for line in (directory / "lean.jsonl").read_text().splitlines()]
    if actual != frames:
        mismatch = next(((x, y) for x, y in zip(frames, actual) if x != y), None)
        raise AssertionError(f"Lean host circuit differs from integer oracle: {mismatch}")
    rtl = directory / "transfer-host.sv"
    rtl.write_text(run([tools["circt"], directory / "transfer-host.mlir", "--canonicalize", "--lower-seq-to-sv",
        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label+"-lower"))

    def simulate(source, stage, registers, *, traffic=rows, expectations=frames, negative=False):
        tb, executable = directory / (stage+"-tb.sv"), directory / (stage+".vvp")
        tb.write_text(testbench(data, startup, traffic, registers))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], label+"-"+stage+"-compile")
        trace = run([tools["vvp"], executable], label+"-"+stage+"-simulate")
        (directory / (stage+"-trace.txt")).write_text(trace)
        want = controller.expected(expectations, registers)
        try:
            memory.check_trace(trace, want)
        except AssertionError as error:
            if negative:
                controller.concrete_mismatch(trace, want)
                return str(error)
            raise
        if negative:
            raise AssertionError("Accepted actual host RTL mutation: " + stage)

    simulate(rtl, "rtl", True)
    recovery_rows = [dict.fromkeys(reference.INPUT_ROLES, 0), dict.fromkeys(reference.INPUT_ROLES, 0)]
    recovery_frames, _, _ = reference.oracle(a, wi, wo, startup, recovery_rows)
    (directory / "phase3-expected.json").write_text(json.dumps(recovery_frames, indent=2)+"\n")
    simulate(rtl, "phase3", True, traffic=recovery_rows, expectations=recovery_frames)
    netlist, netjson, script = directory / "synth.v", directory / "synth.json", directory / "synth.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {data['module']}\n"
        f"synth -top {data['module']}\ncheck -assert\nwrite_json {rr.yosys_quote(netjson)}\n"
        f"write_verilog -noattr {rr.yosys_quote(netlist)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], label+"-synthesize")
    simulate(netlist, "synth", False)
    controls = []
    for name, changed in mutations(rtl.read_text(), data):
        source = directory / (name+".sv")
        source.write_text(changed)
        controls.append({"mutation": name, "rejection": simulate(source, name, True, negative=True)})
    module = json.loads(netjson.read_text())["modules"][data["module"]]
    cells = Counter(cell["type"] for cell in module["cells"].values())
    return {"configuration": [a, wi, wo], "edges_per_form": len(rows), "phase3_edges": 2,
            "typed_registers": len(data["registers"]), "typed_outputs": len(data["outputs"]),
            "coverage": coverage, "host_ledger": ledger["host_reads"], "jobs": len(ledger["jobs"]),
            "generic_cells": sum(cells.values()), "cell_types": dict(cells),
            "rtl_mutations_rejected": controls, "artifact_certificate": "not_run"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer-host", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Independent host/memory/job-snapshot oracle versus Lean and emitted RTL at all registers and "
                    "pre/post outputs; synthesized external replay after reset and full host memory loading. "
                    "Reset does not initialize words/Q. Kernel artifact correspondence and physical timing are separate gates."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.TransferHostCircuitProofs", "Pinwheel.Hardware.Emit"], "build", timeout=900)
        controller.prepare_support(run, out)
        run(["python3", "test/test_transfer_host_validation.py"], "oracle-and-descriptor-tests")
        structural = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryTransferHostCircuit.lean"], "structural-tests")
        if "standard axioms only" not in structural:
            raise AssertionError("Missing host structural proof axiom audit")
        for a, wi, wo in MATRIX:
            report["configurations"].append(configuration(run, tools, out, a, wi, wo))
        if source_hashes() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during validation")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic()-started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
