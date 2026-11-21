#!/usr/bin/env python3
"""Replay the open transfer controller against an independent integer oracle."""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
import os
from pathlib import Path
import re
import time

import transfer_controller_oracle as reference
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("transfer_memory_checks", ROOT / "scripts/check-memory-command.py")
memory = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(memory)
rr = memory.rr
MATRIX = [(1, 1, 1), (2, 8, 8), (3, 8, 4), (2, 4, 17)]


def lean_command(out, *args):
    return ["lake", "env", "env",
            "LEAN_PATH=" + str(out / "support") + os.pathsep + str(ROOT / ".lake/build/lib/lean"),
            "lean", "-DwarningAsError=true", *args]


def prepare_support(run, out):
    target = out / "support/MemoryTransferSupport.olean"
    target.parent.mkdir(parents=True)
    run(lean_command(out, "-o", target, "test/MemoryTransferSupport.lean"), "test-map-build")


def source_hashes():
    paths = {ROOT / p for p in ("scripts/check-memory-transfer.py", "scripts/transfer_controller_oracle.py",
        "test/test_transfer_controller_validation.py",
        "scripts/check-memory-command.py", "scripts/check-round-robin-circuit.py", "scripts/validation_run.py",
        "scripts/process_group.py", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "tools/hardware-toolchain.json")}
    pending = [ROOT / p for p in ("test/MemoryTransferEmit.lean", "test/MemoryTransferReplay.lean", "test/MemoryTransferSupport.lean",
        "test/MemoryTransferCircuit.lean", "test/MemoryTransferContracts.lean",
        "Pinwheel/Hardware/Memory/TransferCircuitProofs.lean")]
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
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def widths(a, wi, wo):
    return [1, 1, a, a, a+1, 1, 1, wi, 1], [1, 1, 1, 1, 1, a, 1, 1, a, wo, 1], [2, a, a, a+1, a+1, 1, 1]


def validate_descriptor(data, a, wi, wo):
    for key, value in (("schema", 1), ("address_width", a), ("input_width", wi), ("output_width", wo),
                       ("clock", "clk"), ("transform", "invert_resize")):
        if data.get(key) != value:
            raise ValueError("Wrong transfer descriptor field: " + key)
    if not rr.IDENTIFIER.fullmatch(data.get("module", "")):
        raise ValueError("Invalid transfer module")
    names = {"clk"}
    for group, roles, group_widths in zip(("inputs", "outputs", "registers"),
            (reference.INPUT_ROLES, reference.OUTPUT_ROLES, reference.REGISTER_ROLES), widths(a, wi, wo), strict=True):
        role_map = data["register_roles" if group == "registers" else "roles"]
        if len(data[group]) != len(roles):
            raise ValueError("Incomplete transfer " + group)
        for port, role, width in zip(data[group], roles, group_widths, strict=True):
            name = port["name"]
            if not isinstance(name, str) or not rr.IDENTIFIER.fullmatch(name) or name in names or \
                    port["width"] != width or type(port["width"]) is not int or role_map.get(role) != name:
                raise ValueError("Invalid transfer typed binding: " + role)
            if group == "registers" and port.get("reference") != name:
                raise ValueError("Transfer state reference is not bound to its declared register")
            names.add(name)


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


def expected(frames, registers):
    rows = []
    for frame in frames:
        rows += [("PRE", frame["cycle"], *frame["pre"]), ("POST", frame["cycle"], *frame["post"])]
        if registers:
            rows.append(("REG", frame["cycle"], *frame["registers"]))
    return rows


def concrete_mismatch(trace, want):
    """Accept only value differences in complete, aligned binary observations."""
    observations = []
    for line in trace.splitlines():
        if line.startswith(("PRE,", "POST,", "REG,")):
            fields = line.split(",")
            if any(not value.isdecimal() for value in fields[1:]):
                raise AssertionError("Mutation produced unknown rather than a semantic mismatch")
            observations.append((fields[0], *map(int, fields[1:])))
    # Reuse the strict parser for completion placement, extra text and EOF.
    memory.check_trace(trace, observations)
    if len(observations) != len(want) or any(
            len(actual) != len(reference) or actual[:2] != reference[:2]
            for actual, reference in zip(observations, want)):
        raise AssertionError("Mutation changed observation shape or edge ordering")
    if not any(actual[2:] != reference[2:] for actual, reference in zip(observations, want)):
        raise AssertionError("Mutation did not produce a concrete value mismatch")


def mutations(text, data):
    header = text.index(");") + 2
    for name, role in (("ignore-source-stall", "source_ready"), ("ignore-destination-stall", "destination_ready")):
        changed, count = re.subn(r"\b" + re.escape(data["roles"][role]) + r"\b", "1'b1", text[header:])
        if count == 0:
            raise ValueError("No uses for mutation " + name)
        yield name, text[:header] + changed
    for name, role in (("invert-active-payload", "destination_data"), ("suppress-memory-reset", "memory_reset")):
        pattern = r"(\bassign\s+" + re.escape(data["roles"][role]) + r"\s*=\s*)([^;]+);"
        changed, count = re.subn(pattern,
            lambda m: m[1] + (data["roles"]["destination_valid"] + " ? ~(" + m[2].strip() + ") : (" +
                              m[2].strip() + ");" if role == "destination_data" else "1'b0;"), text)
        if count != 1 or changed == text:
            raise ValueError("Expected one output assignment for " + name)
        yield name, changed
    reg = data["register_roles"]["index"]
    changed, count = re.subn(r"(\b" + re.escape(reg) + r"\s*<=\s*)([^;]+);", lambda m: m[1] + "'0;", text)
    if count != 1 or changed == text:
        raise ValueError("Expected one progress register update")
    yield "erase-progress-index", changed


def configuration(run, tools, out, a, wi, wo):
    directory = out / f"transfer-{a}-{wi}-{wo}"
    directory.mkdir()
    label = directory.name
    run(lean_command(out, "--run", "test/MemoryTransferEmit.lean", a, wi, wo, directory), label + "-emit")
    data = json.loads((directory / "interface.json").read_text())
    validate_descriptor(data, a, wi, wo)
    startup, rows, coverage = reference.stimulus(a, wi, wo)
    frames, events = reference.oracle(a, wi, wo, startup, rows)
    for filename, value in (("startup.json", startup), ("expected.json", frames), ("events.json", events)):
        (directory / filename).write_text(json.dumps(value, indent=2) + "\n")
    (directory / "stimulus.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
    run(lean_command(out, "--run", "test/MemoryTransferReplay.lean", a, wi, wo,
         directory / "stimulus.jsonl", directory / "startup.json", directory / "lean.jsonl"), label + "-lean")
    actual = [json.loads(line) for line in (directory / "lean.jsonl").read_text().splitlines()]
    if actual != frames:
        mismatch = next(((x, y) for x, y in zip(frames, actual) if x != y), None)
        raise AssertionError(f"Lean controller differs from integer oracle: {mismatch}")
    rtl = directory / "transfer.sv"
    rtl.write_text(run([tools["circt"], directory / "transfer.mlir", "--canonicalize", "--lower-seq-to-sv",
        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label + "-lower"))

    def simulate(source, stage, registers, *, traffic=rows, expectations=frames, negative=False):
        tb, executable = directory / (stage + "-tb.sv"), directory / (stage + ".vvp")
        tb.write_text(testbench(data, startup, traffic, registers))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], label + "-" + stage + "-compile")
        trace = run([tools["vvp"], executable], label + "-" + stage + "-simulate")
        (directory / (stage + "-trace.txt")).write_text(trace)
        try:
            memory.check_trace(trace, expected(expectations, registers))
        except AssertionError as error:
            if negative:
                # The control must produce an actual binary value mismatch.
                # X values, malformed output or truncation are harness failures.
                concrete_mismatch(trace, expected(expectations, registers))
                return str(error)
            raise
        if negative:
            raise AssertionError("Accepted actual transfer mutation: " + stage)

    simulate(rtl, "rtl", True)
    recovery_rows = [dict.fromkeys(reference.INPUT_ROLES, 0), dict.fromkeys(reference.INPUT_ROLES, 0)]
    recovery_frames, _ = reference.oracle(a, wi, wo, startup, recovery_rows)
    (directory / "reserved-phase-expected.json").write_text(json.dumps(recovery_frames, indent=2) + "\n")
    simulate(rtl, "reserved-phase", True, traffic=recovery_rows, expectations=recovery_frames)
    netlist, netjson, script = directory / "synth.v", directory / "synth.json", directory / "synth.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {data['module']}\n"
        f"synth -top {data['module']}\ncheck -assert\nwrite_json {rr.yosys_quote(netjson)}\n"
        f"write_verilog -noattr {rr.yosys_quote(netlist)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], label + "-synthesize")
    simulate(netlist, "synth", False)
    controls = []
    for name, changed in mutations(rtl.read_text(), data):
        source = directory / (name + ".sv")
        source.write_text(changed)
        controls.append({"mutation": name, "rejection": simulate(source, name, True, negative=True)})
    module = json.loads(netjson.read_text())["modules"][data["module"]]
    cells = Counter(cell["type"] for cell in module["cells"].values())
    return {"configuration": [a, wi, wo], "edges_per_form": len(rows), "reserved_phase_edges": len(recovery_rows),
            "coverage": coverage, "generic_cells": sum(cells.values()), "cell_types": dict(cells),
            "rtl_mutations_rejected": controls, "artifact_certificate": "not_run"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Open controller only. Independent integer oracle versus Lean and emitted RTL, all state/output "
                    "endpoints; synthesized external replay from reset; reserved-phase recovery; concrete RTL faults. "
                    "External memory correctness, closed accelerator, artifact proof and physical timing are separate gates."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.TransferCircuitProofs", "Pinwheel.Hardware.Emit"], "build", timeout=900)
        prepare_support(run, out)
        run(["python3", "test/test_transfer_controller_validation.py"], "negative-evidence-guards")
        run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryTransferCircuit.lean"], "structural-tests")
        audit = run(["lake", "env", "lean", "-DwarningAsError=true", "test/MemoryTransferContracts.lean"], "structural-audit")
        if "standard axioms only" not in audit:
            raise AssertionError("Missing structural proof axiom audit")
        for a, wi, wo in MATRIX:
            report["configurations"].append(configuration(run, tools, out, a, wi, wo))
        if source_hashes() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
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
