#!/usr/bin/env python3
"""Fresh byte-adapter RTL replay, explicit RAM loading, and corruption controls.

Emitted RTL is checked at every register and both edge observations. Synthesized
RTL starts uninitialized and receives full-word stores before any operation that
depends on old RAM contents. This finite campaign is separate from kernel RTL
correspondence, eventual-response assumptions, and physical timing.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import time

import byte_adapter_oracle as reference

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("byte_adapter_cad", ROOT / "scripts/check-round-robin-circuit.py")
rr = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(rr)
MATRIX = (1, 2, 3)
LEAN_ROOTS = ("test/MemoryByteAdapterEmit.lean", "test/MemoryByteAdapterReplay.lean",
              "test/MemoryByteAdapterCircuit.lean", "test/MemoryByteAdapterEffects.lean")


def source_hashes():
    pending, paths = [ROOT / name for name in LEAN_ROOTS], set()
    while pending:
        path = pending.pop()
        if path in paths:
            continue
        paths.add(path)
        for line in path.read_text().splitlines():
            if match := re.match(r"^import\s+(.+)$", line):
                for module in match[1].split("--", 1)[0].split():
                    if module == "Pinwheel" or module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    paths.update(ROOT / name for name in (
        "scripts/check-memory-byte-adapter.py", "scripts/byte_adapter_oracle.py",
        "scripts/check-round-robin-circuit.py", "scripts/validation_run.py", "scripts/process_group.py",
        "test/test_memory_byte_adapter_driver.py", "test/test_byte_adapter_oracle.py",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain", "tools/hardware-toolchain.json"))
    return {str(path.relative_to(ROOT)): rr.sha(path) for path in sorted(paths)}


def widths(a):
    if type(a) is not int or a <= 0:
        raise ValueError("HDL address width must be a positive integer")
    return ([1, 1, 1, 1, 2, a, 2, 32, 1], [1, 1, 2, 32], reference.register_widths(a))


def validate_descriptor(data, a):
    expected_widths = widths(a)
    for key, value in (("schema", 1), ("address_width", a), ("data_width", 32), ("depth", 1 << a)):
        if type(data.get(key)) is not int or data[key] != value:
            raise ValueError("Wrong byte adapter descriptor field: " + key)
    if data.get("clock") != "clk" or data.get("module") != f"byte_adapter_a{a}_w32":
        raise ValueError("Wrong byte adapter module or clock")
    names = {"clk"}
    for group, values in zip(("inputs", "outputs", "registers"), expected_widths, strict=True):
        if type(data.get(group)) is not list or len(data[group]) != len(values):
            raise ValueError("Incomplete typed byte adapter " + group)
        for index, (port, width) in enumerate(zip(data[group], values, strict=True)):
            if type(port) is not dict or type(port.get("name")) is not str or \
                    not rr.IDENTIFIER.fullmatch(port["name"]) or port["name"] in names or \
                    type(port.get("width")) is not int or port["width"] != width or \
                    type(port.get("index")) is not int or port["index"] != index:
                raise ValueError("Invalid typed byte adapter signal/order")
            if group == "registers" and port.get("reference") != port["name"]:
                raise ValueError("Register reference must name its declared register")
            names.add(port["name"])
    roles, registers = data.get("roles"), data.get("register_roles")
    if type(roles) is not dict or set(roles) != set(reference.INPUT_ROLES + reference.OUTPUT_ROLES):
        raise ValueError("Incomplete byte adapter port role map")
    for group, order in (("inputs", reference.INPUT_ROLES), ("outputs", reference.OUTPUT_ROLES)):
        if [roles[k] for k in order] != [p["name"] for p in data[group]]:
            raise ValueError("Changed byte adapter port role order")
    if type(registers) is not dict or set(registers) != {"words", "q", *reference.METADATA_ROLES} or \
            type(registers["words"]) is not list or len(registers["words"]) != 1 << a:
        raise ValueError("Incomplete byte adapter register roles")
    ordered = registers["words"] + [registers["q"]] + [registers[k] for k in reference.METADATA_ROLES]
    if ordered != [p["name"] for p in data["registers"]]:
        raise ValueError("Register roles do not enumerate all words/Q/metadata/pending in typed order")
    codes = data.get("response_codes")
    if type(codes) is not dict or codes != {"read": 0, "stored": 1, "reserved_size": 2, "misaligned": 3} or \
            any(type(value) is not int for value in codes.values()):
        raise ValueError("Changed physical response encoding")
    for key, value in {
        "startup": "arbitrary words, Q, six retained metadata fields and pending; no power-up initialization",
        "reset_behavior": "suppresses both handshakes and clears pending only; preserves words, Q and all request metadata",
        "commit_behavior": "valid store changes memory only on response acceptance; faulting requests issue no memory command",
    }.items():
        if data.get(key) != value:
            raise ValueError("Missing hardware boundary: " + key)
    return data


def validate_frames(a, rows, frames):
    if type(frames) is not list or len(frames) != len(rows):
        raise ValueError("Incomplete Lean/oracle frame trace")
    for cycle, (row, frame) in enumerate(zip(rows, frames, strict=True)):
        reference.validate_row(a, row)
        if type(frame) is not dict or set(frame) != {"cycle", "input", "pre", "post", "registers"} or \
                type(frame["cycle"]) is not int or frame["cycle"] != cycle or \
                json.dumps(frame["input"], sort_keys=True) != json.dumps(row, sort_keys=True):
            raise ValueError("Malformed frame/input/edge order")
        for key, sizes in (("pre", widths(a)[1]), ("post", widths(a)[1]), ("registers", widths(a)[2])):
            values = frame[key]
            if type(values) is not list or len(values) != len(sizes) or any(
                    type(value) is not int or not 0 <= value < 1 << width
                    for value, width in zip(values, sizes, strict=True)):
                raise ValueError("Malformed or out-of-width frame " + key)


def initialization_evidence(a, rows, initialization_edges):
    """Check the loader independently of claimed coverage and oracle RAM values."""
    if type(initialization_edges) is not int or not 0 < initialization_edges <= len(rows) or not rows[0]["reset"]:
        raise ValueError("Synthesized replay requires an explicit initial reset and bounded loading prefix")
    known_words, pending, q_known, commits = set(), None, False, []
    for cycle, item in enumerate(rows[:initialization_edges]):
        reference.validate_row(a, item)
        if item["reset"]:
            pending = None
        elif pending is not None:
            if item["response_ready"]:
                if pending["write"]:
                    if pending["size"] != 2 or pending["offset"] != 0:
                        raise ValueError("Initialization must use full-word stores")
                    known_words.add(pending["address"])
                    commits.append({"cycle": cycle, "address": pending["address"], "value": pending["data"]})
                elif not q_known:
                    raise ValueError("Initialization observed an uninitialized read")
                pending = None
        elif item["request_valid"]:
            if item["size"] != 2 or item["offset"] != 0 or \
                    (not item["write"] and known_words != set(range(1 << a))):
                raise ValueError("Read/subword operation precedes complete explicit RAM loading")
            q_known = item["address"] in known_words
            pending = item
    if known_words != set(range(1 << a)) or not q_known or pending is not None:
        raise ValueError("Loading prefix must establish all words and prime Q, with no pending request")
    return {"edges": initialization_edges, "full_word_commits": commits, "q_primed": True,
            "synthesized_registers_forced": False,
            "observations_compared": "all pre/post outputs, starting with the first reset edge"}


def testbench(data, startup, rows, registers):
    lines, connections = ["`timescale 1ns/1ps", "module tb;", "reg clk = 0;"], [".clk(clk)"]
    for group, kind in (("inputs", "reg"), ("outputs", "wire")):
        for port in data[group]:
            lines.append(f"{kind} [{port['width']-1}:0] {port['name']}{' = 0' if kind == 'reg' else ''};")
            connections.append(f".{port['name']}({port['name']})")
    lines += [f"{data['module']} dut({', '.join(connections)});", "initial begin"]
    if registers:
        lines += [f"force dut.{p['reference']} = {p['width']}'h{x:x};" for p, x in zip(data["registers"], startup, strict=True)]
        lines += ["#1;"] + [f"release dut.{p['reference']};" for p in data["registers"]]
    outputs = ", ".join(p["name"] for p in data["outputs"])
    register_args = ", ".join("dut." + p["reference"] for p in data["registers"])
    for cycle, row in enumerate(rows):
        for role, port in zip(reference.INPUT_ROLES, data["inputs"], strict=True):
            lines.append(f"{port['name']} = {port['width']}'h{int(row[role]):x};")
        lines += ["#1;", f'$display("PRE,{cycle}{",%0d" * len(data["outputs"])}", {outputs});', "clk = 1; #1;",
                  f'$display("POST,{cycle}{",%0d" * len(data["outputs"])}", {outputs});']
        if registers:
            lines.append(f'$display("REG,{cycle}{",%0d" * len(startup)}", {register_args});')
        lines += ["clk = 0; #1;"]
    return "\n".join(lines + ['$display("BYTE_ADAPTER_DONE"); $finish;', "end", "endmodule", ""])


def expected(frames, registers):
    observations = []
    for frame in frames:
        observations += [("PRE", frame["cycle"], *frame["pre"]), ("POST", frame["cycle"], *frame["post"])]
        if registers:
            observations.append(("REG", frame["cycle"], *frame["registers"]))
    return observations


class TraceError(AssertionError):
    """Malformed/unknown/incomplete output is never a semantic negative result."""


class ConcreteMismatch(AssertionError):
    def __init__(self, witness):
        self.witness = witness
        super().__init__("Concrete byte adapter value mismatch: " + json.dumps(witness, sort_keys=True))


def check_trace(text, want, data):
    observations, done, finish = [], 0, 0
    for line in text.splitlines():
        if line == "BYTE_ADAPTER_DONE":
            done += 1
        elif line.startswith(("PRE,", "POST,", "REG,")):
            fields = line.split(",")
            if done or len(fields) < 3 or any(not value.isascii() or not value.isdecimal() for value in fields[1:]):
                raise TraceError("Unknown or out-of-order byte adapter observation")
            observations.append((fields[0], *map(int, fields[1:])))
        elif re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)", line):
            finish += 1
            if done != 1 or finish > 1:
                raise TraceError("Misplaced or duplicate simulator finish")
        elif line.strip():
            raise TraceError("Unexpected simulation output: " + line)
    if done != 1 or len(observations) != len(want):
        raise TraceError("Incomplete byte adapter observations/completion")
    # Validate the whole trace before considering an early value mismatch.
    for actual, expected_row in zip(observations, want, strict=True):
        ports = data["registers" if actual[0] == "REG" else "outputs"]
        if actual[:2] != expected_row[:2] or len(actual) != len(expected_row) or len(actual) != len(ports)+2 or \
                any(value >= 1 << port["width"] for value, port in zip(actual[2:], ports, strict=True)):
            raise TraceError("Changed observation shape, edge order, or signal width")
    for actual, expected_row in zip(observations, want, strict=True):
        ports = data["registers" if actual[0] == "REG" else "outputs"]
        for index, (value, expected_value) in enumerate(zip(actual[2:], expected_row[2:], strict=True)):
            if value != expected_value:
                raise ConcreteMismatch({"observation": actual[0], "cycle": actual[1], "signal": ports[index]["name"],
                                        "expected": expected_value, "actual": value})
    return len(observations)


def mutations(text, data):
    roles, registers = data["roles"], data["register_roles"]
    header = text.index(");")+2
    changed, count = re.subn(r"\b" + re.escape(roles["response_ready"]) + r"\b", "1'b1", text[header:])
    if not count:
        raise ValueError("Missing response-ready uses for RTL mutation")
    yield "ignore-response-stall", text[:header]+changed
    for name, role, expression in (
        ("accept-while-pending", "request_ready", lambda value: "~"+roles["reset"]),
        ("invert-active-read", "response_data", lambda value:
         f"({roles['response_valid']} & ({roles['response_code']} == 2'd0)) ? (({value}) ^ 32'h80000000) : ({value})"),
    ):
        changed, count = re.subn(r"(\bassign\s+"+re.escape(roles[role])+r"\s*=\s*)([^;]+);",
                                lambda match: match[1]+expression(match[2].strip())+";", text)
        if count != 1 or changed == text:
            raise ValueError("Expected one output assignment for " + name)
        yield name, changed
    accepted = f"({roles['request_ready']} & {roles['request_valid']})"
    for name, register, expression in (
        ("clear-retained-data", registers["data"], lambda value: f"{accepted} ? ({value}) : 32'd0"),
        ("clear-word-on-reset", registers["words"][0], lambda value: f"{roles['reset']} ? 32'd0 : ({value})"),
        ("write-before-ack", registers["words"][0], lambda value:
         f"({accepted} & {roles['write']} & ({roles['size']} == 2'd2) & ({roles['offset']} == 2'd0) & "
         f"({roles['address']} == 0)) ? {roles['data']} : ({value})"),
        ("fault-changes-q", registers["q"], lambda value:
         f"({accepted} & ({roles['size']} == 2'd3)) ? ~{registers['q']} : ({value})"),
        ("refill-on-completion", registers["pending"], lambda value:
         f"({roles['response_valid']} & {roles['response_ready']} & {roles['request_valid']}) ? 1'b1 : ({value})"),
    ):
        changed, count = re.subn(r"(\b"+re.escape(register)+r"\s*<=\s*)([^;]+);",
                                lambda match: match[1]+expression(match[2].strip())+";", text)
        if count != 1 or changed == text:
            raise ValueError("Expected one register assignment for " + name)
        yield name, changed


def configuration(run, tools, out, a):
    directory = out / f"byte-adapter-{a}-32"
    directory.mkdir()
    label = directory.name
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryByteAdapterEmit.lean", a, directory], label+"-emit")
    data = validate_descriptor(json.loads((directory / "interface.json").read_text()), a)
    startup, rows, coverage = reference.stimulus(a)
    loading = initialization_evidence(a, rows, coverage["initialization_edges"])
    frames, events, ledger = reference.oracle(a, startup, rows)
    validate_frames(a, rows, frames)
    if ledger["pending"] is not None or ledger["startup_pending"] != 1 or ledger["stores"] == 0 or ledger["faults"] == 0:
        raise AssertionError("Incomplete byte adapter ledger/coverage")
    for filename, value in (("startup.json", startup), ("expected.json", frames), ("events.json", events), ("ledger.json", ledger)):
        (directory / filename).write_text(json.dumps(value, indent=2)+"\n")
    (directory / "stimulus.jsonl").write_text("".join(json.dumps(row)+"\n" for row in rows))
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryByteAdapterReplay.lean", a,
         directory / "stimulus.jsonl", directory / "startup.json", directory / "lean.jsonl"], label+"-lean")
    actual = [json.loads(line) for line in (directory / "lean.jsonl").read_text().splitlines()]
    validate_frames(a, rows, actual)
    if actual != frames:
        mismatch = next((dict(expected=x, actual=y) for x, y in zip(frames, actual, strict=True) if x != y), None)
        raise AssertionError("Lean byte adapter differs from integer oracle: " + json.dumps(mismatch))
    rtl = directory / "byte-adapter.sv"
    rtl.write_text(run([tools["circt"], directory / "byte-adapter.mlir", "--canonicalize", "--lower-seq-to-sv",
        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label+"-lower"))

    def simulate(source, stage, registers, negative=False):
        tb, executable = directory / (stage+"-tb.sv"), directory / (stage+".vvp")
        tb.write_text(testbench(data, startup, rows, registers))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], label+"-"+stage+"-compile")
        trace = run([tools["vvp"], executable], label+"-"+stage+"-simulate")
        (directory / (stage+"-trace.txt")).write_text(trace)
        try:
            check_trace(trace, expected(frames, registers), data)
        except ConcreteMismatch as error:
            if negative:
                witness = error.witness
                cycle = witness["cycle"]
                return {**witness, "input": rows[cycle], "event": events[cycle],
                        "before_registers": startup if cycle == 0 else frames[cycle-1]["registers"],
                        "expected_post_registers": frames[cycle]["registers"]}
            raise
        if negative:
            raise AssertionError("Accepted actual byte adapter RTL mutation: " + stage)

    simulate(rtl, "rtl", True)
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
        controls.append({"mutation": name, "witness": simulate(source, name, True, negative=True)})
    modules = json.loads(netjson.read_text())["modules"]
    if set(modules) != {data["module"]} or modules[data["module"]].get("memories"):
        raise AssertionError("Unexpected synthesized hierarchy or unlowered memory")
    cells = Counter(cell["type"] for cell in modules[data["module"]]["cells"].values())
    return {"configuration": a, "data_width": 32, "edges_per_form": len(rows),
            "typed_registers": len(data["registers"]), "typed_outputs": len(data["outputs"]),
            "coverage": coverage, "initialization": loading, "ledger": ledger,
            "generic_cells": sum(cells.values()), "cell_types": dict(cells),
            "rtl_mutations_rejected": controls, "artifact_certificate": "not_run"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = rr.fresh_directory(ROOT / "build/memory-byte-adapter", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [], "matrix": list(MATRIX),
              "boundary": "Independent integer/array/request-occurrence oracle versus Lean and emitted RTL at all raw "
                          "registers and pre/post outputs; synthesized external replay from reset and explicit full-word "
                          "loading, with no forced synthesized state. Stores commit on accepted responses; reset cancels "
                          "pending work and preserves previous memory effects. Kernel artifact correspondence and physical "
                          "timing are separate gates. Address width four is not part of this matrix."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.ByteAdapterCircuitProofs",
             "Pinwheel.Hardware.Memory.ByteAdapterEffects", "Pinwheel.Hardware.Emit"], "build", timeout=900)
        run(["python3", "test/test_byte_adapter_oracle.py"], "oracle-tests")
        run(["python3", "test/test_memory_byte_adapter_driver.py"], "driver-tests")
        for name in ("Circuit", "Effects"):
            result = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", f"test/MemoryByteAdapter{name}.lean"],
                         name.lower()+"-tests", timeout=900)
            if "standard axioms only" not in result:
                raise AssertionError("Missing byte adapter " + name + " axiom audit")
        for a in MATRIX:
            report["configurations"].append(configuration(run, tools, out, a))
        if source_hashes() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during validation")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic()-started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): rr.sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
