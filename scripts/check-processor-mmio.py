#!/usr/bin/env python3
"""Fresh all-endpoint MMIO RTL/synthesis replay with an independent event oracle.

This finite campaign does not certify imported RTL or serial-wire behavior.
Synthesis replay begins with a synchronous reset and never forces DUT registers.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import time

import mmio_oracle as reference

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("mmio_cad", ROOT / "scripts/check-round-robin-circuit.py")
rr = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(rr)
LEAN_ROOTS = ("test/ProcessorMmioEmit.lean", "test/ProcessorMmioReplay.lean", "test/ProcessorMmioCircuit.lean")
BOUNDARIES = {
    "startup": "arbitrary eight physical registers; inactive TX/RX bytes retained until capture or reset",
    "reset_behavior": "synchronous reset clears every register; all outputs are masked during reset",
    "operation_behavior": "always-ready atomic request/response edge with no response backpressure; invalid device faults without CPU effect",
    "frontend_boundary": "TX completion, RX arrival and framing error are explicit external events; no serial-wire claim",
}


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
        "scripts/check-processor-mmio.py", "scripts/mmio_oracle.py", "scripts/check-round-robin-circuit.py",
        "scripts/validation_run.py", "scripts/process_group.py", "test/test_mmio_oracle.py",
        "test/test_processor_mmio_driver.py", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "tools/hardware-toolchain.json"))
    return {str(path.relative_to(ROOT)): rr.sha(path) for path in sorted(paths)}


def validate_descriptor(data):
    if type(data.get("schema")) is not int or data["schema"] != 1 or \
            data.get("clock") != "clk" or data.get("module") != "processor_mmio":
        raise ValueError("Wrong MMIO schema/module/clock")
    names = {"clk"}
    groups = (("inputs", reference.INPUT_WIDTHS), ("outputs", reference.OUTPUT_WIDTHS), ("registers", reference.REGISTER_WIDTHS))
    for group, widths in groups:
        if type(data.get(group)) is not list or len(data[group]) != len(widths):
            raise ValueError("Incomplete typed MMIO " + group)
        for index, (port, width) in enumerate(zip(data[group], widths, strict=True)):
            if type(port) is not dict or type(port.get("name")) is not str or \
                    not rr.IDENTIFIER.fullmatch(port["name"]) or port["name"] in names or \
                    type(port.get("width")) is not int or port["width"] != width or \
                    type(port.get("index")) is not int or port["index"] != index:
                raise ValueError("Invalid typed MMIO signal/order")
            if group == "registers" and port.get("reference") != port["name"]:
                raise ValueError("Register reference must name its declared register")
            names.add(port["name"])
    roles, registers = data.get("roles"), data.get("register_roles")
    if type(roles) is not dict or set(roles) != set(reference.INPUT_ROLES + reference.OUTPUT_ROLES):
        raise ValueError("Incomplete MMIO port role map")
    for group, order in (("inputs", reference.INPUT_ROLES), ("outputs", reference.OUTPUT_ROLES)):
        if [roles[k] for k in order] != [p["name"] for p in data[group]]:
            raise ValueError("Changed MMIO port role order")
    if type(registers) is not dict or set(registers) != set(reference.REGISTER_ROLES) or \
            [registers[k] for k in reference.REGISTER_ROLES] != [p["name"] for p in data["registers"]]:
        raise ValueError("Incomplete or changed register roles")
    for key, expected_codes in (
        ("response_codes", {"read": 0, "stored": 1, "register_hole": 2, "direction": 3, "tx_busy": 4, "rx_empty": 5}),
        ("device_codes", {"gpio": 0, "timer": 1, "uart": 2, "invalid": 3}),
    ):
        codes = data.get(key)
        if type(codes) is not dict or codes != expected_codes or any(type(v) is not int for v in codes.values()):
            raise ValueError("Changed physical encoding: " + key)
    for key, value in BOUNDARIES.items():
        if data.get(key) != value:
            raise ValueError("Missing hardware boundary: " + key)
    return data


def validate_frames(rows, frames):
    if type(frames) is not list or len(frames) != len(rows):
        raise ValueError("Incomplete Lean/oracle frame trace")
    for cycle, (row, frame) in enumerate(zip(rows, frames, strict=True)):
        reference.validate_row(row)
        if type(frame) is not dict or set(frame) != {"cycle", "input", "pre", "post", "registers"} or \
                type(frame["cycle"]) is not int or frame["cycle"] != cycle or \
                json.dumps(frame["input"], sort_keys=True) != json.dumps(row, sort_keys=True):
            raise ValueError("Malformed frame/input/edge order")
        for key, sizes in (("pre", reference.OUTPUT_WIDTHS), ("post", reference.OUTPUT_WIDTHS), ("registers", reference.REGISTER_WIDTHS)):
            values = frame[key]
            if type(values) is not list or len(values) != len(sizes) or any(
                    type(v) is not int or not 0 <= v < 1 << w for v, w in zip(values, sizes, strict=True)):
                raise ValueError("Malformed or out-of-width frame " + key)


def initialization_evidence(rows):
    if not rows:
        raise ValueError("Empty MMIO replay")
    for row in rows:
        reference.validate_row(row)
    if not rows[0]["reset"]:
        raise ValueError("Synthesized replay must begin with a synchronous reset")
    return {"initial_reset_edges": 1, "synthesized_registers_forced": False,
            "all_registers_initialized_by_reset": True, "pre_reset_outputs": "all reset-masked"}


def testbench(data, startup, rows, registers, *, segments=None):
    if segments is None:
        segments = [{"startup": startup, "rows": rows}]
    if not registers:
        if len(segments) != 1:
            raise ValueError("Synthesized replay cannot use forced raw segments")
        initialization_evidence(rows)
    lines, connections = ["`timescale 1ns/1ps", "module tb;", "reg clk = 0;"], [".clk(clk)"]
    for group, kind in (("inputs", "reg"), ("outputs", "wire")):
        for port in data[group]:
            lines.append(f"{kind} [{port['width']-1}:0] {port['name']}{' = 0' if kind == 'reg' else ''};")
            connections.append(f".{port['name']}({port['name']})")
    lines += [f"{data['module']} dut({', '.join(connections)});", "initial begin"]
    outputs = ", ".join(p["name"] for p in data["outputs"])
    register_args = ", ".join("dut." + p["reference"] for p in data["registers"])
    cycle = 0
    for segment in segments:
        bank = reference.restore(segment["startup"])
        if registers:
            lines += [f"force dut.{p['reference']} = {p['width']}'h{x:x};" for p, x in zip(data["registers"], bank, strict=True)]
            lines += ["#1;"] + [f"release dut.{p['reference']};" for p in data["registers"]]
        for row in segment["rows"]:
            reference.validate_row(row)
            for role, port in zip(reference.INPUT_ROLES, data["inputs"], strict=True):
                lines.append(f"{port['name']} = {port['width']}'h{int(row[role]):x};")
            lines += ["#1;", f'$display("PRE,{cycle}{",%0d" * len(data["outputs"])}", {outputs});', "clk = 1; #1;",
                      f'$display("POST,{cycle}{",%0d" * len(data["outputs"])}", {outputs});']
            if registers:
                lines.append(f'$display("REG,{cycle}{",%0d" * len(bank)}", {register_args});')
            lines += ["clk = 0; #1;"]
            cycle += 1
    return "\n".join(lines + ['$display("MMIO_DONE"); $finish;', "end", "endmodule", ""])


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
        super().__init__("Concrete MMIO value mismatch: " + json.dumps(witness, sort_keys=True))


def check_trace(text, want, data):
    observations, done, finish = [], 0, 0
    for line in text.splitlines():
        if line == "MMIO_DONE":
            done += 1
        elif line.startswith(("PRE,", "POST,", "REG,")):
            fields = line.split(",")
            if done or len(fields) < 3 or any(not v.isascii() or not v.isdecimal() for v in fields[1:]):
                raise TraceError("Unknown or out-of-order MMIO observation")
            observations.append((fields[0], *map(int, fields[1:])))
        elif re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)", line):
            finish += 1
            if done != 1 or finish > 1:
                raise TraceError("Misplaced or duplicate simulator finish")
        elif line.strip():
            raise TraceError("Unexpected simulation output: " + line)
    if done != 1 or len(observations) != len(want):
        raise TraceError("Incomplete MMIO observations/completion")
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


def mutations(text, data):
    p, r = data["roles"], data["register_roles"]
    active = f"(~{p['reset']} & {p['request_valid']})"
    clear = f"({active} & ({p['device']} == 2'd2) & ({p['word']} == 6'd3) & {p['write']})"
    for name, register, expression in (
        ("fault-writes-gpio", r["gpio"], lambda value:
         f"({active} & ({p['device']} == 2'd0) & {p['write']}) ? {p['data']} : ({value})"),
        ("freeze-timer", r["timer"], lambda value: f"{p['reset']} ? 32'd0 : {r['timer']}"),
        ("saturate-timer", r["timer"], lambda value:
         f"(~{p['reset']} & ({r['timer']} == 32'hffffffff)) ? {r['timer']} : ({value})"),
        ("cancel-new-tx", r["tx_active"], lambda value: f"{p['tx_complete']} ? 1'b0 : ({value})"),
        ("drop-rx-refill", r["rx_data"], lambda value:
         f"(~{p['reset']} & {r['rx_valid']} & {p['rx_valid']}) ? {r['rx_data']} : ({value})"),
        ("clear-new-overrun", r["overrun"], lambda value: f"{clear} ? 1'b0 : ({value})"),
        ("clear-new-framing", r["framing"], lambda value: f"{clear} ? 1'b0 : ({value})"),
        ("ignore-gpio-reset", r["gpio"], lambda value: f"{p['reset']} ? {r['gpio']} : ({value})"),
    ):
        changed, count = re.subn(r"(\b"+re.escape(register)+r"\s*<=\s*)([^;]+);",
                                lambda m: m[1]+expression(m[2].strip())+";", text)
        if count != 1 or changed == text:
            raise ValueError("Expected one register assignment for " + name)
        yield name, changed
    for name, role, expression in (
        ("invalid-selector-success", "response_code", lambda value:
         f"({active} & ({p['device']} == 2'd3)) ? 3'd0 : ({value})"),
        ("corrupt-active-read", "response_data", lambda value:
         f"({p['response_valid']} & ({p['response_code']} == 3'd0)) ? (({value}) ^ 32'h80000000) : ({value})"),
        ("leak-inactive-tx", "tx_data", lambda value: r["tx_data"]),
        ("respond-during-reset", "response_valid", lambda value: p["request_valid"]),
    ):
        changed, count = re.subn(r"(\bassign\s+"+re.escape(p[role])+r"\s*=\s*)([^;]+);",
                                lambda m: m[1]+expression(m[2].strip())+";", text)
        if count != 1 or changed == text:
            raise ValueError("Expected one output assignment for " + name)
        yield name, changed


def configuration(run, tools, out):
    directory = out / "mmio"
    directory.mkdir()
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/ProcessorMmioEmit.lean", directory], "mmio-emit")
    data = validate_descriptor(json.loads((directory / "interface.json").read_text()))
    startup, rows, coverage = reference.stimulus()
    initialization = initialization_evidence(rows)
    frames, events, ledger = reference.oracle(startup, rows)
    validate_frames(rows, frames)
    if any(ledger[key] <= 0 for key in ("reads", "stores", "faults", "invalid_selectors", "resets", "ticks", "tx_completions", "rx_accepted", "rx_dropped")):
        raise AssertionError("Incomplete MMIO event coverage")

    def replay(label, initial, items, target):
        for suffix, value in (("startup.json", initial), ("expected.json", target)):
            (directory / (label+suffix)).write_text(json.dumps(value, indent=2)+"\n")
        stimulus = directory / (label+"stimulus.jsonl")
        stimulus.write_text("".join(json.dumps(row)+"\n" for row in items))
        result = directory / (label+"lean.jsonl")
        run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/ProcessorMmioReplay.lean",
             stimulus, directory / (label+"startup.json"), result], "mmio-"+label+"lean")
        actual = [json.loads(line) for line in result.read_text().splitlines()]
        validate_frames(items, actual)
        if actual != target:
            mismatch = next(dict(expected=x, actual=y) for x, y in zip(target, actual, strict=True) if x != y)
            raise AssertionError("Lean MMIO differs from integer oracle: " + json.dumps(mismatch))

    replay("", startup, rows, frames)
    for filename, value in (("events.json", events), ("ledger.json", ledger)):
        (directory / filename).write_text(json.dumps(value, indent=2)+"\n")
    segments, raw_frames, raw_events, raw_rows, raw_before = reference.raw_cases(), [], [], [], []
    for segment in segments:
        fs, es, summary = reference.oracle(segment["startup"], segment["rows"])
        replay(segment["name"]+"-", segment["startup"], segment["rows"], fs)
        (directory / (segment["name"]+"-ledger.json")).write_text(json.dumps(summary, indent=2)+"\n")
        for index, (frame, event) in enumerate(zip(fs, es, strict=True)):
            cycle = len(raw_frames)
            raw_frames.append({**frame, "cycle": cycle})
            raw_events.append({**event, "cycle": cycle})
            raw_rows.append(frame["input"])
            raw_before.append(segment["startup"] if index == 0 else fs[index-1]["registers"])
    for filename, value in (("raw-segments.json", segments), ("raw-expected.json", raw_frames), ("raw-events.json", raw_events)):
        (directory / filename).write_text(json.dumps(value, indent=2)+"\n")
    rtl = directory / "mmio.sv"
    rtl.write_text(run([tools["circt"], directory / "mmio.mlir", "--canonicalize", "--lower-seq-to-sv",
        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], "mmio-lower"))

    def simulate(source, stage, registers, *, negative=False, raw=False):
        tb, executable = directory / (stage+"-tb.sv"), directory / (stage+".vvp")
        tb.write_text(testbench(data, startup, rows, registers, segments=segments if raw else None))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], "mmio-"+stage+"-compile")
        trace = run([tools["vvp"], executable], "mmio-"+stage+"-simulate")
        (directory / (stage+"-trace.txt")).write_text(trace)
        fs, items, es = (raw_frames, raw_rows, raw_events) if raw else (frames, rows, events)
        try:
            check_trace(trace, expected(fs, registers), data)
        except ConcreteMismatch as error:
            if negative:
                witness, cycle = error.witness, error.witness["cycle"]
                before = raw_before[cycle] if raw else startup if cycle == 0 else frames[cycle-1]["registers"]
                return {**witness, "campaign": "raw" if raw else "reset", "input": items[cycle], "event": es[cycle],
                        "before_registers": before, "expected_post_registers": fs[cycle]["registers"]}
            raise
        if negative:
            raise AssertionError("Accepted actual MMIO RTL mutation: " + stage)

    simulate(rtl, "rtl", True)
    simulate(rtl, "raw", True, raw=True)
    netlist, netjson, script = directory / "synth.v", directory / "synth.json", directory / "synth.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {data['module']}\n"
        f"synth -top {data['module']}\ncheck -assert\nwrite_json {rr.yosys_quote(netjson)}\n"
        f"write_verilog -noattr {rr.yosys_quote(netlist)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], "mmio-synthesize")
    simulate(netlist, "synth", False)
    controls = []
    for name, changed in mutations(rtl.read_text(), data):
        source = directory / (name+".sv")
        source.write_text(changed)
        controls.append({"mutation": name, "witness": simulate(source, name, True, negative=True, raw=name == "saturate-timer")})
    modules = json.loads(netjson.read_text())["modules"]
    if set(modules) != {data["module"]} or modules[data["module"]].get("memories"):
        raise AssertionError("Unexpected synthesized hierarchy or memory")
    cells = Counter(cell["type"] for cell in modules[data["module"]]["cells"].values())
    return {"configuration": "mmio", "edges_per_form": len(rows), "additional_raw_edges": len(raw_frames),
            "raw_startup_images": len(segments), "typed_registers": 8, "typed_outputs": 7,
            "coverage": coverage, "initialization": initialization, "ledger": ledger,
            "generic_cells": sum(cells.values()), "cell_types": dict(cells),
            "rtl_mutations_rejected": controls, "artifact_certificate": "not_run"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = rr.fresh_directory(ROOT / "build/processor-mmio", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
              "boundary": "Independent integer/ordered-event oracle versus Lean and emitted RTL at all eight raw registers "
                          "and seven pre/post outputs; synthesized external replay from synchronous reset without forced state. "
                          "Every nonreset offered operation has one atomic response, including faults. Timer progression is not "
                          "CPU retirement. Frontend events are input pins; imported-RTL certification and serial-wire correctness are separate."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Processor.MmioCircuitProofs", "Pinwheel.Hardware.Emit"], "build", timeout=900)
        run(["python3", "test/test_mmio_oracle.py"], "oracle-tests")
        run(["python3", "test/test_processor_mmio_driver.py"], "driver-tests")
        result = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/ProcessorMmioCircuit.lean"], "circuit-tests", timeout=900)
        if "standard axioms only" not in result:
            raise AssertionError("Missing MMIO axiom audit")
        report["configurations"].append(configuration(run, tools, out))
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
