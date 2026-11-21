#!/usr/bin/env python3
"""Replay fractional UART receive in Lean and emitted hierarchical RTL."""
from __future__ import annotations

import argparse
from bisect import bisect_left
from itertools import product
import json
from pathlib import Path

import typed_circuit_hierarchy as hierarchy
import typed_circuit_readback as readback
import typed_module_checks as checks
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
EMITTER = ROOT / "test/FractionalUartRxEmit.lean"
MODULE = "Pinwheel.Hardware.Uart.FractionalRx"
PROFILE = checks.profile(MODULE, MODULE + ".flat 6")
SCALE = 16
HALF_BIT = 60
FRAMES = (0xA6, 0x59)


def source_hashes():
    paths = {*checks.source_paths(), *hierarchy.source_paths(), Path(__file__).resolve(),
             ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"}
    pending = [EMITTER, *(path for path in paths if path.suffix == ".lean")]
    visited = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        visited.add(path)
        paths.add(path)
        for line in path.read_text().splitlines():
            if line.startswith("import Pinwheel."):
                pending.append(ROOT / (line.split()[1].replace(".", "/") + ".lean"))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def ceil_units(units):
    return (units + SCALE - 1) // SCALE


def case(sender_bit, phase, consumer):
    """Independent absolute-time sender, sample schedule and one-slot consumer."""
    starts = [SCALE * 5 + phase, SCALE * 5 + phase + 10 * sender_bit]
    detected = [ceil_units(start) + 2 for start in starts]
    half_edges = [[start + ceil_units(k * HALF_BIT) for k in range(1, 20)] for start in detected]
    sample_edges = [edges[::2] for edges in half_edges]
    complete = [edges[-1] for edges in half_edges]
    arrivals = dict(zip(complete, FRAMES, strict=True))
    first, last = complete
    take = {"drain": {first + 1, last + 1}, "replace": {last, last + 1},
            "overrun": {last + 1}}[consumer]
    held, overrun = None, False
    delivered, dropped = [], []
    traffic, expected = [], []

    def raw_line(cycle):
        wire_time = cycle * SCALE
        for start, data in zip(starts, FRAMES, strict=True):
            if start <= wire_time < start + 10 * sender_bit:
                symbol = (wire_time - start) // sender_bit
                return 0 if symbol == 0 else 1 if symbol == 9 else (data >> (symbol - 1)) & 1
        return 1

    def sampler(cycle, reset):
        if reset:
            return [0, 0, 0]
        for start, edges in zip(detected, half_edges, strict=True):
            if start < cycle <= edges[-1]:
                index = bisect_left(edges, cycle)
                return [1, int(index % 2 == 0 and edges[index] == cycle), index]
            if cycle == edges[-1] + 1:
                return [0, 0, 19]
        return [0, 0, 0]

    def observe(cycle, reset):
        return [int(held is not None), held if held is not None else 0, 0, int(overrun),
                *sampler(cycle, reset)]

    for cycle in range(last + 5):
        reset = cycle == 0
        clear = cycle == last + 3
        traffic.append([int(reset), raw_line(cycle), int(cycle in take), int(clear), HALF_BIT, SCALE])
        before = observe(cycle, reset)
        if cycle in take and held is not None:
            delivered.append(held)
            held = None
        if clear:
            overrun = False
        if cycle in arrivals:
            if held is None:
                held = arrivals[cycle]
            else:
                overrun = True
                dropped.append(arrivals[cycle])
        expected.append([before, observe(cycle + 1, reset)])

    assert delivered == list(FRAMES[:1] if consumer == "overrun" else FRAMES)
    assert dropped == ([FRAMES[1]] if consumer == "overrun" else [])
    for start, edges in zip(starts, sample_edges, strict=True):
        # Account for the common transport delay of the two synchronizer flops.
        assert all((SCALE * (cycle - 2) - start) // sender_bit == symbol
                   for symbol, cycle in enumerate(edges))
    return traffic, expected, {"sender_bit_units": sender_bit, "start_phase_units": phase,
                               "consumer": consumer, "samples": sample_edges,
                               "delivered": delivered, "dropped": dropped}


def fixture():
    traffic, trace, scenarios = [], [], []
    for parameters in product((118, 120, 126), (0, 1, 15), ("drain", "replace", "overrun")):
        inputs, outputs, summary = case(*parameters)
        scenarios.append({"first_edge": len(traffic), **summary})
        traffic.extend(inputs)
        trace.extend(outputs)
    trace[0][0] = None
    return traffic, trace, scenarios


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/fractional-uart-rx", args.tag)
    report = {"schema": 1, "status": "running", "commands": [],
              "boundary": "Two-state synchronous RTL under the Yosys JSON interpretation."}
    run = checks.cad.Commands(out, report["commands"])
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, tool_paths = checks.tool_config()
        report["tool_manifest"] = manifest
        report["tool_sha256"] = checks.cad.tool_hashes(tool_paths)
        run(["lake", "--no-cache", "build", MODULE, "Pinwheel.UART.FractionalTiming",
             "Pinwheel.Hardware.Artifact", "Pinwheel.Hardware.Readback.Boolean"], "lean-build")
        directory = out / "uart"
        directory.mkdir()
        traffic, trace, report["scenarios"] = fixture()
        report["replay_cycles"] = len(traffic)
        (directory / "traffic.json").write_text(json.dumps(traffic) + "\n")
        (directory / "oracle-trace.json").write_text(json.dumps(trace) + "\n")
        run(["lake", "env", "lean", "-DwarningAsError=true", "--run", EMITTER, directory], "emit-and-simulate")
        seen = json.loads((directory / "lean-trace.json").read_text())
        for cycle, (actual, expected) in enumerate(zip(seen, trace, strict=True)):
            if actual != expected:
                raise ValueError(f"Lean edge {cycle}: saw {actual}, expected {expected}")
        descriptor = json.loads((directory / "interface.json").read_text())
        leaves = hierarchy.lower_leaves(run, tools, directory, descriptor)
        flat = hierarchy.import_assembly(run, tools, directory, descriptor, leaves, normalize_muxes=True)
        tb, replay = directory / "tb.sv", directory / "replay.vvp"
        tb.write_text(checks.testbench(descriptor, traffic, trace))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", replay, directory / "hierarchical.sv", tb],
            "compile-replay")
        if run([tools["vvp"], replay], "replay").strip() != "Artifact replay passed":
            raise ValueError("Missing completed replay marker")
        profile = PROFILE + f"abbrev assembly := {MODULE}.hierarchy 6\n"
        modules, report["rtl"] = readback.generate(directory, flat, directory / "flat.mlir",
                                                  directory / "import.json", tools["z3"], profile=profile,
                                                  interface_checks=hierarchy.path_checks(descriptor, "assembly"))
        compile_modules(run, directory, modules)
        if "standard axioms only" not in (directory / "Audit.log").read_text():
            raise RuntimeError("Missing RTL proof audit marker")
        if report["source_sha256"] != source_hashes() or report["tool_sha256"] != checks.cad.tool_hashes(tool_paths):
            raise RuntimeError("Source or tool drift during validation")
        report["status"] = "passed"
    except BaseException as error:
        report.update(status="failed", error=str(error))
        raise
    finally:
        report["artifact_sha256"] = {str(path.relative_to(out)): sha(path)
                                     for path in sorted(out.rglob("*")) if path.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
