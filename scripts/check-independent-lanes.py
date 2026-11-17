#!/usr/bin/env python3
"""Build the standalone lane client, replay both implementations, and certify their RTL."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path

import typed_circuit_readback as readback
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
CLIENT = ROOT / "examples/independent-lanes"
EMITTER = CLIENT / "EmitAndSimulate.lean"
spec = importlib.util.spec_from_file_location(
    "hardware_tools", ROOT / "scripts/check-round-robin-circuit.py"
)
cad = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cad)

DEFAULT_CONFIGS = ((3, 17, 1), (2, 8, 2))
FIFO_DEPTH = 3


def source_hashes():
    paths = {
        *readback.source_paths(),
        Path(__file__).resolve(),
        ROOT / "lean-toolchain",
        ROOT / "lakefile.toml",
        ROOT / "lake-manifest.json",
        ROOT / "scripts/check-round-robin-circuit.py",
        ROOT / "scripts/validation_run.py",
        ROOT / "tools/hardware-toolchain.json",
        CLIENT / "lean-toolchain",
        CLIENT / "lakefile.toml",
        CLIENT / "lake-manifest.json",
        EMITTER,
    }
    pending = [CLIENT / "LaneClient.lean"]
    while pending:
        path = pending.pop()
        if path in paths:
            continue
        paths.add(path)
        for line in path.read_text().splitlines():
            if line.startswith("import Pinwheel."):
                module = line.split()[1]
                pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def observe(queue, stages, reset, downstream):
    """Return the external pins and each stage's replacement permission."""
    can_replace = [False] * len(stages)
    ready = downstream
    for k in reversed(range(len(stages))):
        ready = stages[k] is None or ready
        can_replace[k] = ready
    pop = bool(queue) and can_replace[0]
    tail = stages[-1]
    pins = (
        [0, 0, 0] if reset
        else [int(len(queue) - pop < FIFO_DEPTH), int(tail is not None), tail or 0]
    )
    return pins, pop, can_replace


def fixture(count, width, extra):
    """An integer FIFO and an array of optional words model the pins independently."""
    mask = (1 << width) - 1
    queues = [[] for _ in range(count)]
    pipelines = [[None] * (extra + 1) for _ in range(count)]
    held = [False] * count
    coverage = [
        dict(accepted=0, emitted=0, stalled=0, full_replacement=0, cancelled=0, wrapped=0)
        for _ in range(count)
    ]
    inputs, expected = [], []
    fill = extra + FIFO_DEPTH + 6
    refreeze = 2 * fill + 5
    resume = refreeze + fill + 2 * count
    drain = resume + 24
    for cycle in range(drain + extra + FIFO_DEPTH + 3):
        row, before, after = [], [], []
        for lane in range(count):
            queue, stages, stats = queues[lane], pipelines[lane], coverage[lane]
            reset = cycle == 0 or cycle == refreeze + fill + 2 * lane
            valid = 0 < cycle < drain or held[lane]
            downstream = fill <= cycle < refreeze or (
                cycle >= resume and (cycle >= drain or (cycle + lane) % 4 != 0)
            )
            payload = (mask + stats["accepted"] * (2 * lane + 1)) & mask
            row.extend((int(reset), int(valid), int(downstream), payload))
            pins, pop, can_replace = observe(queue, stages, reset, downstream)
            before.extend(pins)
            if reset:
                stats["cancelled"] += len(queue) + sum(word is not None for word in stages)
                held[lane] = False
                queue = []
                stages = [None] * len(stages)
            else:
                accepted = valid and pins[0]
                emitted = bool(pins[1]) and downstream
                held[lane] = valid and not accepted
                stats["emitted"] += int(emitted)
                stats["stalled"] += int(bool(pins[1]) and not downstream)
                stats["full_replacement"] += int(accepted and pop and len(queue) == FIFO_DEPTH)
                stats["wrapped"] += int(emitted and pins[2] == 0)
                head = queue[0] if queue else None
                upstream = [None if head is None else (head + 1) & mask, *stages[:-1]]
                stages = [new if take else old for new, take, old in zip(upstream, can_replace, stages, strict=True)]
                if pop:
                    queue.pop(0)
                if accepted:
                    queue.append(payload)
                    stats["accepted"] += 1
            queues[lane], pipelines[lane] = queue, stages
            after.extend(observe(queue, stages, reset, downstream)[0])
        inputs.append(row)
        # The first active edge establishes reset. Compare its post-edge pins,
        # then compare both observations on every subsequent edge.
        expected.append([before if cycle else None, after])
    for queue, stages, pending, stats in zip(queues, pipelines, held, coverage, strict=True):
        if queue or pending or any(word is not None for word in stages):
            raise AssertionError("The fixture must drain every lane")
        if not all(stats.values()) or stats["accepted"] != stats["emitted"] + stats["cancelled"]:
            raise AssertionError(f"Incomplete lane traffic coverage: {stats}")
    return inputs, expected, coverage


def testbench(descriptor, traffic, expected):
    ins, outs = descriptor["inputs"], descriptor["outputs"]
    lines = ["`timescale 1ns/1ps", "module tb;", "reg clk = 0;"]
    for kind, ports in (("reg", ins), ("wire", outs)):
        lines.extend(f"{kind} [{p['width'] - 1}:0] {p['name']};" for p in ports)
    connections = ", ".join(f".{p['name']}({p['name']})" for p in ins + outs)
    lines.extend([f"{descriptor['module']} dut(.clk(clk), {connections});", "initial begin"])
    for cycle, (row, edge) in enumerate(zip(traffic, expected, strict=True)):
        for p, value in zip(ins, row, strict=True):
            lines.append(f"  {p['name']} = {p['width']}'d{value};")
        lines.append("  #1;")
        for phase, values in zip(("before", "after"), edge, strict=True):
            if phase == "after":
                lines.append("  clk = 1; #1;")
            if values is not None:
                for p, value in zip(outs, values, strict=True):
                    name = p["name"]
                    lines.append(
                        f"  if ({name} !== {p['width']}'d{value}) "
                        f'$fatal(1, "cycle {cycle} {phase} {name}: expected {value}, got %0h", {name});'
                    )
        lines.append("  clk = 0; #1;")
    lines.extend(['  $display("Lane replay passed");', "end", "endmodule"])
    return "\n".join(lines) + "\n"


def profile(count, width, extra, backend):
    circular = "true" if backend == "circular" else "false"
    return f"""import LaneClient
abbrev laneCount := {count}
abbrev wordWidth := {width}
abbrev extraStages := {extra}
abbrev fifo := LaneClient.selectFifo wordWidth {circular}
abbrev Input := LaneClient.Input laneCount wordWidth
abbrev Output := LaneClient.Output laneCount wordWidth
abbrev Register := LaneClient.Register laneCount fifo extraStages
abbrev circuit := LaneClient.circuit laneCount fifo extraStages
abbrev inputs := LaneClient.inputs laneCount wordWidth
abbrev outputs := LaneClient.outputs laneCount wordWidth
abbrev registers := LaneClient.registers laneCount fifo extraStages
"""


INITIALIZED = """import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact

theorem initialized_trace (s : Values Register) (i : Values Input)
    (resetAll : ∀ k, i (.at k Stream.reset) = 1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (LaneClient.model laneCount wordWidth 3 extraStages).trace
        (LaneClient.empty laneCount wordWidth extraStages) traffic := by
  rw [correspondence.refinement.trace_eq _ _ rfl, correspondence.step_eq]
  exact LaneClient.initialized_trace laneCount fifo extraStages s i resetAll traffic

end Pinwheel.TypedArtifact
"""


def verify(run, tools, out, config, backend):
    count, width, extra = config
    label = f"{count}x{width}-extra{extra}-{backend}"
    directory = out / label
    directory.mkdir()
    traffic, expected, coverage = fixture(*config)
    (directory / "traffic.json").write_text(json.dumps(traffic) + "\n")
    (directory / "oracle-trace.json").write_text(json.dumps(expected) + "\n")
    run(["lake", "-d", CLIENT, "env", "lean", "-DwarningAsError=true", "--run", EMITTER,
         count, width, extra, backend, directory], label + "-lean")
    actual = json.loads((directory / "lean-trace.json").read_text())
    if actual != expected:
        if len(actual) != len(expected):
            raise ValueError(f"{label}: Lean trace length differs")
        for cycle, (seen, wanted) in enumerate(zip(actual, expected, strict=True)):
            if seen != wanted:
                raise ValueError(f"{label}: cycle {cycle}: Lean {seen}, expected {wanted}")

    descriptor = json.loads((directory / "interface.json").read_text())
    readback.validate_descriptor(descriptor)
    mlir, rtl = directory / "lanes.mlir", directory / "lanes.sv"
    rtl.write_text(run([tools["circt"], mlir, "--lower-seq-to-sv", "--lower-hw-to-sv",
                        "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label + "-lower"))
    tb, replay = directory / "tb.sv", directory / "replay.vvp"
    tb.write_text(testbench(descriptor, traffic, expected))
    run([tools["iverilog"], "-g2012", "-s", "tb", "-o", replay, rtl, tb], label + "-compile-replay")
    if run([tools["vvp"], replay], label + "-replay").strip() != "Lane replay passed":
        raise ValueError(f"{label}: missing completed replay marker")

    script, imported = directory / "import.ys", directory / "import.json"
    script.write_text(
        f"read_verilog -sv {cad.yosys_quote(rtl)}\nhierarchy -check -top {descriptor['module']}\n"
        f"proc\npmuxtree\nopt_clean\ncheck -assert\nwrite_json {cad.yosys_quote(imported)}\n"
    )
    run([tools["yosys"], "-Q", "-T", "-s", script], label + "-import")
    modules, evidence = readback.generate(
        directory, descriptor, mlir, imported, tools["z3"], profile=profile(*config, backend)
    )
    (directory / "Initialized.lean").write_text(INITIALIZED)
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import Initialized"))
    modules.insert(-1, "Initialized")
    compile_modules(run, directory, modules, extra_lean_paths=(CLIENT / ".lake/build/lib/lean",))
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise RuntimeError(f"{label}: missing Lean axiom audit")
    return {
        **evidence,
        "label": label,
        "configuration": config,
        "backend": backend,
        "registers": len(descriptor["registers"]),
        "outputs": len(descriptor["outputs"]),
        "initialized_trace_checked": True,
        "replay_cycles": len(traffic),
        "replay_output_values": (2 * len(traffic) - 1) * len(descriptor["outputs"]),
        "coverage_by_lane": coverage,
    }


def configuration(text):
    try:
        lanes, width, extra = map(int, text.split(","))
    except ValueError as error:
        raise argparse.ArgumentTypeError("Use LANES,WIDTH,EXTRA") from error
    if lanes < 1 or width < 1 or extra < 0:
        raise argparse.ArgumentTypeError("LANES and WIDTH must be positive and EXTRA nonnegative")
    return lanes, width, extra


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", type=configuration, metavar="LANES,WIDTH,EXTRA")
    args = parser.parse_args()
    configs = args.config or DEFAULT_CONFIGS
    if len(set(configs)) != len(configs):
        parser.error("Configurations must be distinct")

    out = fresh_directory(ROOT / "build/independent-lanes", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": []}
    run = cad.Commands(out, report["commands"])
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, tool_paths = cad.selected_tools()
        root = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = root / "bin/z3"
        tool_paths += [tools["z3"], root / "libexec/z3"]
        report["tool_manifest"] = manifest
        report["tool_sha256"] = cad.tool_hashes(tool_paths)
        run(["lake", "-d", CLIENT, "--no-cache", "build"], "client-build", timeout=900)
        run(["lake", "--no-cache", "build", "Pinwheel.Hardware.Readback.Boolean"], "readback-build", timeout=900)
        for config in configs:
            for backend in ("shift", "circular"):
                report["configurations"].append(verify(run, tools, out, config, backend))
        if report["source_sha256"] != source_hashes() or report["tool_sha256"] != cad.tool_hashes(tool_paths):
            raise RuntimeError("Source or tool drift during validation")
        report["status"] = "passed"
    except BaseException as error:
        report.update(status="failed", error=str(error))
        raise
    finally:
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
