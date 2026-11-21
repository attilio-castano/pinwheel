#!/usr/bin/env python3
"""Build the standalone lane client, replay both implementations, and certify their RTL."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import typed_module_checks as checks
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
CLIENT = ROOT / "examples/independent-lanes"
EMITTER = CLIENT / "EmitAndSimulate.lean"
DEFAULT_CONFIGS = ((3, 17, 1), (2, 8, 2))
FIFO_DEPTH = 3


def source_hashes():
    paths = {
        *checks.source_paths(),
        Path(__file__).resolve(),
        ROOT / "lean-toolchain",
        ROOT / "lakefile.toml",
        ROOT / "lake-manifest.json",
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


def profile(count, width, extra, backend):
    circular = "true" if backend == "circular" else "false"
    return checks.profile(
        "LaneClient", f"LaneClient.design laneCount wordWidth extraStages {circular}",
        bindings=f"""abbrev laneCount := {count}
abbrev wordWidth := {width}
abbrev extraStages := {extra}
abbrev fifo := LaneClient.selectFifo wordWidth {circular}
""",
    )


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

    evidence = checks.verify(
        run, tools, directory, "lanes", profile(*config, backend), INITIALIZED, traffic, expected,
        extra_lean_paths=(CLIENT / ".lake/build/lib/lean",),
        swap_outputs=(2, 5) if count >= 2 and backend == "shift" else None,
    )
    return {
        **evidence,
        "label": label,
        "configuration": config,
        "backend": backend,
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
    run = checks.cad.Commands(out, report["commands"])
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, tool_paths = checks.tool_config()
        report["tool_manifest"] = manifest
        report["tool_sha256"] = checks.cad.tool_hashes(tool_paths)
        run(["lake", "-d", CLIENT, "--no-cache", "build"], "client-build", timeout=900)
        run(["lake", "--no-cache", "build", "Pinwheel.Hardware.Readback.Boolean"], "readback-build", timeout=900)
        for config in configs:
            for backend in ("shift", "circular"):
                report["configurations"].append(verify(run, tools, out, config, backend))
        if report["source_sha256"] != source_hashes() or report["tool_sha256"] != checks.cad.tool_hashes(tool_paths):
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
