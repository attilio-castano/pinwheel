#!/usr/bin/env python3
"""Fresh-source packet-switch logical contracts and independent cycle replay.

This command does not emit or certify RTL and does not run synthesis. Its receipts
cover the executable Lean model, proofs, and independent Python validation only.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import random
import re
import sys
import time

import switch_oracle as oracle
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
MATRIX = ((1, 1, 1, 1), (1, 3, 1, 8), (3, 1, 1, 8), (2, 2, 2, 8),
          (3, 3, 3, 17), (5, 3, 2, 8), (3, 5, 3, 1), (4, 2, 8, 17),
          (2, 4, 3, 17), (5, 5, 1, 8), (4, 4, 8, 8))
LEAN_ROOTS = ("test/SwitchReplay.lean", "test/SwitchContracts.lean", "test/RoundRobin.lean", "test/SwitchModel.lean")


def source_hashes():
    """Hash the owning transitive local Lean imports, excluding unrelated campaigns."""
    pending = [ROOT / name for name in LEAN_ROOTS]
    sources = set()
    while pending:
        path = pending.pop()
        if path in sources:
            continue
        if not path.is_file():
            raise FileNotFoundError(f"Missing owning Lean source: {path}")
        sources.add(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if not match:
                continue
            for module in match[1].split("--", 1)[0].split():
                if module.startswith(("Pinwheel.", "test.")):
                    pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    sources.update(ROOT / name for name in (
        "lakefile.toml", "lean-toolchain", "lake-manifest.json", "scripts/check-switch-model.py",
        "scripts/switch_oracle.py", "scripts/validation_run.py", "scripts/process_group.py",
        "test/test_switch_oracle.py"))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(sources)}


def traffic(inputs, outputs, depth, width, seed=0x53574954):
    rng = random.Random(seed)
    mask = (1 << width) - 1
    rows, phases = [], []
    serial = 0

    def add(phase, destinations, ready, reset=False):
        nonlocal serial
        offers = []
        for source, destination in enumerate(destinations):
            offers.append(None if destination is None else
                          {"destination": destination, "payload": (serial * inputs + source) & mask})
        rows.append({"reset": reset, "offered": offers, "ready": list(ready)})
        phases.append(phase)
        serial += 1

    drain = inputs * depth + outputs + 3
    add("cold-reset", [None] * inputs, [False] * outputs, True)
    for _ in range(5):
        add("idle", [None] * inputs, [True] * outputs)
    for _ in range(4 * inputs + depth + 32):
        add("contention", [0] * inputs, [True] * outputs)
    for _ in range(drain):
        add("drain-contention", [None] * inputs, [True] * outputs)
    # Independent blocked outputs plus changing destinations expose HOL queues.
    for edge in range(3 * depth + 4 * inputs + 32):
        add("independent-stalls", [(edge + k) % outputs for k in range(inputs)],
            [o != 0 for o in range(outputs)])
    for edge in range(3 * depth + 4 * inputs + 32):
        add("opposite-stalls", [(edge + k) % outputs for k in range(inputs)],
            [o == 0 for o in range(outputs)])
    add("loaded-reset", [0] * inputs, [False] * outputs, True)
    for _ in range(depth + inputs + 8):
        add("fill", [0] * inputs, [False] * outputs)
    for _ in range(3 * inputs + depth + 16):
        add("full-replacement", [0] * inputs, [True] * outputs)
    for _ in range(900):
        destinations = [None if rng.randrange(3) == 0 else rng.randrange(outputs) for _ in range(inputs)]
        add("random", destinations, [bool(rng.randrange(2)) for _ in range(outputs)], rng.randrange(79) == 0)
    for _ in range(drain):
        add("final-drain", [None] * inputs, [True] * outputs)
    return rows, phases


def coverage(rows, frames, phases, inputs, outputs, depth):
    result = {"accepted_by_input": [0] * inputs, "emitted_by_output": [0] * outputs,
              "grants_by_input": [0] * inputs, "contended_refills": 0,
              "full_queue_replacements": 0, "independent_output_progress": 0,
              "head_of_line_blocked_cycles": 0, "stalled_output_cycles": 0,
              "simultaneous_output_transfers": 0, "cursor_wraps": 0,
              "reset_edges": 0, "max_queue_occupancy": 0, "phase_edges": {}}
    previous = {"queues": [[] for _ in range(inputs)], "slots": [None] * outputs,
                "cursor": [0] * outputs}
    for row, frame, phase in zip(rows, frames, phases, strict=True):
        result["phase_edges"][phase] = result["phase_edges"].get(phase, 0) + 1
        state, pre, grants = frame["state"], frame["pre"], frame["grants"]
        result["max_queue_occupancy"] = max(result["max_queue_occupancy"],
                                             *(len(q) for q in state["queues"]))
        if row["reset"]:
            result["reset_edges"] += 1
            previous = state
            continue
        stalled = [o for o in range(outputs) if previous["slots"][o] is not None and not row["ready"][o]]
        result["stalled_output_cycles"] += len(stalled)
        moving = [o for o in range(outputs) if grants[o] is not None]
        result["independent_output_progress"] += bool(stalled and moving)
        emitted = 0
        for o in range(outputs):
            if pre["offered"][o] is not None and row["ready"][o]:
                result["emitted_by_output"][o] += 1
                emitted += 1
            k = grants[o]
            if k is not None:
                result["grants_by_input"][k] += 1
                result["cursor_wraps"] += k == inputs - 1
                requests = sum(bool(q) and q[0]["destination"] == o for q in previous["queues"])
                result["contended_refills"] += requests > 1
        result["simultaneous_output_transfers"] += emitted > 1
        for k, queue in enumerate(previous["queues"]):
            if row["offered"][k] is not None and pre["ready"][k]:
                result["accepted_by_input"][k] += 1
                result["full_queue_replacements"] += len(queue) == depth and k in grants
            if queue and queue[0]["destination"] in stalled:
                result["head_of_line_blocked_cycles"] += any(
                    p["destination"] not in stalled and p["destination"] != queue[0]["destination"]
                    for p in queue[1:])
        previous = state
    if not all(result["accepted_by_input"]) or not all(result["emitted_by_output"]):
        raise AssertionError("Fixture did not exercise every external port")
    if not result["full_queue_replacements"]:
        raise AssertionError("Fixture did not exercise full-queue replacement")
    if inputs > 1 and (not result["contended_refills"] or not result["cursor_wraps"]):
        raise AssertionError("Fixture did not exercise contention and cursor wraparound")
    return result


def json_lines(path, rows):
    path.write_text("".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows))


def configuration(run, out, config):
    inputs, outputs, depth, width = config
    label = f"i{inputs}-o{outputs}-d{depth}-w{width}"
    directory = out / label
    directory.mkdir()
    rows, phases = traffic(*config)
    stimulus, trace = directory / "stimulus.jsonl", directory / "lean-trace.jsonl"
    json_lines(stimulus, rows)
    run([ROOT / ".lake/build/bin/switch_replay", *config, stimulus, trace], label + "-replay", timeout=180)
    frames = [json.loads(line) for line in trace.read_text().splitlines() if line]
    accounting = oracle.check_trace(rows, frames, inputs, outputs, depth, require_drained=True)
    covered = coverage(rows, frames, phases, inputs, outputs, depth)
    evidence = {"configuration": config, "edges": len(rows), "accounting": accounting,
                "coverage": covered, "stimulus_sha256": sha(stimulus), "trace_sha256": sha(trace)}
    (directory / "result.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"PASS switch model {config}: {len(rows)} edges; exact cycle replay and occurrence conservation", flush=True)
    return evidence


def parse_config(value):
    try:
        result = tuple(map(int, value.split(",")))
    except ValueError as error:
        raise argparse.ArgumentTypeError("Use INPUTS,OUTPUTS,DEPTH,WIDTH") from error
    if len(result) != 4 or any(n <= 0 for n in result):
        raise argparse.ArgumentTypeError("All four configuration parameters must be positive")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", type=parse_config,
                        help="INPUTS,OUTPUTS,DEPTH,WIDTH; default is the 11-fixture campaign matrix")
    args = parser.parse_args()
    configs = args.config or MATRIX
    if len(set(configs)) != len(configs):
        parser.error("Duplicate configurations are not allowed")
    out = fresh_directory(ROOT / "build/switch-model", args.tag)
    records = []
    run = Commands(ROOT, out, records, default_timeout=300)
    started = time.monotonic()
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "boundary": "Logical single-flit switch model with valid Fin destinations; no RTL emission, "
                          "RTL correspondence, synthesis, physical timing or fabrication evidence."}
    try:
        report["source_sha256"] = source_hashes()
        run(["lake", "build", "switch_replay", "Pinwheel.Hardware.Switch.Progress",
             "Pinwheel.Hardware.Switch.Certified"], "build")
        run(["lake", "env", "lean", "-DwarningAsError=true", "test/SwitchContracts.lean"], "switch-contracts")
        run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/RoundRobin.lean"], "round-robin")
        run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/SwitchModel.lean"], "switch-model-tests")
        run([sys.executable, "-B", "-m", "unittest", "discover", "-s", "test", "-p", "test_switch_oracle.py", "-v"],
            "oracle-tests")
        for config in configs:
            report["configurations"].append(configuration(run, out, config))
        if source_hashes() != report["source_sha256"]:
            raise RuntimeError("Owning sources changed during validation; preserve this receipt and use a fresh tag")
        report["executable_sha256"] = sha(ROOT / ".lake/build/bin/switch_replay")
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 3)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
