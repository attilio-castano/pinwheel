#!/usr/bin/env python3
"""Replay, certify and synthesize the 2x2 depth-three switch with both FIFO layouts."""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path

import typed_module_checks as checks
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
EMITTER = ROOT / "test/SwitchFifoEmit.lean"
CONFIG = (2, 2, 3, 4)


def helper(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


switch = helper("switch_checks", "check-switch-artifact.py")
model = helper("switch_traffic", "check-switch-model.py")


def source_hashes():
    hashes = switch.sources((str(EMITTER.relative_to(ROOT)),))
    for path in (*checks.source_paths(), Path(__file__).resolve(),
                 ROOT / "scripts/check-switch-model.py", ROOT / "scripts/switch_oracle.py"):
        hashes[str(path.relative_to(ROOT))] = sha(path)
    return hashes


def profile(kind):
    circular = "true" if kind == "circular" else "false"
    return checks.profile(
        "SwitchFifoEmit", f"SwitchFifoEmit.design {circular}",
        bindings=f"abbrev fifo := SwitchFifoEmit.fifo {circular}\n",
    )


TRACE = """import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
theorem initialized_trace (r : Values Register) (i : Values Input) (h : i Switch.Physical.reset = 1)
    (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i r) traffic =
      (Switch.Physical.component SwitchFifoEmit.encoding 3).trace Switch.initial traffic :=
  Switch.WithFifo.artifact_initialized_trace (w := 4) (depth := 3) SwitchFifoEmit.encoding fifo
    rtlComponent correspondence i r h traffic
end Pinwheel.TypedArtifact
"""


def fixtures(directory):
    ni, no, depth, width = CONFIG
    rows, _ = model.traffic(ni, no, depth, width)
    frames = model.oracle.simulate(rows, ni, no, depth)
    accounting = model.oracle.check_trace(rows, frames, ni, no, depth, require_drained=True)
    # Switch.Physical.In enumerates reset, input valids, destinations, payloads
    # and downstream readies. Out enumerates input readies, valids and payloads.
    traffic, expected = [], []
    for cycle, (row, frame) in enumerate(zip(rows, frames, strict=True)):
        offers = row["offered"]
        traffic.append([
            int(row["reset"]), *(int(p is not None) for p in offers),
            *(p["destination"] if p else 0 for p in offers),
            *(p["payload"] if p else 0 for p in offers), *map(int, row["ready"]),
        ])
        observations = []
        for phase in ("pre", "post"):
            observation = frame[phase]
            packets = observation["offered"]
            observations.append([
                *map(int, observation["ready"]), *(int(p is not None) for p in packets),
                *(p["payload"] if p else 0 for p in packets),
            ])
        expected.append([observations[0] if cycle else None, observations[1]])
    (directory / "traffic.json").write_text(json.dumps(traffic) + "\n")
    (directory / "oracle-trace.json").write_text(json.dumps(expected) + "\n")
    return traffic, expected, accounting


def configuration(run, tools, out, kind):
    directory = out / kind
    directory.mkdir()
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", EMITTER,
         kind, directory], kind + "-emit")
    traffic, expected, accounting = fixtures(directory)
    mapped = directory / "mapped.json"
    evidence = checks.verify(
        run, tools, directory, "switch", profile(kind), TRACE, traffic, expected,
        extra_lean_paths=(out,), swap_outputs=(4, 5) if kind == "shift" else None, mapped=mapped,
    )
    descriptor = json.loads((directory / "interface.json").read_text())
    name = descriptor["module"]
    cells = Counter(c["type"] for c in json.loads(mapped.read_text())["modules"][name]["cells"].values())
    return {
        **evidence,
        "rtl_state_bits": sum(p["width"] for p in descriptor["registers"]),
        "mapped_cells": cells.total(),
        "mapped_flip_flops": sum(v for k, v in cells.items() if "DFF" in k),
        "mapped_cell_types": dict(sorted(cells.items())),
        "replay_accounting": accounting,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/switch-fifo-backends", args.tag)
    report = {"status": "running", "commands": [], "configurations": {}}
    run = checks.cad.Commands(out, report["commands"])
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = checks.tool_config()
        report["tool_manifest"] = manifest
        report["tool_sha256"] = checks.cad.tool_hashes(paths)
        run(["lake", "--no-cache", "build", "Pinwheel.Hardware.Switch.Backend",
             "Pinwheel.Hardware.Stream.CircularFifo3", "Pinwheel.Hardware.TypedModule",
             "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        run(["lake", "env", "lean", "-DwarningAsError=true",
             "-o", out / "SwitchFifoEmit.olean", EMITTER], "build-switch-design")
        for kind in ("shift", "circular"):
            report["configurations"][kind] = configuration(run, tools, out, kind)
        if report["source_sha256"] != source_hashes() or report["tool_sha256"] != checks.cad.tool_hashes(paths):
            raise RuntimeError("Campaign inputs changed during run")
        report["status"] = "passed"
    except BaseException as error:
        report.update(status="failed", error=str(error))
        raise
    finally:
        report["artifact_sha256"] = {
            str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()
        }
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
