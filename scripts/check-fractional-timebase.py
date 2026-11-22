#!/usr/bin/env python3
"""Prove and replay one emitted TX image using programmable beat periods."""
from __future__ import annotations

import argparse
from bisect import bisect_left
import json
from pathlib import Path

import typed_module_checks as checks
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
EMITTER = ROOT / "test/FractionalTxEmit.lean"
IMAGE = 0xA6
TIMING = "Pinwheel.Hardware.Timebase.Tx"
DESIGN = checks.profile(TIMING, "Pinwheel.Hardware.Timebase.Tx.module 4")
INITIALIZED = """import Proof
open Pinwheel.Hardware Pinwheel.Hardware.Timebase
namespace Pinwheel.TypedArtifact

theorem initialized_trace (s : Values Register) (i : Values Input)
    (reset : i Tx.reset = 1#1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Tx.component 4).trace (fun {_} _ => 0) traffic := by
  rw [trace_eq, correspondence.step_eq]
  congr 1
  funext b r
  exact Tx.reset_eq i s reset r

theorem active_timing (p : Period) (i : Values Input) (s : Values Register)
    (unreset : i Tx.reset ≠ 1#1) (active : s Tx.remainingReg ≠ 0#4)
    (hp : (s Tx.numeratorReg).toNat = p.numerator) (hq : (s Tx.denominatorReg).toNat = p.denominator)
    (phase : (s Tx.phaseReg).toNat < p.numerator) :
    (rtlComponent.step i s Tx.phaseReg).toNat = advance p (s Tx.phaseReg).toNat ∧
      rtlComponent.observe i s Tx.completedBit = BitVec.ofBool (beat p (s Tx.phaseReg).toNat) := by
  rw [congrFun (congrFun (correspondence.step_eq i s) 5) Tx.phaseReg,
    congrFun (congrFun (correspondence.output_eq i s) 1) Tx.completedBit]
  exact Tx.active_timing p i s unreset active hp hq phase

end Pinwheel.TypedArtifact
"""


def source_hashes():
    paths = {*checks.source_paths(), Path(__file__).resolve(), ROOT / "lean-toolchain",
             ROOT / "lakefile.toml", ROOT / "lake-manifest.json"}
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


def fixture():
    idle = [0, 1, 0]
    traffic = [[1, 1, IMAGE, 8, 1]]
    expected = [[None, idle]]
    profile_windows = []

    def append(inputs, before, after):
        traffic.append(inputs)
        expected.append([before, after])

    for numerator, denominator in ((15, 0), (1, 2)):
        append([0, 1, IMAGE, numerator, denominator], idle, idle)

    for numerator, denominator in ((8, 1), (15, 2), (15, 14), (1, 1)):
        # Closing edges from the exact rational schedule. This oracle does not
        # model the hardware accumulator or its shifting register.
        closes = [(k * numerator + denominator - 1) // denominator for k in range(1, 9)]

        def observe(elapsed):
            bit = bisect_left(closes, elapsed)
            if bit == 8:
                return idle
            return [1, (IMAGE >> bit) & 1, int(closes[bit] == elapsed)]

        start = len(traffic)
        append([0, 1, IMAGE, numerator, denominator], idle, observe(1))
        for elapsed in range(1, closes[-1] + 1):
            # Request an incompatible image and rate while busy. This must not
            # change any active bit or the already-latched period.
            append([0, int(elapsed == 1), IMAGE ^ 0xff, 2, 1],
                   observe(elapsed), observe(elapsed + 1))
        append([0, 0, 0, 0, 0], idle, idle)
        profile_windows.append((numerator, denominator, start, closes))

    # Reset an in-flight frame before its first beat and return to idle.
    append([0, 1, IMAGE, 15, 2], idle, [1, IMAGE & 1, 0])
    append([1, 1, IMAGE, 15, 2], idle, idle)
    append([0, 0, 0, 0, 0], idle, idle)
    return traffic, expected, profile_windows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/fractional-timebase", args.tag)
    report = {
        "schema": 1, "status": "running", "commands": [],
        "boundary": "Two-state synchronous RTL under the Yosys JSON interpretation.",
    }
    run = checks.cad.Commands(out, report["commands"])
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, tool_paths = checks.tool_config()
        report["tool_manifest"] = manifest
        report["tool_sha256"] = checks.cad.tool_hashes(tool_paths)
        run(["lake", "--no-cache", "build", TIMING, "Pinwheel.Hardware.Artifact",
             "Pinwheel.Hardware.Readback.Boolean"], "lean-build")
        directory = out / "tx"
        directory.mkdir()
        traffic, expected, windows = fixture()
        (directory / "traffic.json").write_text(json.dumps(traffic) + "\n")
        (directory / "oracle-trace.json").write_text(json.dumps(expected) + "\n")
        run(["lake", "env", "lean", "-DwarningAsError=true", "--run", EMITTER, directory], "emit-and-simulate")
        actual = json.loads((directory / "lean-trace.json").read_text())
        for edge, (a, e) in enumerate(zip(actual, expected, strict=True)):
            if a != e:
                raise ValueError(f"Lean edge {edge}: saw {a}, expected {e}")
        report["rtl"] = checks.verify(run, tools, directory, "fractional_tx", DESIGN, INITIALIZED,
                                      traffic, expected, swap_outputs=(1, 2))
        report["profiles"] = []
        for numerator, denominator, start, closes in windows:
            observed = [(edge - start, actual[edge][0][1])
                        for edge in range(start + 1, start + closes[-1] + 1) if actual[edge][0][2]]
            report["profiles"].append({"numerator": numerator, "denominator": denominator,
                                       "image": IMAGE, "completed_edges": [edge for edge, _ in observed],
                                       "bits": [bit for _, bit in observed]})
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
