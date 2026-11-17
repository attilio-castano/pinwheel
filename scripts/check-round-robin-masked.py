#!/usr/bin/env python3
"""Fresh matched comparison of proved masked selectors, rotated trees and baseline.

Reuses the frozen baseline runner's synthesis, exhaustive simulation and SAT
checks. All three implementations are generated again for each fresh tag.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "round_robin_baseline_validation", ROOT / "scripts/check-round-robin-baseline.py")
baseline = importlib.util.module_from_spec(spec)
spec.loader.exec_module(baseline)
rr = baseline.rr


def source_hashes():
    result = baseline.source_hashes()
    pending = [ROOT / "test/RoundRobinMasked.lean"]
    while pending:
        path = pending.pop()
        name = str(path.relative_to(ROOT))
        if name in result:
            continue
        result[name] = rr.sha(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for module in match[1].split("--", 1)[0].split():
                    if module == "Pinwheel" or module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    result[str(Path(__file__).resolve().relative_to(ROOT))] = rr.sha(__file__)
    return dict(sorted(result.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = rr.fresh_directory(ROOT / "build/round-robin-masked", args.tag)
    records = []
    run = rr.Commands(out, records)
    started = time.monotonic()
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "boundary": "Universal Lean value-selection proof and standard-axiom audit; exhaustive "
                          "binary RTL simulation and Yosys SAT equivalence under legal one-hot cursors "
                          "before and after generic synthesis. Fresh rotated/masked/handwritten two-pass "
                          "comparison uses the same tools and settings. No kernel-certified RTL "
                          "interpretation, physical area/timing, switch integration or fairness claim.",
              "synthesis_settings": "Reuses frozen check-round-robin-baseline.py's common generic "
                                    "synthesis function without a cell library.",
              "tool_hash_scope": "Selected launchers, executables, ABC and Icarus backend; "
                                 "not a complete host dynamic-library closure."}
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, tool_paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(tool_paths)
        report["comparator_mutations_rejected"] = rr.checker_self_test()
        run(["lake", "env", "lean", "--version"], "lean-version")
        run([tools["circt"], "--version"], "circt-version")
        run([tools["iverilog"], "-V"], "iverilog-version")
        run([tools["yosys"], "-V"], "yosys-version")
        run(["lake", "build", "Pinwheel.Hardware.Arbitration.RoundRobinMasked", "Pinwheel.Hardware.Emit"],
            "build", timeout=900)
        directories = {name: out / name for name in ("rotated", "masked")}
        for name, directory in directories.items():
            directory.mkdir()
            emitted = directory / "emitted"
            emitted.mkdir()
            test = "RoundRobinCircuit" if name == "rotated" else "RoundRobinMasked"
            text = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", f"test/{test}.lean", emitted],
                       name + "-audit-and-emit")
            if "standard axioms only" not in text or "2306 exhaustive selections" not in text:
                raise AssertionError(f"Missing {name} structural audit/exhaustive test receipt")
        report["lean_structural_cases_per_selector"] = 2306
        report["lean_masked_value_width"] = 17
        for count in rr.COUNTS:
            results = {}
            for name, directory in directories.items():
                def prefixed(command, label, timeout=300):
                    return run(command, name + "-" + label, timeout)
                results[name] = baseline.configuration(prefixed, directory, directory / "emitted", tools, count)
            old, new = results["rotated"], results["masked"]
            if old["baseline"] != new["baseline"]:
                raise AssertionError("Repeated matched baseline produced inconsistent resource/coverage results")
            old_cells, new_cells, base_cells = (old["generated"]["generic_cells"],
                                                new["generated"]["generic_cells"],
                                                new["baseline"]["generic_cells"])
            report["configurations"].append({
                "request_count": count, "rotated": old, "masked": new,
                "masked_minus_rotated_cells": new_cells - old_cells,
                "masked_minus_baseline_cells": new_cells - base_cells})
            print(f"MATCHED N={count}: rotated={old_cells}, masked={new_cells}, baseline={base_cells}", flush=True)
        if source_hashes() != report["source_sha256"]:
            raise RuntimeError("Owning sources changed during validation; use a fresh tag")
        if rr.tool_hashes(tool_paths) != report["tool_sha256"]:
            raise RuntimeError("Selected tools changed during validation; use a fresh tag")
        report["masked_cell_regressions_vs_baseline"] = [
            row["request_count"] for row in report["configurations"] if row["masked_minus_baseline_cells"] > 0]
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["artifact_sha256"] = {str(path.relative_to(out)): rr.sha(path)
                                     for path in sorted(out.rglob("*")) if path.is_file()}
        report["seconds"] = round(time.monotonic() - started, 3)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
