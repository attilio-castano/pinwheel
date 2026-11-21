#!/usr/bin/env python3
"""Compare an isolated proved shared-selection switch to both frozen references.

State layout and FIFO/control wiring match the existing structural switch. The
independent conventional SystemVerilog baseline is rerun with the same tools.
All three implementations consume the same directed/seeded cycle campaign.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("shared_switch_metrics", ROOT / "scripts/check-switch-baseline.py")
metrics = importlib.util.module_from_spec(spec)
spec.loader.exec_module(metrics)
sw, rr = metrics.sw, metrics.rr


def source_hashes():
    result = metrics.source_hashes()
    pending = [ROOT / "test/SwitchSharedSelectionEmit.lean"]
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
                    if module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    result["scripts/check-switch-shared-selection.py"] = rr.sha(Path(__file__))
    return dict(sorted(result.items()))


def configuration(run, out, tools, config, random_edges):
    references = metrics.configuration(run, out, tools, config, random_edges)
    ni, no, depth, width = config
    label = f"i{ni}-o{no}-d{depth}-w{width}"
    original_dir = out / label
    original = sw.descriptor(original_dir / "interface.json", config)
    directory = out / (label + "-shared")
    directory.mkdir()
    audit = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/SwitchSharedSelectionEmit.lean",
                 *config, directory], label + "-shared-emit")
    if "Shared switch audit:" not in audit or "standard axioms only" not in audit:
        raise AssertionError("Missing candidate standard-axiom audit")
    data = sw.descriptor(directory / "interface.json", config)
    if {k: v for k, v in data.items() if k != "module"} != \
            {k: v for k, v in original.items() if k != "module"}:
        raise AssertionError("Candidate changed typed ports, register layout, reset or role metadata")
    rows, _ = sw.traffic(config, random_edges)
    _, _, frames = sw.expected_frames(data, rows, config)
    sw.model_checks.json_lines(directory / "oracle-trace.jsonl", frames)
    # The original replay was compared to these exact frames, including every
    # post-edge register. Both RTL forms now consume the same stimulus objects.
    original_frames = [json.loads(line) for line in (original_dir / "oracle-trace.jsonl").read_text().splitlines()]
    if original_frames != frames:
        raise AssertionError("Reference and candidate expected traces diverged")
    rtl = directory / "switch.sv"
    rtl.write_text(run([tools["circt"], directory / "switch.mlir", "--canonicalize", "--lower-seq-to-sv",
                        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"],
                       label + "-shared-export"))

    def simulate(source, stage, registers, negative=False):
        tb, executable = directory / (stage + "-tb.sv"), directory / (stage + ".vvp")
        tb.write_text(sw.testbench(data, rows, registers))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb],
            label + "-shared-" + stage + "-compile")
        text = run([tools["vvp"], executable], label + "-shared-" + stage + "-simulate")
        (directory / (stage + "-trace.txt")).write_text(text)
        try:
            edges = sw.check_rtl_trace(text, frames, registers)
        except AssertionError as error:
            if negative and str(error).startswith("RTL mismatch"):
                return {"detected": True, "reason": str(error), "source_sha256": rr.sha(source)}
            raise
        if negative:
            raise AssertionError(f"Intentional candidate RTL mutation {stage} escaped validation")
        return edges

    rtl_edges = simulate(rtl, "rtl", True)
    script = directory / "synth.ys"
    script.write_text(metrics.synthesis_script(rtl, data["module"], directory))
    run([tools["yosys"], "-Q", "-s", script], label + "-shared-synth")
    resources = metrics.resources(directory, data["module"])
    gate_edges = simulate(directory / "gates.sv", "gates", False)
    negatives = {}
    for mutation in ("drop_ready", "ignore_reset") + (("wrong_route",) if no > 1 else ()):
        altered = directory / (mutation + ".sv")
        altered.write_text(sw.mutate_rtl(rtl.read_text(), data, mutation))
        negatives[mutation] = simulate(altered, mutation, True, negative=True)
    original_stats, baseline_stats = references["generated"], references["baseline"]
    result = {"configuration": config, "edges_per_implementation_per_form": len(rows),
              "original": original_stats, "baseline": baseline_stats,
              "shared": dict(resources, rtl_edges=rtl_edges, synthesized_edges=gate_edges),
              "shared_minus_original_cells": resources["generic_cells"] - original_stats["generic_cells"],
              "shared_minus_baseline_cells": resources["generic_cells"] - baseline_stats["generic_cells"],
              "shared_minus_original_levels": resources["logic_depth"]["max_combinational_cell_levels"] -
                  original_stats["logic_depth"]["max_combinational_cell_levels"],
              "same_source_register_layout": True,
              "shared_register_bits_minus_original": resources["logic_depth"]["register_bits"] -
                  original_stats["logic_depth"]["register_bits"],
              "reset_coverage": references["reset_coverage"], "coverage": references["coverage"],
              "accounting": references["accounting"],
              "original_rtl_negative_controls": references["generated_rtl_negative_controls"],
              "shared_rtl_negative_controls": negatives}
    (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"SHARED {config}: cells original/shared/baseline="
          f"{original_stats['generic_cells']}/{resources['generic_cells']}/{baseline_stats['generic_cells']}; "
          f"levels={original_stats['logic_depth']['max_combinational_cell_levels']}/"
          f"{resources['logic_depth']['max_combinational_cell_levels']}/"
          f"{baseline_stats['logic_depth']['max_combinational_cell_levels']}", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", type=sw.model_checks.parse_config)
    parser.add_argument("--random-edges", type=int, default=384)
    args = parser.parse_args()
    configs = args.config or sw.MATRIX
    if args.random_edges < 0 or len(configs) != len(set(configs)):
        parser.error("Use nonnegative random edges and distinct configurations")
    out = rr.fresh_directory(ROOT / "build/switch-shared-selection", args.tag)
    started, records = time.monotonic(), []
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "boundary": "Universal Lean candidate step/output equality with the original for legal one-hot "
                          "cursors; arbitrary-state reset recovery; inherited physical implementation/trace refinement. "
                          "Fresh finite RTL simulation checks all outputs pre/post and every post-edge register "
                          "in unsynthesized original/candidate RTL; synthesized outputs checked from reset. "
                          "Independent conventional baseline and deque/occurrence oracle rerun. No candidate RTL "
                          "kernel artifact certificate, physical area, timing or fabrication claim.",
              "synthesis_settings": "Same read_verilog -sv; hierarchy -check; synth generic ABC; check -assert; "
                                    "stat -json. Unit-cost cell depth excludes clock endpoints and cuts at flip-flops.",
              "tool_hash_scope": "Selected launchers, executables, ABC and Icarus backend; "
                                 "not complete host dynamic-library closure."}
    run = rr.Commands(out, records)
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        report["trace_mutations_rejected"] = sw.checker_self_test()
        run(["lake", "build", "Pinwheel.Hardware.Switch.SharedSelectionCandidate", "Pinwheel.Hardware.Emit"],
            "build", timeout=900)
        for pattern, label in (("test_switch_oracle.py", "oracle-tests"), ("test_switch_baseline.py", "depth-metric-tests")):
            run([sys.executable, "-B", "-m", "unittest", "discover", "-s", "test", "-p", pattern, "-v"], label)
        audit_file = out / "ProofAudit.lean"
        audit_file.write_text(sw.audit_source())
        if "standard axioms only" not in run(["lake", "env", "lean", "-DwarningAsError=true", audit_file],
                                              "original-proof-audit"):
            raise AssertionError("Missing original circuit proof audit")
        for config in configs:
            report["configurations"].append(configuration(run, out, tools, config, args.random_edges))
        if source_hashes() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during validation; use a fresh tag")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): rr.sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
