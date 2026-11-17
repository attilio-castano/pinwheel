#!/usr/bin/env python3
"""Compare a conventional host accelerator with the frozen Lean RTL campaign."""
from __future__ import annotations

import argparse
from collections import Counter
import copy
import importlib.util
import json
from pathlib import Path
import re
import shutil
import time

import transfer_host_baseline as baseline
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("host_baseline_checks", ROOT / "scripts/check-memory-transfer-host.py")
host = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(host)
rr = host.rr
MATRIX = host.MATRIX


def sources():
    result = host.source_hashes()
    result.update({name: sha(ROOT / name) for name in (
        "scripts/transfer_host_baseline.py", "scripts/check-memory-transfer-host-baseline.py",
        "test/test_transfer_host_baseline.py")})
    return dict(sorted(result.items()))


def contained(base, name):
    path = (base / name).resolve()
    if not path.is_relative_to(base.resolve()):
        raise ValueError("Receipt artifact leaves its directory: " + name)
    return path


def verify_positive(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != host.source_hashes() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed host RTL receipt matching current sources and selected tools")
    configurations = [tuple(c["configuration"]) for c in report.get("configurations", [])]
    if configurations != MATRIX:
        raise ValueError("Positive receipt does not cover the exact matched matrix")
    hashes = report.get("artifact_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("Positive receipt has no artifact identities")
    for name, expected in hashes.items():
        if sha(contained(receipt.parent, name)) != expected:
            raise ValueError("Positive artifact changed: " + name)
    for config in MATRIX:
        label = "host-"+"-".join(map(str, config))
        for filename in ("transfer-host.sv", "interface.json", "startup.json", "stimulus.jsonl", "expected.json",
                         "lean.jsonl", "events.json", "ledger.json", "synth.v", "synth.json", "phase3-expected.json"):
            if f"{label}/{filename}" not in hashes:
                raise ValueError("Positive receipt omits required artifact: " + filename)
    return report


def testbench(data, startup, rows, registers):
    text = host.testbench(data, startup, rows, registers)
    if registers:
        # Icarus does not support force/release of an unpacked array word.
        # Direct hierarchical assignments establish only this simulation's
        # arbitrary startup; neither RTL design contains initialization code.
        text = text.replace("force dut.", "dut.")
        text = re.sub(r"^release dut\.[^;]+;\n", "", text, flags=re.M)
    return text


def depth(run, tools, directory, netjson, top, label):
    script = directory / (label+"-depth.ys")
    # Use the exact mapped cell graph, without reparsing behavioral FF blocks
    # from write_verilog or introducing a second optimization flow.
    script.write_text(f"read_json {rr.yosys_quote(netjson)}\nhierarchy -check -top {top}\nltp -noff\n")
    output = run([tools["yosys"], "-Q", "-T", "-s", script], directory.name+"-"+label+"-depth")
    matches = re.findall(r"longest topological path in [^\n]*?\(length=(\d+)\)", output, re.I)
    if len(matches) != 1:
        raise AssertionError("Expected exactly one combinational logic depth result")
    return int(matches[0])


def configuration(run, tools, out, positive_root, positive_entry):
    a, wi, wo = positive_entry["configuration"]
    label = f"host-{a}-{wi}-{wo}"
    original, directory = positive_root / label, out / label
    directory.mkdir()
    for old, new in (("transfer-host.sv", "source.sv"), ("lean.jsonl", "oracle-trace.jsonl"),
                     *((name, name) for name in ("interface.json", "startup.json", "stimulus.jsonl", "expected.json",
                                                 "events.json", "ledger.json")),
                     ("synth.v", "source-synth.v"), ("synth.json", "source-synth.json")):
        shutil.copyfile(original / old, directory / new)
    data = json.loads((directory / "interface.json").read_text())
    host.validate_descriptor(data, a, wi, wo)
    startup = json.loads((directory / "startup.json").read_text())
    rows = [json.loads(line) for line in (directory / "stimulus.jsonl").read_text().splitlines()]
    frames = json.loads((directory / "expected.json").read_text())
    if [json.loads(line) for line in (directory / "oracle-trace.jsonl").read_text().splitlines()] != frames:
        raise AssertionError("Frozen oracle and Lean trace differ")
    if len(rows) != len(frames) or len(rows) != positive_entry["edges_per_form"] or not rows[0]["reset"]:
        raise AssertionError("Frozen baseline trace lacks its expected reset/length")
    rtl = directory / "baseline.sv"
    rtl.write_text(baseline.generate(a, wi, wo, data["module"]))
    internal = copy.deepcopy(data)
    for port, ref in zip(internal["registers"], baseline.register_references(a), strict=True):
        port["reference"] = ref
    (directory / "baseline-registers.json").write_text(json.dumps(internal["registers"], indent=2)+"\n")

    def simulate(source, stage, registers, *, traffic=rows, expectations=frames, negative=False):
        tb, executable = directory / (stage+"-tb.sv"), directory / (stage+".vvp")
        tb.write_text(testbench(internal if registers else data, startup, traffic, registers))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], label+"-"+stage+"-compile")
        trace = run([tools["vvp"], executable], label+"-"+stage+"-simulate")
        (directory / (stage+"-trace.txt")).write_text(trace)
        want = host.controller.expected(expectations, registers)
        try:
            host.memory.check_trace(trace, want)
        except AssertionError as error:
            if negative:
                host.controller.concrete_mismatch(trace, want)
                return str(error)
            raise
        if negative:
            raise AssertionError("Accepted actual baseline mutation: " + stage)

    simulate(rtl, "baseline-rtl", True)
    # Reuse the retained phase3 expectations, also independently bound by the
    # immutable positive artifact set, to cover reset-free raw recovery.
    recovery = json.loads((original / "phase3-expected.json").read_text())
    (directory / "phase3-expected.json").write_text(json.dumps(recovery, indent=2)+"\n")
    simulate(rtl, "baseline-phase3", True, traffic=[f["input"] for f in recovery], expectations=recovery)
    netlist, netjson, script = directory / "baseline-synth.v", directory / "baseline-synth.json", directory / "baseline-synth.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {data['module']}\n"
        f"synth -top {data['module']}\ncheck -assert\nwrite_json {rr.yosys_quote(netjson)}\n"
        f"write_verilog -noattr {rr.yosys_quote(netlist)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], label+"-baseline-synthesize")
    simulate(netlist, "baseline-synth", False)
    controls = []
    for name, text in baseline.mutations(rtl.read_text(), wi, wo):
        mutant = directory / (name+".sv")
        mutant.write_text(text)
        controls.append({"mutation": name, "rejection": simulate(mutant, name, True, negative=True)})
    baseline_module = json.loads(netjson.read_text())["modules"][data["module"]]
    baseline_cells = Counter(c["type"] for c in baseline_module["cells"].values())
    lean_module = json.loads((directory / "source-synth.json").read_text())["modules"][data["module"]]
    lean_cells = Counter(c["type"] for c in lean_module["cells"].values())
    if sum(lean_cells.values()) != positive_entry["generic_cells"] or dict(lean_cells) != positive_entry["cell_types"]:
        raise AssertionError("Frozen Lean cell report does not match its actual netlist")
    baseline_depth = depth(run, tools, directory, netjson, data["module"], "baseline")
    lean_depth = depth(run, tools, directory, directory / "source-synth.json", data["module"], "source")
    return {"configuration": [a, wi, wo], "edges_per_form": len(rows), "phase3_edges": len(recovery),
            "baseline_generic_cells": sum(baseline_cells.values()), "lean_generic_cells": sum(lean_cells.values()),
            "baseline_cell_types": dict(baseline_cells), "lean_cell_types": dict(lean_cells),
            "baseline_logic_depth": baseline_depth, "lean_logic_depth": lean_depth,
            "rtl_mutations_rejected": controls,
            "flow": "identical Yosys synth -top; mapped generic primitives; ltp -noff counts combinational cells"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer-host-baseline", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Independent conventional SystemVerilog baseline checked against frozen host oracle traffic, "
                    "every unsynthesized state/output and synthesized outputs. Matching generic synthesis and logic-depth "
                    "comparison; no technology timing/area, physical qualification, or baseline kernel proof."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        receipt = args.positive_report.resolve()
        positive = verify_positive(receipt, report["tool_sha256"])
        report["positive_receipt"] = {"path": str(receipt), "sha256": sha(receipt)}
        shutil.copyfile(receipt, out / "positive-report.json")
        run(["python3", "test/test_transfer_host_baseline.py"], "baseline-generator-tests")
        for entry in positive["configurations"]:
            report["configurations"].append(configuration(run, tools, out, receipt.parent, entry))
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during matched baseline validation")
        verify_positive(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_receipt"]["sha256"]:
            raise RuntimeError("Frozen positive receipt changed during baseline validation")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic()-started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
