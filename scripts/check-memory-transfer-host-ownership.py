#!/usr/bin/env python3
"""Validate the proven phase-only ownership candidate on immutable host traffic."""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import shutil
import time

from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("host_ownership_baseline", ROOT / "scripts/check-memory-transfer-host-baseline.py")
baseline = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(baseline)
rr, host = baseline.rr, baseline.host
MATRIX = host.MATRIX


def sources():
    result = baseline.sources()
    pending = [ROOT / name for name in ("test/MemoryTransferHostOwnershipEmit.lean",
        "test/MemoryTransferHostOwnership.lean", "Pinwheel/Hardware/Memory/TransferHostOwnershipCandidate.lean")]
    paths = {ROOT / "scripts/check-memory-transfer-host-ownership.py"}
    while pending:
        path = pending.pop()
        if path in paths:
            continue
        paths.add(path)
        for line in path.read_text().splitlines():
            if match := re.match(r"^import\s+(.+)$", line):
                for module in match[1].split("--", 1)[0].split():
                    if module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    result.update({str(path.relative_to(ROOT)): sha(path) for path in paths})
    return dict(sorted(result.items()))


def verify_positive(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != baseline.sources() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed baseline matrix receipt matching current sources/tools")
    if [tuple(c["configuration"]) for c in report.get("configurations", [])] != MATRIX:
        raise ValueError("Baseline receipt must contain the complete ordered ownership matrix")
    hashes = report.get("artifact_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("Missing baseline artifact identities")
    for name, expected in hashes.items():
        if sha(baseline.contained(receipt.parent, name)) != expected:
            raise ValueError("Baseline artifact changed: " + name)
    for config in MATRIX:
        label = "host-"+"-".join(map(str, config))
        for filename in ("source.sv", "baseline.sv", "interface.json", "startup.json", "stimulus.jsonl",
                         "oracle-trace.jsonl", "expected.json", "events.json", "ledger.json", "phase3-expected.json",
                         "source-synth.v", "source-synth.json", "baseline-synth.v", "baseline-synth.json"):
            if f"{label}/{filename}" not in hashes:
                raise ValueError("Baseline receipt omits required checked artifact: " + filename)
    return report


def configuration(run, tools, out, positive_root, positive_entry):
    a, wi, wo = positive_entry["configuration"]
    label = f"host-{a}-{wi}-{wo}"
    original, directory = positive_root / label, out / label
    directory.mkdir()
    copies = [("source.sv", "reference.sv"), ("source-synth.v", "reference-synth.v"),
              ("source-synth.json", "reference-synth.json")]
    copies += [(name, name) for name in ("baseline.sv", "baseline-synth.v", "baseline-synth.json", "interface.json",
        "startup.json", "stimulus.jsonl", "oracle-trace.jsonl", "expected.json", "events.json", "ledger.json",
        "phase3-expected.json")]
    for source, target in copies:
        shutil.copyfile(original / source, directory / target)
    data = json.loads((directory / "interface.json").read_text())
    host.validate_descriptor(data, a, wi, wo)
    startup = json.loads((directory / "startup.json").read_text())
    rows = [json.loads(line) for line in (directory / "stimulus.jsonl").read_text().splitlines()]
    frames = json.loads((directory / "expected.json").read_text())
    if [json.loads(line) for line in (directory / "oracle-trace.jsonl").read_text().splitlines()] != frames:
        raise AssertionError("Frozen independent oracle and trace differ")
    if len(rows) != len(frames) or len(rows) != positive_entry["edges_per_form"] or not rows[0]["reset"]:
        raise AssertionError("Frozen ownership trace lacks expected reset/length")
    run(host.controller.lean_command(out, "--run", "test/MemoryTransferHostOwnershipEmit.lean", a, wi, wo, directory),
        label+"-emit")
    rtl = directory / "source.sv"
    rtl.write_text(run([tools["circt"], directory / "transfer-host.mlir", "--canonicalize", "--lower-seq-to-sv",
        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label+"-lower"))

    def simulate(source, stage, registers, *, traffic=rows, expectations=frames, negative=False):
        tb, executable = directory / (stage+"-tb.sv"), directory / (stage+".vvp")
        tb.write_text(host.testbench(data, startup, traffic, registers))
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
            raise AssertionError("Accepted actual ownership RTL mutation: " + stage)

    simulate(rtl, "rtl", True)
    recovery = json.loads((directory / "phase3-expected.json").read_text())
    simulate(rtl, "phase3", True, traffic=[f["input"] for f in recovery], expectations=recovery)
    netlist, netjson, script = directory / "synth.v", directory / "synth.json", directory / "synth.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {data['module']}\n"
        f"synth -top {data['module']}\ncheck -assert\nwrite_json {rr.yosys_quote(netjson)}\n"
        f"write_verilog -noattr {rr.yosys_quote(netlist)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], label+"-synthesize")
    simulate(netlist, "synth", False)
    controls = []
    for name, changed in host.mutations(rtl.read_text(), data):
        mutant = directory / (name+".sv")
        mutant.write_text(changed)
        controls.append({"mutation": name, "rejection": simulate(mutant, name, True, negative=True)})
    variants = {}
    for variant, filename, prefix in (("candidate", "synth.json", None),
                                      ("reference", "reference-synth.json", "lean"),
                                      ("baseline", "baseline-synth.json", "baseline")):
        graph = directory / filename
        module = json.loads(graph.read_text())["modules"][data["module"]]
        cells = Counter(cell["type"] for cell in module["cells"].values())
        level = baseline.depth(run, tools, directory, graph, data["module"], variant)
        if prefix is not None and (sum(cells.values()) != positive_entry[prefix+"_generic_cells"] or
                dict(cells) != positive_entry[prefix+"_cell_types"] or level != positive_entry[prefix+"_logic_depth"]):
            raise AssertionError("Retained reference/baseline comparison differs from its receipt")
        variants[variant] = {"generic_cells": sum(cells.values()), "cell_types": dict(cells), "logic_depth": level}
    return {"configuration": [a, wi, wo], "edges_per_form": len(rows), "phase3_edges": len(recovery),
            "variants": variants, "rtl_mutations_rejected": controls,
            "flow": "identical Yosys synth -top; exact mapped JSON ltp -noff combinational-cell depth"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer-host-ownership", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Phase-only ownership candidate has parameterized all-raw-state Lean correspondence to the original. "
                    "This campaign independently checks emitted state/output and synthesized outputs against frozen "
                    "host oracle traffic, plus actual RTL faults. Generic cell/depth comparison is not physical timing "
                    "or post-synthesis kernel correspondence; reset does not initialize memory contents/Q."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        receipt = args.positive_report.resolve()
        positive = verify_positive(receipt, report["tool_sha256"])
        report["positive_receipt"] = {"path": str(receipt), "sha256": sha(receipt)}
        shutil.copyfile(receipt, out / "positive-report.json")
        run(["lake", "build", "Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate", "Pinwheel.Hardware.Emit"],
            "build", timeout=900)
        host.controller.prepare_support(run, out)
        audit = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryTransferHostOwnership.lean"],
                    "raw-equivalence-tests")
        if "standard axioms only" not in audit:
            raise AssertionError("Missing ownership proof axiom audit")
        for entry in positive["configurations"]:
            report["configurations"].append(configuration(run, tools, out, receipt.parent, entry))
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during ownership validation")
        verify_positive(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_receipt"]["sha256"]:
            raise RuntimeError("Frozen baseline receipt changed during ownership validation")
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
