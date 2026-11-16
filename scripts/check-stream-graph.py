#!/usr/bin/env python3
"""Validate typed fork/join graphs, independent branch stalls and RTL certificates."""
from __future__ import annotations

import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import random

import generic_stream_readback as readback

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("stream_check", ROOT / "scripts/check-stream-hardware.py")
base = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(base)


def stimuli(width, left, right):
    rng = random.Random(0x464F524B)
    mask = (1 << width) - 1
    drain = left + right + 8
    rows = [(1, 0, 0, mask)]
    rows += [(0, 1, 1, n & mask) for n in range(64)]
    rows += [(0, 0, 1, mask)] * drain
    rows += [(0, 1, 0, mask)] * (drain + 16)
    rows += [(0, 1, 1, 0)] * 48
    rows += [(1, 1, 0, mask)]
    rows += [(0, 1, 1, mask if n % 2 else 0) for n in range(64)]
    rows += [(int(rng.randrange(61) == 0), rng.randrange(2), rng.randrange(2), rng.getrandbits(width))
             for _ in range(600)]
    rows += [(0, 0, 1, mask)] * drain
    return rows


def scoreboard(stimulus, observed, width, left, right):
    if len(stimulus) != len(observed):
        raise AssertionError("Missing or extra observations")
    pending, previous = [], None
    mask = (1 << width) - 1
    accepted = emitted = 0
    for k, ((rst, valid, ready, data), row) in enumerate(zip(stimulus, observed, strict=True)):
        cycle, ir, ov, od, _, _, _ = row
        if cycle != k or ir not in (0, 1) or ov not in (0, 1):
            raise AssertionError("Invalid cycle or controls")
        if rst:
            if ir or ov:
                raise AssertionError("Transfer during reset")
            pending.clear()
        else:
            if previous and previous[0] and not previous[1] and (ov, od) != (previous[0], previous[2]):
                raise AssertionError("Joined result changed while stalled")
            if ov and ready:
                if not pending or od != pending[0][0]:
                    raise AssertionError(f"Incorrect or mismatched branch pair at edge {k}")
                _, birth = pending.pop(0)
                if 1 <= birth <= 64 and k != birth + max(left, right):
                    raise AssertionError("Unexpected empty/no-stall latency")
                emitted += 1
            if valid and ir:
                pending.append((((data + 1) & mask) << width | ((~data) & mask), k))
                accepted += 1
        previous = ov, ready, od
    if pending:
        raise AssertionError("Graph failed to drain")
    return {"accepted_across_epochs": accepted, "emitted_across_epochs": emitted}


def testbench(width, directory, hierarchy):
    text = base.testbench(width, directory)
    text = text.replace(f"reg [{2*width-1}:0] in_data", f"reg [{width-1}:0] in_data")
    text = text.replace(f"wire [{width-1}:0] out_data", f"wire [{2*width-1}:0] out_data")
    text = text.replace(f"reg [{width-1}:0] pre_data", f"reg [{2*width-1}:0] pre_data")
    if hierarchy:
        text = text.replace("clk = 1; #5;", '$display("B,%0d,%0d,%0d,%0d,%0d", cycle, dut.core.lr, dut.core.rr, dut.core.lv, dut.core.rv);\n      clk = 1; #5;')
    return text


def branch_coverage(csv_path, stimulus):
    result = {"left_only_blocked": 0, "right_only_blocked": 0, "unpaired_offer": 0}
    for line in csv_path.read_text().splitlines():
        if not line.startswith("B,"):
            continue
        _, cycle, lr, rr, lv, rv = line.split(",")
        if stimulus[int(cycle)][0]:
            continue
        lr, rr, lv, rv = map(int, (lr, rr, lv, rv))
        result["left_only_blocked"] += (lr, rr) == (0, 1)
        result["right_only_blocked"] += (lr, rr) == (1, 0)
        result["unpaired_offer"] += lv != rv
    return result


def prove(run, directory, config, descriptor, source, imported):
    width, left, right = config
    modules, evidence = readback.generate(directory, config, descriptor, source, imported, base.CAD / "z3",
        design_expression=f"diamondDesign {width} {left-1} {right-1}",
        design_import="Pinwheel.Hardware.Stream.Diamond")
    for module in modules:
        run.lean(directory, module)
    return evidence


def configuration(run, config):
    width, left, right = config
    directory = run.root / f"w{width}-l{left}-r{right}"
    directory.mkdir()
    rows = stimuli(*config)
    (directory / "stimulus.csv").write_text("".join(",".join(map(str, row)) + "\n" for row in rows))
    run.command([ROOT / ".lake/build/bin/stream_graph", *config, directory, directory / "stimulus.csv"],
                directory / "lean-simulation.log")
    descriptor = json.loads((directory / "interface.json").read_text())
    base.lower(run, directory / "flat.mlir", directory / "flat.sv")
    for name in descriptor["leaves"]:
        base.lower(run, directory / f"{name}.mlir", directory / f"{name}.sv")
    sources = sorted(directory.glob("stream_core*.sv")) + [directory / "hierarchy_top.sv"]
    (directory / "hierarchical.sv").write_text("\n".join(p.read_text() for p in sources))
    expected = base.read_rows(directory / "lean.csv")
    result = {"configuration": config, "edges": len(rows), "forms": {}}
    for form in ("flat", "hierarchical"):
        rtl, tb, binary = directory / f"{form}.sv", directory / f"{form}-tb.sv", directory / f"{form}.vvp"
        tb.write_text(testbench(width, directory, form == "hierarchical"))
        run.command([base.CAD / "iverilog", "-g2012", "-s", "tb", "-o", binary, rtl, tb],
                    directory / f"{form}-compile.log")
        csv = directory / f"{form}.csv"
        run.command([base.CAD / "vvp", binary], directory / f"{form}-simulation.log", stdout=csv)
        actual = base.read_rows(csv)
        if actual != expected:
            run.command([base.CAD / "vvp", binary, "+waves"], directory / f"{form}-waves.log")
            raise AssertionError(f"Graph {config}/{form} differs from Lean; see waves.vcd")
        accounting = scoreboard(rows, actual, *config)
        proofdir = directory / form
        proofdir.mkdir()
        base.import_rtl(run, rtl, proofdir, descriptor, form == "hierarchical")
        evidence = prove(run, proofdir, config, descriptor, directory / "flat.mlir", proofdir / "import.json")
        result["forms"][form] = {**accounting, **evidence, "sha256": base.sha(rtl)}
    coverage = branch_coverage(directory / "hierarchical.csv", rows)
    if left != right and (not coverage["unpaired_offer"] or
            not coverage["left_only_blocked" if left < right else "right_only_blocked"]):
        raise AssertionError("Unequal branches did not exercise independent blocking")
    result["branch_coverage"] = coverage
    print(f"PASS graph {width}/{left}/{right}: {len(rows)} edges; both RTL certificates; {coverage}", flush=True)
    return result


def negative_controls(run, config):
    w, l, r = config
    source = run.root / f"w{w}-l{l}-r{r}"
    descriptor = json.loads((source / "interface.json").read_text())
    text = (source / "hierarchical.sv").read_text()
    results = []
    for name, before, after in (
            ("one-sided-admission", ".in_valid(in_valid & rr)", ".in_valid(in_valid)"),
            ("premature-left-consumption", ".out_ready(out_ready & rv)", ".out_ready(out_ready)"),
            ("swapped-pair", "{ld, rd}", "{rd, ld}")):
        if text.count(before) != 1:
            raise AssertionError("Mutation must change exactly one graph connection")
        directory = run.root / name
        directory.mkdir()
        rtl = directory / "mutated.sv"
        rtl.write_text(text.replace(before, after))
        base.import_rtl(run, rtl, directory, descriptor, True)
        try:
            prove(run, directory, config, descriptor, source / "flat.mlir", directory / "import.json")
        except RuntimeError:
            module = Path(run.commands[-1]["log"]).stem
            if module not in ("LocalProofs", "Links", "Proof"):
                raise
            results.append({"mutation": name, "rejected_by": module, "sha256": base.sha(rtl)})
        else:
            raise AssertionError(f"Incorrect graph was certified: {name}")
    return results


def provenance():
    result = base.provenance()
    for name in ("scripts/check-stream-graph.py", "test/StreamGraphExample.lean", "test/StreamGraph.lean",
                 "test/StreamBundle.lean", "test/StreamForkJoin.lean", "test/test_stream_graph.py"):
        result["sources"][name] = base.sha(ROOT / name)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", help="WIDTH,LEFT_STAGES,RIGHT_STAGES")
    args = parser.parse_args()
    if not args.tag or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_" for c in args.tag):
        parser.error("Use a simple alphanumeric tag")
    configs = [tuple(map(int, c.split(","))) for c in args.config] if args.config else list(
        itertools.product((1, 8, 17), (1, 2, 4), (1, 3, 4)))
    if any(len(c) != 3 or min(c) <= 0 for c in configs):
        parser.error("Configurations require three positive integers")
    root = ROOT / "build/stream-graph" / args.tag
    root.mkdir(parents=True, exist_ok=False)
    run = base.Run(root)
    report = {"schema": 1, "status": "running", "configurations": [], "commands": run.commands,
              "boundary": "Atomic admission; ordered join; two-state RTL; trusted Yosys/JSON interpretation."}
    try:
        report["provenance"] = provenance()
        run.command(["lake", "build", "stream_graph", "stream_example"], root / "build.log", timeout=300)
        for name in ("StreamBundle", "StreamForkJoin", "StreamGraph", "StreamAudit"):
            run.command(["lake", "env", "lean", "-DwarningAsError=true", f"test/{name}.lean"], root / f"{name}.log")
        run.command(["python3", "-B", "-m", "unittest", "discover", "-s", "test", "-p", "test_stream_graph.py", "-v"],
                    root / "negative-unit.log")
        for config in configs:
            report["configurations"].append(configuration(run, config))
        report["negative_controls"] = negative_controls(run, next((c for c in configs if c[0] > 1), configs[0]))
        if report["provenance"] != provenance():
            raise RuntimeError("Sources or tools changed during validation")
        report["artifacts"] = {str(p.relative_to(root)): base.sha(p) for p in sorted(root.rglob("*"))
                               if p.is_file() and p.suffix in (".lean", ".json", ".mlir", ".sv", ".csv")}
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", str(error)
        raise
    finally:
        (root / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
