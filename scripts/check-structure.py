#!/usr/bin/env python3
"""Compare Lean's structural arrival levels with evidence already retained.

The Lean report needs no CAD tool. It is checked against three earlier, more
expensive measurements recorded in tracked manifests: operation depth measured on
emitted MLIR, logic depth of technology-mapped cache cones, and extracted
slow-corner slack per launch family. Levels are ordinal: agreement means the same
ranking and direction of change, never nanoseconds.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENTS = ROOT / "physical/experiments"
# Mapped-cone family names -> Lean launch families.
FAMILIES = {"cursor": "loader cursor", "protocol": "incoming", "command": "command", "reset": "init/reset"}
PORTS = {"protocol": "incoming", "loader_command": "command", "reset": "init/reset", "loader_data": "data"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pearson(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    return cov / (sum((x - mx) ** 2 for x in xs) * sum((y - my) ** 2 for y in ys)) ** 0.5


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.tag): parser.error("Invalid tag")
    out = ROOT / "build/structure" / args.tag
    if out.exists(): raise RuntimeError("Choose a fresh tag to retain earlier evidence")
    out.mkdir(parents=True)
    manifests = {name: EXPERIMENTS / name for name in (
        "bank-selection-results.json", "cache-enable-results.json", "combined-physical-results.json")}
    sources = [*sorted((ROOT / "Pinwheel").rglob("*.lean")), ROOT / "test/Structure.lean", ROOT / "lakefile.toml",
               ROOT / "lean-toolchain", Path(__file__).resolve(), *manifests.values()]
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    started = time.monotonic()
    for command, label in ((["lake", "build", "Pinwheel", "structure_report"], "build"),
                           ([str(ROOT / ".lake/build/bin/structure_report"), str(out)], "report")):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=3600)
        (out / f"{label}.log").write_text(result.stdout + result.stderr)
        if result.returncode: raise RuntimeError(f"{label}: {(result.stdout + result.stderr)[-2000:]}")
    lean = {v: json.loads((out / f"{v}.json").read_text()) for v in ("command-split", "late-bank", "enable-split")}
    bank, enable, physical = (json.loads(p.read_text()) for p in manifests.values())

    def level(variant, table, family, endpoint, key="latest"):
        rows = [r for r in lean[variant][table] if r["family"] == family and r["endpoint"] == endpoint]
        if len(rows) != 1: raise RuntimeError(f"Missing Lean row: {variant} {family} {endpoint}")
        return rows[0][key]

    # 1. Exact: depth from the loader cursor on the emitted operation graph.
    exact = []
    def expect(label, variant, key, recorded):
        measured = lean[variant]["source_depth_from_cursor"][key]
        exact.append({"quantity": label, "recorded_from_mlir": recorded, "lean": measured})
        if measured != recorded: raise RuntimeError(f"{label}: Lean {measured} differs from recorded {recorded}")
    for role, variant in (("control", "command-split"), ("candidate", "late-bank")):
        for key, stage in bank["source_stages"][role].items():
            if key in lean[variant]["source_depth_from_cursor"]:
                expect(f"{variant} {key}", variant, key, stage["expression_depth_from_cursor"])
    for role, variant in (("control", "command-split"), ("candidate", "enable-split")):
        for scope, key in (("complete", "enable_complete"), ("successor_abstracted", "enable_successor_abstracted")):
            expect(f"{variant} cache {key}", variant, key,
                   enable["source_enable_dependencies"][role][scope]["expression_depth_from_cursor"])

    # 2. Ordinal: technology-mapped logic depth into the cached word.
    points, directions = [], []
    cones = {"command-split": bank["mapped_cache_cones"]["typical"]["control"]["families"],
             "late-bank": bank["mapped_cache_cones"]["typical"]["candidate"]["families"],
             "enable-split": enable["mapped_cache_cones"]["typical"]["candidate"]["families"]}
    for variant, families in cones.items():
        if (families["loader_data"]["reached_cache_pins"] == 0) != (level(variant, "gates", "data", "cached word") is None):
            raise RuntimeError(f"{variant}: loader-data reachability of the cached word disagrees")
        for mapped_name, family in FAMILIES.items():
            points.append({"variant": variant, "family": family,
                           "mapped_logic_depth": families[mapped_name]["maximum_logic_depth"],
                           "lean_gate_levels": level(variant, "gates", family, "cached word")})
    for variant in ("late-bank", "enable-split"):
        for mapped_name, family in FAMILIES.items():
            mapped = cones[variant][mapped_name]["maximum_logic_depth"] - cones["command-split"][mapped_name]["maximum_logic_depth"]
            model = level(variant, "gates", family, "cached word") - level("command-split", "gates", family, "cached word")
            agrees = (mapped > 0) == (model > 0) and (mapped < 0) == (model < 0)
            directions.append({"variant": variant, "family": family, "mapped_change": mapped,
                               "lean_change": model, "same_direction": agrees})
    if not all(d["same_direction"] for d in directions):
        raise RuntimeError("A candidate's mapped depth moved against the Lean levels")
    correlation = pearson([p["mapped_logic_depth"] for p in points], [p["lean_gate_levels"] for p in points])
    if correlation < 0.9: raise RuntimeError(f"Weak agreement with mapped cones: r = {correlation:.3f}")

    # 3. Ordinal: extracted slack of equally budgeted port families in the routed control.
    routed = physical["slow_launch_families"]["composed-control-01"]
    deepest = {}
    for sta_name, family in PORTS.items():
        depths = [r["latest"] for r in lean["command-split"]["gates"]
                  if r["family"] == family and r["latest"] is not None and r["endpoint"] != "outputs"]
        deepest[sta_name] = max(depths)
    by_slack = sorted(PORTS, key=lambda k: routed[k]["worst_ns"])
    by_depth = sorted(PORTS, key=lambda k: -deepest[k])
    ranking = {"by_extracted_slack_worst_first": by_slack, "by_lean_depth_deepest_first": by_depth,
               "extracted_worst_ns": {k: routed[k]["worst_ns"] for k in PORTS}, "lean_deepest_levels": deepest}
    tied = deepest["loader_command"] == deepest["reset"]
    if by_slack != by_depth and not (tied and sorted(by_slack[1:3]) == sorted(by_depth[1:3]) and
                                     by_slack[0] == by_depth[0] and by_slack[3] == by_depth[3]):
        raise RuntimeError(f"Port-family ranking disagrees: {ranking}")
    sampled_pins = [r for r in lean["command-split"]["sampled_gates"]
                    if r["family"] == "incoming" and r["latest"] is not None]
    if [r["endpoint"] for r in sampled_pins] != ["pin stages"]:
        raise RuntimeError("Pins reach more than the first pipeline stage")
    worst_endpoint = max((r for r in lean["command-split"]["gates"] if r["family"] == "registers"
                          and r["endpoint"] != "outputs"), key=lambda r: r["latest"])["endpoint"]
    if worst_endpoint != "cached word": raise RuntimeError("Deepest endpoint is not the cached word")

    if hashes != {str(p.relative_to(ROOT)): sha(p) for p in sources}:
        raise RuntimeError("Sources changed during the check")
    report = {"source_sha256": hashes, "exact_source_depths": exact, "mapped_cone_points": points,
              "mapped_cone_directions": directions, "mapped_cone_pearson_r": round(correlation, 4),
              "routed_port_family_ranking": ranking, "deepest_register_endpoint": worst_endpoint,
              "sampled_pin_reach": [r["endpoint"] for r in sampled_pins],
              "loop_stages_gate_levels": {v: lean[v]["loop_stages_gates"] for v in lean},
              "self_loops_gate_levels": lean["command-split"]["self_loops_gates"],
              "update_cones_gate_levels": {v: lean[v]["update_cones_gates"] for v in lean},
              "gating_policies": lean["command-split"]["policies"],
              "gating_plan_sha256": {p.name: sha(p) for p in sorted(out.glob("plan-*.tsv"))},
              "artifact_sha256": {p.name: sha(p) for p in sorted(out.glob("*.json"))},
              "elapsed_seconds": round(time.monotonic() - started, 3),
              "boundary": "Lean levels are an ordinal structural model. Exact agreement is claimed only for operation "
                          "depth on the emitted graph. Mapped and routed comparisons check direction and ranking on "
                          "retained evidence; no delay, buffering, placement or routing claim follows."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{len(exact)} source depths match exactly; mapped-cone r = {correlation:.3f} over {len(points)} points, "
          f"{len(directions)} candidate changes in the same direction; port families rank {by_depth}.")


if __name__ == "__main__":
    main()
