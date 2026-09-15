#!/usr/bin/env python3
"""Collect completed physical-run evidence without equating flow exit with sign-off."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "build/physical"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tag", default="initial")
    args = parser.parse_args()
    invocation_path = BASE / (args.tag + "-invocation.json")
    invocation = json.loads(invocation_path.read_text())
    if "exit_code" not in invocation:
        raise RuntimeError("Run has not completed; no final result can be collected")
    run = BASE / "core/runs" / args.tag
    states = sorted(run.glob("[0-9]*-*/state_out.json"), key=lambda p: int(p.parent.name.split("-", 1)[0]))
    if not states:
        raise RuntimeError("No completed physical-flow steps")
    last = json.loads(states[-1].read_text())
    metrics = last["metrics"]
    resolved = json.loads((run / "resolved.json").read_text())
    stages = {}
    for path in states:
        stage_metrics = json.loads(path.read_text())["metrics"]
        stages[path.parent.name] = {k: v for k, v in stage_metrics.items() if k in [
            "design__instance__area", "design__instance__count", "design__core__area",
            "design__die__area", "design__instance__utilization", "timing__setup__ws",
            "timing__hold__ws", "route__drc_errors", "design__unconnected_pin__count",
        ]}
    artifacts = {}

    def collect(value):
        if isinstance(value, dict):
            for v in value.values():
                collect(v)
        elif isinstance(value, list):
            for v in value:
                collect(v)
        elif isinstance(value, str) and value.startswith("/work/core/"):
            path = BASE / "core" / value.removeprefix("/work/core/")
            if path.is_file():
                artifacts[str(path.relative_to(ROOT))] = sha(path)

    collect({k: v for k, v in last.items() if k != "metrics"})
    checks = {k: v for k, v in metrics.items() if any(s in k for s in [
        "violation", "_vio__", "unconstrained", "unannotated", "drc", "antenna",
        "lvs", "unconnected", "floating",
    ])}
    routing_passes = []
    for log in run.glob("*-openroad-detailedrouting/openroad-detailedrouting.log"):
        iteration = None
        for line in log.read_text().splitlines():
            if match := re.search(r"Start (\d+)(?:st|nd|rd|th) (?:optimization|stubborn tiles|guides tiles) iteration", line):
                iteration = int(match[1])
            if match := re.search(r"Number of violations = (\d+)", line):
                routing_passes.append({"iteration": iteration, "violations": int(match[1])})
    report = {
        "tag": args.tag, "flow_exit_code": invocation["exit_code"],
        "last_completed_step": states[-1].parent.name,
        "completed_steps": [p.parent.name for p in states],
        "detailed_routing_completed": any("-openroad-detailedrouting" in p.parent.name for p in states),
        "extracted_timing_completed": any("-openroad-stapostpnr" in p.parent.name for p in states),
        "metrics_note": "Flow states inherit older metrics. Mid-PnR timing may update only typical-corner values; do not interpret inherited fast/slow values as current. Final multi-corner extracted STA is required.",
        "requested_stop": invocation["stop_step"],
        "resume_step": invocation.get("resume_step"),
        "checkpoint_sha256": invocation.get("checkpoint_sha256"),
        "checkpoint": invocation.get("checkpoint"),
        "termination_note": (BASE / (args.tag + "-stop-reason.txt")).read_text() if (BASE / (args.tag + "-stop-reason.txt")).exists() else None,
        "invocation_sha256": sha(invocation_path), "resolved_config_sha256": sha(run / "resolved.json"),
        "clock_period_ns": resolved["CLOCK_PERIOD"], "sta_corners": resolved["STA_CORNERS"],
        "timing_violation_corners": resolved["TIMING_VIOLATION_CORNERS"],
        "enabled_checks": {k: v for k, v in resolved.items() if k.startswith("RUN_")},
        "metrics": metrics, "checks": checks, "stages": stages, "artifact_sha256": artifacts,
        "routing_passes": routing_passes,
        "boundary": invocation["boundary"] + " Flow completion alone is not comprehensive sign-off. Inspect enabled checks, timing constraints, extracted RC assumptions, and all violations. Formal translation equivalence and asynchronous pin behavior remain separate.",
    }
    (BASE / (args.tag + "-report.json")).write_text(json.dumps(report, indent=2) + "\n")
    print("Flow exit:", report["flow_exit_code"], "last completed step:", report["last_completed_step"])
    print("Checks:", json.dumps(checks, indent=2))


if __name__ == "__main__":
    main()
