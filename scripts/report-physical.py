#!/usr/bin/env python3
"""Collect completed physical-run evidence without equating flow exit with sign-off."""
import argparse
import hashlib
import json
from pathlib import Path
import physical_checkpoint
from routing_evidence import reconcile_iterations

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
    if invocation.get("stop_reason") == "wall_time_limit" and invocation.get(
            "container_termination", {}).get("status") not in {"stopped", "absent"}:
        raise RuntimeError("Timed-out container termination is unconfirmed; "
                           "artifacts may still be changing, so no final result can be collected")
    # Receipts written before designs were selectable describe the original one.
    design = BASE / invocation.get("design", "core")
    run = design / "runs" / args.tag
    states = sorted(run.glob("[0-9]*-*/state_out.json"), key=lambda p: int(p.parent.name.split("-", 1)[0]))
    if states:
        state_path = states[-1]
        state_origin = "completed_step"
    elif invocation.get("checkpoint"):
        checkpoint = invocation["checkpoint"]
        state_path = physical_checkpoint.artifact_path(checkpoint["state_path"], design)
        if sha(state_path) != checkpoint["snapshot_state_sha256"]:
            raise RuntimeError("Changed input checkpoint state")
        state_origin = "input_checkpoint"
    else:
        raise RuntimeError("No completed physical-flow steps or input checkpoint")
    last = json.loads(state_path.read_text())
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
            path = design / value.removeprefix("/work/core/")
            if path.is_file():
                artifacts[str(path.relative_to(ROOT))] = sha(path)

    collect({k: v for k, v in last.items() if k != "metrics"})
    checks = {k: v for k, v in metrics.items() if any(s in k for s in [
        "violation", "_vio__", "unconstrained", "unannotated", "drc", "antenna",
        "lvs", "unconnected", "floating",
    ])}
    routing_passes = []
    for log in run.glob("*-openroad-detailedrouting/openroad-detailedrouting.log"):
        outer = BASE / (args.tag + ".log")
        counts = reconcile_iterations(log.read_text(), outer.read_text() if outer.exists() else None)
        routing_passes.extend(dict(routing_pass=p, iteration=i, violations=v) for (p, i), v in counts.items())
    report = {
        "tag": args.tag, "flow_exit_code": invocation["exit_code"],
        "variant": invocation.get("variant", "small-dense-cached"),
        "design": invocation.get("design", "core"),
        "timeout_seconds": invocation.get("timeout_seconds"),
        "stop_reason": invocation.get("stop_reason"),
        "container_termination": invocation.get("container_termination"),
        "last_completed_step": states[-1].parent.name if states else None,
        "state_origin": state_origin,
        "state_path": "/work/core/" + state_path.relative_to(design).as_posix(),
        "state_sha256": sha(state_path),
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
