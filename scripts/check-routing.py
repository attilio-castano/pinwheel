#!/usr/bin/env python3
"""Check retained routing evidence and calibrate screens without routing search.

The input manifest selects exact runs, iterations and geometry exports. Fresh
DRC reports are separate measurements, never replacements for historical logs.
"""
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import time

import physical_checkpoint
from physical_checkpoint import sha
from routing_evidence import (parse_report, reconcile_iterations, geometry_checks,
                              compare_passes, marker_key, screen_candidate)

ROOT = Path(__file__).resolve().parents[1]


def read_json(path, inputs):
    inputs[str(path.relative_to(ROOT))] = sha(path)
    return json.loads(path.read_text())


def check_selection(design, invocation_path, selection, inputs):
    invocation = read_json(invocation_path, inputs)
    if "exit_code" not in invocation or (invocation.get("stop_reason") == "wall_time_limit" and
            invocation.get("container_termination", {}).get("status") not in {"stopped", "absent"}):
        raise ValueError("Run is active or timeout termination is unconfirmed")
    context_path, report_path = (ROOT / selection[k] for k in ("context", "report"))
    context = read_json(context_path, inputs)
    database = physical_checkpoint.artifact_path(context["database"], design)
    if sha(database) != context["database_sha256"]:
        raise ValueError("Context database hash changed")
    tag = invocation_path.name.removesuffix("-invocation.json")
    run = design / "runs" / tag
    if not all(p.resolve().is_relative_to(run.resolve()) for p in [report_path, database]):
        raise ValueError("Report and snapshot must belong to the selected run")
    pass_index, iteration = selection["pass"], selection["iteration"]
    if report_path.parent.name != f"drt-run-{pass_index}" or report_path.name != f"tt_um_pinwheel.drc-{iteration}.rpt":
        raise ValueError("Report does not match the selected pass and iteration")
    step = report_path.parent.parent
    step_log, outer_log = step / "openroad-detailedrouting.log", invocation_path.with_name(tag + ".log")
    counts = reconcile_iterations(step_log.read_text(), outer_log.read_text() if outer_log.exists() else None)
    if database.name != f"drt_iter{iteration}.odb" or not (
            database.parent == report_path.parent or
            (database.parent == step and pass_index == max(p for p, i in counts))):
        raise ValueError("Snapshot belongs to a different routing pass/iteration")
    markers = parse_report(report_path.read_text())
    if counts.get((pass_index, iteration)) != len(markers):
        raise ValueError("Report does not match a completed logged iteration")
    if context.get("drc_report_sha256") != sha(report_path):
        raise ValueError("Wire selection does not bind the retained DRC report")
    for p in [database, report_path, step_log, *([outer_log] if outer_log.exists() else [])]:
        inputs[str(p.relative_to(ROOT))] = sha(p)
    row = dict(routing_pass=pass_index, iteration=iteration, retained=geometry_checks(markers, context))
    if "fresh_drc" in selection:
        spec = selection["fresh_drc"]
        receipt_path, fresh_path, script_path = (ROOT / spec[k] for k in ["receipt", "report", "script"])
        receipt = read_json(receipt_path, inputs)
        if receipt.get("exit_code") != 0 or receipt.get("source_database_sha256") != sha(database):
            raise ValueError("Fresh DRC receipt must identify this exact snapshot and a completed check")
        if receipt.get("settled") is False or receipt.get("source_unchanged") is False:
            raise ValueError("Fresh DRC source changed or container termination is unconfirmed")
        config_path = step / "config.json"
        config = read_json(config_path, inputs)
        low, high = config["RT_MIN_LAYER"], config["RT_MAX_LAYER"]
        clock = f'{config.get("RT_CLOCK_MIN_LAYER") or low}-{config.get("RT_CLOCK_MAX_LAYER") or high}'
        if (receipt.get("config_sha256") != sha(config_path) or
                receipt.get("signal_layers") != f"{low}-{high}" or receipt.get("clock_layers") != clock):
            raise ValueError("Fresh DRC must use the selected step's resolved routing limits")
        if "raw_receipt_sha256" in receipt:
            raw_path = ROOT / spec["raw_receipt"]
            if receipt["raw_receipt_sha256"] != sha(raw_path):
                raise ValueError("Original fresh DRC receipt changed")
            inputs[str(raw_path.relative_to(ROOT))] = sha(raw_path)
        if receipt.get("report_sha256") != sha(fresh_path) or receipt.get("script_sha256") != sha(script_path):
            raise ValueError("Fresh DRC script/report changed")
        if sha(fresh_path) not in context.get("wire_selection_reports_sha256", {}).values():
            raise ValueError("Fresh DRC nets were not included in the exact geometry export")
        for p in [fresh_path, script_path]:
            inputs[str(p.relative_to(ROOT))] = sha(p)
        fresh = parse_report(fresh_path.read_text())
        a, b = Counter(map(marker_key, markers)), Counter(map(marker_key, fresh))
        row["fresh_drc"] = geometry_checks(fresh, context)
        row["fresh_drc"].update(seconds=receipt["seconds"],
            retained_markers_absent_from_fresh=sum((a-b).values()),
            fresh_markers_absent_from_retained=sum((b-a).values()))
    return row, markers, context


def load_screen(spec, inputs):
    design = ROOT / spec["design"]
    state_path, context_path, guide_path = (ROOT / spec[k] for k in ["state", "context", "guide"])
    state, context = read_json(state_path, inputs), read_json(context_path, inputs)
    database = physical_checkpoint.artifact_path(state["odb"], design)
    if (state_path.parent != database.parent or guide_path.parent != database.parent or
            context["database"] != state["odb"] or context["database_sha256"] != sha(database)):
        raise ValueError("Global-routing state, guide and context do not match")
    log_path = state_path.parent / "openroad-globalrouting.log"
    text = log_path.read_text().split("Final congestion report:")[-1]
    overflow = {m[1]: int(m[2]) for m in re.finditer(r"^\s*(Metal\d+|Total)\s+.*?/\s*\d+\s*/\s*(\d+)\s*$", text, re.M)}
    if "Total" not in overflow:
        raise ValueError("Missing completed congestion report")
    module_spec = importlib.util.spec_from_file_location("routing_guides", ROOT / "scripts/report-routing-guides.py")
    guides = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(guides)
    overlaps = guides.summarize(guides.parse_guides(guide_path.read_text(), context["dbu_per_micron"]), context)
    metrics = state["metrics"]
    timing_path = ROOT / spec["timing_state"]
    timing = read_json(timing_path, inputs)["metrics"]
    if any(metrics[k] != timing[k] for k in ["timing__setup__ws", "timing__hold__ws"]):
        raise ValueError("Inherited timing does not match the identified source state")
    names = dict(instance_area="design__instance__area", repair_area="design__instance__area__class:timing_repair_buffer",
                 power_violations="design__power_grid_violation__count", slew="design__max_slew_violation__count",
                 capacitance="design__max_cap_violation__count", fanout="design__max_fanout_violation__count",
                 setup_slack="timing__setup__ws", hold_slack="timing__hold__ws")
    for p in [database, guide_path, log_path]:
        inputs[str(p.relative_to(ROOT))] = sha(p)
    return dict(overflow=overflow, metal4_guides=overlaps["overlapping_guides"].get("Metal4", {}).get("rectangles", 0),
                wirelength_um=int(re.search(r"Total wirelength: (\d+) um", text)[1]),
                timing_stage=re.sub(r"^\d+-", "", timing_path.parent.name),
                **{k: metrics[v] for k, v in names.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started, inputs = time.monotonic(), {}
    manifest = read_json(args.manifest.resolve(), inputs)
    if manifest.get("schema") != 1:
        raise ValueError("Unsupported diagnostic manifest")
    rows, changes, previous = [], [], None
    for selected in manifest["routing"]:
        row, markers, context = check_selection(ROOT / selected["design"], ROOT / selected["invocation"], selected, inputs)
        row["name"] = selected["name"]
        rows.append(row)
        chain = selected["invocation"]
        if previous is not None and previous[3] == chain and previous[4] + 1 == selected["pass"]:
            changes.append(dict(before=previous[0], after=selected["name"],
                                **compare_passes(previous[1], markers, previous[2], context)))
        previous = selected["name"], markers, context, chain, selected["pass"]
    screens = {s["name"]: load_screen(s, inputs) for s in manifest.get("global_screens", [])}
    calibration = []
    for spec in manifest.get("calibration", []):
        result = screen_candidate(screens[spec["baseline"]], screens[spec["candidate"]],
                                  spec.get("minimum_overflow_improvement", .2))
        if result["decision"] != spec["expected"]:
            raise ValueError(f"Calibration disagrees with retained experiment: {spec['candidate']}")
        calibration.append(dict(**spec, **result))
    for name in ["check-routing.py", "routing_evidence.py", "physical_floorplan.py", "physical_checkpoint.py", "report-routing-guides.py"]:
        p = ROOT / "scripts" / name
        inputs[str(p.relative_to(ROOT))] = sha(p)
    result = dict(schema=1, routing=rows, repair_changes=changes, global_screens=screens,
                  calibration=calibration, input_sha256=inputs, seconds=round(time.monotonic()-started, 3),
                  boundary="A cheap diagnostic gate. Fresh static DRC uses the pinned router's checker, not the foundry rule deck. Screens rank candidates; they do not establish physical closure.")
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "report.json").write_text(json.dumps(result, indent=2) + "\n")
    lines = ["# Routing diagnostic gate", "", "| Pass | Retained markers | Unique retained | Fresh static DRC | Fresh check seconds |", "| --- | ---: | ---: | ---: | ---: |"]
    for row in rows:
        fresh = row.get("fresh_drc", {})
        lines.append(f'| {row["name"]} | {row["retained"]["markers"]} | {row["retained"]["unique_markers"]} | {fresh.get("markers", "unmeasured")} | {fresh.get("seconds", "")} |')
    lines += ["", result["boundary"], "", "## Historical screen calibration", ""]
    lines += [f'- {c["candidate"]}: {c["decision"]}.' for c in calibration]
    (args.output / "report.md").write_text("\n".join(lines) + "\n")
    print(json.dumps(dict(seconds=result["seconds"], passes=len(rows), calibrated_screens=len(calibration)), indent=2))


if __name__ == "__main__":
    main()
