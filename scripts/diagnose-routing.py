#!/usr/bin/env python3
"""Classify retained routing markers without treating them as final signoff.

Requires a stopped run, an iteration report, and context exported from the
matching iteration's OpenDB snapshot by routing_context.py. Counts describe
markers, not independent root causes; connectivity and proximity are evidence
for investigation, not automatic causal attribution.
"""
import argparse
from collections import Counter
import html
import json
import math
from pathlib import Path
import re

import physical_checkpoint
from physical_checkpoint import sha

from routing_evidence import parse_report, iteration_counts, reconcile_iterations


def distance(left, right):
    return math.hypot(max(left[0] - right[2], right[0] - left[2], 0),
                      max(left[1] - right[3], right[1] - left[3], 0))


def summarize(markers, context):
    macros = {name: inst for name, inst in context["instances"].items() if inst["macro"]}
    net_counts = Counter(net for marker in markers for net in marker["nets"])
    tiles = Counter((int((m["bbox"][0] + m["bbox"][2]) / 100),
                     int((m["bbox"][1] + m["bbox"][3]) / 100)) for m in markers)
    power_count = sum(any(context["nets"].get(n, {}).get("type") in {"POWER", "GROUND"}
                          for n in m["nets"]) for m in markers)
    clock_count = sum(any(context["nets"].get(n, {}).get("type") == "CLOCK"
                          for n in m["nets"]) for m in markers)
    net_details = []
    for name, count in net_counts.most_common(30):
        net = context["nets"].get(name, {})
        terms = net.get("terminals", [])
        drivers = [dict(**term, cell=context["instances"][term["instance"]]["cell"])
                   for term in terms if term["direction"] in {"OUTPUT", "INOUT"}]
        repairs = sorted({t["instance"] for t in terms
                          if re.match(r"(?:hold|fanout|slew|cap|wire|rebuffer)", t["instance"])})
        net_details.append(dict(net=name, markers=count, type=net.get("type"),
            drivers=drivers[:16], driver_count=len(drivers),
            terminal_count=len(terms), ports=net.get("ports", []),
            connected_macros=sorted({t["instance"] for t in terms if t["instance"] in macros}),
            repair_instances=repairs[:16], repair_instance_count=len(repairs)))
    return dict(marker_count=len(markers),
        exact_unique_markers=len({(m["rule"], m["sources"], tuple(m["bbox"]), m["layer"]) for m in markers}),
        by_rule=dict(Counter(m["rule"] for m in markers)),
        by_layer=dict(Counter(m["layer"] for m in markers)),
        by_rule_layer=dict(Counter(m["rule"] + " / " + m["layer"] for m in markers)),
        involving_power_net=power_count, involving_clock_net=clock_count,
        near_macros={str(limit): sum(any(distance(m["bbox"], inst["bbox"]) <= limit
                            for inst in macros.values()) for m in markers) for limit in [0, 5, 20]},
        hottest_50um_tiles=[dict(bbox=[x*50, y*50, (x+1)*50, (y+1)*50], markers=count)
                           for (x, y), count in tiles.most_common(12)],
        net_details=net_details,
        unrecognized_nets=sorted(set(net_counts) - set(context["nets"])), macros=macros)


def layout_svg(markers, context):
    x0, y0, x1, y1 = context["die"]
    colors = {"Metal1": "#176aaf", "Metal2": "#ed772c", "Metal3": "#8b45bd", "Metal4": "#bd2944"}
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{x0-8} {-y1-8} {x1-x0+16} {y1-y0+16}">',
             '<rect x="-8" y="-1000" width="1600" height="1600" fill="#f6f5f1"/>']

    def rect(bbox, attrs, title=""):
        a, b, c, d = bbox
        return (f'<rect x="{a}" y="{-d}" width="{c-a}" height="{d-b}" {attrs}>'
                f'<title>{html.escape(title)}</title></rect>')

    parts.append(rect(context["die"], 'fill="none" stroke="#44505b" stroke-width="1"', "Official die outline"))
    for inst in context["instances"].values():
        if not inst["macro"]:
            parts.append(rect(inst["bbox"], 'fill="#8997a3" opacity="0.15"'))
    for shape in context["power_shapes"]:
        parts.append(rect(shape["bbox"], 'fill="#508f76" opacity="0.15"', shape["net"] + " / " + shape["layer"]))
    for name, inst in context["instances"].items():
        if inst["macro"]:
            parts.append(rect(inst["bbox"], 'fill="#c6d8ec" stroke="#274d79" stroke-width="1"', name))
            x, y, _, _ = inst["bbox"]
            parts.append(f'<text x="{x+6}" y="{-y-8}" fill="#173a64" font-size="12">{html.escape(name)}</text>')
    for pin in context.get("macro_pins", []):
        if pin["type"] in {"POWER", "GROUND"}:
            parts.append(rect(pin["bbox"], 'fill="#508f76" opacity="0.4"', pin["instance"] + " / " + pin["pin"]))
    for port in context["ports"]:
        if context["nets"].get(port["name"], {}).get("type") not in {"POWER", "GROUND"}:
            parts.append(rect(port["bbox"], 'fill="#164d67"', port["name"]))
    for m in markers:
        a, b, c, d = m["bbox"]
        title = html.escape(f'{m["rule"]} / {m["layer"]}: {m["sources"]}')
        color = colors.get(m["layer"], "#b21e39")
        parts.append(f'<circle cx="{(a+c)/2}" cy="{-(b+d)/2}" r="2.8" fill="{color}" opacity="0.75"><title>{title}</title></circle>')
    parts.append('</svg>')
    return "\n".join(parts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--design", type=Path, required=True)
    parser.add_argument("--invocation", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--context", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    invocation = json.loads(args.invocation.read_text())
    if "exit_code" not in invocation or (invocation.get("stop_reason") == "wall_time_limit" and
            invocation.get("container_termination", {}).get("status") not in {"stopped", "absent"}):
        raise RuntimeError("Run must be completed and any timed-out container confirmed stopped")
    context = json.loads(args.context.read_text())
    database = physical_checkpoint.artifact_path(context["database"], args.design)
    if sha(database) != context["database_sha256"]:
        raise RuntimeError("Context does not match the retained database")
    report_iteration = re.fullmatch(r".+\.drc-(\d+)\.rpt", args.report.name)
    if not report_iteration or database.name != f"drt_iter{report_iteration[1]}.odb":
        raise RuntimeError("DRC report and database must describe the same routing iteration")
    run = args.design / "runs" / args.invocation.name.removesuffix("-invocation.json")
    if not args.report.resolve().is_relative_to(run.resolve()) or not database.resolve().is_relative_to(run.resolve()):
        raise RuntimeError("Report and database must belong to the recorded run")
    markers = parse_report(args.report.read_text())
    route_run = re.fullmatch(r"drt-run-(\d+)", args.report.parent.name)
    log = args.report.parent.parent / "openroad-detailedrouting.log"
    outer_log = args.invocation.with_name(args.invocation.name.removesuffix("-invocation.json") + ".log")
    counts = reconcile_iterations(log.read_text(), outer_log.read_text() if outer_log.exists() else None)
    if not route_run or counts.get(
            (int(route_run[1]), int(report_iteration[1]))) != len(markers):
        raise RuntimeError("Report count does not match a completed routing iteration in the log")
    if not (database.parent.resolve() == args.report.parent.resolve() or
            (database.parent.resolve() == log.parent.resolve() and
             int(route_run[1]) == max(p for p, i in counts))):
        raise RuntimeError("Snapshot belongs to a different routing pass")
    summary = summarize(markers, context)
    history = []
    for file in args.report.parent.glob("*.drc-*.rpt"):
        iteration = int(re.fullmatch(r".+\.drc-(\d+)\.rpt", file.name)[1])
        if iteration <= int(report_iteration[1]):
            parsed = parse_report(file.read_text())
            history.append(dict(iteration=iteration, markers=len(parsed), sha256=sha(file)))
    summary.update(iteration=int(report_iteration[1]), history=sorted(history, key=lambda item: item["iteration"]),
        input_sha256={str(path): sha(path) for path in
                      [args.invocation, args.report, args.context, database, log, Path(__file__)] +
                      ([outer_log] if outer_log.exists() else []) + [Path(__file__).with_name("routing_evidence.py")]},
        boundary="Intermediate router markers, not final foundry DRC or physical closure. Proximity and net connectivity do not prove root cause.")
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "report.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "markers.json").write_text(json.dumps(markers, indent=2) + "\n")
    svg = layout_svg(markers, context)
    (args.output / "layout.svg").write_text(svg + "\n")
    page = ('<!doctype html><html><meta charset="utf-8"><title>Pinwheel routing diagnosis</title>'
            '<style>body{font:16px system-ui;margin:30px;background:#f6f5f1;color:#183047}svg{width:100%;max-height:75vh}'
            'pre{white-space:pre-wrap;font-size:13px}</style>'
            f'<h1>Routing iteration {summary["iteration"]}: {len(markers)} markers</h1>'
            '<p>Orange: Metal2. Purple: Metal3. Blue: Metal1. Red: Metal4. Pale green: power wiring. '
            'Hover markers for rule and net names. Marker size is enlarged for visibility.</p>' + svg +
            '<p>Intermediate routing evidence; this is not a final layout-check result.</p><pre>' +
            html.escape(json.dumps({k: summary[k] for k in ['by_rule_layer', 'involving_power_net',
                'involving_clock_net', 'near_macros', 'hottest_50um_tiles', 'net_details']}, indent=2)) + '</pre></html>')
    (args.output / "index.html").write_text(page)
    print(json.dumps({k: summary[k] for k in ["iteration", "marker_count", "by_rule_layer", "near_macros"]}, indent=2))


if __name__ == "__main__":
    main()
