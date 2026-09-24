#!/usr/bin/env python3
"""Measure coarse guide overlap with SRAM bodies before detailed routing.

Guide overlap is a screening metric, not a wire short or a proof of routability.
The guide and database must come from the same completed global-routing step.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path

from physical_checkpoint import artifact_path, sha
from physical_floorplan import overlaps, to_dbu


def parse_guides(text, units):
    if type(units) is not int or units <= 0:
        raise ValueError("Invalid database units")
    lines = iter(line.strip() for line in text.splitlines() if line.strip())
    result = []
    for net in lines:
        if net in ("(", ")") or next(lines, None) != "(":
            raise ValueError("Malformed guide header")
        for line in lines:
            if line == ")":
                break
            parts = line.split()
            if len(parts) != 5:
                raise ValueError("Malformed guide rectangle")
            rect_dbu = list(map(int, parts[:4]))
            x0, y0, x1, y1 = (v / units for v in rect_dbu)
            if x0 >= x1 or y0 >= y1:
                raise ValueError("Invalid guide rectangle")
            result.append(dict(net=net, layer=parts[4], bbox=[x0, y0, x1, y1], bbox_dbu=rect_dbu))
        else:
            raise ValueError("Truncated guide block")
    if not result:
        raise ValueError("No routing guides")
    return result


def summarize(guides, context):
    macros = {n: v for n, v in context["instances"].items() if v["macro"]}
    layers = defaultdict(lambda: dict(rectangles=0, nets=set(), macro_connected_nets=set()))
    for guide in guides:
        net = context["nets"].get(guide["net"])
        if net is None:
            raise ValueError(f"Guide net missing from database: {guide['net']}")
        if "dbu_per_micron" in context and "bbox_dbu" in guide:
            intersects = any(overlaps(guide["bbox_dbu"], macro.get("bbox_dbu") or
                             to_dbu(macro["bbox"], context["dbu_per_micron"])) for macro in macros.values())
        else:
            intersects = any(overlaps(guide["bbox"], macro["bbox"]) for macro in macros.values())
        if intersects:
            row = layers[guide["layer"]]
            row["rectangles"] += 1
            row["nets"].add(guide["net"])
            if any(term["instance"] in macros for term in net["terminals"]):
                row["macro_connected_nets"].add(guide["net"])
    return dict(macros=macros, overlapping_guides={layer: {
        "rectangles": row["rectangles"], "nets": len(row["nets"]),
        "macro_connected_nets": len(row["macro_connected_nets"])}
        for layer, row in sorted(layers.items())})


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--design', type=Path, required=True)
    p.add_argument('--state', type=Path, required=True)
    p.add_argument('--context', type=Path, required=True)
    p.add_argument('--guide', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    state = json.loads(args.state.read_text())
    context = json.loads(args.context.read_text())
    database = artifact_path(state['odb'], args.design)
    if (args.state.parent.resolve() != database.parent.resolve() or
            args.guide.parent.resolve() != database.parent.resolve()):
        raise ValueError('Guide, database and completed state must belong to the same step')
    if context['database'] != state['odb'] or context['database_sha256'] != sha(database):
        raise ValueError('Context does not match the completed database')
    guides = parse_guides(args.guide.read_text(), context['dbu_per_micron'])
    report = dict(boundary=__doc__, **summarize(guides, context),
                  artifacts={str(p): sha(p) for p in [args.state, args.context, args.guide, database]},
                  reporter_sha256=sha(Path(__file__)))
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps(report['overlapping_guides'], indent=2))


if __name__ == '__main__':
    main()
