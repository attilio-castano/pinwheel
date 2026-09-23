"""Small, deterministic checks over retained routing evidence.

Geometry checks establish only the predicates named in their output. They are
not a replacement for pin access, foundry DRC, antenna checks, or extracted STA.
"""
from collections import Counter
import math
import re

from physical_floorplan import overlaps, to_dbu

NUMBER = r"[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?"
MARKER = re.compile(
    rf"violation type: ([^\n]+)\n\s*srcs: ([^\n]*)\n\s*"
    rf"bbox = \(({NUMBER}),\s*({NUMBER})\) - \(({NUMBER}),\s*({NUMBER})\)"
    rf" on Layer (\S+)\s*")


def parse_report(text):
    markers, position = [], 0
    for match in MARKER.finditer(text):
        if text[position:match.start()].strip():
            raise ValueError("Unrecognized or truncated DRC report before marker")
        bbox = list(map(float, match.group(3, 4, 5, 6)))
        if not all(map(math.isfinite, bbox)) or bbox[0] > bbox[2] or bbox[1] > bbox[3]:
            raise ValueError("Invalid DRC marker bounding box")
        sources = match[2].strip()
        markers.append(dict(rule=match[1].strip(), sources=sources,
            nets=sorted(set(re.findall(r"\bnet:(\S+)", sources))), bbox=bbox, layer=match[7]))
        position = match.end()
    if text[position:].strip():
        raise ValueError("Unrecognized or truncated DRC report tail")
    return markers


def iteration_counts(text):
    """Count completed iterations, preserving antenna reroute boundaries."""
    run, iteration, counts = -1, None, {}
    for line in text.splitlines():
        if "Start detail routing." in line:
            run, iteration = run + 1, None
        if match := re.search(r"Start (\d+)(?:st|nd|rd|th) (?:optimization|stubborn tiles|guides tiles) iteration", line):
            iteration = int(match[1])
        if match := re.search(r"Number of violations = (\d+)", line):
            key, value = (run, iteration), int(match[1])
            if key in counts and counts[key] != value:
                raise ValueError("Conflicting counts for one routing iteration")
            counts[key] = value
    return counts


def reconcile_iterations(step_text, outer_text=None):
    """Accept a truncated prefix, but never silently choose between conflicts."""
    step = iteration_counts(step_text)
    if outer_text is None:
        return step
    outer = iteration_counts(outer_text)
    a, b = list(step.items()), list(outer.items())
    if a[:min(len(a), len(b))] != b[:min(len(a), len(b))]:
        raise ValueError("Routing logs disagree; neither is a consistent prefix")
    return outer if len(b) > len(a) else step


def transform_rect(rect, orientation, offset):
    """OpenDB orientation about the master origin, then its placement offset."""
    transforms = {
        "R0": lambda x, y: (x, y), "R90": lambda x, y: (-y, x),
        "R180": lambda x, y: (-x, -y), "R270": lambda x, y: (y, -x),
        "MX": lambda x, y: (x, -y), "MY": lambda x, y: (-x, y),
        "MXR90": lambda x, y: (y, x), "MYR90": lambda x, y: (-y, -x),
    }
    if orientation not in transforms or any(type(x) is not int for x in [*rect, *offset]):
        raise ValueError("Unsupported transform or non-integer coordinates")
    points = [transforms[orientation](x, y) for x in (rect[0], rect[2]) for y in (rect[1], rect[3])]
    return [min(p[0] for p in points)+offset[0], min(p[1] for p in points)+offset[1],
            max(p[0] for p in points)+offset[0], max(p[1] for p in points)+offset[1]]


def inside(a, b):
    return b[0] <= a[0] <= a[2] <= b[2] and b[1] <= a[1] <= a[3] <= b[3]


def centerline_crosses(segment, rect):
    """Positive-length centerline penetration into a rectangle's interior."""
    (x0, y0), (x1, y1) = segment["start"], segment["end"]
    if x0 == x1:
        return rect[0] < x0 < rect[2] and max(min(y0, y1), rect[1]) < min(max(y0, y1), rect[3])
    if y0 == y1:
        return rect[1] < y0 < rect[3] and max(min(x0, x1), rect[0]) < min(max(x0, x1), rect[2])
    raise ValueError("Non-Manhattan wire segment")


def marker_key(marker):
    return marker["rule"], marker["layer"], tuple(marker["nets"]), tuple(marker["bbox"])


def marker_group(marker):
    return marker["rule"], marker["layer"], tuple(marker["nets"])


def compare_passes(before, after, before_context, after_context):
    """Separate literal markers, recurring net groups, and physical mutations."""
    a, b = Counter(map(marker_key, before)), Counter(map(marker_key, after))
    groups_a, groups_b = set(map(marker_group, before)), set(map(marker_group, after))
    old, new = before_context["instances"], after_context["instances"]
    added = {n: new[n] for n in new.keys()-old.keys()}
    removed = {n: old[n] for n in old.keys()-new.keys()}
    changed = {n: dict(before=old[n], after=new[n]) for n in old.keys() & new.keys() if old[n] != new[n]}
    old_nets, new_nets = before_context["nets"], after_context["nets"]
    changed_nets = sorted(n for n in old_nets.keys() | new_nets.keys() if old_nets.get(n) != new_nets.get(n))
    return dict(persistent_exact_markers=sum((a & b).values()), removed_exact_markers=sum((a-b).values()),
        added_exact_markers=sum((b-a).values()), recurring_groups=len(groups_a & groups_b),
        new_groups=len(groups_b-groups_a), resolved_groups=len(groups_a-groups_b),
        added_instances=added, removed_instances=removed, changed_instances=changed,
        added_cell_types=dict(Counter(x["cell"] for x in added.values())), changed_nets=changed_nets,
        boundary="Net groups are diagnostic groupings, not independent root causes; net names can change during repair.")


def geometry_checks(markers, context):
    if context.get("schema", 1) < 2:
        raise ValueError("Exact geometry export required; regenerate context with schema 2")
    macros = {n: i for n, i in context["instances"].items() if i["macro"]}
    units = context["dbu_per_micron"]
    fixed = [dict(p, owner=p["instance"]) for p in context["macro_pins"] if p["type"] in {"POWER", "GROUND"}]
    fixed += [dict(p, owner="power_grid") for p in context["power_shapes"]]
    segments = context["signal_segments"]
    crossings = []
    for seg in segments:
        for shape in fixed:
            if shape["layer"] == seg["layer"] and shape["net"] != seg["net"] and centerline_crosses(seg, shape["bbox_dbu"]):
                crossings.append(dict(net=seg["net"], layer=seg["layer"], start=seg["start"], end=seg["end"],
                                     fixed_net=shape["net"], owner=shape["owner"], fixed_bbox_dbu=shape["bbox_dbu"]))
    resolved = []
    for m in markers:
        rect = to_dbu(m["bbox"], units)
        support = [c for c in crossings if c["layer"] == m["layer"] and c["net"] in m["nets"] and
                   c["fixed_net"] in m["nets"] and overlaps(rect, c["fixed_bbox_dbu"]) and
                   centerline_crosses(c, rect)]
        resolved.append(dict(**m, inside_macros=sorted(n for n, i in macros.items() if inside(rect, i["bbox_dbu"])),
                             fixed_power_crossings=support))
    unknown = sorted({n for m in markers for n in m["nets"]} - context["nets"].keys())
    if unknown:
        raise ValueError(f"Marker nets absent from matching database: {unknown[:5]}")
    return dict(markers=len(markers), unique_markers=len(set(map(marker_key, markers))),
        by_layer=dict(Counter(m["layer"] for m in markers)),
        power_involved=sum(any(context["nets"][n]["type"] in {"POWER", "GROUND"} for n in m["nets"]) for m in markers),
        inside_macros=sum(bool(m["inside_macros"]) for m in resolved),
        markers_with_fixed_power_centerline_crossing=sum(bool(m["fixed_power_crossings"]) for m in resolved),
        fixed_power_centerline_crossings=crossings, marker_details=resolved,
        corridor=context.get("exclusions"), route_coverage=context["route_coverage"],
        boundary="Centerline intersections are exact positive geometric evidence. Wire width, vias, spacing and antenna rules are not checked; absence of a crossing is inconclusive.")


def screen_candidate(baseline, candidate, minimum_overflow_improvement=.2):
    """An improvement gate permits a bounded trial; it never certifies routing."""
    if not 0 <= minimum_overflow_improvement <= 1:
        raise ValueError("Invalid improvement threshold")
    for row in [baseline, candidate]:
        numbers = [*row["overflow"].values(), *(v for k, v in row.items() if k not in {"overflow", "timing_stage"})]
        if any(type(v) not in (int, float) or not math.isfinite(v) for v in numbers):
            raise ValueError("Screen metrics must be finite numbers")
    checks = dict(overflow=candidate["overflow"]["Total"] <= (1-minimum_overflow_improvement)*baseline["overflow"]["Total"],
                  metal4_guides=candidate["metal4_guides"] < baseline["metal4_guides"],
                  wirelength=candidate["wirelength_um"] <= 1.1*baseline["wirelength_um"])
    for field in ["instance_area", "repair_area"]:
        checks[field] = candidate[field] <= 1.05*baseline[field]
    checks["power"] = candidate["power_violations"] == 0
    for field in ["slew", "capacitance", "fanout"]:
        checks[field] = candidate[field] <= baseline[field]
    checks["setup_met"] = candidate["setup_slack"] >= 0
    checks["hold_met"] = candidate["hold_slack"] >= 0
    checks["same_timing_stage"] = bool(baseline.get("timing_stage")) and baseline.get("timing_stage") == candidate.get("timing_stage")
    return dict(checks=checks, decision="eligible_for_bounded_trial" if all(checks.values()) else "reject",
                boundary="Inherited timing must have a matching, explicitly identified source stage. Coarse guide overlap and congestion do not prove pin access or routability.")


def pin_access_summary(text):
    keys = ["stdCellPinCnt", "stdCellPinNoAp", "macroGenAp", "macroValidPlanarAp", "macroValidViaAp", "macroNoAp"]
    counts = {k: int(m[1]) for k in keys if (m := re.search(r"^#" + k + r"\s*=\s*(\d+)\s*$", text, re.M))}
    complete = "Complete pin access." in text and len(counts) == len(keys)
    decision = "inconclusive"
    if complete and counts["stdCellPinCnt"] > 0 and counts["macroGenAp"] > 0:
        decision = "pass" if counts["stdCellPinNoAp"] == counts["macroNoAp"] == 0 else "reject"
    return dict(counts=counts, decision=decision,
                off_grid_warnings=len(re.findall(r"\[WARNING DRT-0418\]", text)),
                boundary="Minimum-one-access-point probe. Initial grid warnings are separate from final no-access counts; this does not establish simultaneous routability.")
