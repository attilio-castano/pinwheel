"""Trace frozen PSM Metal1 edges to the hierarchical GDS drawing."""

import argparse
from bisect import bisect_left
from collections import Counter
import csv
from itertools import pairwise
import math
from pathlib import Path
import re

import klayout.db as kdb

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import TOP, read, require, sha, write
from streaming_8x4_hold_cap_ir_readback import DBU, SHEET, VOLTAGES, csv_rows, node
from streaming_8x4_hold_cap_physical import TARGET, TRIAL


ROOT = TRIAL / "power-dc"
DEF = TRIAL / "trial.def"
IR_SHA = "d1bb974807b3caf1e1daa85cbddd314e06dede45980074f6d8c932d03c8de7e9"
DEF_SHA = "0ebc4418da924037d2c9cb5beeff5a7d9c830b5ca8091a5cdf1616b790475962"
HEATED = "i2c-sparse-r1-sheet105-01"
MIN_WIDTH = 160
HALF_RAIL = 220
MARGIN = 1800


def narrow_edges(path, rail, sheet):
    with (path / f"{rail}.spice").open() as spice, (path / f"{rail}-current.csv").open() as current:
        rows = csv_rows(current, "Node0 Layer,Node0 X location,Node0 Y location,Node1 Layer,"
                                 "Node1 X location,Node1 Y location,Current")
        for line in spice:
            if not line.startswith("R"):
                continue
            resistor, a, b, value = line.split()
            first, second = node(a), node(b)
            if first[0] != "Node" or second[0] != "Node":
                continue
            layer0, x0, y0, layer1, x1, y1, amps = next(rows)
            require((layer0, round(float(x0) * DBU), round(float(y0) * DBU)) == first[1:]
                    and (layer1, round(float(x1) * DBU), round(float(y1) * DBU)) == second[1:],
                    "SPICE and current CSV endpoints differ")
            if (layer0, layer1) != ("Metal1", "Metal1"):
                continue
            points = (first[2:], second[2:])
            length = max(abs(first[2] - second[2]), abs(first[3] - second[3]))
            resistance = float(value.removeprefix("R="))
            width = sheet * length / resistance
            require(width > 0 and math.isclose(width, round(width), abs_tol=0.01), "Nonintegral modeled width")
            if round(width) < MIN_WIDTH:
                yield points, dict(resistor=resistor, psm_width_dbu=round(width), current_ma=float(amps) * 1000)
        require(next(rows, None) is None, "Extra native current rows")


def rail_rows(text, top_shapes):
    section = text.split("\nSPECIALNETS 2 ;\n", 1)[1].split("\nEND SPECIALNETS\n", 1)[0]
    chunks = re.split(r"^\s+- (VPWR|VGND) \(", section, flags=re.M)
    rails = {}
    for rail, body in zip(chunks[1::2], chunks[2::2], strict=True):
        rows = {}
        for match in re.finditer(r"Metal1 440 \+ SHAPE FOLLOWPIN \( (\d+) (\d+) \) \( (\d+) (\d+) \)",
                                 body):
            x0, y0, x1, y1 = map(int, match.groups())
            require(x0 < x1 and y0 == y1 and y0 not in rows, "Unexpected Metal1 FOLLOWPIN shape")
            box = kdb.Box(x0, y0 - HALF_RAIL, x1, y0 + HALF_RAIL)
            require((kdb.Region(box) - top_shapes).is_empty(), "DEF row is absent from direct GDS drawing")
            rows[y0] = (x0, x1)
        require(rows, "Missing routed row rails")
        rails[rail] = rows
    require(set(rails) == set(VOLTAGES), "Wrong DEF rail inventory")
    return rails


def local_drawing(top, layer, box):
    region = kdb.Region()
    it = top.begin_shapes_rec_touching(layer, box)
    while not it.at_end():
        polygon = it.shape().polygon
        require(polygon is not None, "Non-drawing geometry in Metal1")
        region.insert(polygon.transformed(it.trans()))
        it.next()
    return (region & kdb.Region(box)).merged()


def vertical_strip(polygon, point, center, xmin, xmax):
    x, y = point
    if abs(y - center) <= HALF_RAIL:
        if xmin <= x <= xmax:
            return kdb.Box(max(xmin, x - MIN_WIDTH), center - HALF_RAIL,
                           min(xmax, x + MIN_WIDTH), center + HALF_RAIL)
        return None
    bottom, top = sorted((y, center))
    left, right = max(xmin, x - 2 * MIN_WIDTH), min(xmax, x + 2 * MIN_WIDTH)
    if right - left < MIN_WIDTH:
        return None
    window = kdb.Box(left, bottom, right, top)
    gaps = (kdb.Region(window) - polygon).merged()
    intervals = sorted((gap.bbox().left, gap.bbox().right) for gap in gaps.each())
    uncovered = left
    for gap_left, gap_right in intervals + [(right, right)]:
        if uncovered <= x <= gap_left and gap_left - uncovered >= MIN_WIDTH:
            return kdb.Box(uncovered, bottom, gap_left, top)
        uncovered = max(uncovered, gap_right)
    return None


def row_corridor(polygon, points, centers, rows):
    ymin, ymax = sorted((points[0][1], points[1][1]))
    low = bisect_left(centers, ymin - MARGIN)
    high = bisect_left(centers, ymax + MARGIN)
    for center in sorted(centers[low:high], key=lambda y: abs(y * 2 - ymin - ymax)):
        xmin, xmax = rows[center]
        if not all(xmin <= x <= xmax for x, _ in points):
            continue
        legs = [vertical_strip(polygon, point, center, xmin, xmax) for point in points]
        if any(leg is None or leg.width() < MIN_WIDTH for leg in legs):
            continue
        rail = kdb.Box(min(leg.left for leg in legs), center - HALF_RAIL,
                       max(leg.right for leg in legs), center + HALF_RAIL)
        rects = [legs[0], rail, legs[1]]
        require(all(a.overlaps(b) for a, b in pairwise(rects))
                and all((kdb.Region(rect) - polygon).is_empty() for rect in rects),
                "Corridor is not contained in connected drawing")
        return dict(row_center_dbu=center,
                    rectangles_dbu=[[r.left, r.bottom, r.right, r.top] for r in rects],
                    certified_min_width_dbu=min(HALF_RAIL * 2, *(leg.width() for leg in legs)))
    return None


def classify(top, layer, points, centers, rows):
    (x0, y0), (x1, y1) = points
    box = kdb.Box(min(x0, x1) - MARGIN, min(y0, y1) - MARGIN,
                  max(x0, x1) + MARGIN, max(y0, y1) + MARGIN)
    region = local_drawing(top, layer, box)
    first, second = (kdb.Point(*p) for p in points)
    components = list(region.each())
    for polygon in components:
        if polygon.inside(first) and polygon.inside(second):
            corridor = row_corridor(kdb.Region(polygon), points, centers, rows)
            return ("same_rail_corridor", corridor) if corridor else ("connected_drawing", None)
    if all(any(polygon.inside(point) for polygon in components) for point in (first, second)):
        return "separate_local_polygons", None
    return "endpoint_outside_drawing", None


def checked_case(index, case):
    row, = [row for row in index["cases"] if row["case"] == case]
    native = row["native"]
    require(bound(native["path"]) == native, "Native readback changed")
    evidence = read(native["path"])
    inputs = evidence["artifacts"] + [row["request"]]
    require(all(bound(item["path"]) == item for item in inputs), "Power case artifacts changed")
    return row, inputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    table = out.with_suffix(".tsv")
    require(out.parent == ROOT and out.suffix == ".json" and not out.exists() and not table.exists(),
            "Use a fresh JSON readback in power-dc")
    ir = ROOT / "ir-em-readback.json"
    require(sha(ir) == IR_SHA and sha(DEF) == DEF_SHA and sha(TARGET["gds"]) == TARGET["gds_sha256"]
            and sha(TARGET["odb"]) == TARGET["odb_sha256"], "Frozen inputs changed")
    index = read(ir)
    layout = kdb.Layout()
    layout.read(str(TARGET["gds"]))
    top, = layout.top_cells()
    layer = layout.find_layer(8, 0)
    require(top.name == TOP and layout.dbu == 0.001 and layer is not None, "Wrong GDS top, units or drawing layer")
    rails = rail_rows(DEF.read_text(), kdb.Region(top.shapes(layer)).merged())
    golden, _ = checked_case(index, HEATED)
    geometry = {}
    for rail, rows in rails.items():
        request = read(golden["request"]["path"])
        scale = request["sheet_resistance_scale"]["Metal1"]
        cache = {}
        centers = sorted(rows)
        for points, sample in narrow_edges(ROOT / HEATED, rail, SHEET["Metal1"] * scale):
            state, corridor = classify(top, layer, points, centers, rows)
            require(points not in cache, "Duplicate narrow edge")
            cache[points] = (sample["psm_width_dbu"], state, corridor)
        require(len(cache) == golden["rails"][rail]["segments"]["Metal1"]["outside_table"],
                "Narrow edge count differs from accepted readback")
        geometry[rail] = cache
    cases = []
    for row in index["cases"]:
        case, bindings = checked_case(index, row["case"])
        scale = read(case["request"]["path"]).get("sheet_resistance_scale", {}).get("Metal1", 1)
        results = {}
        for rail, cache in geometry.items():
            counts, peaks, seen = Counter(), {}, set()
            for points, sample in narrow_edges(ROOT / case["case"], rail, SHEET["Metal1"] * scale):
                width, state, corridor = cache[points]
                require(points not in seen and width == sample["psm_width_dbu"], "Model geometry differs across cases")
                seen.add(points)
                counts[state] += 1
                if state not in peaks or sample["current_ma"] > peaks[state]["current_ma"]:
                    peaks[state] = dict(sample, endpoints_dbu=points, corridor=corridor)
            require(seen == cache.keys(), "Missing narrow geometry in a case")
            results[rail] = dict(geometry_counts=counts, highest_currents=peaks)
        cases.append(dict(case=case["case"], rails=results, native_artifacts=bindings))
    require(sha(TARGET["gds"]) == TARGET["gds_sha256"] and sha(DEF) == DEF_SHA, "Geometry inputs changed")
    with table.open("x", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(("rail", "x0_dbu", "y0_dbu", "x1_dbu", "y1_dbu", "psm_width_dbu",
                         "classification", "row_y_dbu", "certified_min_width_dbu", "rectangles_dbu"))
        for rail, cache in geometry.items():
            for (first, second), (width, state, corridor) in sorted(cache.items()):
                certificate = (corridor["row_center_dbu"], corridor["certified_min_width_dbu"],
                               "|".join(",".join(map(str, box)) for box in corridor["rectangles_dbu"])) if corridor else ("", "", "")
                writer.writerow((rail, *first, *second, width, state, *certificate))
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-narrow-metal1.v1", status="diagnostic",
                    gds=bound(TARGET["gds"]), odb=bound(TARGET["odb"]), def_view=bound(DEF),
                    power_readback=bound(ir), producer=bound(Path(__file__)), klayout_version=kdb.__version__,
                    min_corridor_width_dbu=MIN_WIDTH, local_search_margin_dbu=MARGIN, drawing_layer=[8, 0],
                    direct_followpin_rows={rail: len(rows) for rail, rows in rails.items()}, cases=cases,
                    endpoint_certificates=bound(table),
                    physical_current_density_qualified=False))


if __name__ == "__main__":
    main()
