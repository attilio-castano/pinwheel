"""Resolve reviewed macro-local parent contact rectangles to frozen Metal4 nodes."""

import argparse
from decimal import Decimal
import math
from pathlib import Path

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, write
from streaming_8x4_hold_cap_ir import VOLTAGES
from streaming_8x4_hold_cap_ir_readback import DBU, node, rail_rectangles
from streaming_8x4_hold_cap_physical import EVIDENCE, TARGET, TRIAL


ROOT = TRIAL / "power-dc"
LEF = TRIAL / "views/official-format.lef"
RECTANGLES = TRIAL / "views/rehearsal-view-readback.json"
DISTRIBUTED_SHA = {
    "VPWR": "2711022261c51c2d9bbfed170493f69893e4f74ecaa27c563225446ddb142a95",
    "VGND": "505a32cf618abb8bfbc27bfce436e2ec09dada1ab6730fd42fd02e6509c72a92",
}
INPUT_SCHEMA = "pinwheel.streaming-8x4-hold-cap-parent-power-input.v1"
OUTPUT_SCHEMA = "pinwheel.streaming-8x4-hold-cap-parent-power-resolved.v1"


def numerical(value, label):
    require(type(value) in (int, float) and math.isfinite(value) and value >= 0,
            f"{label} must be a finite nonnegative number")
    return value


def dbu(um):
    value = Decimal(str(numerical(um, "Contact dimension"))) * DBU
    require(value == value.to_integral_value(), "Use the frozen macro's 1 nm database grid")
    return int(value)


def read_input(path):
    entry = read(path)
    require(set(entry) == {"schema", "classification", "coordinate_frame", "target_odb_sha256",
                           "target_gds_sha256", "contact_map", "source_voltage", "external_impedance", "evidence"}
            and entry["schema"] == INPUT_SCHEMA and entry["classification"] in ("reviewed_parent", "illustrative")
            and entry["coordinate_frame"] == "macro_local_um"
            and all(entry[f"target_{kind}_sha256"] == TARGET[f"{kind}_sha256"] for kind in ("odb", "gds")),
            "Use the exact candidate, classified source data and macro-local coordinates")
    evidence = entry["evidence"]
    require(isinstance(evidence, list) and all(set(item) == {"path", "sha256"} and bound(item["path"]) == item
                                               for item in evidence)
            and (entry["classification"] == "illustrative" or evidence), "Missing or changed boundary source evidence")
    source = entry["source_voltage"]
    require(set(source) == {"reference_point", "minimum_v", "maximum_v"} and source["reference_point"].strip(),
            "Supply the guaranteed source range and reference point")
    minimum = numerical(source["minimum_v"], "Source minimum")
    maximum = numerical(source["maximum_v"], "Source maximum")
    require(0 < minimum <= maximum, "Invalid source range")
    impedance = entry["external_impedance"]
    require(set(impedance) == {"interpretation", "vpwr_ohm", "vgnd_ohm", "return_path"}
            and impedance["interpretation"] == "ohm_per_resolved_source_node" and impedance["return_path"].strip(),
            "Supply explicit per-node DC resistance and return path")
    for rail in VOLTAGES:
        require(numerical(impedance[f"{rail.lower()}_ohm"], rail) <= 100, "Resistance exceeds the runner's range")
    contact_map = entry["contact_map"]
    require(set(contact_map) == {"ownership", "contacts"} and contact_map["ownership"].strip()
            and isinstance(contact_map["contacts"], list)
            and {contact["rail"] for contact in contact_map["contacts"]} == set(VOLTAGES),
            "The contact map must identify its owner and cover both rails")
    return entry


def source_nodes(rail, pins):
    path = ROOT / "ports-03" / f"{rail}.spice"
    item = bound(path)
    require(item["sha256"] == DISTRIBUTED_SHA[rail], "Distributed physical grid changed")
    pins.append(item)
    points, resistive = set(), set()
    with path.open() as stream:
        for line in stream:
            if line.startswith("V"):
                name, reference, dc, voltage = line.split()[1:]
                kind, layer, x, y = node(name)
                require((kind, layer, reference, dc, float(voltage)) == ("Node", "Metal4", "0", "DC", VOLTAGES[rail]),
                        "Wrong source in native pin-node census")
                points.add((x, y))
            elif line.startswith("R"):
                for name in line.split()[1:3]:
                    if name.startswith("Node_Metal4_"):
                        resistive.add(node(name)[2:])
    require(len(points) == 5215 and resistive == points, "Incomplete physical Metal4 node census")
    return points


def resolve(contacts, rail, rectangles, nodes):
    rail_rectangles_dbu = [tuple(map(dbu, box)) for box in rectangles]
    assignments = []
    all_nodes = set()
    for contact in contacts:
        require(set(contact) == {"rail", "layer", "x_um", "y_um", "width_um", "height_um"}
                and contact["layer"] == "Metal4", "Unsupported parent contact shape or layer")
        if contact["rail"] != rail:
            continue
        x, y, width, height = (dbu(contact[key]) for key in ("x_um", "y_um", "width_um", "height_um"))
        left, bottom, right, top = (x - width / 2, y - height / 2, x + width / 2, y + height / 2)
        require(width > 0 and height > 0 and any(x0 <= left <= right <= x1 and y0 <= bottom <= top <= y1
                                                for x0, y0, x1, y1 in rail_rectangles_dbu),
                f"{rail} contact is outside a verified macro rail rectangle")
        selected = {(px, py) for px, py in nodes if left <= px <= right and bottom <= py <= top}
        require(selected and all_nodes.isdisjoint(selected), f"{rail} contact has no exact node or overlaps another contact")
        assignments.append(dict(contact=contact, source_nodes_um=[[a / DBU, b / DBU] for a, b in sorted(selected)]))
        all_nodes.update(selected)
    return assignments, sorted(all_nodes)


def source_csv(points, voltage):
    # OpenROAD multiplies a parsed double by DBU and truncates to int. Adding
    # one hundredth of a DBU retains the intended exact coordinate after that
    # conversion. Its integer half-size truncates this 1 DBU probe to a point.
    return "".join(f"{(x + 0.01) / DBU:.5f},{(y + 0.01) / DBU:.5f},0.001,{voltage}\n" for x, y in points)


def prepare(path):
    pins = [bound(path), bound(LEF), bound(RECTANGLES)]
    entry = read_input(path)
    pins.extend(entry["evidence"])
    require(pins[2]["sha256"] == EVIDENCE["views/rehearsal-view-readback.json"]
            and pins[1]["sha256"] == read(RECTANGLES)["view_sha256"]["lef"], "Frozen pin geometry changed")
    for kind in ("odb", "gds"):
        item = bound(TARGET[kind])
        require(item["sha256"] == TARGET[f"{kind}_sha256"], "Frozen physical candidate changed")
        pins.append(item)
    rectangles = rail_rectangles(LEF)
    resolved = {}
    for rail in VOLTAGES:
        records, points = resolve(entry["contact_map"]["contacts"], rail, rectangles[rail], source_nodes(rail, pins))
        resolved[rail] = dict(contacts=records, nodes_um=[[x / DBU, y / DBU] for x, y in points],
                              csv=source_csv(points, VOLTAGES[rail]),
                              external_ohm=entry["external_impedance"][f"{rail.lower()}_ohm"])
    require(all(bound(item["path"]) == item for item in pins), "Boundary inputs changed during resolution")
    return entry, pins, resolved


def run(path, out):
    require(out.parent == ROOT and not out.exists(), "Use a fresh ignored power-dc directory")
    entry, pins, resolved = prepare(path)
    out.mkdir(exist_ok=False)
    results = {}
    for rail, context in resolved.items():
        source_file = out / f"{rail}.vsrc"
        source_file.write_text(context.pop("csv"))
        results[rail] = dict(context, vsrc=bound(source_file))
    source = entry["source_voltage"]
    write(out / "resolved.json", dict(schema=OUTPUT_SCHEMA, inputs=pins, input=entry, producer=bound(__file__),
          target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"], rails=results,
          diagnostic_rail_voltages_v=VOLTAGES,
          nominal_in_declared_source_range=source["minimum_v"] <= VOLTAGES["VPWR"] <= source["maximum_v"],
          contacts_reconciled_to_frozen_metal4=True, qualified_ir_drop=False, transient_droop_analyzed=False))


def check_resolved(path):
    item = bound(path)
    receipt = read(path)
    require(receipt["schema"] == OUTPUT_SCHEMA and set(receipt["rails"]) == set(VOLTAGES)
            and receipt["diagnostic_rail_voltages_v"] == VOLTAGES
            and receipt["producer"] == bound(__file__), "Invalid parent resolution receipt")
    entry, pins, resolved = prepare(Path(receipt["inputs"][0]["path"]))
    require(receipt["input"] == entry and receipt["inputs"] == pins
            and all(receipt[f"target_{kind}_sha256"] == TARGET[f"{kind}_sha256"] for kind in ("odb", "gds"))
            and item == bound(path), "Parent resolution inputs changed")
    require(receipt["nominal_in_declared_source_range"] and
            entry["source_voltage"]["minimum_v"] <= VOLTAGES["VPWR"] <= entry["source_voltage"]["maximum_v"],
            "The nominal diagnostic source is outside the declared parent range")
    for rail, row in receipt["rails"].items():
        source = Path(row["vsrc"]["path"])
        expected = resolved[rail]
        require(source.read_text() == expected.pop("csv") and bound(source) == row["vsrc"]
                and row == dict(expected, vsrc=row["vsrc"]), "Parent contact CSV or nodes changed")
    return receipt, item


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.input.resolve(strict=True), args.out.resolve())
    print(args.out / "resolved.json")


if __name__ == "__main__":
    main()
