"""Rehearse physical macro power attachment against the published TT0004 die."""

import argparse
from collections import Counter
from pathlib import Path

import klayout.db as db

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, write
from streaming_8x4_hold_cap_ir_readback import rail_rectangles
from streaming_8x4_hold_cap_parent_power import dbu, resolve, source_nodes
from streaming_8x4_hold_cap_physical import EVIDENCE, TARGET, TRIAL


ROOT = TRIAL.parents[1] / "tt-parent-attachment-20261115"
PDK_LAYERS = {"Metal4": (50, 0), "Metal4.pin": (50, 2), "TopVia1": (125, 0), "TopMetal1": (126, 0)}
RAILS = {"VPWR", "VGND"}
CALIBRATION = "tt_um_factory_test"
VALIDATION = ("tt_um_2048_vga_game", "tt_um_lisa", "tt_um_urish_sic1")
TT0004_INPUTS = {
    "tt0004-foundry-01/TT0004.oas": "c102e52ab4de3df230e481dfa856f318d86492ece29ee186d6489e7928ca92de",
    "tt0004-reference-01/tt_um_factory_test.lef": "8bc2f42ea55a0dd56484d80ecf16db0a9bc7221e02f71bc43d3b5f70f0532d75",
    "tt0004-reference-01/tt_um_factory_test.oas": "7964c93e380efc43075bab8698f32f173cb6ad9f1db965b8184da8753f72bd5d",
    "tt0004-reference-01/tt_um_2048_vga_game.lef": "11cc1ed1ba7983d3ff1baf098a47349c6b0b1e4ee9dfc770559fb4554ded4224",
    "tt0004-reference-01/tt_um_2048_vga_game.oas": "b7423bd15d109beee0070e0cdee31fa335e7857c4f45d1f2b47fd3b9292fce77",
    "tt0004-reference-01/tt_um_lisa.lef": "286014945325039c73584197b94ad36e93a6c4a52d771de18c1167fae3d4023c",
    "tt0004-reference-01/tt_um_lisa.oas": "f5551cda77ddd28a1a65b0e6c7f4b382181fc402a186f5849208d351c5040089",
    "tt0004-reference-01/tt_um_urish_sic1.lef": "e1d39765228d05aebbfceb4f36815e34f61b921bdb30881f52b66ca802f6c925",
    "tt0004-reference-01/tt_um_urish_sic1.oas": "3a375c71c11b447a8e9bd9a2bf268e60b2b2c6d604af7eadd79dfa1c47b5f410",
    "tt0004-reference-01/pdn.tcl": "8a5ec831f337899da0432a6c06b655a0f176c4e235240dce7b8de20181fe1679",
    "tt0004-reference-01/odb_power.py": "18e78f6bb11ca359ca5b944cdcb2ceda6c8189253ee0ab6c50ef6d91b0a35daa",
}


def checked(path, digest):
    item = bound(path)
    require(item["sha256"] == digest, f"Unexpected frozen input: {path.name}")
    return item


def load(path):
    layout = db.Layout()
    layout.read(str(path))
    require(abs(layout.dbu - 0.001) < 1e-12, f"{path.name} does not use 1 nm coordinates")
    return layout


def box_data(box):
    return [box.left, box.bottom, box.right, box.top]


def layer(layout, name):
    index = layout.find_layer(*PDK_LAYERS[name])
    require(index is not None, f"Missing required {name} stream layer")
    return index


def region_of(boxes):
    result = db.Region()
    for box in boxes:
        result.insert(box)
    return result


def pins_in_drawing(layout, cell, lef):
    rectangles = {rail: [db.Box(*map(dbu, box)) for box in values]
                  for rail, values in rail_rectangles(lef).items()}
    pins = db.Region(cell.shapes(layer(layout, "Metal4.pin")))
    drawn = db.Region(cell.shapes(layer(layout, "Metal4")))
    require(not (region_of(rectangles["VGND"]) & region_of(rectangles["VPWR"])).area(),
            "Overlapping LEF power rails")
    for rail, boxes in rectangles.items():
        zone = region_of(boxes)
        require((zone - pins).is_empty() and (zone - drawn).is_empty(), f"{rail} LEF shape differs from GDS")
    labels = {}
    for pair in ((50, 25), (50, 1), (50, 2)):
        index = layout.find_layer(*pair)
        if index is None:
            continue
        for shape in cell.shapes(index).each():
            if shape.is_text() and shape.text_string in RAILS:
                labels.setdefault(shape.text_string, set()).add(tuple(box_data(shape.bbox())[:2]))
    require(set(labels) == RAILS and all(
        any(box.contains(db.Point(*point)) for box in rectangles[rail]) for rail in sorted(RAILS) for point in labels[rail]),
        "Missing or displaced named power-pin labels")
    return rectangles, {rail: sorted(points) for rail, points in labels.items()}


def chip_geometry(layout, cell):
    top = []
    for shape in cell.shapes(layer(layout, "TopMetal1")).each():
        box = shape.bbox()
        if shape.is_path() and box.width() > 2_700_000 and box.height() == 10_000:
            require((db.Region(shape.path) ^ db.Region(box)).is_empty(), "Top strap is not a rectangular segment")
            top.append(box)
    families = Counter((box.left, box.right) for box in top)
    require(sorted(families.values()) == [52, 52, 52],
            "Wrong TT0004 parent strap inventory")
    cut_layer = layer(layout, "TopVia1")
    bottom_layer = layer(layout, "Metal4")
    top_layer = layer(layout, "TopMetal1")
    vias = []
    wrong_layer_vias = []
    via3 = layout.find_layer(49, 0)
    require(via3 is not None, "Missing Via3 stream layer for the negative control")
    for inst in cell.each_inst():
        if not inst.cell.name.startswith("VIA_via4_5_2100_10000_"):
            continue
        require(not inst.is_regular_array(), "Unexpected array of attachment instances")
        master = inst.cell
        pads = [db.Region(master.shapes(index)).transformed(inst.trans).bbox() for index in (bottom_layer, top_layer)]
        boxes = [shape.bbox().transformed(inst.trans) for shape in master.shapes(cut_layer).each() if shape.is_box()]
        require(len(boxes) == 22 and all(pad.contains(cut.p1) and pad.contains(cut.p2) for pad in pads for cut in boxes),
                "The reference TopVia1 footprint lacks complete enclosure")
        via_bottom, via_top = pads
        strap, = [box for box in top if box.contains(via_top.p1) and box.contains(via_top.p2)]
        vias.append((via_bottom, boxes, (strap.left, strap.right), strap.center().y))
        if not master.shapes(via3).is_empty():
            wrong_layer_vias.append(vias[-1])
    require(len(vias) == 2180, "Wrong TT0004 macro attachment primitive count")
    return top, vias, wrong_layer_vias


def attachments(rectangles, placement, vias, family_rails=None):
    zones = {rail: [box.transformed(placement) for box in boxes] for rail, boxes in rectangles.items()}
    result = []
    for landing, cuts, family, strap_y in vias:
        if not any(landing.overlaps(box) for boxes in zones.values() for box in boxes):
            continue
        owners = [(rail, i) for rail, boxes in zones.items() for i, box in enumerate(boxes)
                  if box.contains(landing.p1) and box.contains(landing.p2)]
        require(len(owners) == 1, "A parent attachment is partially supported or overlaps two pins")
        rail, i = owners[0]
        if family_rails is not None:
            require(family_rails.get(family) == rail, "Parent stripe family connects to the wrong named macro rail")
        result.append(dict(rail=rail, pin_index=i, landing_dbu=box_data(landing.transformed(placement.inverted())),
                           cuts_dbu=sorted(box_data(cut.transformed(placement.inverted())) for cut in cuts),
                           parent_strap_span_dbu=family, parent_strap_y_dbu=strap_y))
    require({(row["rail"], row["pin_index"]) for row in result}
            == {(rail, i) for rail, boxes in zones.items() for i in range(len(boxes))},
            "One or more named macro rail pins has no attached parent cuts")
    return sorted(result, key=lambda row: (row["rail"], row["landing_dbu"]))


def project_control(layout, top, vias, name, family_rails=None):
    project, = [inst for inst in top.each_inst() if inst.cell.name == name]
    require(not project.is_regular_array(), "Expected one scalar project instance")
    reference = ROOT / "tt0004-reference-01"
    leaf = load(reference / f"{name}.oas")
    source = leaf.cell(name)
    require(source is not None and source.bbox() == project.cell.bbox(), "Placed leaf dimensions changed")
    for surface in ("Metal4", "Metal4.pin"):
        actual = db.Region(project.cell.shapes(layer(layout, surface)))
        expected = db.Region(source.shapes(layer(leaf, surface)))
        require((actual ^ expected).is_empty(), "Placed leaf Metal4 differs from separately published project")
    lef = reference / f"{name}.lef"
    rectangles, labels = pins_in_drawing(leaf, source, lef)
    _, placed_labels = pins_in_drawing(layout, project.cell, lef)
    require(labels == placed_labels, "Named placed macro rail labels changed")
    contacts = attachments(rectangles, project.trans, vias, family_rails)
    return dict(placement=str(project.trans), bounds_dbu=box_data(project.bbox()),
                pin_labels_dbu=labels, macro_pin_counts={rail: len(boxes) for rail, boxes in rectangles.items()},
                contacts=contacts), rectangles, project.trans


def rejected(action, reason):
    try:
        action()
    except ValueError as error:
        require(reason in str(error), f"Wrong negative control rejection: {error}")
        return str(error)
    raise ValueError(f"Accepted negative control instead of rejecting {reason}")


def geometry_controls(layout, top, vias, wrong_layer_vias):
    factory, factory_pins, factory_transform = project_control(layout, top, vias, CALIBRATION)
    families = {}
    for row in factory["contacts"]:
        span, rail = row["parent_strap_span_dbu"], row["rail"]
        require(families.setdefault(span, rail) == rail, "A parent strap spans two named power families")
    require(set(families.values()) == RAILS and len(families) == 2, "Calibration did not name both parent families")
    projects = {CALIBRATION: factory}
    for name in VALIDATION:
        projects[name], _, _ = project_control(layout, top, vias, name, families)
    shifted = factory_transform * db.Trans(1800, 0)
    swapped = {span: ("VGND" if rail == "VPWR" else "VPWR") for span, rail in families.items()}
    controls = dict(wrong_layer=rejected(lambda: attachments(factory_pins, factory_transform, wrong_layer_vias, families),
                                         "has no attached parent cuts"),
                    wrong_rail=rejected(lambda: attachments(factory_pins, factory_transform, vias, swapped),
                                        "wrong named macro rail"),
                    shifted_1800_dbu=rejected(lambda: attachments(factory_pins, shifted, vias, families),
                                              "partially supported"))
    return families, projects, controls


def projection(straps, families, candidate, transform, nodes):
    result = {}
    for rail, pins in candidate.items():
        contacts = []
        covered = set()
        trunks = sorted((box.bbox() for box in region_of(pins).merged().each()), key=lambda box: box.left)
        require(len(trunks) == 35 and all(box.height() == 710_640 for box in trunks)
                and (region_of(trunks) ^ region_of(pins)).is_empty(), "Wrong frozen 8×4 rail stripe geometry")
        for i, pin in enumerate(trunks):
            placed = pin.transformed(transform)
            for strap in straps:
                if families.get((strap.left, strap.right)) != rail or not placed.overlaps(strap):
                    continue
                contact = (placed & strap).transformed(transform.inverted())
                covered.add(i)
                contacts.append(dict(rail=rail, layer="Metal4", x_um=(contact.left + contact.right) / 2000,
                                     y_um=(contact.bottom + contact.top) / 2000,
                                     width_um=contact.width() / 1000, height_um=contact.height() / 1000))
        rectangles = [tuple(axis / 1000 for axis in box_data(box)) for box in pins]
        assignments, selected = resolve(contacts, rail, rectangles, nodes[rail])
        result[rail] = dict(contact_count=len(contacts), matched_stripe_count=len(covered), stripe_count=len(trunks),
                            lef_pin_rectangles=len(pins),
                            node_count=len(selected), contact_assignments=assignments)
    return dict(historical_phase=str(transform), actual_parent_attachment=False, rails=result)


def run(out):
    require(out.parent == ROOT and not out.exists(), "Use a fresh ignored parent attachment receipt")
    inputs = [checked(ROOT / name, digest) for name, digest in TT0004_INPUTS.items()]
    inputs.extend(checked(TARGET[kind], TARGET[f"{kind}_sha256"]) for kind in ("odb", "gds"))
    views = TRIAL / "views/rehearsal-view-readback.json"
    inputs.append(checked(views, EVIDENCE["views/rehearsal-view-readback.json"]))
    lef = TRIAL / "views/official-format.lef"
    inputs.append(checked(lef, read(views)["view_sha256"]["lef"]))
    layout = load(ROOT / "tt0004-foundry-01/TT0004.oas")
    top, = layout.top_cells()
    require(top.name == "TT0004" and box_data(top.bbox()) == [0, 0, 3_600_000, 5_000_000], "Wrong foundry top")
    straps, vias, wrong_layer_vias = chip_geometry(layout, top)
    families, projects, controls = geometry_controls(layout, top, vias, wrong_layer_vias)
    candidate_layout = load(TARGET["gds"])
    candidate_cell, = candidate_layout.top_cells()
    candidate, labels = pins_in_drawing(candidate_layout, candidate_cell, lef)
    nodes = {rail: source_nodes(rail, inputs) for rail in sorted(RAILS)}
    phases = {name: db.Trans.from_s(projects[name]["placement"]) for name in ("tt_um_urish_sic1", "tt_um_lisa")}
    results = {name: projection(straps, families, candidate, transform, nodes) for name, transform in phases.items()}
    require(all(bound(item["path"]) == item for item in inputs), "Geometry input changed during readback")
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-parent-attachment.v1", inputs=inputs,
                    producer=bound(__file__), pdk_layers=PDK_LAYERS, tt0004_projects=projects,
                    tt0004_strap_families=[dict(x_span_dbu=span, inferred_rail=rail) for span, rail in sorted(families.items())],
                    negative_controls=controls, frozen_macro_labels_dbu=labels, candidate_historical_projections=results,
                    actual_27a_attachment_verified=False, parent_supply_model_qualified=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.out.resolve())
    print(args.out)


if __name__ == "__main__":
    main()
