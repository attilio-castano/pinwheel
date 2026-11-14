"""Locate drawn contacts at peak modeled terminal loads and connectors."""

import argparse
import csv
from pathlib import Path
import re

import klayout.db as kdb

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import TOP, read, require, sha, write
from streaming_8x4_hold_cap_metal1_trace import DEF, DEF_SHA, ROOT, rail_rows
from streaming_8x4_hold_cap_physical import TARGET, TRIAL


CURRENTS = ROOT / "terminal-currents-03/readback.json"
CURRENTS_SHA = "88acc8523eef86e47b3cc667b7b4987a02cbdef25218b34937bf1dbf48ac6008"
INVENTORY = TRIAL / "views/actual-signal/inventory.json"
INVENTORY_SHA = "d1a6e5fb7f084cc186a4d213e377bcb48869a036f503bfd136859de9baa50fa2"


def contact_geometry(layout, top, master, origin, orient, pin, point, own_rows):
    drawing, labels, contacts = (layout.find_layer(*layer) for layer in ((8, 0), (8, 25), (6, 0)))
    cell = layout.cell(master)
    label, = [shape.text.trans.disp for shape in cell.shapes(labels).each() if shape.text.string == pin]
    polygon, = [shape.polygon for shape in cell.shapes(drawing).each() if shape.polygon.inside(label)]
    cut_shapes = {shape.bbox() for shape in cell.shapes(contacts).each() if shape.is_box()}
    require(cut_shapes and all(cut.width() == cut.height() == 160 for cut in cut_shapes),
            "Unexpected contact drawing")
    local_cuts = [cut for cut in cut_shapes if (kdb.Region(cut) - kdb.Region(polygon)).is_empty()]
    # The standard cell placement origin is its DEF lower-left. S/FS use
    # the cell's 3780 DBU site height, and S also uses its PG pin extent.
    pins = layout.find_layer(8, 2)
    rail_box, = [shape.bbox() for shape in cell.shapes(pins).each() if shape.bbox().contains(label)]
    require(rail_box.left == 0 and orient in {"S", "FS"}, "Unexpected selected cell orientation")
    x, y = origin
    expected = kdb.Trans(kdb.Trans.R180, x + rail_box.right, y + 3780) if orient == "S" else (
        kdb.Trans(kdb.Trans.M0, x, y + 3780))
    instance, = [item for item in top.each_inst() if item.cell_index == cell.cell_index() and item.trans == expected]
    metal = polygon.transformed(instance.trans)
    port = rail_box.transformed(instance.trans)
    center = port.center().y
    xmin, xmax = own_rows[center]
    require(xmin <= port.left < port.right <= xmax and port.height() == 440, "Wrong same-rail pin landing")
    boxes = sorted((box.left, box.bottom, box.right, box.top)
                   for box in (cut.transformed(instance.trans) for cut in local_cuts))
    return dict(master=master, transform=str(instance.trans), followpin_y_dbu=center,
                pin_box_dbu=[port.left, port.bottom, port.right, port.top], contact_boxes_dbu=boxes,
                contact_count=len(boxes), solver_point_in_pin_polygon=metal.inside(kdb.Point(*point)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    require(out.parent == ROOT and not out.exists() and sha(CURRENTS) == CURRENTS_SHA and sha(INVENTORY) == INVENTORY_SHA
            and sha(DEF) == DEF_SHA and sha(TARGET["gds"]) == TARGET["gds_sha256"], "Frozen inputs or output differ")
    current = read(CURRENTS)
    require(current["target_gds_sha256"] == TARGET["gds_sha256"]
            and current["target_odb_sha256"] == TARGET["odb_sha256"], "Terminal current target differs")
    inventory = read(INVENTORY)["instances"]
    design = DEF.read_text()
    layout = kdb.Layout()
    layout.read(str(TARGET["gds"]))
    top, = layout.top_cells()
    require(top.name == TOP and layout.dbu == 0.001, "Wrong GDS units or top")
    rows = rail_rows(design, kdb.Region(top.shapes(layout.find_layer(8, 0))).merged())
    matches = {}
    for rail, report in current["rails"].items():
        connector = report["terminal_edge_peaks"]["ITerm Node"]
        terminal, = [connector[end].rsplit(": ", 1)[1] for end in ("a", "b") if connector[end].startswith("ITerm ")]
        targets = (report["peak_instance_load"]["terminal"], terminal)
        item = report["terminal_nodes_csv"]
        require(bound(item["path"]) == item, "Terminal rows changed")
        with Path(item["path"]).open() as stream:
            selected = {row["terminal"]: row for row in csv.DictReader(stream) if row["terminal"] in targets}
        for target in targets:
            instance, pin = target.rsplit("/", 1)
            master = inventory[instance]["master"]
            require(inventory[instance]["terminals"][pin]["net"] == rail, "Wrong selected instance rail")
            placed, = re.findall(rf"^\s+- {re.escape(instance)} {master} .* \+ PLACED \( (\d+) (\d+) \) (S|FS) ;$",
                                  design, re.M)
            x, y, orient = placed
            row = selected[target]
            point = (int(row["x_dbu"]), int(row["y_dbu"]))
            geometry = contact_geometry(layout, top, master, (int(x), int(y)), orient, pin, point, rows[rail])
            require(geometry["contact_count"] > 0, "No drawn contacts under selected rail conductor")
            matches[target] = dict(rail=rail, point_dbu=point, net_modeled_load_a=abs(float(row["j_a"])), **geometry)

    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-terminal-contact-geometry.v1", status="diagnostic",
                    current_readback=bound(CURRENTS), gds=bound(TARGET["gds"]), def_view=bound(DEF),
                    klayout_version=kdb.__version__, sites=matches, contact_drawing_layer=[6, 0],
                    individual_contact_currents_solved=False))


if __name__ == "__main__":
    main()
