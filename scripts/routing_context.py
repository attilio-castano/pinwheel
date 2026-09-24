#!/usr/bin/env python3
"""Export layout/connectivity context from a retained OpenDB routing snapshot.

Run with the pinned `openroad -python` executable. This reads the database;
it does not repair, place, route, or change its contents.
"""
import argparse
import hashlib
import json
from pathlib import Path
import physical_floorplan
from routing_evidence import parse_report, transform_rect


def decode_segments(net, odb):
    """Export centerlines, deliberately excluding width/spacing/via DRC claims."""
    wire = net.getWire()
    if wire is None:
        return [], dict(wire=False, vias=0, patches=0)
    decoder = odb.dbWireDecoder()
    decoder.begin(wire)
    last, layer, points, segments = None, None, {}, []
    coverage = dict(wire=True, vias=0, patches=0)
    while True:
        op = decoder.next()
        if op == decoder.END_DECODE:
            break
        if op in (decoder.PATH, decoder.SHORT, decoder.VWIRE):
            last, layer = None, decoder.getLayer().getName()
        elif op == decoder.JUNCTION:
            last = points[decoder.getJunctionValue()]
            layer = decoder.getLayer().getName()
        elif op in (decoder.POINT, decoder.POINT_EXT):
            point = list(decoder.getPoint() if op == decoder.POINT else decoder.getPoint_ext()[:2])
            if last is not None and last != point:
                if last[0] != point[0] and last[1] != point[1]:
                    raise ValueError("Non-Manhattan route")
                start, end = sorted([last, point])
                segments.append(dict(net=net.getName(), layer=layer, start=start, end=end))
            points[decoder.getJunctionId()] = point
            last = point
        elif op in (decoder.VIA, decoder.TECH_VIA):
            coverage["vias"] += 1
            layer = decoder.getLayer().getName()
        elif op == decoder.RECT:
            coverage["patches"] += 1
        elif op not in (decoder.RULE, decoder.ITERM, decoder.BTERM):
            raise ValueError(f"Unsupported wire opcode: {op}")
    return segments, coverage


def main():
    import odb

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--placement-exclusions", type=Path,
                        help="Check reserved rectangles against actual blockages, rows and instances")
    parser.add_argument("--drc-report", type=Path,
                        help="Export wire centerlines for non-power nets named by this report")
    parser.add_argument("--extra-drc-report", type=Path, action="append", default=[],
                        help="Include additional diagnostic report nets in the wire selection")
    args = parser.parse_args()
    db = odb.read_db(odb.dbDatabase.create(), str(args.database))
    block = db.getChip().getBlock()
    units = block.getDbUnitsPerMicron()

    def box(rect):
        return [round(v / units, 6) for v in
                [rect.xMin(), rect.yMin(), rect.xMax(), rect.yMax()]]

    def ibox(rect):
        return [rect.xMin(), rect.yMin(), rect.xMax(), rect.yMax()]

    instances = {inst.getName(): dict(cell=inst.getMaster().getName(),
        macro=inst.getMaster().isBlock(), bbox=box(inst.getBBox()),
        bbox_dbu=ibox(inst.getBBox()), orientation=str(inst.getOrient())) for inst in block.getInsts()}
    nets = {}
    power = []
    for net in block.getNets():
        nets[net.getName()] = dict(type=str(net.getSigType()),
            terminals=[dict(instance=it.getInst().getName(), pin=it.getMTerm().getName(),
                            direction=str(it.getIoType())) for it in net.getITerms()],
            ports=[bt.getName() for bt in net.getBTerms()])
        for wire in net.getSWires():
            for shape in wire.getWires():
                if not shape.isVia() and shape.getTechLayer():
                    power.append(dict(net=net.getName(), layer=shape.getTechLayer().getName(),
                                      bbox=box(shape), bbox_dbu=ibox(shape)))
    ports = [dict(name=bt.getName(), layer=shape.getTechLayer().getName(), bbox=box(shape), bbox_dbu=ibox(shape))
             for bt in block.getBTerms() for pin in bt.getBPins() for shape in pin.getBoxes()
             if shape.getTechLayer()]
    macro_pins = [dict(instance=inst.getName(), pin=it.getMTerm().getName(),
                      net=it.getNet().getName() if it.getNet() else None,
                      type=str(it.getSigType()), layer=layer.getName(), bbox=box(rect), bbox_dbu=ibox(rect))
                  for inst in block.getInsts() if inst.getMaster().isBlock()
                  for it in inst.getITerms() for layer, rect in it.getGeometries()]
    with args.database.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    macro_obstructions = []
    for inst in block.getInsts():
        if not inst.getMaster().isBlock():
            continue
        master, offset = inst.getMaster(), inst.getTransform().getOffset()
        orient = str(inst.getOrient())
        if transform_rect([0, 0, master.getWidth(), master.getHeight()], orient, offset) != ibox(inst.getBBox()):
            raise ValueError("Macro transform does not reproduce its placed bounding box")
        if master.getPolygonObstructions():
            raise ValueError("Polygon macro obstructions require an explicit geometry exporter")
        # Independently check the transform against OpenDB's placed pin geometry.
        for it in inst.getITerms():
            expected = sorted((g.getTechLayer().getName(), transform_rect(ibox(g), orient, offset))
                              for pin in it.getMTerm().getMPins() for g in pin.getGeometry() if g.getTechLayer())
            actual = sorted((layer.getName(), ibox(rect)) for layer, rect in it.getGeometries())
            if expected != actual:
                raise ValueError("Macro pin transform differs from OpenDB geometry")
        for obs in master.getObstructions():
            if obs.getTechLayer():
                macro_obstructions.append(dict(instance=inst.getName(), layer=obs.getTechLayer().getName(),
                    bbox_dbu=transform_rect(ibox(obs), orient, offset)))
    signal_segments, coverage = [], {}
    if args.drc_report:
        selected = {n for p in [args.drc_report, *args.extra_drc_report]
                    for m in parse_report(p.read_text()) for n in m["nets"]}
        if selected - nets.keys():
            raise ValueError("DRC report contains nets absent from this database")
        for net in block.getNets():
            if net.getName() in selected and str(net.getSigType()) not in {"POWER", "GROUND"}:
                segments, cov = decode_segments(net, odb)
                signal_segments.extend(segments)
                coverage[net.getName()] = cov
    report = dict(schema=2, database=str(args.database), database_sha256=digest,
                  extractor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  units="micrometres", dbu_per_micron=units, die=box(block.getDieArea()),
                  evidence_helper_sha256=hashlib.sha256(Path(__file__).with_name("routing_evidence.py").read_bytes()).hexdigest(),
                  instances=instances, nets=nets, power_shapes=power, ports=ports, macro_pins=macro_pins,
                  macro_obstructions=macro_obstructions, signal_segments=signal_segments,
                  route_coverage=coverage,
                  routing_obstructions=[dict(layer=o.getBBox().getTechLayer().getName(), bbox_dbu=ibox(o.getBBox()),
                                             except_power_nets=o.isExceptPGNetsObstruction()) for o in block.getObstructions()],
                  layers={l.getName(): dict(width_dbu=l.getWidth(), pitch_x_dbu=l.getPitchX(), pitch_y_dbu=l.getPitchY(),
                                           spacing_dbu=l.getSpacing(), direction=str(l.getDirection()))
                          for l in db.getTech().getLayers() if l.getRoutingLevel() > 0})
    if args.drc_report:
        report["drc_report_sha256"] = hashlib.sha256(args.drc_report.read_bytes()).hexdigest()
        report["wire_selection_reports_sha256"] = {
            str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in [args.drc_report, *args.extra_drc_report]}
    if args.placement_exclusions:
        report["rows"] = [dict(name=r.getName(), bbox=box(r.getBBox()), bbox_dbu=ibox(r.getBBox())) for r in block.getRows()]
        report["placement_blockages"] = [dict(bbox=box(b.getBBox()), soft=b.isSoft(),
            bbox_dbu=ibox(b.getBBox()), max_density=b.getMaxDensity()) for b in block.getBlockages()]
        exclusions = json.loads(args.placement_exclusions.read_text())
        report["exclusions"] = physical_floorplan.exclusion_report(report, exclusions)
        report["exclusions_sha256"] = hashlib.sha256(args.placement_exclusions.read_bytes()).hexdigest()
        report["exclusion_checker_sha256"] = hashlib.sha256(Path(physical_floorplan.__file__).read_bytes()).hexdigest()
    with args.output.open("x") as stream:
        json.dump(report, stream, separators=(",", ":"))
        stream.write("\n")
    print(f"Exported {len(instances)} instances, {len(nets)} nets, {len(power)} power shapes")


if __name__ == "__main__":
    main()
