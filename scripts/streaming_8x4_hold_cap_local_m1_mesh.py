"""Geometry-conforming Metal1 replacement for the frozen VGND decap neighborhood."""

from dataclasses import dataclass
from functools import cached_property
import math
import re

import klayout.db as kdb
import numpy as np

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import TOP, read, require, sha
from streaming_8x4_hold_cap_contact_model import (
    CONTACT_OHM, CONT_REFERENCE_A, GEOMETRY, GEOMETRY_SHA, M1, M1_SHEET_OHM,
    Network, add_source, box_mask, contact_regions, coordinates, local_region, mesh, polygon_mask, rect,
)
from streaming_8x4_hold_cap_ir_readback import metal_limit_ma
from streaming_8x4_hold_cap_metal1_trace import DEF, DEF_SHA
from streaming_8x4_hold_cap_physical import TARGET
from streaming_8x4_hold_cap_terminal_geometry import INVENTORY, INVENTORY_SHA
from streaming_8x4_hold_cap_via_audit import parse_def


TERMINAL = "FILLER_3_3251/VSS"
REFERENCE_POINT_DBU = (1565935, 18900)
SECTION_X_DBU = (1565700, 1565800, 1565900, REFERENCE_POINT_DBU[0])
ROW_SPAN_DBU = (18680, 19120)
SELECTED_VIA_CENTER_DBU = (1567400, 18900)
WINDOWS = {
    "pre_via": (1563300, 16600, 1566700, 21100),
    "with_via": (1562400, 16600, 1569100, 21100),
    "wide": (1559030, 16600, 1570150, 21100),
}


@dataclass
class LocalGeometry:
    layout: object
    top: object
    window: object
    metal: object
    lower: dict
    cuts: dict
    via_cut_boxes_dbu: tuple
    seams: dict
    bindings: list

    @cached_property
    def inventory(self):
        return read(INVENTORY)["instances"]

    @cached_property
    def placements(self):
        # DEF has named instances while GDS contains the placed master refs.
        pattern = re.compile(r"^\s+- (\S+) (\S+) [^\n]*?\+ (?:PLACED|FIXED) \( (\d+) (\d+) \) (\w+) ;$", re.M)
        return {name: (master, int(x), int(y), orient) for name, master, x, y, orient in
                pattern.findall(DEF.read_text().split("\nEND COMPONENTS\n", 1)[0])}

    def load_polygon(self, terminal):
        instance, pin = terminal.rsplit("/", 1)
        master, x, y, orient = self.placements[instance]
        require(self.inventory[instance]["master"] == master
                and self.inventory[instance]["terminals"][pin]["net"] == "VGND",
                f"Terminal is not on the target rail: {terminal}")
        cell = self.layout.cell(master)
        bounds, = list(local_region(self.layout, cell, (189, 4)).each_merged())
        origin = bounds.bbox()
        w, h = origin.width(), origin.height()
        require((origin.left, origin.bottom) == (0, 0), "Unexpected master site origin")
        transform, dx, dy = {"N": (kdb.Trans.R0, 0, 0), "S": (kdb.Trans.R180, w, h),
                             "FN": (kdb.Trans.M90, w, 0), "FS": (kdb.Trans.M0, 0, h)}[orient]
        placement = kdb.Trans(transform, x + dx, y + dy)
        require(sum(ref.cell_index == cell.cell_index() and ref.trans == placement
                    for ref in self.top.each_inst()) == 1, f"GDS placement differs: {terminal}")
        pin_labels = self.layout.find_layer(8, 25)
        label, = [shape.text.trans.disp for shape in cell.shapes(pin_labels).each()
                  if shape.is_text() and shape.text.string == pin]
        polygon, = [p for p in local_region(self.layout, cell, M1).each_merged() if p.inside(label)]
        landed = (kdb.Region(polygon.transformed(placement)) & kdb.Region(self.metal)).merged()
        require(not landed.is_empty(), f"No geometric landing for {terminal} in replacement region")
        return landed


def seam_intersections(poly, window):
    groups = dict(left=[], right=[], bottom=[], top=[])
    for edge in kdb.Region(poly).edges().each():
        a, b = edge.p1, edge.p2
        if a.x == b.x == window.left:
            groups["left"].append(tuple(sorted((a.y, b.y))))
        elif a.x == b.x == window.right:
            groups["right"].append(tuple(sorted((a.y, b.y))))
        elif a.y == b.y == window.bottom:
            groups["bottom"].append(tuple(sorted((a.x, b.x))))
        elif a.y == b.y == window.top:
            groups["top"].append(tuple(sorted((a.x, b.x))))
    require(groups == dict(left=[ROW_SPAN_DBU], right=[ROW_SPAN_DBU], bottom=[], top=[]),
            f"Crop cuts an unexpected conductor boundary: {groups}")
    return {side: spans[0] for side, spans in groups.items() if spans}


def geometric_via(layout, top, window, metal):
    families, placements = parse_def(DEF)
    name, = [key for key, value in families.items() if value["cut"] == "Via1"]
    exact_arrays = {point for point in placements["VGND", name] if window.contains(kdb.Point(*point))}
    center = SELECTED_VIA_CENTER_DBU
    require(exact_arrays == ({center} if window.contains(kdb.Point(*center)) else set()),
            f"Unexpected VGND Via1 array centers in the crop: {exact_arrays}")
    if not exact_arrays:
        # The split plane must not cut a part of a neighboring physical via.
        for x, y in placements["VGND", name]:
            for l, b, r, t in families[name]["boxes"]:
                contact = kdb.Box(x+l, y+b, x+r, y+t)
                require((kdb.Region(contact) & kdb.Region(metal)).is_empty(),
                        "Crop intersects Via1 with center outside")
        return ()
    cell = layout.cell("VIA_" + name)
    pos = kdb.Trans(*center)
    ref, = [ref for ref in top.each_inst() if ref.cell_index == cell.cell_index() and ref.trans == pos]
    require(not ref.is_regular_array(), "Unexpected regular via reference")
    cuts = local_region(layout, cell, (19, 0))
    require(all(poly.is_box() for poly in cuts.each_merged()), "GDS via cuts are not boxes")
    local_boxes = {tuple(coordinates(cut.bbox())) for cut in cuts.each_merged()}
    require(local_boxes == families[name]["boxes"] and len(local_boxes) == 2,
            "GDS and DEF Via1 cut footprints differ")
    landed = cuts.transformed(pos)
    require((landed - kdb.Region(metal)).is_empty(), "Via1 does not land fully in replacement Metal1")
    m2 = (kdb.Region(top.begin_shapes_rec_touching(layout.find_layer(10, 0), window))
          & kdb.Region(window))
    require((landed - m2).is_empty(), "Via1 does not land fully in retained GDS Metal2")
    return tuple(sorted(tuple(coordinates(cut.bbox())) for cut in landed.each_merged()))


def geometry(window_dbu):
    require(all(sha(path) == digest for path, digest in (
        (DEF, DEF_SHA), (TARGET["gds"], TARGET["gds_sha256"]), (TARGET["odb"], TARGET["odb_sha256"]),
        (GEOMETRY, GEOMETRY_SHA), (INVENTORY, INVENTORY_SHA))), "Frozen local geometry inputs changed")
    layout = kdb.Layout()
    layout.read(str(TARGET["gds"]))
    top, = layout.top_cells()
    require(layout.dbu == 0.001 and top.name == TOP, "Unexpected GDS grid or top cell")
    site = read(GEOMETRY)["sites"][TERMINAL]
    lower, cuts = contact_regions(layout, site)
    window = kdb.Box(*window_dbu)
    layer = layout.find_layer(*M1)
    metal = kdb.Region(top.begin_shapes_rec_touching(layer, window)) & kdb.Region(window)
    marker = layout.find_layer(8, 29)
    if marker is not None:
        metal -= kdb.Region(top.begin_shapes_rec_touching(marker, window))
    metal, = [poly for poly in metal.each_merged() if poly.inside(kdb.Point(*REFERENCE_POINT_DBU))]
    require(all((kdb.Region(kdb.Box(*box)) - kdb.Region(metal)).is_empty() for box in cuts),
            "Decap contact lands outside selected connected M1 component")
    return LocalGeometry(layout, top, window, metal, lower, cuts, geometric_via(layout, top, window, metal),
                         seam_intersections(metal, window), [bound(path) for path in
                         (DEF, TARGET["gds"], TARGET["odb"], GEOMETRY, INVENTORY)])


def patch_polygons(shape, point, radius, limit):
    require(0 < radius <= limit, "Invalid load patch radius")
    landed = shape & kdb.Region(rect(*point, radius))
    if not landed.is_empty():
        return list(landed.each_merged()), radius
    # A PSM centroid can sit between disjoint drawn fingers or outside
    # the crop. Its assigned portion may only land on its own VSS geometry.
    grown = radius
    while landed.is_empty() and grown < limit:
        grown = min(limit, grown * 2)
        landed = shape & kdb.Region(rect(*point, grown))
    require(not landed.is_empty(), f"No same-terminal converted patch near {point}")
    return list(landed.each_merged()), grown


@dataclass
class LocalMesh:
    matrix: object
    rhs: object
    ports: dict
    port_edges: dict
    coordinates: tuple
    network: Network
    m1: object
    m1_count: int
    cut_edges: dict
    load_landings: list
    geometry: LocalGeometry

    def metrics(self, voltage):
        require(voltage.shape == self.rhs.shape and np.isfinite(voltage).all(), "Invalid local field voltage")
        cx, cy, dx, dy = self.coordinates
        a, b, g = self.network.chunks[0]
        horizontal = (voltage[a] - voltage[b]) * g
        valid = (self.m1[:, :-1] >= 0) & (self.m1[:, 1:] >= 0)
        sections = np.zeros(valid.shape)
        sections[valid] = horizontal
        row_samples = []
        exact_sections = {}
        for idx, x in enumerate((cx[:-1] + dx[:-1] / 2)):
            span_edges = np.flatnonzero(np.diff(np.r_[False, valid[:, idx], False])).reshape(-1, 2)
            for lo, hi in span_edges:
                width_um = dy[lo:hi].sum() / 1000
                limit_a = metal_limit_ma("Metal1", width_um)
                if limit_a is None:
                    continue
                span = (float(cy[lo] - dy[lo] / 2), float(cy[hi - 1] + dy[hi - 1] / 2))
                current_a = float(sections[lo:hi, idx].sum())
                result = dict(x_dbu=float(x), span_dbu=span, width_um=float(width_um),
                              current_a_positive_x=current_a, current_ref_a=limit_a / 1000,
                              utilization=abs(current_a) * 1000 / limit_a)
                row_samples.append(result)
                for expected_x in SECTION_X_DBU:
                    if abs(x - expected_x) < 1e-6 and span == ROW_SPAN_DBU:
                        exact_sections[expected_x] = result
        require(row_samples and REFERENCE_POINT_DBU[0] in exact_sections,
                "Mesh did not preserve the reference 440 nm slice")
        fluxes_m1 = np.zeros(self.m1_count)
        cut_results = []
        for box, (label, a, b, g) in self.cut_edges.items():
            flux = (voltage[a] - voltage[b]) * g
            np.add.at(fluxes_m1, a, flux)
            cut_results.append(dict(box_dbu=box, lower_component=label, current_a_m1_to_lower=float(flux.sum())))
        ports = {}
        transfer_m1 = np.zeros(self.m1_count)
        for name, edges in self.port_edges.items():
            amps = []
            for a, b, g in edges:
                flux = (voltage[b] - voltage[a]) * g
                np.add.at(transfer_m1, a, flux)
                amps.append(float(flux.sum()))
            ports[name] = dict(current_a_into_local=sum(amps), constituent_currents_a_into_local=amps)

        # A second accounting path sums local sources, seam/via injections
        # and contact transfer strictly to the left of all vertical sections.
        column = np.where(self.m1 >= 0)[1]
        lhs = sections.sum(axis=0)
        rhs = np.cumsum(np.bincount(column, self.rhs[:self.m1_count] + transfer_m1 - fluxes_m1,
                                    minlength=len(cx)))[:-1]
        slice_residual = float(np.max(np.abs(lhs - rhs)))
        require(slice_residual < 2e-10, f"Local vertical sections did not balance: {slice_residual}")
        port_ids = np.concatenate(list(self.ports.values()))
        interior = np.ones(len(voltage), dtype=bool)
        interior[port_ids] = False
        local_kcl = float(np.max(np.abs((self.matrix @ voltage - self.rhs)[interior])))
        require(local_kcl < 2e-10, f"Local finite-volume KCL did not balance: {local_kcl}")
        via_cut_results = []
        if "via" in ports:
            via_cut_results = [dict(box_dbu=box, current_a_upper_to_m1=amps, utilization_0p4ma=abs(amps) / 0.0004)
                               for box, amps in zip(self.geometry.via_cut_boxes_dbu,
                                                    ports["via"]["constituent_currents_a_into_local"], strict=True)]
        return dict(
            reference_section=exact_sections[REFERENCE_POINT_DBU[0]], additional_row_sections=[
                exact_sections[x] for x in SECTION_X_DBU if x != REFERENCE_POINT_DBU[0] and x in exact_sections],
            peak_section=max(row_samples, key=lambda row: row["utilization"]),
            max_local_node_kcl_residual_a=local_kcl, max_slice_kcl_residual_a=slice_residual, ports=ports,
            m1_nodes=self.m1_count, total_nodes=self.network.n,
            local_m1_voltage_bounds_v=[float(np.min(voltage[:self.m1_count])), float(np.max(voltage[:self.m1_count]))],
            device_cont_cuts=cut_results, via1_cuts=via_cut_results,
            peak_device_cont_current_a=max((abs(row["current_a_m1_to_lower"]) for row in cut_results), default=0.0),
            peak_device_cont_ref_utilization=max((abs(row["current_a_m1_to_lower"]) / CONT_REFERENCE_A
                                                   for row in cut_results), default=0.0),
            load_landings=self.load_landings,
        )


def build_mesh(local, ports, terminal_loads, *, mesh_limit=20, port_radius=80, sheet_ohm=M1_SHEET_OHM,
               lower_sheet_ohm=5.0, contact_corner="typ"):
    """Return pure local L, injection vector, and one node per exterior port.

    Seam interface resistors account for the half-cell distance. Via
    conductances integrate the actual cut area to a separate M2 port.
    Each terminal's j_a is its already-allocated interior signed load.
    """
    require(mesh_limit > 0 and sheet_ohm > 0 and (lower_sheet_ohm is None or lower_sheet_ohm >= 0),
            "Non-passive sheet parameter")
    lower = local.lower if lower_sheet_ohm is not None else {}
    cuts = local.cuts if lower else {}
    port_by_name = {port["name"]: port for port in ports}
    expected = {"left", "right"} | ({"via"} if local.via_cut_boxes_dbu else set())
    require(len(port_by_name) == len(ports) and port_by_name.keys() == expected, "Wrong or duplicate exterior ports")
    for name in ("left", "right"):
        port = port_by_name[name]
        seam_x = getattr(local.window, name)
        require(port["kind"] == "seam" and port["side"] == name
                and tuple(port["span_dbu"]) == local.seams[name]
                and port["point_dbu"][0] == seam_x and local.seams[name][0] <= port["point_dbu"][1] <= local.seams[name][1],
                f"Port is not the verified full {name} seam")
    if local.via_cut_boxes_dbu:
        via = port_by_name["via"]
        require(via["kind"] == "via" and tuple(map(tuple, via["cut_boxes_dbu"])) == local.via_cut_boxes_dbu
                and via["resistance_ohm"] > 0, "Via port differs from exact GDS/DEF array")

    loads = {}
    auxiliary_polys = {}
    for load in terminal_loads:
        terminal = load["terminal"]
        native_point = tuple(load["point_dbu"])
        require(terminal not in loads and math.isfinite(load["j_a"]), "Duplicate or invalid local terminal load")
        loads[terminal] = dict(load)
        if terminal == TERMINAL and lower:
            loads[terminal]["geometry_basis"] = "full selected decap lower tap conductor through its seven physical Cont cuts"
            continue
        conductor = local.load_polygon(terminal)
        patches, grown = patch_polygons(conductor, native_point, port_radius, 2560)
        names = [f"{terminal}:{idx}" for idx in range(len(patches))]
        auxiliary_polys.update(zip(names, patches))
        loads[terminal].update(geometry_basis="verified VSS drawing clipped to centroid patch",
                               patch_radius_dbu=grown, patch_geometry_names=names,
                               patch_boxes_dbu=[coordinates(polygon.bbox()) for polygon in patches])

    # A zero-width rectangle acts only as a guaranteed x mesh break at the
    # reference cross-section. The actual conductivity remains from artwork.
    y = REFERENCE_POINT_DBU[1]
    references = [kdb.Box(x, y, x, y) for x in SECTION_X_DBU]
    via_boxes = local.via_cut_boxes_dbu
    cx, cy, dx, dy = mesh(local.metal, lower | auxiliary_polys, [*cuts, *via_boxes], references, mesh_limit)
    network = Network(dx, dy)
    m1 = network.nodes(polygon_mask(local.metal, cx, cy))
    network.sheet(m1, sheet_ohm)
    m1_count = network.n
    require(abs(float(network.area[m1 >= 0].sum()) - local.metal.area()) < 1e-6,
            "Mesh did not preserve exact GDS M1 area")
    lower_ids, cut_edges = {}, {}
    for name, poly in lower.items():
        ids = network.nodes(polygon_mask(poly, cx, cy), equipotential=lower_sheet_ohm == 0)
        lower_ids[name] = ids
        if lower_sheet_ohm:
            network.sheet(ids, lower_sheet_ohm)
    for box, name in cuts.items():
        mask = box_mask(box, cx, cy)
        other = lower_ids[name]
        require(np.all(m1[mask] >= 0) and np.all(other[mask] >= 0)
                and math.isclose(float(network.area[mask].sum()), 160**2), "A selected Cont footprint was truncated")
        r = CONTACT_OHM[contact_corner][int(name.startswith("poly-"))]
        a, b, g = m1[mask], other[mask], network.area[mask] / (160**2 * r)
        network.edges(a, b, g)
        cut_edges[box] = (name, a, b, g)
    port_indices, port_edges = {}, {}
    for name in ("left", "right"):
        span = local.seams[name]
        is_left = name == "left"
        planes = cx - dx / 2 if is_left else cx + dx / 2
        col, = np.flatnonzero(abs(planes - getattr(local.window, name)) < 1e-6)
        mask = (span[0] < cy) & (cy < span[1])
        a = m1[:, col][mask]
        require(np.all(a >= 0) and math.isclose(float(dy[mask].sum()), span[1] - span[0]),
                "Interior mesh does not cover complete seam face")
        b = np.full(len(a), network.n, dtype=np.int32)
        g = 2 * dy[mask] / (sheet_ohm * dx[col])
        port_indices[name] = np.array([network.n], dtype=np.int32)
        port_edges[name] = [(a, b, g)]
        network.edges(a, b, g)
        network.n += 1
    if via_boxes:
        resistance = port_by_name["via"]["resistance_ohm"]
        port_indices["via"] = np.array([network.n], dtype=np.int32)
        port_edges["via"] = []
        for box in via_boxes:
            mask = box_mask(box, cx, cy)
            area = network.area[mask]
            a = m1[mask]
            require(np.all(a >= 0) and math.isclose(float(area.sum()), 190**2), "A Via1 cut footprint was truncated")
            b = np.full(len(a), network.n, dtype=np.int32)
            g = area / (190**2 * resistance)
            network.edges(a, b, g)
            port_edges["via"].append((a, b, g))
        network.n += 1

    rhs = np.zeros(network.n)
    for terminal, load in loads.items():
        if terminal == TERMINAL and lower:
            correct = [box for box, name in cuts.items() if name.startswith("ptap-")]
            for box in correct:
                mask = box_mask(box, cx, cy)
                ids = lower_ids[cuts[box]]
                add_source(rhs, ids[mask], network.area[mask], load["j_a"] / len(correct))
        else:
            mask = np.logical_or.reduce([polygon_mask(auxiliary_polys[name], cx, cy)
                                         for name in load["patch_geometry_names"]])
            require(np.all(m1[mask] >= 0), "Load lands outside selected M1 conductor")
            add_source(rhs, m1[mask], network.area[mask], load["j_a"])
            load["patch_area_um2"] = float(network.area[mask].sum() / 1e6)
    require(math.isclose(math.fsum(load["j_a"] for load in loads.values()), float(rhs.sum()), abs_tol=1e-16),
            "Converted terminal loads did not preserve signed total")
    return LocalMesh(network.matrix(), rhs, port_indices, port_edges, (cx, cy, dx, dy),
                     network, m1, m1_count, cut_edges, list(loads.values()), local)
