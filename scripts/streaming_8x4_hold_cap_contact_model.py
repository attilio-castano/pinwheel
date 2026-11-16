"""Solve conditional local M1 and FEOL redistribution at two PSM decap hotspots."""

import argparse
from collections import Counter
import csv
import math
from pathlib import Path
import re

import klayout.db as kdb
import numpy as np
import scipy
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from scipy.sparse.linalg import splu

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import TOP, read, require, sha, write
from streaming_8x4_hold_cap_terminal_geometry import CURRENTS, CURRENTS_SHA, ROOT
from streaming_8x4_hold_cap_ir import SHEET_TC
from streaming_8x4_hold_cap_ir_readback import PROCESS_SPEC, metal_limit_ma
from streaming_8x4_hold_cap_physical import TARGET


GEOMETRY = ROOT / "terminal-contact-geometry-01.json"
GEOMETRY_SHA = "adee588f7eff95a4fdcc2bd668eba2a162fbe6fe87472ac3b9bbc97f31fea824"
FEEDBACK = ROOT / "decap-feedback-02.json"
FEEDBACK_SHA = "d3a92260fc2f9e2f78a0bb994db8d29d44dff137456e3eb2bdaaf4a55e108d78"
HOTSPOTS = {"VGND": "FILLER_3_3251/VSS", "VPWR": "FILLER_7_3350/VDD"}
CUT_NAMES = {"VGND": {"ptap": 7, "nSD": 3, "poly": 2}, "VPWR": {"ntap": 7, "pSD": 9, "poly": 2}}
M1_SHEET_OHM = 0.17195244
CONTACT_OHM = {"min": (8, 8), "typ": (17, 15), "max": (22, 20)}
CONT_REFERENCE_A = 0.0003
PDK_INPUT = {
    "libs.tech/klayout/tech/lvs/rule_decks/layers_definitions.lvs":
        "2165a344d178eff60c2c79ad73108d74b8a1d2b1a5183e8b3492aa249887e58c",
    "libs.tech/klayout/tech/lvs/rule_decks/general_derivations.lvs":
        "d386598b10809388bfa690644b5a6a8f49c532b9d04caf9d2d014f4de12db043",
    "libs.tech/klayout/tech/lvs/rule_decks/general_connections.lvs":
        "8872e0ac58260896616260b8a51c4762dfd303b682c0320eb36430d490ad2a9b",
    "libs.ref/sg13cmos5l_stdcell/cdl/sg13cmos5l_stdcell.cdl":
        "6354feb07a2e5a0f51ea44d782b8c8adc2dd477ca7fe3b0876f1a54717a66203",
}
CDL_DEVICES = {
    "MN0 VSS VDD VSS VSS sg13_lv_nmos m=1 w=840.00n l=1.000u ng=2",
    "MP0 VDD VSS VDD VDD sg13_lv_pmos m=1 w=2.000u l=1.000u ng=2",
}
CASE_NAMES = {
    "metal_only": ("current", None, None, "metal"),
    "current_max_finite": ("current", "max", 5.0, "tap"),
    "current_typ_finite": ("current", "typ", 5.0, "tap"),
    "current_min_finite": ("current", "min", 5.0, "tap"),
    "current_min_low_sheet": ("current", "min", 2.0, "tap"),
    "current_max_high_sheet": ("current", "max", 20.0, "tap"),
    "current_min_equipotential": ("current", "min", 0.0, "tap"),
    "current_typ_distributed_load": ("current", "typ", 5.0, "all"),
    "voltage_typ_finite": ("voltage", "typ", 5.0, "tap"),
    "revised_voltage_typ_finite": ("revised_voltage", "typ", 5.0, "tap"),
    "coupled_typ_finite": ("coupled", "typ", 5.0, "tap"),
}
M1 = (8, 0)
NODE = re.compile(r"Node: \(([\d.]+), ([\d.]+)\) on Metal1$")


def checked(item):
    path = Path(item["path"])
    require(bound(path) == item, f"Artifact differs: {path}")
    return path


def coordinates(box):
    return [box.left, box.bottom, box.right, box.top]


def rect(x, y, radius):
    return kdb.Box(x - radius, y - radius, x + radius, y + radius)


def local_region(layout, cell, layer):
    index = layout.find_layer(*layer)
    return kdb.Region() if index is None else kdb.Region(cell.shapes(index)).merged()


def lower_regions(layout, cell):
    # The frozen primitive has none of the special-purpose layers excluded
    # from these active/poly/tap derivations in the CMOS5L LVS rules.
    absent = [(1, 22), (5, 22), (7, 21), (8, 29), (19, 0), (24, 0), (28, 0), (32, 0), (40, 0),
              (44, 0), (46, 21), (60, 0), (99, 31), (128, 0)]
    require(all(local_region(layout, cell, layer).is_empty() for layer in absent),
            "Unexpected special layer in selected decap")
    active, poly, psd, well = (local_region(layout, cell, layer) for layer in ((1, 0), (5, 0), (14, 0), (31, 0)))
    nactive, pactive = active - psd, active & psd
    ngate, pgate = nactive & poly, pactive & poly
    nsd = (nactive - well).interacting(ngate) - ngate
    psd = (pactive & well).interacting(pgate) - pgate
    ntap, ptap = (nactive & well) - poly, (pactive - well) - poly
    for sd, tap in ((nsd, ptap), (psd, ntap)):
        require((sd.edges() & tap.edges()).is_empty(), "Unexpected salicide-abutted S/D and tap")
    return {"nSD": nsd, "pSD": psd, "ntap": ntap, "ptap": ptap, "poly": poly}


def contact_regions(layout, site):
    cell = layout.cell(site["master"])
    trans = kdb.Trans.from_s(site["transform"])
    components, cuts = {}, {}
    local_cuts = local_region(layout, cell, (6, 0))
    for label, region in lower_regions(layout, cell).items():
        for index, polygon in enumerate(sorted(region.each_merged(), key=lambda poly: coordinates(poly.bbox()))):
            component = f"{label}-{index}"
            lower = kdb.Region(polygon)
            components[component] = polygon.transformed(trans)
            for clipped in local_cuts.interacting(lower).each_merged():
                require(clipped.is_box() and clipped.area() == 160 ** 2 and (kdb.Region(clipped) - lower).is_empty(),
                        f"Cut differs or crosses lower conductor {component}")
                key = tuple(coordinates(clipped.bbox().transformed(trans)))
                require(key not in cuts, "Cut touches more than one lower-conductor class")
                cuts[key] = component
    selected = {tuple(coords): cuts[tuple(coords)] for coords in site["contact_boxes_dbu"]}
    require(Counter(component.split("-")[0] for component in selected.values()) == CUT_NAMES[site["rail"]],
            "Contact classes differ")
    return {label: components[label] for label in sorted(set(selected.values()))}, selected


def read_branches(rail, target, report, dump):
    match = f": {target}"
    selected = []
    path = checked(report["terminal_edges_csv"])
    with path.open() as handle:
        for row in csv.DictReader(handle):
            if row["a_node"].endswith(match):
                grid, terminal, sign = "b", "a", -1
            elif row["b_node"].endswith(match):
                grid, terminal, sign = "a", "b", 1
            else:
                continue
            coords = NODE.fullmatch(row[f"{grid}_node"])
            require(coords and float(row["conductance_s"]) == 1000, "Unexpected terminal branch")
            point = [int(round(float(item) * 1000)) for item in coords.groups()]
            selected.append(dict(point_dbu=point, current_a_into_metal=sign * float(row["current_a_a_to_b"]),
                                 grid_index=int(row[f"{grid}_solver_index"]),
                                 terminal_index=int(row[f"{terminal}_solver_index"])))
    require(len(selected) == (5 if rail == "VGND" else 3)
            and len({item["terminal_index"] for item in selected}) == 1, "Missing terminal branches")
    terminal_index = selected[0]["terminal_index"]
    indices = {item["grid_index"] for item in selected} | {terminal_index}
    vpath = checked(dump["solver_dumps"][rail]["psm_V.txt"])
    voltages = {}
    with vpath.open() as handle:
        for index, line in enumerate(handle):
            if index in indices:
                prefix, value = line.rstrip().split(" = ")
                require(prefix == f"V[{index}]", "Voltage index differs")
                voltages[index] = float(value)
    for item in selected:
        item["grid_voltage_v"] = voltages[item["grid_index"]]
        item["native_terminal_voltage_v"] = voltages[terminal_index]
        require(math.isclose((item["grid_voltage_v"] - voltages[terminal_index]) * 1000,
                             item["current_a_into_metal"], rel_tol=1e-12, abs_tol=1e-15),
                "Current and voltage differ")
    return sorted(selected, key=lambda item: item["point_dbu"])


def metal_region(layout, top, site, branches, margin):
    x0, _, x1, _ = site["pin_box_dbu"]
    y0, y1 = min(box[1] for box in site["contact_boxes_dbu"]), max(box[3] for box in site["contact_boxes_dbu"])
    ys = [item["point_dbu"][1] for item in branches]
    xmin, xmax = x0 - margin, x1 + margin
    ymin, ymax = min(y0, *ys) - margin, max(y1, *ys) + margin
    window = kdb.Box(xmin, ymin, xmax, ymax)
    layer = layout.find_layer(*M1)
    clipped = kdb.Region(top.begin_shapes_rec_touching(layer, window)) & kdb.Region(window)
    resistor_layer = layout.find_layer(8, 29)
    if resistor_layer is not None:
        clipped -= kdb.Region(top.begin_shapes_rec_touching(resistor_layer, window))
    center = kdb.Point((x0 + x1) // 2, site["followpin_y_dbu"])
    metal, = [poly for poly in clipped.merged().each_merged() if poly.inside(center)]
    require(all((kdb.Region(kdb.Box(*box)) - kdb.Region(metal)).is_empty()
                for box in site["contact_boxes_dbu"]), "Selected cut outside top M1 component")
    return metal, window


def polygon_rings(poly):
    return [list(poly.each_point_hull())] + [list(poly.each_point_hole(i)) for i in range(poly.holes())]


def refine(vertices, limit):
    ordered = sorted(set(vertices))
    intervals = [np.linspace(a, b, int(math.ceil((b - a) / limit)), endpoint=False)
                 for a, b in zip(ordered, ordered[1:])]
    return np.concatenate([*intervals, [ordered[-1]]])


def mesh(metal, lower, contacts, branch_patches, limit):
    polygons = [metal, *lower.values()]
    rings = [ring for polygon in polygons for ring in polygon_rings(polygon)]
    vertices = [point for ring in rings for point in ring]
    boxes = [*contacts, *(coordinates(box) for box in branch_patches)]
    for ring in rings:
        require(all(a.x == b.x or a.y == b.y for a, b in zip(ring, ring[1:] + ring[:1])),
                "Mesh requires orthogonal GDS polygons")
    ex = refine([point.x for point in vertices] + [box[i] for box in boxes for i in (0, 2)], limit)
    ey = refine([point.y for point in vertices] + [box[i] for box in boxes for i in (1, 3)], limit)
    dx, dy = np.diff(ex), np.diff(ey)
    cx, cy = ex[:-1] + dx / 2, ey[:-1] + dy / 2
    return cx, cy, dx, dy


def polygon_mask(poly, cx, cy):
    inside = np.zeros((cy.size, cx.size), dtype=bool)
    for ring in polygon_rings(poly):
        for a, b in zip(ring, ring[1:] + ring[:1]):
            if a.x == b.x:
                inside ^= ((min(a.y, b.y) < cy) & (cy < max(a.y, b.y)))[:, None] & (cx < a.x)[None, :]
    return inside


def box_mask(box, cx, cy):
    x0, y0, x1, y1 = box
    return ((y0 < cy) & (cy < y1))[:, None] & ((x0 < cx) & (cx < x1))[None, :]


class Network:
    def __init__(self, dx, dy):
        self.n = 0
        self.chunks = []
        self.dx = dx
        self.dy = dy
        self.area = dy[:, None] * dx[None, :]

    def nodes(self, mask, equipotential=False):
        ids = np.full(mask.shape, -1, dtype=np.int32)
        count = 1 if equipotential else int(mask.sum())
        ids[mask] = self.n if equipotential else np.arange(self.n, self.n + count)
        self.n += count
        return ids

    def edges(self, a, b, g):
        self.chunks.append((a, b, g))

    def sheet(self, ids, ohms):
        dx, dy = self.dx, self.dy
        a, b = ids[:, :-1], ids[:, 1:]
        valid_x = (a >= 0) & (b >= 0)
        g = 2 * dy[:, None] / (ohms * (dx[:-1] + dx[1:])[None, :])
        self.edges(a[valid_x], b[valid_x], g[valid_x])
        a, b = ids[:-1, :], ids[1:, :]
        valid_y = (a >= 0) & (b >= 0)
        g = 2 * dx[None, :] / (ohms * (dy[:-1] + dy[1:])[:, None])
        self.edges(a[valid_y], b[valid_y], g[valid_y])
        return [dy[:, None].repeat(dx.size - 1, axis=1)[valid_x],
                dx[None, :].repeat(dy.size - 1, axis=0)[valid_y]]

    def matrix(self):
        a, b, g = (np.concatenate(arrays) for arrays in zip(*self.chunks))
        matrix = coo_matrix((np.concatenate((g, g, -g, -g)),
                             (np.concatenate((a, b, a, b)), np.concatenate((a, b, b, a)))),
                            shape=(self.n, self.n)).tocsr()
        require(connected_components(matrix, directed=False, return_labels=False) == 1,
                "Discretized rail network disconnected")
        return matrix


def add_source(rhs, ids, weights, value):
    require(len(ids) > 0 and sum(weights) > 0, "Empty boundary/load patch")
    np.add.at(rhs, ids, value * weights / np.sum(weights))


def solve_boundary(matrix, rhs, groups, drive, branches, feedback):
    if drive == "current":
        indices = groups[0][:1]
    else:
        indices = np.concatenate(groups)
    free = np.ones(len(rhs), dtype=bool)
    free[indices] = False
    reduced = splu(matrix[free][:, free].tocsc())
    coupling = matrix[free][:, indices]
    voltage = np.zeros(len(rhs))
    metadata = {}
    if drive == "coupled":
        # Join each patch as one equipotential terminal. The local
        # Dirichlet-to-Neumann map uses f(V) = Y V + i0, amperes into M1.
        gather = np.repeat(np.arange(len(groups)), [len(ids) for ids in groups])
        prolongation = np.eye(len(groups))[gather]
        voltage[free] = reduced.solve(rhs[free])
        i0 = prolongation.T @ (matrix[indices][:, free] @ voltage[free] - rhs[indices])
        response = reduced.solve(-coupling @ prolongation)
        admittance = prolongation.T @ (matrix[indices][:, indices] @ prolongation
                                       + matrix[indices][:, free] @ response)
        require(np.max(np.abs(admittance - admittance.T)) < 1e-10
                and np.max(np.abs(admittance.sum(axis=1))) < 1e-9
                and np.min(np.linalg.eigvalsh(admittance)) > -1e-10,
                "Local port admittance is not passive and reciprocal")
        impedance = np.array(feedback["port_impedance_ohm"])
        require(impedance.shape == (len(groups), len(groups))
                and np.max(np.abs(impedance - impedance.T)) < 1e-10
                and np.min(np.linalg.eigvalsh(impedance)) > 0,
                "External port impedance is not passive and reciprocal")
        opened = np.array(feedback["open_port_voltage_v"])
        ref_v = opened[0]
        port_v = np.linalg.solve(np.eye(len(groups)) + impedance @ admittance,
                                 opened - ref_v - impedance @ i0)
        voltage[indices] = prolongation @ port_v
        metadata = dict(port_admittance_s=admittance.tolist(), port_load_a_at_zero_v=i0.tolist(),
                        coupled_port_voltage_v=(ref_v + port_v).tolist(),
                        open_port_voltage_v=opened.tolist())
    elif drive != "current":
        port_v = (np.asarray([branch["grid_voltage_v"] for branch in branches]) if drive == "voltage"
                  else np.asarray([item["revised_voltage_v"] for item in feedback["patch_voltages"]]))
        ref_v = port_v[0]
        voltage[indices] = np.repeat(port_v - ref_v, [len(group) for group in groups])
        metadata = dict(clamped_port_voltage_v=port_v.tolist())
    voltage[free] = reduced.solve(rhs[free] - coupling @ voltage[indices])
    residual = matrix @ voltage - rhs
    if drive == "coupled":
        solved_i = np.array([residual[ids].sum() for ids in groups])
        error = float(np.max(np.abs(port_v - (opened - ref_v - impedance @ solved_i))))
        require(error < 1e-10, "Coupled ports do not close against external Thevenin relation")
        metadata.update(coupled_port_current_a_into_local=solved_i.tolist(), port_voltage_residual_v=error)
    return voltage, residual, free, metadata


def solve_case(metal, lower, cuts, branches, mesh_limit, radius, case, feedback):
    drive, resistance, lower_sheet, load_case = CASE_NAMES[case]
    patches = [rect(*branch["point_dbu"], radius) for branch in branches]
    cx, cy, dx, dy = mesh(metal, lower, cuts, patches, mesh_limit)
    network = Network(dx, dy)
    m1 = network.nodes(polygon_mask(metal, cx, cy))
    face_widths = network.sheet(m1, M1_SHEET_OHM)
    m1_node_count = network.n
    lower_ids, cut_edges = {}, {}
    if lower_sheet is not None:
        for name, poly in lower.items():
            ids = network.nodes(polygon_mask(poly, cx, cy), equipotential=lower_sheet == 0)
            lower_ids[name] = ids
            if lower_sheet:
                network.sheet(ids, lower_sheet)
        for box, name in cuts.items():
            mask = box_mask(box, cx, cy)
            ids = lower_ids[name]
            require(np.all(m1[mask] >= 0) and np.all(ids[mask] >= 0)
                    and np.isclose(np.sum(network.area[mask]), 160 ** 2), "Incomplete contact footprint")
            r_cut = CONTACT_OHM[resistance][int(name.startswith("poly-"))]
            edge = (m1[mask], ids[mask], network.area[mask] / (160 ** 2 * r_cut))
            network.edges(*edge)
            cut_edges[box] = edge

    matrix = network.matrix()
    rhs = np.zeros(network.n)
    load = -sum(branch["current_a_into_metal"] for branch in branches)
    if load_case == "metal":
        cid = len(branches) // 2
        mask = (m1 >= 0) & box_mask(coordinates(patches[cid]), cx, cy)
        add_source(rhs, m1[mask], network.area[mask], load)
    else:
        load_cuts = [box for box, label in cuts.items()
                     if load_case == "all" or label.startswith(("ntap-", "ptap-"))]
        for box in load_cuts:
            ids = lower_ids[cuts[box]]
            mask = box_mask(box, cx, cy)
            add_source(rhs, ids[mask], network.area[mask], load / len(load_cuts))

    groups = []
    occupied = set()
    for branch, patch in zip(branches, patches):
        mask = (m1 >= 0) & box_mask(coordinates(patch), cx, cy)
        ids = m1[mask]
        require(len(ids) and not (occupied & set(ids)), "Empty or overlapping Metal1 boundary patch")
        occupied.update(ids)
        groups.append(ids)
        if drive == "current":
            add_source(rhs, ids, network.area[mask], branch["current_a_into_metal"])
    voltage, residual, free, boundary = solve_boundary(matrix, rhs, groups, drive, branches, feedback)
    error = np.max(np.abs(residual if drive == "current" else residual[free]))
    require(np.isfinite(voltage).all() and error < 1e-12, "Local solve failed KCL")
    patches_report = [
        dict(point_dbu=branch["point_dbu"], patch_area_um2=np.sum(network.area[m1 >= 0][ids]) / 1e6,
             patch_mean_voltage_relative_v=float(np.mean(voltage[ids])),
             actual_current_a_into_metal=(float(residual[ids].sum()) if drive != "current"
                                         else branch["current_a_into_metal"]))
        for ids, branch in zip(groups, branches)
    ]

    # Integrate M1 current on every internal vertical mesh edge line. For a
    # connected M1 slice, compare the algebraic through-current to the drawn
    # total width. This is an average, not corner-scale current crowding.
    ax, bx, gx = network.chunks[0]
    ix = (voltage[ax] - voltage[bx]) * gx
    flows = np.zeros((len(cy), len(cx) - 1))
    mask_x = (m1[:, :-1] >= 0) & (m1[:, 1:] >= 0)
    flows[mask_x] = ix
    cross_sections = []
    for col, axis_x in enumerate(cx[:-1] + dx[:-1] / 2):
        breakpoints = np.flatnonzero(np.diff(np.r_[False, mask_x[:, col], False])).reshape(-1, 2)
        for lo, hi in breakpoints:
            width = float(dy[lo:hi].sum() / 1000)
            amps = float(flows[lo:hi, col].sum())
            limit_ma = metal_limit_ma("Metal1", width)
            if limit_ma is not None:
                cross_sections.append(dict(x_dbu=float(axis_x), y_span_dbu=[float(cy[lo] - dy[lo] / 2),
                                                                           float(cy[hi - 1] + dy[hi - 1] / 2)],
                                           width_um=width, current_a_positive_x=amps,
                                           current_ref_a=limit_ma / 1000, ratio=abs(amps) * 1000 / limit_ma))
    require(cross_sections, "No Metal1 cross sections above the tabulated minimum width")
    face_density = []
    for (a, b, conductance), widths in zip(network.chunks[:2], face_widths):
        face_density.append(float(np.max(np.abs((voltage[a] - voltage[b]) * conductance) * 1000 / widths)))

    cut_currents = {}
    m1_to_lower = np.zeros(m1_node_count)
    component_currents = dict.fromkeys(lower, 0.0)
    for name, (a, b, g) in cut_edges.items():
        currents = (voltage[a] - voltage[b]) * g
        value = float(np.sum(currents))
        np.add.at(m1_to_lower, a, currents)
        cut_currents[name] = value
        component_currents[cuts[name]] += value
    require(abs(sum(cut_currents.values()) + load) < 1e-12 if cut_currents else not lower_ids,
            "Cut currents fail lower-side KCL")
    for name, amps in component_currents.items():
        if name in lower_ids:
            ids = lower_ids[name]
            expected = -np.sum(rhs[np.unique(ids[ids >= 0])])
            require(abs(amps - expected) < 1e-12, f"Lower component KCL: {name}")
    # Independently close the whole-region slice against the prescribed patch
    # sources (or measured Dirichlet reactions), leakage and contact flux.
    m1_col = np.where(m1 >= 0)[1]
    m1_injection = rhs[:m1_node_count].copy()
    if drive != "current":
        for ids in groups:
            m1_injection[ids] += residual[ids]
    m1_left_injection = np.cumsum(np.bincount(m1_col, weights=m1_injection, minlength=cx.size))[:-1]
    m1_left_transfer = np.cumsum(np.bincount(m1_col, weights=m1_to_lower, minlength=cx.size))[:-1]
    net_all_sections = flows.sum(axis=0)
    slice_error = np.max(np.abs(net_all_sections - (m1_left_injection - m1_left_transfer)))
    require(slice_error < 1e-11, "Complete vertical section fails independent KCL")
    worst_section = max(cross_sections, key=lambda x: x["ratio"])
    axes_x = cx[:-1] + dx[:-1] / 2
    worst_index, = np.nonzero(axes_x == worst_section["x_dbu"])[0]
    same_x = [row for row in cross_sections if row["x_dbu"] == worst_section["x_dbu"]]
    all_sections_at_peak = dict(
        integrated_current_a_positive_x=float(net_all_sections[worst_index]),
        prescribed_injection_a_left_of_slice=float(m1_left_injection[worst_index]),
        current_a_to_lower_left_of_slice=float(m1_left_transfer[worst_index]),
        connected_spans=int(np.count_nonzero(np.diff(np.r_[False, mask_x[:, worst_index], False])) / 2),
        comparison_eligible_spans=len(same_x),
        alternate_span_net_current_a=float(net_all_sections[worst_index] - worst_section["current_a_positive_x"]),
    )
    result = dict(drive=drive, metal_nodes=m1_node_count, total_nodes=network.n,
                  max_kcl_residual_a=float(error), assigned_net_leakage_a_into_device=-load,
                  lower_sheet_ohm_per_square=lower_sheet, contacted_load_distribution=load_case,
                  cut_resistance_corner=resistance, patch_radius_dbu=radius, mesh_max_tile_dbu=mesh_limit,
                  patches=patches_report, boundary=boundary, worst_M1_section_along_rail=worst_section,
                  all_M1_sections_at_peak_x=all_sections_at_peak,
                  max_vertical_slice_kcl_residual_a=float(slice_error),
                  worst_M1_mesh_face_a_per_um={"x": face_density[0], "y": face_density[1]},
                  local_M1_voltage_swing_v=float(np.ptp(voltage[:m1_node_count])),
                  individual_contacts=[
                      dict(box_dbu=box, lower_component=cuts[box], current_a_m1_to_lower=amps)
                      for box, amps in cut_currents.items()],
                  contact_component_net_current_a_into_device=component_currents,
                  worst_contact_a=max(map(abs, cut_currents.values()), default=None))
    if cut_currents:
        result["worst_contact_reference_utilization"] = result["worst_contact_a"] / CONT_REFERENCE_A
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--pdk", type=Path, required=True,
                        help="Exact pinned ihp-sg13cmos5l PDK with LVS rules and stdcell CDL")
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.parent == ROOT and not out.exists(), "Choose a fresh local result")
    require(sha(CURRENTS) == CURRENTS_SHA and sha(GEOMETRY) == GEOMETRY_SHA and sha(FEEDBACK) == FEEDBACK_SHA,
            "Frozen receipts differ")
    inputs = [bound(item) for item in (CURRENTS, GEOMETRY, FEEDBACK)]
    feedback = read(FEEDBACK)
    require(feedback["schema"] == "pinwheel.streaming-8x4-hold-cap-decap-feedback.v1"
            and feedback["status"] == "diagnostic"
            and feedback["target_gds_sha256"] == TARGET["gds_sha256"]
            and feedback["target_odb_sha256"] == TARGET["odb_sha256"], "Wrong feedback input")
    pdk_inputs = [bound((args.pdk / name).resolve()) for name in PDK_INPUT]
    require([item["sha256"] for item in pdk_inputs] == list(PDK_INPUT.values()), "LVS derivation/CDL source differs")
    cdl = Path(pdk_inputs[-1]["path"]).read_text()
    primitive, = re.findall(r"^\.SUBCKT sg13cmos5l_decap_8 VDD VSS\n(.*?)^\.ENDS$", cdl, re.M | re.S)
    require({line for line in primitive.splitlines() if line.startswith("M")} == CDL_DEVICES,
            "Decap CDL device topology differs")
    inputs.extend(pdk_inputs)
    current = read(CURRENTS)
    geom = read(GEOMETRY)
    require(current["target_odb_sha256"] == TARGET["odb_sha256"]
            and current["target_gds_sha256"] == TARGET["gds_sha256"]
            and geom["gds"]["sha256"] == TARGET["gds_sha256"]
            and checked(geom["gds"]) == TARGET["gds"] and checked(geom["current_readback"]) == CURRENTS
            and sha(TARGET["odb"]) == TARGET["odb_sha256"],
            "Wrong frozen target")
    dump = read(checked(current["dump"]))
    log = checked(dump["log"]).read_text()
    require(f"Metal1: {M1_SHEET_OHM} Ohm per square" in log and "Cont: 22 Ohm per cut" in log,
            "Native resistance evidence differs")
    inputs.extend([geom["gds"], bound(TARGET["odb"]), current["dump"], dump["log"]])
    layout = kdb.Layout()
    layout.read(str(TARGET["gds"]))
    top, = layout.top_cells()
    require(top.name == TOP and layout.dbu == 0.001, "Unexpected GDS cell or units")
    rails = {}
    tc = SHEET_TC["Metal1"]
    heated_sheet = 0.135 * (1 + tc * (105 + 273.15 - 300)) / (1 + tc * (25 + 273.15 - 300))
    require(math.isclose(heated_sheet, M1_SHEET_OHM, rel_tol=6e-8), "Temperature-factor readback differs")
    for rail, target in HOTSPOTS.items():
        site = geom["sites"][target]
        report = current["rails"][rail]
        branches = read_branches(rail, target, report, dump)
        external = feedback["rails"][rail]
        require(external["removed_terminal"] == target
                and [item["point_dbu"] for item in branches] ==
                [item["point_dbu"] for item in external["patch_voltages"]]
                and [item["grid_voltage_v"] for item in branches] ==
                [item["old_voltage_v"] for item in external["patch_voltages"]], "Feedback ports differ")
        signed_sum = sum(item["current_a_into_metal"] for item in branches)
        require(math.isclose(abs(signed_sum), site["net_modeled_load_a"], abs_tol=6e-12)
                and (signed_sum > 0) == (rail == "VPWR"), "Signed leakage balance differs")
        lower, cuts = contact_regions(layout, site)
        inputs.extend([report["terminal_edges_csv"], dump["solver_dumps"][rail]["psm_V.txt"]])
        derivatives = {}
        for margin in (500, 1000, 2000, 5000):
            metal, window = metal_region(layout, top, site, branches, margin)
            require(all(metal.inside(kdb.Point(*item["point_dbu"])) for item in branches),
                    "Boundary point outside connected GDS Metal1")
            analyses = [(case, 20, 80) for case in CASE_NAMES]
            if margin == 500:
                for case in ("current_typ_finite", "coupled_typ_finite"):
                    analyses += [(case, limit, 80) for limit in (80, 40, 10)]
                    analyses += [(case, 20, radius) for radius in (40, 160)]
            else:
                analyses = [(case, 20, 80) for case in ("current_typ_finite", "coupled_typ_finite")]
            derivatives[margin] = dict(window_dbu=coordinates(window), conductor_bbox_dbu=coordinates(metal.bbox()),
                                       conductor_area_um2=metal.area() / 1e6, results={})
            for case, limit, radius in analyses:
                tag = f"{case}-{limit}nm-{radius}nm"
                solved = solve_case(metal, lower, cuts, branches, limit, radius, case, external)
                derivatives[margin]["results"][tag] = solved
                print(rail, margin, tag, solved["worst_contact_a"],
                      solved["worst_M1_section_along_rail"]["ratio"], flush=True)
        rails[rail] = dict(terminal=target, branches=branches, lower_components={
            name: dict(bbox_dbu=coordinates(polygon.bbox()), bbox_basis="exact drawn polygon bounding box",
                       cut_count=sum(label == name for label in cuts.values()))
            for name, polygon in lower.items()},
            net_branch_current_a=signed_sum, native_net_load_magnitude_a=site["net_modeled_load_a"],
            scenarios_by_crop_margin_dbu=derivatives)
    require(all(bound(item["path"]) == item for item in inputs), "Input changed during solve")
    spec = dict(PROCESS_SPEC, contact_resistance_section="§3.4, PDF page 18",
                contact_current_section="§3.5, PDF page 19",
                contact_resistance_ohm=dict(active=(8, 17, 22), poly=(8, 15, 20)),
                single_Cont_current_ref_a=CONT_REFERENCE_A)
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-contact-model.v1", status="diagnostic",
                    target_gds_sha256=TARGET["gds_sha256"], target_odb_sha256=TARGET["odb_sha256"],
                    producer=bound(__file__), inputs=inputs, klayout_version=kdb.__version__,
                    numpy_version=np.__version__, scipy_version=scipy.__version__, process_reference=spec,
                    metal1_sheet_ohm_per_square=M1_SHEET_OHM,
                    metal1_sheet_basis=dict(ohm_sq_at_25c_used_per_native=0.135, sheet_tc_per_k=tc,
                                            published_reference_k=300, ratio_target_c=105,
                                            prior_base_c=25, unrounded_ohm_sq=heated_sheet),
                    decap_cdl_devices=sorted(CDL_DEVICES), rails=rails,
                    device_side_model=[
                        "Physical cut joins only its GDS-derived salicided diffusion island, tap or gate component.",
                        "Different tap, diffusion and gate component nodes remain separate. No MOS channel, junction "
                        "leakage, neighboring FEOL, well/substrate sheet or capacitive current is solved.",
                        "Finite 2, 5 and 20 ohm/square are parameter sweeps for lower conductors. The equipotential "
                        "case shorts only within each locally drawn lower component. Samples are not global bounds.",
                        "Net device current is the signed sum of retained 1 milliohm terminal branches. The residue "
                        "against native j is recorded via the two source values. Loads at selected cut footprints "
                        "distribute across taps or all cuts. This allocation is hypothetical.",
                    ],
                    boundary_model=[
                        "Geometry-conforming area/face-weighted rectangular finite volume. Top GDS Metal1 "
                        "includes adjacent shapes connected to the selected port. Non-port crop faces insulate.",
                        "Neumann scenarios impose signed native currents across finite Metal1 patches and "
                        "independently calibrate total device leakage. Dirichlet sensitivity clamps the patch "
                        "voltages from the original native grid that still contains idealized terminal shortcuts. "
                        "A second voltage clamp uses grid voltages after removing only that terminal star "
                        "and redistributing its leakage at the retained ports.",
                        "The coupled case joins the external grid's star-removed impedance and open voltages "
                        "to the local field's port admittance. Decap leakage appears once on the device side. "
                        "Existing grid paths remain in parallel, so this is an added physical bypass sensitivity.",
                        "M1 current comparisons are average vertical slices along the horizontal rail and use "
                        "the reference width table. Pointwise face density is a mesh diagnostic. No thermal or "
                        "coupled grid solve, surrounding via/FEOL coupling or package boundary is represented.",
                    ], em_qualified=False, ir_drop_qualified=False))


if __name__ == "__main__":
    main()
