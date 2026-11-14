"""Resolve retained PSM branch currents into a local two-sheet cut model."""

import argparse
from collections import Counter, defaultdict
from itertools import product
import json
import math
from pathlib import Path
import re

import gdstk
import klayout.db as kdb
import numpy as np
import scipy
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import splu

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import TOP, read, require, sha
from streaming_8x4_hold_cap_ir_readback import PROCESS_SPEC, SHEET, VIA
from streaming_8x4_hold_cap_metal1_trace import HEATED, ROOT, local_drawing
from streaming_8x4_hold_cap_physical import TARGET, TRIAL
from streaming_8x4_hold_cap_via_audit import DEF_SHA, LIMIT_MA, dbu, gds_arrays, nearest, parse_def


DEF = TRIAL / "trial.def"
FEEDS = ROOT / "via-feeds-01.json"
FEEDS_SHA = "4cad8af2c8271f58277efc49202ae20e8b710c5058796fb5eeba768b07a7045b"
AUDIT_SHA = "a96eed9482c8ac0d2aeb12b5fe2ea4e5159900f99215741984638a4d7f4e7d97"
DRAWING = {"Metal1": 8, "Metal2": 10, "Metal3": 30, "Metal4": 50}
WIDTH = {"Metal2": 1000, "Metal3": 2100, "Metal4": 2100}
ALONG = {"Metal2": 1, "Metal3": 0, "Metal4": 1}
WINDOW_DBU = 2300
ALTERNATE_WINDOW_DBU = 2380
PITCHES_DBU = (120, 80, 45, 25)
VIA_OHMS = (5, 9, 20)
LIMIT = float(LIMIT_MA)
METRICS = ("max_abs_cut_ma", "placement_max_abs_cut_ma")
# Scale the process-table minimum and target from its 300 K reference.
HOT_SHEETS = {name: value * (1 + 0.0035 * (378.15 - 300)) for name, value in
              (("pdk_min_105c", 0.073), ("pdk_target_105c", 0.088))}


def box_tuple(box):
    return box.left, box.bottom, box.right, box.top


def translated(box, center):
    return tuple(value + center[index % 2] for index, value in enumerate(box))


def rectangle_region(boxes):
    region = kdb.Region()
    for box in boxes:
        region.insert(kdb.Box(*box))
    return region.merged()


def boxes_of(region):
    shapes = list(region.decompose_trapezoids_to_region().each())
    require(shapes and all(shape.is_box() for shape in shapes), "Expected rectilinear rail metal")
    return sorted(box_tuple(shape.bbox()) for shape in shapes)


def def_stripes():
    section = DEF.read_text().split("\nSPECIALNETS 2 ;\n", 1)[1].split("\nEND SPECIALNETS\n", 1)[0]
    chunks = re.split(r"^\s+- (VPWR|VGND) \(", section, flags=re.M)
    pattern = (r"Metal([234]) ([1-9]\d*) \+ SHAPE STRIPE "
               r"\( (\d+) (\d+) \) \( (\d+) (\d+) \)")
    stripes = {}
    for rail, body in zip(chunks[1::2], chunks[2::2], strict=True):
        for number, width, x0, y0, x1, y1 in re.findall(pattern, body):
            layer = f"Metal{number}"
            width, x0, y0, x1, y1 = map(int, (width, x0, y0, x1, y1))
            require(width == WIDTH[layer], "Unexpected rail stripe width")
            if ALONG[layer] == 0:
                require(x0 < x1 and y0 == y1, "Unexpected horizontal stripe")
                key, box = y0, (x0, y0 - width // 2, x1, y1 + width // 2)
            else:
                require(x0 == x1 and y0 < y1, "Unexpected vertical stripe")
                key, box = x0, (x0 - width // 2, y0, x1 + width // 2, y1)
            require((rail, layer, key) not in stripes, "Duplicate rail stripe")
            stripes[rail, layer, key] = box
    require(Counter(layer for _, layer, _ in stripes) == {"Metal2": 70, "Metal3": 28, "Metal4": 70},
            "Unexpected rail stripe inventory")
    return stripes


def gds_pads(families):
    library = gdstk.read_gds(TARGET["gds"])
    cells = {cell.name: cell for cell in library.cells}
    pads = {}
    for name, family in families.items():
        for layer in family["layers"]:
            drawing, = [polygon for polygon in cells[f"VIA_{name}"].polygons
                        if (polygon.layer, polygon.datatype) == (DRAWING[layer], 0)]
            points = {(dbu(x), dbu(y)) for x, y in drawing.points}
            x, y = [sorted({point[axis] for point in points}) for axis in (0, 1)]
            require(len(x) == len(y) == 2 and points == set(product(x, y)), "Irregular GDS via pad")
            pads[name, layer] = x[0], y[0], x[1], y[1]
    return pads


def rail_window(layout, top, rail, layer, center, window, stripe, pads, placements):
    stripe = kdb.Box(*stripe)
    local = [box_tuple(stripe & window)]
    for (name, metal), pad in pads.items():
        if metal == layer:
            for site in placements[rail, name]:
                if max(abs(site[axis] - center[axis]) for axis in (0, 1)) <= window.width() // 2 + 1100:
                    box = kdb.Box(*translated(pad, site)) & window
                    if not box.empty() and box.area() and box.overlaps(stripe):
                        local.append(box_tuple(box))
    selected = rectangle_region(local)
    drawing = local_drawing(top, layout.find_layer(DRAWING[layer], 0), window)
    require((selected - drawing).is_empty(), "Named DEF stripe or via pad differs from drawn GDS")
    actual = kdb.Region()
    for polygon in drawing.each():
        if (kdb.Region(polygon) & selected).area():
            actual.insert(polygon)
    require(actual.count() == 1 and (selected - actual).is_empty(), "Local same-rail region is disconnected")
    return boxes_of(actual), (actual - selected).area()


def source_boxes(request):
    result = {}
    for rail in ("VPWR", "VGND"):
        record = request["inputs"][f"/input/{rail}.vsrc"]
        require(bound(record["path"]) == record, "External source locations changed")
        for row in Path(record["path"]).read_text().splitlines():
            x, y, size, _voltage = map(float, row.split(","))
            x, y, size = dbu(x), dbu(y), dbu(size)
            require(size == 1000, "Unexpected external source footprint")
            result[rail, (x, y)] = (x - size // 2, y - size // 2, x + size // 2, y + size // 2)
    require(len(result) == 8, "Unexpected external source count")
    return result


def adjacent_via(rail, side, neighbor, families, axes):
    pair = sorted((side["layer"], neighbor["layer"]))
    name, = [name for name, family in families.items() if list(family["layers"]) == pair]
    coords = axes[rail, name]
    first, second = [tuple(nearest(axis, point) for axis, point in zip(coords, endpoint["point_dbu"], strict=True))
                     for endpoint in (side, neighbor)]
    require(first == second and all(max(abs(x - cx) for x, cx in zip(endpoint["point_dbu"], first)) < 2500
            for endpoint in (side, neighbor)), "Adjacent feed does not locate one drawn via array")
    return sorted(translated(cut, first) for cut in families[name]["boxes"])


def ports_for(site, families, axes, sources, window):
    ports = []
    for layer_index, side in enumerate(site["sides"]):
        node = side["node"]
        layer = node["layer"]
        axis = ALONG[layer]
        for edge in side["other"]:
            neighbor = edge["neighbor"]
            point = neighbor["point_dbu"]
            amount = -1000 * edge["outward_a"]
            if neighbor["kind"] == "Source Node":
                require(layer == neighbor["layer"] == "Metal4" and point == node["point_dbu"],
                        "External source attached away from its PSM node")
                kind, boxes = "external_source", [sources[site["rail"], tuple(point)]]
            elif neighbor["kind"] == "Node" and neighbor["layer"] != layer:
                kind, boxes = "adjacent_via", adjacent_via(site["rail"], node, neighbor, families, axes)
            else:
                require(neighbor["kind"] == "Node" and neighbor["layer"] == layer
                        and point[1 - axis] == node["point_dbu"][1 - axis]
                        and window[axis] < node["point_dbu"][axis] < window[axis + 2],
                        "Unexpected lateral branch alignment")
                sign = 1 if point[axis] > node["point_dbu"][axis] else -1
                edge_at = window[axis + (2 if sign == 1 else 0)]
                require(sign * (point[axis] - edge_at) >= 0, "Lateral neighbor within the local window")
                kind, boxes = "lateral", []
            port = dict(kind=kind, layer=layer_index, current_ma=amount, boxes_dbu=boxes,
                        psm_neighbor=neighbor)
            if kind == "lateral":
                port.update(axis=axis, sign=sign, edge_dbu=edge_at)
            ports.append(port)
    residual = math.fsum(port["current_ma"] for port in ports)
    require(abs(residual) < 1e-8, "Retained ports do not balance")
    return ports, residual


def axis_nodes(breaks, pitch):
    result = []
    for low, high in zip(breaks[:-1], breaks[1:], strict=True):
        count = math.ceil((high - low) / pitch)
        result.extend(low + np.arange(count) * (high - low) / count)
    return np.array([*result, breaks[-1]])


def mesh_geometry(metal, cuts, ports, pitch):
    boxes = metal[0] + metal[1] + cuts + [box for port in ports for box in port["boxes_dbu"]]
    x, y = [axis_nodes(sorted({box[axis + offset] for box in boxes for offset in (0, 2)}), pitch)
            for axis in (0, 1)]
    dx, dy = np.diff(x), np.diff(y)
    area = dx[:, None] * dy[None, :]
    xm, ym = (x[:-1] + x[1:]) / 2, (y[:-1] + y[1:]) / 2

    def within(box):
        x0, y0, x1, y1 = box
        return ((x0 < xm) & (xm < x1))[:, None] & ((y0 < ym) & (ym < y1))[None, :]

    grids = []
    size = 0
    for layer in metal:
        mask = np.logical_or.reduce([within(box) for box in layer])
        grid = np.full(mask.shape, -1, dtype=np.int32)
        count = int(mask.sum())
        grid[mask] = np.arange(size, size + count)
        grids.append(grid)
        size += count

    cut_nodes = []
    for box in cuts:
        mask = within(box)
        weights = area[mask]
        require(mask.any() and all(np.all(grid[mask] >= 0) for grid in grids)
                and math.isclose(float(weights.sum()), (box[2] - box[0]) * (box[3] - box[1]), abs_tol=1e-6),
                "Cut footprint not fully present on both layers")
        cut_nodes.append((grids[0][mask], grids[1][mask], weights / weights.sum()))

    injections = []
    for port in ports:
        layer = port["layer"]
        grid = grids[layer]
        if port["kind"] == "lateral":
            axis = port["axis"]
            transverse = np.broadcast_to((dy[None, :] if axis == 0 else dx[:, None]), grid.shape)
            nodes = x if axis == 0 else y
            edges = nodes[1:] if port["sign"] == 1 else nodes[:-1]
            edge_mask = np.isclose(edges, port["edge_dbu"], rtol=0, atol=1e-8)
            broadcast = edge_mask[:, None] if axis == 0 else edge_mask[None, :]
            mask = (grid >= 0) & broadcast
            weights = transverse[mask]
            require(math.isclose(float(weights.sum()), WIDTH[port["psm_neighbor"]["layer"]], abs_tol=1e-6),
                    "Lateral cut does not meet one complete stripe")
        else:
            mask = np.logical_or.reduce([within(box) for box in port["boxes_dbu"]])
            weights = area[mask]
            area_dbu = sum((x1 - x0) * (y1 - y0) for x0, y0, x1, y1 in port["boxes_dbu"])
            require(np.all(grid[mask] >= 0) and math.isclose(float(weights.sum()), area_dbu, abs_tol=1e-6),
                    "An injection footprint is cropped or not in the rail drawing")
        injections.append((grid[mask], weights / weights.sum(), port["current_ma"]))
    return grids, dx, dy, size, cut_nodes, injections


def solve(mesh, sheet, ohms, residual, *, bound_placement):
    grids, dx, dy, size, cuts, ports = mesh
    links = []
    g_x = dy[None, :] / ((dx[:-1] + dx[1:]) / 2)[:, None]
    g_y = dx[:, None] / ((dy[:-1] + dy[1:]) / 2)[None, :]
    for grid, resistance in zip(grids, sheet, strict=True):
        for left, right, geom in ((grid[:-1], grid[1:], g_x), (grid[:, :-1], grid[:, 1:], g_y)):
            keep = (left >= 0) & (right >= 0)
            links.append((left[keep], right[keep], geom[keep] / resistance))
    links.extend((left, right, weights / resistance)
                 for (left, right, weights), resistance in zip(cuts, ohms, strict=True))
    left, right, conductance = [np.concatenate(parts) for parts in zip(*links, strict=True)]
    matrix = coo_matrix((np.tile(conductance, 4) * np.repeat([1, 1, -1, -1], conductance.size),
                         (np.concatenate((left, right, left, right)), np.concatenate((left, right, right, left)))),
                        shape=(size, size)).tocsc()
    # Fix one arbitrary voltage reference. Restore it for the full KCL check.
    factor = splu(matrix[:-1, :-1])
    rhs = np.zeros(size)
    for indices, weights, current in ports:
        rhs[indices] += weights * current
    require(abs(float(rhs.sum()) - residual) < 1e-11, "Mesh injection did not conserve port current")
    rhs[-1] -= residual
    voltage = np.append(factor.solve(rhs[:-1]), 0)
    kcl = float(np.max(np.abs(matrix @ voltage - rhs)))
    require(kcl < 1e-8, "Large finite-volume KCL residual")

    sense = np.zeros((size, len(cuts)), order="F")
    for index, ((left, right, weights), resistance) in enumerate(zip(cuts, ohms, strict=True)):
        sense[left, index] = weights / resistance
        sense[right, index] = -weights / resistance
    values = voltage @ sense
    result = dict(max_abs_cut_ma=float(np.max(np.abs(values))), cut_ma=values.tolist(), max_kcl_residual_ma=kcl,
                  min_abs_cut_ma=float(np.min(np.abs(values))))
    if bound_placement:
        influence = np.vstack((factor.solve(sense[:-1]), np.zeros((1, len(cuts)))))
        lo = np.zeros(len(cuts))
        hi = np.zeros(len(cuts))
        for indices, _, current in ports:
            choices = current * influence[indices]
            lo += choices.min(axis=0)
            hi += choices.max(axis=0)
        require(np.all(lo <= values + 1e-10) and np.all(values <= hi + 1e-10), "Adjoint bounds lost the uniform result")
        result.update(placement_max_abs_cut_ma=float(np.max(np.maximum(-lo, hi))),
                      placement_lower_ma=lo.tolist(), placement_upper_ma=hi.tolist())
    return result


def uniform_cases(mesh, sheet, residual, total):
    results = {}
    for ohm in VIA_OHMS:
        result = solve(mesh, sheet, [ohm] * len(mesh[4]), residual, bound_placement=True)
        require(abs(math.fsum(result["cut_ma"]) - total) < 1e-8,
                "Solved current differs from retained PSM cut total")
        result["opposing_cut_count"] = sum(value * total < 0 for value in result["cut_ma"])
        results[str(ohm)] = result
    return results


def mixed_cases(mesh, sheet, residual, total):
    variants = []
    for index in range(len(mesh[4])):
        ohms = [20] * len(mesh[4])
        ohms[index] = 5
        result = solve(mesh, sheet, ohms, residual, bound_placement=True)
        require(abs(math.fsum(result["cut_ma"]) - total) < 1e-8, "Mixed-R solve did not conserve branch total")
        result["opposing_cut_count"] = sum(value * total < 0 for value in result["cut_ma"])
        variants.append(dict(low_cut_index=index, **result))
    return variants


def read_inputs():
    paths = (FEEDS, DEF, TARGET["gds"], TARGET["odb"])
    expected = (FEEDS_SHA, DEF_SHA, TARGET["gds_sha256"], TARGET["odb_sha256"])
    require(all(sha(path) == digest for path, digest in zip(paths, expected, strict=True)), "Frozen mesh inputs changed")
    feeds = read(FEEDS)
    for record in (feeds["via_readback"], feeds["def_view"], feeds["dump"], feeds["terminal_readback"]):
        require(bound(record["path"]) == record, "Signed feed input changed")
    require(feeds["case"] == HEATED and feeds["target_gds_sha256"] == TARGET["gds_sha256"]
            and feeds["target_odb_sha256"] == TARGET["odb_sha256"] and feeds["via_readback"]["sha256"] == AUDIT_SHA
            and feeds["def_view"] == bound(DEF), "Signed feed scope differs")
    audit = read(feeds["via_readback"]["path"])
    require(bound(audit["dc_readback"]["path"]) == audit["dc_readback"], "Accepted DC index changed")
    heated, = [case for case in read(audit["dc_readback"]["path"])["cases"] if case["case"] == HEATED]
    request = heated["request"]
    require(bound(request["path"]) == request, "Retained heated request changed")
    return feeds, audit, read(request["path"]), request


def run():
    feeds, audit, request, request_record = read_inputs()
    families, placements = parse_def(DEF)
    gds_arrays(TARGET["gds"], families, placements)
    pads = gds_pads(families)
    axes = {key: [sorted({point[axis] for point in points}) for axis in (0, 1)]
            for key, points in placements.items()}
    by_cut = {family["cut"]: name for name, family in families.items()}
    sources = source_boxes(request)
    stripes = def_stripes()
    layout = kdb.Layout()
    layout.read(str(TARGET["gds"]))
    top, = layout.top_cells()
    require(top.name == TOP and layout.dbu == 0.001, "Unexpected GDS top or units")
    report = []
    sparse_cases = {
        case["case"]: {(rail, cut, tuple(dbu(point) for point in array["center_um"])): array
                       for rail, groups in case["rails"].items() for cut, group in groups.items()
                       for array in group["arrays_requiring_sharing"]}
        for case in audit["cases"] if "sparse" in case["case"]
    }
    require(len(sparse_cases) == 4 and len(feeds["arrays"]) == 48
            and all(len(array) == 48 for array in sparse_cases.values()), "Unexpected sparse via census")
    hot_sites = {cut: max((site for site in feeds["arrays"] if site["cut"] == cut),
                          key=lambda site: abs(site["lower_to_upper_a"])) for cut in ("Via2", "Via3")}
    for site in feeds["arrays"]:
        rail, cut, center = site["rail"], site["cut"], tuple(site["center_dbu"])
        key = rail, cut, center
        family = families[by_cut[cut]]
        layers = family["layers"]
        require(center in placements[rail, by_cut[cut]] and len(site["sides"]) == len(layers)
                and tuple(side["node"]["layer"] for side in site["sides"]) == layers
                and all(key in sample for sample in sparse_cases.values()), "Via site does not match frozen geometry")
        total = site["lower_to_upper_a"] * 1000
        prior = sparse_cases[HEATED][key]
        require(abs(float(prior["array_current_ma"]) - abs(total)) <=
                float(prior["current_upper_rounding_ma"]) - float(prior["array_current_ma"]) + 1e-12,
                "Signed and rounded via evidence disagree")
        geometry = {}
        for half_extent in (WINDOW_DBU, ALTERNATE_WINDOW_DBU):
            window = tuple(point + offset for offset in (-half_extent, half_extent) for point in center)
            evaluated = [rail_window(layout, top, rail, layer, center, kdb.Box(*window),
                                     stripes[rail, layer, center[1 - ALONG[layer]]], pads, placements)
                         for layer in layers]
            metal, added_area = zip(*evaluated, strict=True)
            ports, residual = ports_for(site, families, axes, sources, window)
            geometry[half_extent] = dict(window_dbu=window, actual_metal_boxes_dbu=metal, ports=ports,
                drawing_area_beyond_def_and_enclosures_dbu2=added_area, balance_residual_ma=residual)
        cuts = sorted(translated(box, center) for box in family["boxes"])
        sheet = [SHEET[layer] * request["sheet_resistance_scale"][layer] for layer in layers]
        base = geometry[WINDOW_DBU]
        residual = base["balance_residual_ma"]
        by_pitch = {}
        mixed = {}
        for pitch in PITCHES_DBU:
            mesh = mesh_geometry(base["actual_metal_boxes_dbu"], cuts, base["ports"], pitch)
            by_pitch[str(pitch)] = dict(nodes=mesh[3], uniform_cut_ohm=uniform_cases(mesh, sheet, residual, total))
            if site is hot_sites[cut] and pitch in PITCHES_DBU[-2:]:
                mixed[str(pitch)] = mixed_cases(mesh, sheet, residual, total)
        other = geometry[ALTERNATE_WINDOW_DBU]
        alternate = mesh_geometry(other["actual_metal_boxes_dbu"], cuts, other["ports"], 45)
        other["mesh"] = dict(pitch_dbu=45, nodes=alternate[3],
                             uniform_cut_ohm=uniform_cases(alternate, sheet, other["balance_residual_ma"], total))
        sheet_sensitivity = {name: uniform_cases(mesh, [value] * len(layers), residual, total)
                             for name, value in HOT_SHEETS.items()}
        report.append(dict(rail=rail, cut=cut, center_dbu=center, layers=layers,
                           sheet_ohm_per_square=sheet, geometry_by_half_extent_dbu=geometry,
                           cut_boxes_dbu=cuts, retained_total_ma=total,
                           retained_magnitude_ma_other_sparse_cases={name: values[key]["array_current_ma"]
                               for name, values in sparse_cases.items() if name != HEATED},
                           mesh=by_pitch, mixed_cut_r_hotspot=mixed, sheet_sensitivity=sheet_sensitivity))
    require(len({(row["rail"], row["cut"], row["center_dbu"]) for row in report}) == 48,
            "Duplicate solved via site")
    return report, request_record, feeds


def summarize(sites):
    def group(select):
        result = {}
        for ohm in map(str, VIA_OHMS):
            rows = [(site, select(site)[ohm]) for site in sites]
            maxima = {}
            for metric in METRICS:
                site, solved = max(rows, key=lambda row: row[1][metric])
                maxima[metric] = dict(peak_ma=solved[metric], rail=site["rail"], cut=site["cut"],
                                       center_dbu=site["center_dbu"],
                                       at_or_over_limit=sum(row[metric] >= LIMIT for _, row in rows))
            result[ohm] = dict(maxima, uniform_opposing_cuts=sum(row["opposing_cut_count"] for _, row in rows),
                               uniform_smallest_abs_cut_ma=min(row["min_abs_cut_ma"] for _, row in rows),
                               max_kcl_residual_ma=max(row["max_kcl_residual_ma"] for _, row in rows))
        return result

    def differences(select_a, select_b):
        result = {}
        for metric in METRICS:
            pairs = [(select_a(site)[str(ohm)][metric], select_b(site)[str(ohm)][metric])
                     for site, ohm in product(sites, VIA_OHMS)]
            result[metric] = dict(max_absolute_difference_ma=max(abs(a - b) for a, b in pairs),
                                  max_relative_difference=max(abs(a - b) / b for a, b in pairs))
        return result

    def on_mesh(site, pitch):
        return site["mesh"][str(pitch)]["uniform_cut_ohm"]

    def on_alternate(site):
        return site["geometry_by_half_extent_dbu"][ALTERNATE_WINDOW_DBU]["mesh"]["uniform_cut_ohm"]

    return dict(
        uniform_via_r_by_pitch_dbu={pitch: group(lambda site: on_mesh(site, pitch)) for pitch in PITCHES_DBU},
        uniform_via_r_by_sheet={name: group(lambda site: site["sheet_sensitivity"][name]) for name in HOT_SHEETS},
        convergence_by_pair_dbu={f"{coarse}_to_{fine}": differences(
            lambda site: on_mesh(site, coarse), lambda site: on_mesh(site, fine))
            for coarse, fine in zip(PITCHES_DBU[:-1], PITCHES_DBU[1:], strict=True)},
        changed_halo_at_45dbu=differences(lambda site: on_mesh(site, 45), on_alternate))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out.resolve()
    require(out.parent == ROOT and not out.exists(), "Use a fresh output in the exact candidate power directory")
    rows, request, feeds = run()
    report = dict(schema="pinwheel.streaming-8x4-hold-cap-cut-mesh.v1", qualified=False,
        target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
        producer=bound(__file__), feed_readback=bound(FEEDS), via_readback=feeds["via_readback"],
        def_view=feeds["def_view"], heated_psm_request=request, case=HEATED, process_spec=PROCESS_SPEC,
        per_cut_reference_ma=LIMIT, window_half_extent_dbu=WINDOW_DBU,
        alternate_window_half_extent_dbu=ALTERNATE_WINDOW_DBU, max_mesh_pitch_dbu=PITCHES_DBU,
        alternative_hot_sheet_ohm_per_square=HOT_SHEETS,
        numpy=np.__version__, scipy=scipy.__version__, klayout=kdb.__version__, gdstk=gdstk.__version__,
        uniform_boundaries="Exact signed PSM totals with uniform density along each terminating stripe edge, "
                           "adjacent via's projected cuts onto the participating layer and each external source footprint. "
                           "Positive cut current flows from the lower to upper layer. Positive port totals enter the window.",
        placement_envelope="Independent nonnegative redistribution per signed port, discretized on its footprint "
                           "with fixed branch totals. No opposite-direction subflows within one port are allowed.",
        limitations=["Local DC two-layer sheet approximation with constant sheet and vertical cut conductance.",
                     "Current totals and heat-scaled sheet R retained from one PSM activity/source case. The totals "
                     "stay fixed through all resistance sensitivity solves; adjacent cuts have prescribed boundary "
                     "fluxes and are not coupled to a third sheet.",
                     "No global feedback, temperature-dependent cell power, package/contact physics or 3D crowding.",
                     "Arbitrarily concentrated port weights are finite-mesh extrema and may yield localized "
                     "singular sheet-current density; the reported values integrate each whole via cut.",
                     "IHP resistance range is a chain characteristic. Deliberately mixed extremes are illustrative."],
        summary=summarize(rows), arrays=rows)
    with out.open("x") as stream:
        json.dump(report, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write("\n")


if __name__ == "__main__":
    main()
