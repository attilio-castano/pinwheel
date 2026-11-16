"""Partition the frozen ground grid and extract the exterior port response."""

import argparse
from array import array
from collections import Counter, defaultdict
import math
from pathlib import Path

import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import splu

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, sha, write
from streaming_8x4_hold_cap_psm_currents import parse_nodes, vectors
from streaming_8x4_hold_cap_via_audit import parse_def
from streaming_8x4_hold_cap_via_feeds import DEF_SHA, DUMP_SHA, ROOT, TERMINALS, TERMINAL_SHA
from streaming_8x4_hold_cap_physical import TARGET, TRIAL


RAIL = "VGND"
SITE = "FILLER_3_3251/VSS"
SHEET_R = 0.17195244
Y = 18900
ROW_WIDTH = 440
VIA_R = 20.0
HOTSPOT = 1565935
WINDOWS = {
    "tight": (1563300, 16600, 1566700, 21100),
    "medium": (1562400, 16600, 1569100, 21100),
    "wide": (1559030, 16600, 1570150, 21100),
    "wider": (1555850, 16600, 1575680, 21100),
    "widest": (1552450, 16600, 1579100, 21100),
    "via_pitch": (1542245, 16600, 1592645, 21100),
}


def matrix(size, a, b, g, shunts):
    diagonal = np.bincount(a, weights=g, minlength=size) + np.bincount(b, weights=g, minlength=size)
    diagonal[shunts] += 1
    ix = np.arange(size)
    return coo_matrix((np.concatenate((diagonal, -g, -g)),
                       (np.concatenate((ix, a, b)), np.concatenate((ix, b, a)))),
                      shape=(size, size)).tocsc()


def read_grid(files, sources):
    nodes, ids, _ = parse_nodes(Path(files["psm_nodes.txt"]["path"]))
    size = len(nodes) - 8
    volts = np.asarray(vectors(Path(files["psm_V.txt"]["path"]), "V", len(nodes)))[:size]
    loads = np.asarray(vectors(Path(files["psm_J.txt"]["path"]), "J", len(nodes)))[:size]
    a, b, g = array("i"), array("i"), array("d")
    with Path(files["psm_cond.txt"]["path"]).open() as stream:
        for line in stream:
            labels, value = line.rstrip().rsplit(": ", 1)
            left, right = (ids[name] for name in labels.split(" -> ", 1))
            a.append(left)
            b.append(right)
            g.append(float(value))
    a, b, g = np.asarray(a), np.asarray(b), np.asarray(g)
    source_ix = np.array([source["grid_index"] for source in sources])
    require(len(set(source_ix)) == 4 and len(a) == 709551, "Wrong ground-grid inventory")
    require(all(nodes[ix][:2] == ("Node", "Metal4") and volts[ix] > 0 for ix in source_ix),
            "Unexpected native ground source")
    residual = matrix(size, a, b, g, source_ix) @ volts - loads
    require(np.max(np.abs(residual)) < 1e-10 and np.isclose(loads.sum(), volts[source_ix].sum(), atol=1e-9, rtol=0),
            "Reconstructed original grid differs from its solver dump")
    return nodes[:size], volts, loads, a, b, g, source_ix, float(np.max(np.abs(residual)))


def partitions(nodes, a, b, g, window):
    x0, y0, x1, y1 = window
    inside = np.array([kind == "Node" and layer == "Metal1" and x0 < x < x1 and y0 < y < y1
                       for kind, layer, (x, y), _ in nodes])
    touched_edges = np.flatnonzero(inside[a] | inside[b])
    stars, internal, seams, vias = defaultdict(list), [], [], []
    for edge in touched_edges:
        left, right = a[edge], b[edge]
        if inside[left] and inside[right]:
            internal.append(edge)
            continue
        inner, outer = (left, right) if inside[left] else (right, left)
        kind, layer, _, _ = nodes[outer]
        if kind == "ITerm Node":
            require(g[edge] == 1000, "Wrong terminal connector conductance")
            stars[outer].append(inner)
        elif kind == "Node" and layer == "Metal2":
            require(math.isclose(g[edge], 2 / VIA_R, rel_tol=1e-14), "Unexpected Via1 conductance")
            vias.append((edge, inner, outer))
        else:
            require(kind == "Node" and layer == "Metal1" and nodes[inner][2][1] == nodes[outer][2][1] == Y,
                    "Crossing edge is outside the simple row seam")
            seams.append((edge, inner, outer))
    require(len(seams) == 2 and len(vias) == (x0 < 1567400 < x1), "Unexpected seam or via census")
    require(len(internal) == sum(inside) - 1 and SITE in {nodes[ix][3] for ix in stars},
            "Incomplete replaced row or hotspot star")
    star_ix = np.array(sorted(stars))
    star_edges = np.flatnonzero(np.isin(a, star_ix) | np.isin(b, star_ix))
    for edge in star_edges:
        left, right = a[edge], b[edge]
        star, grid = (left, right) if left in stars else (right, left)
        require(nodes[grid][:2] == ("Node", "Metal1") and g[edge] == 1000,
                "Unexpected star connector")
        if not inside[grid]:
            stars[star].append(grid)
    removed = np.unique(np.concatenate((touched_edges, star_edges)))
    kept = np.ones(len(a), dtype=bool)
    kept[removed] = False
    require(not np.any(inside[a[kept]] | inside[b[kept]]) and
            not np.any(np.isin(a[kept], star_ix) | np.isin(b[kept], star_ix)),
            "Native branch or terminal star survives inside patch")
    require(len(removed) == len(internal) + len(seams) + len(vias) + sum(map(len, stars.values())),
            "Branch ownership classes are incomplete")
    return inside, internal, seams, vias, stars, kept


def reinsertion_control(grid, removed_crossings, native_ports):
    nodes, volts, loads, a, b, g, sources, _ = grid
    size = len(nodes)
    retained = np.ones(len(a), dtype=bool)
    new_a, new_b, new_g, seam_volts = [], [], [], []
    for offset, ((edge, inner, outer), port) in enumerate(zip(removed_crossings, native_ports[:2], strict=True)):
        require(g[edge] == 1 / port["native_original_ohm"] or
                math.isclose(g[edge], 1 / port["native_original_ohm"], rel_tol=1e-14), "Seam clone resistance differs")
        retained[edge] = False
        new_a.extend((inner, size + offset))
        new_b.extend((size + offset, outer))
        new_g.extend((1 / port["native_internal_ohm"], 1 / port["native_external_ohm"]))
        seam_volts.append(port["native_voltage_v"])
    cloned = matrix(size + 2, np.concatenate((a[retained], new_a)), np.concatenate((b[retained], new_b)),
                    np.concatenate((g[retained], new_g)), sources)
    clone_loads = np.pad(loads, (0, 2))
    expected = np.concatenate((volts, seam_volts))
    result = splu(cloned).solve(clone_loads)
    voltage_error = float(np.max(np.abs(result - expected)))
    residual = float(np.max(np.abs(cloned @ result - clone_loads)))
    source_error = float(np.max(np.abs(result[sources] - volts[sources])))
    require(voltage_error < 1e-8 and residual < 1e-10 and source_error < 1e-9,
            "Reinserted original block did not reproduce the native grid")

    def section(electrical):
        flow = Counter()
        for ia, ib, cond in zip(a, b, g, strict=True):
            na, nb = nodes[ia], nodes[ib]
            if na[1] != "Metal1" or nb[1] != "Metal1":
                continue
            xa, ya = na[2]
            xb, yb = nb[2]
            if not (16600 < ya < 21100 and 16600 < yb < 21100 and min(xa, xb) < HOTSPOT <= max(xa, xb)):
                continue
            kind = "metal1" if na[0] == nb[0] == "Node" else "terminal_star"
            sign = 1 if xa < xb else -1
            flow[kind] += sign * (electrical[ia] - electrical[ib]) * cond
        return dict(flow)

    current_original = section(volts)
    current_reinserted = section(result)
    require(all(abs(current_reinserted[key] - value) < 1e-9 for key, value in current_original.items()),
            "Reinserted block changed section current")
    return dict(max_voltage_difference_v=voltage_error, max_source_current_difference_a=source_error,
                max_kcl_residual_a=residual, original_target_section_a=current_original,
                reinserted_target_section_a=current_reinserted)


def exterior(grid, window, via_boxes):
    nodes, volts, loads, a, b, g, sources, residual = grid
    inside, internal, seams, vias, stars, kept = partitions(nodes, a, b, g, window)
    size = len(nodes)
    active = ~inside
    active[list(stars)] = False
    require(np.all(loads[inside] == 0) and np.all(active[sources]), "Patch removed an unmapped native load/source")
    remap = np.full(size, -1)
    remap[active] = np.arange(active.sum())
    ext_loads = loads[active].copy()
    terminal_loads = []
    for star, peers in sorted(stars.items()):
        points = [nodes[ix][2] for ix in peers if inside[ix]]
        share = loads[star] / len(peers)
        require(len(peers) <= 5 and loads[star] > 0, "Wrong local terminal load")
        outer = [ix for ix in peers if not inside[ix]]
        ext_loads[remap[outer]] += share
        terminal_loads.append(dict(terminal=nodes[star][3], point_dbu=nodes[star][2],
                                   attached_points_dbu=points, outside_points_dbu=[nodes[ix][2] for ix in outer],
                                   original_a=float(loads[star]), j_a=float(share * len(points))))
    require(math.isclose(float(ext_loads.sum()) + sum(row["j_a"] for row in terminal_loads),
                         float(loads.sum()), abs_tol=2e-15), "Removed leakage was lost or counted twice")

    x0, _, x1, _ = window
    fixed_a, fixed_b, fixed_g, native_ports = [], [], [], []
    ports = []
    count = int(active.sum())
    crossings = sorted(seams, key=lambda item: nodes[item[2]][2][0])
    for edge, inner, outer in crossings:
        ix, iy = nodes[inner][2]
        ox, oy = nodes[outer][2]
        side, x = ("left", x0) if ox < ix else ("right", x1)
        require(min(ix, ox) < x < max(ix, ox) and iy == oy == Y, "Bad seam edge clipping")
        resistance = 1 / g[edge]
        width = SHEET_R * abs(ix - ox) / resistance
        require(abs(width - ROW_WIDTH) < 0.001, "Native seam shape differs from the drawn row")
        inside_fraction = abs(ix - x) / abs(ix - ox)
        r_inside = inside_fraction * resistance
        r_outside = (1 - inside_fraction) * resistance
        native_current = (volts[inner] - volts[outer]) * g[edge]
        fixed_a.append(remap[outer])
        fixed_b.append(count)
        fixed_g.append(1 / r_outside)
        native_ports.append(dict(name=side, exterior_index=int(remap[outer]), port_index=count,
                                 exterior_point_dbu=(ox, oy), interior_point_dbu=(ix, iy),
                                 native_voltage_v=float(volts[outer] + native_current * r_outside),
                                 native_outward_a=float(native_current), native_internal_ohm=r_inside,
                                 native_external_ohm=r_outside, native_original_ohm=resistance))
        ports.append(dict(name=side, kind="seam", side=side, point_dbu=(x, Y), span_dbu=(Y - 220, Y + 220)))
        count += 1
    if vias:
        edge, inner, outer = vias[0]
        require(nodes[outer][2] == (1567400, Y), "Wrong physical Via1 site")
        native_ports.append(dict(name="via", port_index=int(remap[outer]), native_voltage_v=float(volts[outer]),
                                 native_outward_a=float((volts[inner] - volts[outer]) * g[edge]),
                                 interior_point_dbu=nodes[inner][2], exterior_point_dbu=nodes[outer][2],
                                 native_internal_ohm=1 / g[edge]))
        ports.append(dict(name="via", kind="via", cut_boxes_dbu=via_boxes, resistance_ohm=VIA_R))

    ext_a = np.concatenate((remap[a[kept]], fixed_a)).astype(int)
    ext_b = np.concatenate((remap[b[kept]], fixed_b)).astype(int)
    ext_g = np.concatenate((g[kept], fixed_g))
    shunts = remap[sources]
    ext_loads = np.pad(ext_loads, (0, count - len(ext_loads)))
    ext_matrix = matrix(count, ext_a, ext_b, ext_g, shunts)
    factor = splu(ext_matrix)
    open_volts = factor.solve(ext_loads)
    port_ix = np.array([row["port_index"] for row in native_ports])
    basis = np.zeros((count, len(port_ix)))
    basis[port_ix, np.arange(len(port_ix))] = 1.0
    response = factor.solve(basis)
    impedance = response[port_ix]
    require(np.max(np.abs(impedance - impedance.T)) < 1e-10 and np.linalg.eigvalsh(impedance).min() > 0,
            "Exterior ports are not passive and reciprocal")
    require(np.max(np.abs(ext_matrix @ open_volts - ext_loads)) < 1e-10,
            "Exterior solve did not balance")
    control = reinsertion_control(grid, crossings, native_ports)
    partition = dict(window_dbu=window, baseline_kcl_residual_a=residual, reinsertion_control=control, ports=ports,
                     port_native=native_ports, terminal_loads=terminal_loads,
                     removed_grid_nodes=int(inside.sum()), removed_internal_m1_resistors=len(internal),
                     removed_star_count=len(stars),
                     removed_star_branches=sum(map(len, stars.values())), removed_via_lumps=len(vias),
                     exterior_native_resistors=int(kept.sum()), exterior_solution_nodes=count,
                     open_port_voltages_v=open_volts[port_ix].tolist(), port_impedance_ohm=impedance.tolist(),
                     external_source_response_ohm=response[shunts].tolist(),
                     open_source_voltages_v=open_volts[shunts].tolist(), total_native_load_a=float(loads.sum()))
    return partition


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    def_path = TRIAL / "trial.def"
    require(out.parent == ROOT and not out.exists() and sha(TERMINALS) == TERMINAL_SHA and sha(def_path) == DEF_SHA
            and sha(TARGET["odb"]) == TARGET["odb_sha256"] and sha(TARGET["gds"]) == TARGET["gds_sha256"],
            "Frozen inputs or output changed")
    base = read(TERMINALS)
    require(base["dump"]["sha256"] == DUMP_SHA and bound(base["dump"]["path"]) == base["dump"], "Wrong native dump")
    dump = read(base["dump"]["path"])
    files = dump["solver_dumps"][RAIL]
    require(all(bound(row["path"]) == row for row in files.values()), "Changed native grid dump")
    families, arrays = parse_def(def_path)
    via, = [name for name, family in families.items() if family["cut"] == "Via1"]
    center = (1567400, Y)
    require(center in arrays[RAIL, via], "Nearest ground Via1 not found")
    via_boxes = [[value + center[i % 2] for i, value in enumerate(box)] for box in sorted(families[via]["boxes"])]
    grid = read_grid(files, base["rails"][RAIL]["external_sources"])
    rows = {name: exterior(grid, window, via_boxes) for name, window in WINDOWS.items()}
    require(all(bound(row["path"]) == row for row in files.values()), "Native grid changed during readback")
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-m1-exterior.v1", status="diagnostic",
                    odb=bound(TARGET["odb"]), gds=bound(TARGET["gds"]), def_view=bound(def_path),
                    dump=base["dump"], terminal_readback=bound(TERMINALS), producer=bound(__file__), windows=rows,
                    seam_scope="All interior Metal1 and incident terminal stars removed. Crossing row branches "
                               "are split at the mesh interface; Via1 is replaced to the retained Metal2 node. "
                               "An intersecting star's current is divided by its original attachment count. "
                               "Outside shares are re-stamped on retained grid nodes."))


if __name__ == "__main__":
    main()
