"""Remove one idealized decap terminal star per rail in the retained grid model."""

import argparse
from array import array
import math
from pathlib import Path

import numpy as np
import scipy
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import splu

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, sha, write
from streaming_8x4_hold_cap_psm_currents import parse_nodes, vectors
from streaming_8x4_hold_cap_via_feeds import DUMP_SHA, ROOT, TERMINALS, TERMINAL_SHA
from streaming_8x4_hold_cap_physical import TARGET


HOTSPOTS = {"VGND": "FILLER_3_3251/VSS", "VPWR": "FILLER_7_3350/VDD"}


def solve(rail, evidence, files):
    nodes, indices, _ = parse_nodes(Path(files["psm_nodes.txt"]["path"]))
    count = len(nodes) - 8
    voltage = np.asarray(vectors(Path(files["psm_V.txt"]["path"]), "V", len(nodes)))[:count]
    loads = np.asarray(vectors(Path(files["psm_J.txt"]["path"]), "J", len(nodes)))[:count]
    terminal, = [i for i, node in enumerate(nodes) if node[3] == HOTSPOTS[rail]]
    kept = np.ones(count, dtype=bool)
    kept[terminal] = False
    rows, cols, weights = array("i"), array("i"), array("d")
    removed = []
    with Path(files["psm_cond.txt"]["path"]).open() as stream:
        for line in stream:
            ends, token = line.strip().rsplit(": ", 1)
            a, b = (indices[name] for name in ends.split(" -> ", 1))
            conductance = float(token)
            if terminal in (a, b):
                other = a if b == terminal else b
                require(nodes[other][0] == "Node" and conductance == 1000, "Wrong terminal branch")
                removed.append((other, conductance * (voltage[other] - voltage[terminal])))
            else:
                rows.append(a)
                cols.append(b)
                weights.append(conductance)
    require(len(removed) == (5 if rail == "VGND" else 3), "Unexpected removed decap star")
    require(math.isclose(-math.fsum(amps for _, amps in removed), loads[terminal], abs_tol=6e-12),
            "Native terminal current does not balance")
    a, b, g = np.asarray(rows), np.asarray(cols), np.asarray(weights)
    diagonal = np.bincount(a, g, minlength=count) + np.bincount(b, g, minlength=count)
    source_indices = np.array([row["grid_index"] for row in evidence["external_sources"]])
    require(len(source_indices) == len(set(source_indices)) == 4, "Wrong external source census")
    diagonal[source_indices] += 1.0
    diagonal[terminal] = 1.0
    diagonal_indices = np.arange(count)
    matrix = coo_matrix((np.concatenate((diagonal, -g, -g)),
                         (np.concatenate((diagonal_indices, a, b)), np.concatenate((diagonal_indices, b, a)))),
                        shape=(count, count)).tocsc()
    rhs = np.zeros(count)
    for peer, old_outward_a in removed:
        rhs[peer] += old_outward_a + loads[terminal] / len(removed)
    # Refactor the existing graph around the retained voltages. The delta
    # uses a grounded ideal source on the far end of each 1 Ω branch.
    factor = splu(matrix)
    delta = factor.solve(rhs)
    error = np.max(np.abs(matrix @ delta - rhs))
    require(np.all(np.isfinite(delta)) and error < 1e-11, "Rewired grid solve did not balance")
    sources = []
    for row in evidence["external_sources"]:
        ix = row["grid_index"]
        previous = row["amps_source_to_grid"]
        sources.append(dict(point_dbu=nodes[ix][2], source_to_grid_a=previous - delta[ix],
                            source_current_change_a=-delta[ix]))
    require(abs(math.fsum(item["source_current_change_a"] for item in sources)) < 6e-12,
            "Modeled source total changed")
    max_delta_ix = int(np.argmax(np.abs(delta)))
    patches = [dict(point_dbu=nodes[ix][2], old_voltage_v=voltage[ix],
                    revised_voltage_v=voltage[ix] + delta[ix], old_branch_a_into_terminal=old_amps)
               for ix, old_amps in removed]
    changes = voltage + delta
    old_spread = np.ptp([row["old_voltage_v"] for row in patches])
    new_spread = np.ptp([row["revised_voltage_v"] for row in patches])
    ports = np.array([ix for ix, _ in removed])
    basis = np.zeros((count, len(ports)))
    basis[ports, np.arange(len(ports))] = 1.0
    port_impedance = factor.solve(basis)[ports]
    require(np.allclose(port_impedance, port_impedance.T, rtol=0, atol=1e-9)
            and np.linalg.eigvalsh(port_impedance).min() > 0,
            "Port response violates reciprocity or passivity")
    neutral = delta - factor.solve(basis @ np.full(len(ports), loads[terminal] / len(ports)))
    port_open_v = (voltage + neutral)[ports]
    require(np.allclose(port_open_v + port_impedance @ np.full(len(ports), loads[terminal] / len(ports)),
                        changes[ports], rtol=0, atol=1e-12), "Port response disagrees with whole-grid solve")
    return dict(removed_terminal=HOTSPOTS[rail], removed_connector_count=len(removed),
                total_nodes=count, retained_resistor_count=len(a), net_load_a=loads[terminal],
                redistributed_leakage_per_peer_a=loads[terminal] / len(removed), patch_voltages=patches,
                open_port_voltage_v=port_open_v.tolist(), port_impedance_ohm=port_impedance.tolist(),
                old_patch_swing_v=float(old_spread), revised_patch_swing_v=float(new_spread),
                max_abs_grid_change_v=float(abs(delta[max_delta_ix])),
                max_abs_grid_change_node=nodes[max_delta_ix],
                old_grid_voltage_extrema_v=[float(np.min(voltage[kept])), float(np.max(voltage[kept]))],
                revised_grid_voltage_extrema_v=[float(np.min(changes[kept])), float(np.max(changes[kept]))],
                max_delta_kcl_residual_a=float(error), sources=sources)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    require(out.parent == ROOT and not out.exists() and sha(TERMINALS) == TERMINAL_SHA
            and sha(TARGET["odb"]) == TARGET["odb_sha256"] and sha(TARGET["gds"]) == TARGET["gds_sha256"],
            "Use a fresh readback on the unchanged target")
    base = read(TERMINALS)
    require(base["dump"]["sha256"] == DUMP_SHA and bound(base["dump"]["path"]) == base["dump"],
            "Terminal dump changed")
    dump = read(base["dump"]["path"])
    rails = {}
    for rail, data in base["rails"].items():
        files = dump["solver_dumps"][rail]
        require(all(bound(row["path"]) == row for row in files.values()), "Matrix inputs changed")
        rails[rail] = solve(rail, data, files)
        require(all(bound(row["path"]) == row for row in files.values()), "Matrix inputs changed during solve")
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-decap-feedback.v1", status="diagnostic",
                    target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
                    terminal_readback=bound(TERMINALS), dump=base["dump"], producer=bound(__file__),
                    scipy_version=scipy.__version__, numpy_version=np.__version__, rails=rails,
                    scope="Each rail separately has only its one selected PSM idealized decap star removed. "
                          "Its original net leakage is distributed equally across former attachment nodes. "
                          "The remaining lumped rail, other terminal stars, and source voltage/resistance are frozen. "
                          "No physical cut/terminal model or revised activity is inserted in the full-chip graph."))


if __name__ == "__main__":
    main()
