"""Resolve the retained static I²C rail model under projected parent contacts."""

import argparse
from array import array
from pathlib import Path

import numpy as np
import scipy
from scipy.sparse.linalg import splu

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, write
from streaming_8x4_hold_cap_local_m1_grid import matrix
from streaming_8x4_hold_cap_parent_power import check_resolved, dbu, source_nodes
from streaming_8x4_hold_cap_physical import TARGET
from streaming_8x4_hold_cap_psm_currents import parse_nodes, vectors
from streaming_8x4_hold_cap_via_feeds import DUMP_SHA, ROOT, TERMINALS, TERMINAL_SHA


BASE = "retained_sparse_1ohm"
HISTORICAL = "projected_tt0004_1ohm"
DISTRIBUTED = "distributed_ideal"
CASES = (BASE, HISTORICAL, DISTRIBUTED)
V_TOL = 1e-8
I_TOL = 1e-9


def grid(files, expected_edges):
    nodes, index, _ = parse_nodes(Path(files["psm_nodes.txt"]["path"]))
    right = np.asarray(vectors(Path(files["psm_J.txt"]["path"]), "J", len(nodes)))
    voltage = np.asarray(vectors(Path(files["psm_V.txt"]["path"]), "V", len(nodes)))
    physical = len(nodes) - 8
    require(all(node[0] == "Source Node" for node in nodes[physical:]), "Unexpected original source auxiliaries")
    a, b, g = array("i"), array("i"), array("d")
    with Path(files["psm_cond.txt"]["path"]).open() as stream:
        for line in stream:
            labels, value = line.rstrip().rsplit(": ", 1)
            left, right_node = (index[name] for name in labels.split(" -> ", 1))
            a.append(left)
            b.append(right_node)
            g.append(float(value))
    require(len(a) == expected_edges and min(g) > 0, "Incomplete passive retained rail")
    return nodes[:physical], voltage[:physical], right[:physical], np.asarray(a), np.asarray(b), np.asarray(g)


def placement_nodes(nodes, parent, native):
    index = {node[2]: i for i, node in enumerate(nodes) if node[:2] == ("Node", "Metal4")}
    require(set(index) == native, "Exact distributed Metal4 pin-node inventory differs")
    projected = [tuple(map(dbu, point)) for point in parent["nodes_um"]]
    require(len(projected) == len(set(projected)) and set(projected) <= native, "Duplicate or absent projected node")
    return [index[point] for point in sorted(projected)], [index[point] for point in sorted(native)]


def solve(passive, load, external, ohm):
    if ohm:
        stamped = passive.copy()
        diagonal = stamped.diagonal()
        diagonal[external] += 1 / ohm
        stamped.setdiag(diagonal)
        loss = splu(stamped).solve(load)
        currents = loss[external] / ohm
        residual = stamped @ loss - load
    else:
        free = np.ones(len(load), dtype=bool)
        free[external] = False
        loss = np.zeros(len(load))
        loss[free] = splu(passive[free][:, free].tocsc()).solve(load[free])
        error = passive @ loss - load
        currents, residual = -error[external], error[free]
    require(np.all(np.isfinite(loss)) and loss.min() >= -V_TOL and currents.min() >= -I_TOL
            and abs(currents.sum() - load.sum()) < I_TOL and np.max(np.abs(residual)) < 1e-10,
            "Restamped rail did not satisfy voltage or current balance")
    return loss, currents, float(np.max(np.abs(residual)))


def rail_summary(nodes, a, b, g, terminal_ix, real, indices, volts, currents, residual):
    worst = terminal_ix[int(np.argmax(volts[terminal_ix]))]
    edge_current = np.abs((volts[a] - volts[b]) * g)
    grid = np.flatnonzero(real[a] & real[b])
    edge = grid[int(np.argmax(edge_current[grid]))]
    i = int(np.argmax(currents))
    return dict(worst_terminal_loss_mv=float(volts[worst] * 1000), worst_terminal=nodes[worst][3],
                source_count=len(indices), source_current_total_ma=float(currents.sum() * 1000),
                peak_source_current_ma=float(currents[i] * 1000), peak_source_point_dbu=nodes[indices[i]][2],
                peak_geometric_edge_current_ma=float(edge_current[edge] * 1000),
                peak_geometric_edge=[nodes[a[edge]], nodes[b[edge]]], max_kcl_residual_a=residual)


def run_rail(rail, old, files, parent, bindings):
    nodes, native_v, injected, a, b, g = grid(files, sum(old["edge_counts"].values()))
    source_sign = -1 if rail == "VPWR" else 1
    source = old["external_sources"][0]["fixed_source_v"]
    require(all(abs(row["fixed_source_v"] - source) < 1e-12 for row in old["external_sources"]),
            "Original sources disagree on rail reference")
    expected_loss = source_sign * (native_v - source)
    load = source_sign * injected
    base = [row["grid_index"] for row in old["external_sources"]]
    projected, distributed = placement_nodes(nodes, parent, source_nodes(rail, bindings))
    real = np.array([node[0] == "Node" for node in nodes])
    terms = sorted((node[3].rsplit("/", 1)[0], index) for index, node in enumerate(nodes) if node[0] == "ITerm Node")
    names, term_ix = zip(*terms, strict=True)
    require(len(names) == len(set(names)) == 98_904 and load.min() >= 0
            and np.isclose(load.sum(), old["modeled_load_a"], atol=1e-15, rtol=0),
            "Wrong pinned terminal and I²C workload current")
    term_ix = np.asarray(term_ix)
    passive = matrix(len(nodes), a, b, g, np.array([], dtype=int))
    cases = ((BASE, base, 1), (HISTORICAL, projected, 1), (DISTRIBUTED, distributed, 0))
    results, terminal_losses = {}, {}
    for name, indices, ohm in cases:
        loss, current, residual = solve(passive, load, indices, ohm)
        result = rail_summary(nodes, a, b, g, term_ix, real, indices, loss, current, residual)
        result.update(external_ohm_per_source=ohm)
        if name == BASE:
            expected_currents = np.array([abs(row["amps_source_to_grid"]) for row in old["external_sources"]])
            voltage_error = float(np.max(np.abs(loss - expected_loss)))
            source_error = float(np.max(np.abs(current - expected_currents)))
            require(voltage_error < V_TOL and source_error < I_TOL, "Four-contact reference replay differs from OpenROAD")
            result.update(max_reference_voltage_error_v=voltage_error, max_reference_source_current_error_a=source_error)
        results[name] = result
        terminal_losses[name] = loss[term_ix]
    return results, names, terminal_losses


def run(parent_path, out):
    require(out.parent == ROOT and not out.exists(), "Use a fresh ignored power-dc receipt")
    producer = bound(__file__)
    terminal_item = bound(TERMINALS)
    require(terminal_item["sha256"] == TERMINAL_SHA, "Changed retained terminal currents")
    old = read(TERMINALS)
    dump = read(old["dump"]["path"])
    require(old["dump"]["sha256"] == DUMP_SHA and bound(old["dump"]["path"]) == old["dump"]
            and dump["target_odb_sha256"] == TARGET["odb_sha256"] and dump["target_gds_sha256"] == TARGET["gds_sha256"],
            "Wrong frozen dump")
    parent, parent_item = check_resolved(parent_path)
    require(parent["input"]["classification"] == "illustrative" and
            {rail: len(row["nodes_um"]) for rail, row in parent["rails"].items()} == {"VPWR": 665, "VGND": 630}
            and all(row["external_ohm"] == 1 for row in parent["rails"].values()),
            "Wrong historical diagnostic contact map")
    bindings = [producer, terminal_item, parent_item, old["dump"], *parent["inputs"]]
    rails, names, losses = {}, {}, {}
    for rail, data in old["rails"].items():
        files = dump["solver_dumps"][rail]
        bindings.extend(files.values())
        require(all(bound(item["path"]) == item for item in files.values()), "Changed pinned matrix")
        rails[rail], names[rail], losses[rail] = run_rail(rail, data, files, parent["rails"][rail], bindings)
    require(names["VPWR"] == names["VGND"], "Rail terminal orders differ")
    paired = {}
    for case in CASES:
        loss = losses["VPWR"][case] + losses["VGND"][case]
        worst = int(np.argmax(loss))
        paired[case] = dict(worst_instance=names["VPWR"][worst], minimum_instance_differential_v=1.2 - float(loss[worst]),
                            paired_loss_mv=float(loss[worst] * 1000),
                            summed_rail_extrema_mv=sum(rails[rail][case]["worst_terminal_loss_mv"] for rail in rails))
    require(all(bound(item["path"]) == item for item in bindings), "Restamp input changed")
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-parent-restamp.v1", status="diagnostic",
                    target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
                    inputs=bindings, producer=producer, numpy_version=np.__version__, scipy_version=scipy.__version__,
                    rails=rails, paired=paired, parent_contacts=parent_item,
                    activity="Retained 50 MHz zero-delay I2C read with exact original fixed current injections",
                    scope="Restamps external sources in the retained heated lumped rail; projected contacts are illustrative",
                    transient_droop_analyzed=False, parent_supply_model_qualified=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-contacts", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.parent_contacts.resolve(strict=True), args.out.resolve())
    print(args.out)


if __name__ == "__main__":
    main()
