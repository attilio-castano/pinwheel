"""Check common parent-feed resistance on the illustrative TT0004 projection."""

import argparse
from pathlib import Path

import numpy as np
from scipy.sparse.linalg import splu

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, write
from streaming_8x4_hold_cap_local_m1_grid import matrix
from streaming_8x4_hold_cap_parent_power import check_resolved, source_nodes
from streaming_8x4_hold_cap_parent_restamp import HISTORICAL, I_TOL, V_TOL, grid, placement_nodes, solve
from streaming_8x4_hold_cap_parent_workload_bounds import I2C_RESTAMP, I2C_RESTAMP_SHA
from streaming_8x4_hold_cap_physical import TARGET
from streaming_8x4_hold_cap_via_feeds import DUMP_SHA, ROOT, TERMINALS, TERMINAL_SHA


TOTAL_OHM = (0.0, 0.1, 0.25, 0.5, 1.0)
DIRECT_TOTAL_OHM = (0.25, 0.5)


def stamp(a, b, g, sources, load, ohm):
    # Replace independent ideal source nodes by one physical feed node. Each
    # existing 1 Ω branch now ends at that node, which has a shared resistor
    # to the ideal supply. Loss variables have zero at the ideal end.
    common = len(load)
    network = matrix(common + 1, np.r_[a, sources], np.r_[b, np.full(len(sources), common)],
                     np.r_[g, np.ones(len(sources))], np.array([], dtype=int))
    diagonal = network.diagonal()
    diagonal[common] += 1 / ohm
    network.setdiag(diagonal)
    drive = np.r_[load, 0]
    loss = splu(network).solve(drive)
    branch_currents = loss[sources] - loss[common]
    residual = float(np.max(np.abs(network @ loss - drive)))
    require(residual < 1e-10 and abs(loss[common] / ohm - load.sum()) < I_TOL
            and abs(branch_currents.sum() - load.sum()) < I_TOL, "Common feed failed current balance")
    return loss, branch_currents, residual


def rail_checks(rail, old, files, parent, comparator, bindings):
    nodes, _, inject, a, b, g = grid(files, sum(old["edge_counts"].values()))
    load = -inject if rail == "VPWR" else inject
    total = float(load.sum())
    require(abs(total - old["modeled_load_a"]) < 1e-15
            and abs(total * 1000 - comparator["source_current_total_ma"]) < I_TOL * 1000,
            "Heated I²C current differs from comparator")
    sources, _ = placement_nodes(nodes, parent, source_nodes(rail, bindings))
    network = matrix(len(load), a, b, g, np.array([], dtype=int))
    reference, branch_current, _ = solve(network, load, sources, 1)
    term_ix = [i for i, node in enumerate(nodes) if node[0] == "ITerm Node"]
    require(abs(float(reference[term_ix].max()) - comparator["worst_terminal_loss_mv"] / 1000) < V_TOL
            and abs(float(branch_current.max()) - comparator["peak_source_current_ma"] / 1000) < I_TOL,
            "Historical source and voltage baseline did not reproduce")
    cases = {}
    for combined_ohm in DIRECT_TOTAL_OHM:
        per_rail = combined_ohm / 2
        loss, shifted_branch_current, residual = stamp(a, b, g, sources, load, per_rail)
        shift = total * per_rail
        voltage_error = float(np.max(np.abs(loss[:-1] - reference - shift)))
        current_error = float(np.max(np.abs(shifted_branch_current - branch_current)))
        require(voltage_error < V_TOL and current_error < I_TOL and abs(loss[-1] - shift) < V_TOL,
                "Direct common-feed stamp differs from I × R shift")
        cases[str(combined_ohm)] = dict(per_rail_shared_ohm=per_rail, common_feed_loss_mv=float(loss[-1] * 1000),
                                        total_source_current_ma=float(loss[-1] / per_rail * 1000),
                                        max_node_voltage_difference_v=voltage_error,
                                        max_contact_current_difference_a=current_error, kcl_residual_a=residual)
    return total, cases


def run(out):
    require(out.parent == ROOT and not out.exists(), "Use a fresh ignored power-dc output")
    producer = bound(__file__)
    comparator_item, terminals_item = bound(I2C_RESTAMP), bound(TERMINALS)
    require(comparator_item["sha256"] == I2C_RESTAMP_SHA and terminals_item["sha256"] == TERMINAL_SHA,
            "Changed heated I²C reference")
    comparator, terminals = read(I2C_RESTAMP), read(TERMINALS)
    dump_item = bound(terminals["dump"]["path"])
    require(dump_item == terminals["dump"] and dump_item["sha256"] == DUMP_SHA, "Changed exact rail dump")
    dump = read(dump_item["path"])
    parent, parent_item = check_resolved(Path(comparator["parent_contacts"]["path"]))
    require(parent_item == comparator["parent_contacts"] and parent["input"]["classification"] == "illustrative"
            and all(row["external_ohm"] == 1 for row in parent["rails"].values()), "Wrong diagnostic source geometry")
    bindings = [producer, comparator_item, terminals_item, dump_item, parent_item]
    results, totals = {}, {}
    for rail, baseline in terminals["rails"].items():
        files = dump["solver_dumps"][rail]
        require(all(bound(item["path"]) == item for item in files.values()), "Changed pinned voltage/current dump")
        bindings.extend(files.values())
        totals[rail], results[rail] = rail_checks(
            rail, baseline, files, parent["rails"][rail], comparator["rails"][rail][HISTORICAL], bindings)
    require(abs(totals["VPWR"] - totals["VGND"]) < 1e-15, "Unequal fixed rail loads")
    baseline = comparator["paired"][HISTORICAL]
    sweep = []
    for ohm in TOTAL_OHM:
        delta_mv = ohm / 2 * sum(totals.values()) * 1000
        sweep.append(dict(total_shared_ohm=ohm, added_loss_mv=delta_mv,
                          combined_rail_extrema_mv=baseline["summed_rail_extrema_mv"] + delta_mv,
                          minimum_differential_v=baseline["minimum_instance_differential_v"] - delta_mv / 1000))
    require(all(bound(item["path"]) == item for item in bindings), "Shared-feed study inputs changed")
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-parent-shared-feed.v1", status="diagnostic",
                    target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"], inputs=bindings,
                    source="TT0004 historically projected contacts with retained 1 ohm per contact branch",
                    rail_fixed_load_ma={rail: value * 1000 for rail, value in totals.items()},
                    sweep=sweep, common_feed_stamp_checks=results, transient_power_analyzed=False,
                    actual_parent_impedance_measured=False, qualified_power=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    run(parser.parse_args().out.resolve())


if __name__ == "__main__":
    main()
