"""Bound historical-contact static rail loss for three retained OpenROAD workloads."""

import argparse
import csv
import hashlib
from pathlib import Path

import numpy as np
from scipy.sparse.linalg import splu

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, write
from streaming_8x4_hold_cap_local_m1_grid import matrix
from streaming_8x4_hold_cap_parent_power import check_resolved, source_nodes
from streaming_8x4_hold_cap_parent_restamp import grid, placement_nodes
from streaming_8x4_hold_cap_physical import TARGET
from streaming_8x4_hold_cap_psm_currents import dbu, spice_name, tolerance
from streaming_8x4_hold_cap_via_feeds import DUMP_SHA, ROOT, TERMINALS, TERMINAL_SHA


NATIVE = ROOT / "goal-workload-readback-01.json"
NATIVE_SHA = "583e147c2d7cbad0f1d9d2f137b6029286058b5d861a944c88a648e97c4c6a68"
I2C_RESTAMP = ROOT / "tt0004-parent-restamp-01.json"
I2C_RESTAMP_SHA = "5948dd508726a2c91fde85e1a5d8bf324d5f03573cf4002c55ea317133317979"
SUITE = ("goal-uart-01", "goal-spi-01", "goal-reset-upload-01")
SOURCE = "https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/psm/src/ir_solver.h"
MIN_PRINTED_A = 1e-18
V_TOL = 1e-8


def spice_loads(path, size, names, nodes):
    mean, radius = np.zeros(size), np.zeros(size)
    radius[list(names.values())] = MIN_PRINTED_A
    topology = hashlib.sha256()
    consumed = set()
    pending = None
    with path.open("rb") as stream:
        for raw in stream:
            if raw.startswith((b"R", b"V")):
                topology.update(raw)
            elif raw.startswith(b"* Sink for "):
                require(pending is None, "Unexpected duplicate current-source heading")
                pending = raw.decode("ascii").strip().removeprefix("* Sink for ")
            elif raw.startswith(b"I"):
                _, node, ground, dc, token = raw.decode("ascii").split()
                require(pending in names and pending not in consumed and ground == "0" and dc == "DC",
                        "Unknown or repeated named terminal current")
                idx = names[pending]
                value, width = float(token), tolerance(token)
                require(spice_name(nodes[idx]) == node and np.isfinite(value) and value >= MIN_PRINTED_A and width < value,
                        "Invalid printed current or terminal mapping")
                mean[idx], radius[idx] = value, width
                consumed.add(pending)
                pending = None
    require(pending is None and len(consumed) == 79_065, "Incomplete SPICE current inventory")
    return mean, radius, topology.hexdigest()


def native_comparison(path, nodes, names, loss, error, rail, baseline_v):
    seen = set()
    maximum, excess = 0, 0
    with path.open() as stream:
        rows = csv.reader(stream)
        require(next(rows) == ["Instance", "Terminal", "Layer", "X location", "Y location", "Voltage"],
                "Unexpected native voltage report")
        for instance, pin, layer, x, y, v in rows:
            label = f"{instance}/{pin}"
            ix = names[label]
            require(label not in seen and nodes[ix][1:3] == (layer, (dbu(x), dbu(y))),
                    "Native/retained terminal geometry differs")
            value = baseline_v - float(v) if rail == "VPWR" else float(v) - baseline_v
            delta = abs(loss[ix] - value)
            maximum = max(maximum, delta)
            excess = max(excess, delta - error[ix] - tolerance(v))
            seen.add(label)
    require(len(seen) == len(names) == 98_904 and excess <= V_TOL,
            "Native terminal voltages exceeded propagated current and report rounding bounds")
    return dict(max_difference_v=float(maximum), max_excess_after_rounding_v=float(excess), checked_terminal_voltages=len(seen))


def solve_rail(rail, fields, old, parent, cases, bindings):
    nodes, _, _, a, b, g = grid(fields, sum(old["edge_counts"].values()))
    names = {node[3]: idx for idx, node in enumerate(nodes) if node[0] == "ITerm Node"}
    terms = sorted((name.rsplit("/", 1)[0], idx) for name, idx in names.items())
    projected, _ = placement_nodes(nodes, parent, source_nodes(rail, bindings))
    sparse = [row["grid_index"] for row in old["external_sources"]]
    baseline_v = old["external_sources"][0]["fixed_source_v"]
    original = Path(fields["psm_cond.txt"]["path"]).parent.parent / f"{rail}.spice"
    original_binding = bound(original)
    bindings.append(original_binding)
    _, _, reference_topo = spice_loads(original, len(nodes), names, nodes)
    output = {case: dict() for case in cases}
    drives = {}
    index = np.array([idx for _, idx in terms])
    for case in cases:
        spice = ROOT / case / f"{rail}.spice"
        current, precision, topology = spice_loads(spice, len(nodes), names, nodes)
        require(topology == reference_topo, "Native source/resistor export differs from baseline topology")
        output[case]["load_total_ma"] = float(current.sum() * 1000)
        output[case]["load_total_uncertainty_ma"] = float(precision.sum() * 1000)
        drives[case] = (current, precision)
    for source_name, sources in (("sparse", sparse), ("projected", projected)):
        network = matrix(len(nodes), a, b, g, np.array(sources))
        factor = splu(network)
        for case, (current, precision) in drives.items():
            loss, error = factor.solve(np.column_stack((current, precision))).T
            require(np.all(np.isfinite(loss)) and np.all(np.isfinite(error)) and error.min() >= -V_TOL
                    and np.max(np.abs(network @ loss - current)) < 1e-10
                    and np.max(np.abs(network @ error - precision)) < 1e-10
                    and abs(loss[sources].sum() - current.sum()) < 1e-9,
                    "Passive interval solve did not satisfy KCL")
            error = np.maximum(error, 0) + V_TOL
            entry = dict(source_nodes=len(sources), max_uncertainty_v=float(error[index].max()),
                         rail_loss_mv=float(loss[index].max() * 1000),
                         rail_loss_interval_mv=[float((loss[index] - error[index]).max() * 1000),
                                                float((loss[index] + error[index]).max() * 1000)])
            if source_name == "sparse":
                path = ROOT / case / f"{rail}-voltage.csv"
                entry["native_calibration"] = native_comparison(path, nodes, names, loss, error, rail, baseline_v)
            output[case][source_name] = (entry, loss[index], error[index])
        del factor, network
    return output, [name for name, _ in terms], reference_topo


def run(parent_path, out):
    require(out.parent == ROOT and not out.exists(), "Use a fresh power-dc result")
    bound_inputs = [bound(__file__), bound(NATIVE), bound(I2C_RESTAMP), bound(TERMINALS)]
    require([item["sha256"] for item in bound_inputs[1:]] == [NATIVE_SHA, I2C_RESTAMP_SHA, TERMINAL_SHA],
            "Wrong retained native comparisons")
    native = read(NATIVE)
    old = read(TERMINALS)
    dump_item = bound(old["dump"]["path"])
    require(dump_item == old["dump"] and dump_item["sha256"] == DUMP_SHA, "Wrong native conductance dump")
    dump = read(dump_item["path"])
    parent, parent_item = check_resolved(parent_path)
    require(parent_item == read(I2C_RESTAMP)["parent_contacts"]
            and all(parent["rails"][rail]["external_ohm"] == 1 for rail in parent["rails"]),
            "Projected boundary differs from the verified I2C case")
    bound_inputs += [dump_item, parent_item, *parent["inputs"], *dump["golden_equal"].values()]
    cases = {row["case"]: row for row in native["cases"] if row["case"] in SUITE}
    require(set(cases) == set(SUITE), "Wrong native workload suite")
    for row in cases.values():
        request = read(row["request"]["path"])
        result = read(row["native"]["path"])
        require(row["parent_contacts"] == cases["goal-uart-01"]["parent_contacts"]
                and request["sheet_temperature_c"] == 105 and set(request["external_ohm_per_source"].values()) == {1}
                and row["vcd_annotated_pins"] == 124219,
                "Cases do not share the retained heated sparse boundary")
        bound_inputs.extend([row["request"], row["native"], *result["artifacts"], *request["inputs"].values()])
    require(all(bound(item["path"]) == item for item in bound_inputs), "Native power workload artifacts changed")
    measurements, term_names, topology = {}, {}, {}
    for rail, baseline in old["rails"].items():
        files = dump["solver_dumps"][rail]
        bound_inputs.extend(files.values())
        require(all(bound(item["path"]) == item for item in files.values()), "Changed conductance inputs")
        measurements[rail], term_names[rail], topology[rail] = solve_rail(
            rail, files, baseline, parent["rails"][rail], cases, bound_inputs)
    require(term_names["VPWR"] == term_names["VGND"], "Rail terminal orders differ")
    result = {}
    for case, row in cases.items():
        record = {rail: {key: measurements[rail][case][key] for key in ("load_total_ma", "load_total_uncertainty_ma")}
                  for rail in measurements}
        for source_name in ("sparse", "projected"):
            supply, vdd, e1 = measurements["VPWR"][case][source_name]
            ret, gnd, e2 = measurements["VGND"][case][source_name]
            loss, error = vdd + gnd, e1 + e2
            lower, upper = float(np.max(loss - error)), float(np.max(loss + error))
            if source_name == "sparse":
                observed = 1.2 - row["minimum_instance_differential_v"]
                require(lower - 1.01e-6 <= observed <= upper + 1.01e-6,
                        "Native paired minimum lies outside modeled and output rounding interval")
            record[source_name] = dict(rails={"VPWR": supply, "VGND": ret}, paired_loss_mv=float(loss.max() * 1000),
                                       paired_loss_interval_mv=[lower * 1000, upper * 1000],
                                       min_instance_v=1.2 - float(loss.max()))
        result[case] = record
    require(all(bound(item["path"]) == item for item in bound_inputs), "Workload or model changed during solve")
    write(out, dict(schema="pinwheel.streaming-8x4-hold-cap-parent-workload-bounds.v1", producer=bound_inputs[0],
                    target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
                    cases=result, matched_sparse_topology_sha256=topology, parent_contacts=parent_item, inputs=bound_inputs,
                    native_readback=bound_inputs[1], i2c_comparator=bound_inputs[2], source_threshold_reference=SOURCE,
                    unprinted_current_upper_bound_a=MIN_PRINTED_A, safety_pad_v=V_TOL,
                    full_precision_workload_current_dumps_available=False, qualified_power=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-contacts", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.parent_contacts.resolve(strict=True), args.out.resolve())
    print(args.out)


if __name__ == "__main__":
    main()
