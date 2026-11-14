"""Recover signed terminal and external-source currents from full PDNSim dumps."""

import argparse
from array import array
from collections import Counter
import csv
import math
from pathlib import Path
import re

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, write
from streaming_8x4_hold_cap_ir import VOLTAGES
from streaming_8x4_hold_cap_physical import TARGET, TRIAL
from streaming_8x4_hold_cap_psm_dump import DUMP_NAMES, GOLDEN, golden_case


SCHEMA = "pinwheel.streaming-8x4-hold-cap-psm-currents.v1"
INVENTORY = TRIAL / "views/actual-signal/inventory.json"
INVENTORY_SHA = "d1a6e5fb7f084cc186a4d213e377bcb48869a036f503bfd136859de9baa50fa2"
DESCRIPTION = re.compile(r"(Node|ITerm Node|BPin Node|Source Node): \((-?\d+\.\d{4}), (-?\d+\.\d{4})\) on (Metal[1-4])(?:\: (\S+))?")
REAL_NODES = {"Node", "ITerm Node", "BPin Node"}
AMP_TOL = 5e-9


def dbu(value):
    scaled = float(value) * 1000
    require(abs(scaled - round(scaled)) <= 1e-6, "Off-grid dump coordinate")
    return round(scaled)


def parse_nodes(path):
    nodes, name_to_id, spice_counts = [], {}, Counter()
    with path.open() as stream:
        for index, line in enumerate(stream):
            prefix, name = line.rstrip("\n").split(": ", 1)
            row = DESCRIPTION.fullmatch(name)
            require(int(prefix) == index and row is not None, "Malformed solver node sequence")
            kind, x, y, layer, label = row.groups()
            point = (dbu(x), dbu(y))
            nodes.append((kind, layer, point, label))
            require(bool(label) == (kind == "ITerm Node"), "Wrong solver terminal identity")
            if kind in REAL_NODES:
                require(name not in name_to_id, "Duplicate physical solver node")
                name_to_id[name] = index
                # ITerm metadata is essential if two different terminals share a location.
                spice_counts[spice_name(nodes[-1])] += 1
    require(nodes and len(name_to_id) == len(nodes) - 8 and all(name.startswith("ITermNode_") or count == 1
            for name, count in spice_counts.items()), "Missing nodes or ambiguous grid/SPICE identity")
    return nodes, name_to_id, sum(count > 1 for count in spice_counts.values())


def spice_name(node):
    kind, layer, (x, y), _ = node
    return f"{kind.replace(' ', '')}_{layer}_{x}_{y}"


def vectors(path, name, count):
    values = array("d")
    with path.open() as stream:
        for index, line in enumerate(stream):
            key, text = line.strip().split(" = ", 1)
            value = float(text)
            require(key == f"{name}[{index}]" and math.isfinite(value), "Malformed solver vector")
            values.append(value)
    require(len(values) == count, "Incomplete solver vector")
    return values


def tolerance(token):
    mantissa, _, exponent = token.lower().partition("e")
    fraction = mantissa.partition(".")[2]
    return 0.500001 * 10 ** (int(exponent or "0") - len(fraction))


def rounded(value, token, extra=0):
    return abs(value - float(token)) <= tolerance(token) + extra


def matrix(path, nodes, voltage, j):
    diagonal, residual = (array("d", (0 for _ in nodes)) for _ in range(2))
    edges, positive = {}, {}
    prior = (-1, -1)
    with path.open() as stream:
        for line in stream:
            index, token = line.strip().split(" = ", 1)
            col, row = map(int, index.removeprefix("G[").removesuffix("]").split(", "))
            value = float(token)
            require(prior < (col, row) and 0 <= row < len(nodes) and 0 <= col < len(nodes)
                    and math.isfinite(value) and value != 0, "Malformed or unsorted matrix entry")
            prior = (col, row)
            residual[row] += value * voltage[col]
            if row == col:
                require(value > 0, "Nonpositive conductance diagonal")
                diagonal[row] = value
            else:
                table = positive if value > 0 else edges
                if col < row:
                    table[col, row] = value
                else:
                    require(table.get((row, col)) == value, "Asymmetric solver matrix")
    worst = max(abs(lhs - rhs) for lhs, rhs in zip(residual, j))
    require(worst <= AMP_TOL and len(positive) == 4, "Solver residual or auxiliary source matrix differs")
    return diagonal, edges, positive, worst


def terminal_voltages(path, nodes, voltage, terminals):
    name_to_id = {node[3]: index for index, node in enumerate(nodes) if node[0] == "ITerm Node"}
    require(len(name_to_id) == len(terminals) == 98904 and set(name_to_id) == terminals,
            "Solver ITerm inventory differs from exact ODB")
    seen = set()
    with path.open() as stream:
        rows = csv.reader(stream)
        require(next(rows) == ["Instance", "Terminal", "Layer", "X location", "Y location", "Voltage"],
                "Wrong numerical rail report format")
        for instance, pin, layer, x, y, token in rows:
            name = f"{instance}/{pin}"
            index = name_to_id[name]
            require(name not in seen and nodes[index][1:3] == (layer, (dbu(x), dbu(y)))
                    and rounded(voltage[index], token, 2e-15), "Solver terminal voltage join differs")
            seen.add(name)
    require(seen == terminals, "Missing terminal voltage rows")
    return name_to_id


def physical_edges(out, rail, directory, nodes, ids, voltage, edges, diagonal):
    # Sign convention is conventional current from endpoint A to endpoint B.
    flow, incident_g = (array("d", (0 for _ in nodes)) for _ in range(2))
    count, maxima = Counter(), {}
    terminal_path = out / f"{rail}-terminal-edges.csv"
    with (directory / "psm_cond.txt").open() as cond, (directory.parent / f"{rail}.spice").open() as spice, \
            (directory.parent / f"{rail}-current.csv").open() as current, terminal_path.open("x") as terminal:
        resistors = (line.split() for line in spice if line.startswith("R"))
        current_rows = csv.reader(current)
        require(next(current_rows) == ["Node0 Layer", "Node0 X location", "Node0 Y location", "Node1 Layer",
                                      "Node1 X location", "Node1 Y location", "Current"], "Wrong EM CSV header")
        writer = csv.writer(terminal)
        writer.writerow(("a_node", "b_node", "a_solver_index", "b_solver_index", "conductance_s", "current_a_a_to_b"))
        for line in cond:
            ends, token = line.strip().rsplit(": ", 1)
            a, b = ends.split(" -> ", 1)
            ia, ib = ids[a], ids[b]
            conductance = float(token)
            _, sa, sb, resistance = next(resistors)
            require((sa, sb) == (spice_name(nodes[ia]), spice_name(nodes[ib])) and conductance > 0
                    and rounded(1 / conductance, resistance.removeprefix("R="), 1e-15)
                    and edges.pop(tuple(sorted((ia, ib)))) == -conductance, "Solver matrix/conductance/SPICE edge differs")
            amps = (voltage[ia] - voltage[ib]) * conductance
            flow[ia] += amps
            flow[ib] -= amps
            incident_g[ia] += conductance
            incident_g[ib] += conductance
            ka, kb = nodes[ia][0], nodes[ib][0]
            terminal_kinds = {ka, kb} - {"Node"}
            if terminal_kinds:
                require(len(terminal_kinds) == 1 and "Node" in {ka, kb}, "Unexpected terminal-to-terminal connection")
                kind, = terminal_kinds
                require(conductance == 1000, "Unexpected terminal connector resistance")
                writer.writerow((a, b, ia, ib, token, f"{amps:.15e}"))
                maximum = maxima.get(kind)
                if maximum is None or abs(amps) > abs(maximum["amps_a_to_b"]):
                    maxima[kind] = dict(a=a, b=b, amps_a_to_b=amps)
            else:
                kind = "grid"
                la, x0, y0, lb, x1, y1, magnitude = next(current_rows)
                require(nodes[ia][1:3] == (la, (dbu(x0), dbu(y0))) and nodes[ib][1:3] == (lb, (dbu(x1), dbu(y1)))
                        and rounded(abs(amps), magnitude, conductance * 2e-15), "Solver edge differs from native current CSV")
            count[kind] += 1
        require(next(resistors, None) is None and next(current_rows, None) is None, "Missing physical dump edges")
    require(set(count) == {"grid", "ITerm Node", "BPin Node"}, "Incomplete physical connection classes")
    require(all(g <= d or math.isclose(g, d, rel_tol=1e-13) for g, d in zip(incident_g, diagonal)),
            "Conductance diagonal below physical incident sum")
    return flow, incident_g, dict(edge_counts=dict(count), terminal_edge_peaks=maxima, terminal_edges_csv=bound(terminal_path))


def external_sources(spice, rail, nodes, voltage, j, edges, positive, flow, incident_g):
    grid_ids = {spice_name(node): index for index, node in enumerate(nodes) if node[0] == "Node"}
    sources, summer = [], []
    with spice.open() as stream:
        for line in stream:
            if line.startswith("V"):
                _, name, ground, kind, source_voltage = line.split()
                require(ground == "0" and kind == "DC" and float(source_voltage) == VOLTAGES[rail], "Wrong SPICE source")
                sources.append(grid_ids[name])
    details = []
    for (ideal, auxiliary), constraint in sorted(positive.items()):
        point = nodes[ideal][2]
        require(nodes[ideal] == nodes[auxiliary] == ("Source Node", "Metal4", point, None) and constraint == 1,
                "Wrong fixed-voltage source stamping")
        grid, = [index for index in sources if nodes[index] == ("Node", "Metal4", point, None)]
        require(edges.pop((grid, ideal)) == -1 and j[ideal] == 0 and abs(j[auxiliary] - VOLTAGES[rail]) < 5e-8
                and abs(j[auxiliary] - voltage[ideal]) < 2e-15, "Wrong 1 Ω external source stamping")
        amps = (voltage[ideal] - voltage[grid])
        require(abs(amps + voltage[auxiliary]) <= 3e-15, "External source branch differs from solver auxiliary current")
        flow[grid] -= amps
        incident_g[grid] += 1
        incident_g[ideal] += 1
        summer.append(amps)
        details.append(dict(point_dbu=list(point), grid_index=grid, fixed_source_index=ideal, auxiliary_index=auxiliary,
                            fixed_source_v=voltage[ideal], grid_v=voltage[grid], amps_source_to_grid=amps))
    require(not edges and sorted(sources) == sorted(row["grid_index"] for row in details) and len(details) == 4,
            "Unaccounted matrix edges or selected source nodes")
    return details, math.fsum(summer)


def terminal_loads(out, rail, spice, nodes, name_to_id, j, flow):
    sign = -1 if rail == "VPWR" else 1
    printed, label = {}, None
    with spice.open() as stream:
        for line in stream:
            if line.startswith("* Sink for "):
                require(label is None, "Missing SPICE sink source")
                label = line.strip().removeprefix("* Sink for ")
            elif line.startswith("I"):
                _, node, ground, kind, token = line.split()
                require(ground == "0" and kind == "DC" and label is not None and label not in printed
                        and node == spice_name(nodes[name_to_id[label]]) and float(token) > 0
                        and rounded(sign * j[name_to_id[label]], token), "Rounded SPICE load and exact solver injection differ")
                printed[label] = token
                label = None
    require(label is None and printed, "Missing or dangling printed sink")
    currents = {name: sign * j[index] for name, index in name_to_id.items()}
    require(min(currents.values()) >= 0, "Unexpected reversed instance load")
    unprinted = [amps for name, amps in currents.items() if name not in printed and amps > 0]
    bpins = [(node, index) for index, node in enumerate(nodes) if node[0] == "BPin Node"]
    require(all(j[index] == 0 for _, index in bpins), "Unexpected externally driven boundary terminal")
    path = out / f"{rail}-terminals.csv"
    with path.open("x") as stream:
        writer = csv.writer(stream)
        writer.writerow(("kind", "terminal", "layer", "x_dbu", "y_dbu", "solver_index", "j_a", "outgoing_grid_current_a"))
        for name, index in sorted(name_to_id.items()):
            _, layer, (x, y), _ = nodes[index]
            writer.writerow(("ITerm", name, layer, x, y, index, f"{j[index]:.15e}", f"{flow[index]:.15e}"))
        for (_, layer, (x, y), _), index in bpins:
            writer.writerow(("BPin", rail, layer, x, y, index, f"{j[index]:.15e}", f"{flow[index]:.15e}"))
    peak = max(currents, key=currents.__getitem__)
    return currents, dict(terminal_nodes_csv=bound(path), instance_terminals=len(name_to_id), boundary_pin_nodes=len(bpins),
                          nonzero_loads=sum(amps > 0 for amps in currents.values()), printed_spice_loads=len(printed),
                          unprinted_nonzero_loads=len(unprinted), max_unprinted_load_a=max(unprinted, default=0),
                          summed_unprinted_load_a=math.fsum(unprinted),
                          printed_spice_load_a=math.fsum(map(float, printed.values())),
                          modeled_load_a=math.fsum(currents.values()), peak_instance_load=dict(terminal=peak, amps=currents[peak]),
                          peak_boundary_pin_net_flow_a=max(abs(flow[index]) for _, index in bpins))


def read_rail(out, directory, rail, inventory):
    folder = directory / rail
    nodes, ids, coordinate_aliases = parse_nodes(folder / "psm_nodes.txt")
    voltage = vectors(folder / "psm_V.txt", "V", len(nodes))
    j = vectors(folder / "psm_J.txt", "J", len(nodes))
    diagonal, edges, positive, matrix_residual = matrix(folder / "psm_G.txt", nodes, voltage, j)
    terminals = {f"{name}/{pin}" for name, instance in inventory["instances"].items()
                 for pin, row in instance["terminals"].items() if row["net"] == rail}
    name_to_id = terminal_voltages(directory / f"{rail}-voltage.csv", nodes, voltage, terminals)
    flow, incident_g, edge_summary = physical_edges(out, rail, folder, nodes, ids, voltage, edges, diagonal)
    spice = directory / f"{rail}.spice"
    sources, current = external_sources(spice, rail, nodes, voltage, j, edges, positive, flow, incident_g)
    require(all(math.isclose(g, d, rel_tol=1e-13) for g, d in zip(incident_g, diagonal)), "Solver diagonal cannot be reconstructed")
    residual = max(abs(flow[index] - j[index]) for index, node in enumerate(nodes) if node[0] in REAL_NODES)
    require(residual <= AMP_TOL, "Reconstructed physical-node KCL exceeds tolerance")
    loads, load_summary = terminal_loads(out, rail, spice, nodes, name_to_id, j, flow)
    require(abs(current - (-1 if rail == "VGND" else 1) * load_summary["modeled_load_a"]) <= AMP_TOL,
            "External source currents do not balance modeled load")
    return loads, dict(solver_nodes=len(nodes), spice_iterm_coordinate_aliases=coordinate_aliases,
                       full_matrix_residual_a=matrix_residual, physical_kcl_residual_a=residual,
                       total_current_source_to_grid_a=current, external_series_resistance_ohm=1,
                       external_sources=sources, **load_summary, **edge_summary)


def verify(directory, out):
    require(directory.parent == out.parent == TRIAL / "power-dc" and not out.exists(), "Use a fresh local current readback")
    _, golden, inherited = golden_case()
    receipt_path = directory / "dump-receipt.json"
    receipt = read(receipt_path)
    require(receipt["status"] == "completed" and receipt["target_odb_sha256"] == TARGET["odb_sha256"]
            and receipt["target_gds_sha256"] == TARGET["gds_sha256"] and receipt["golden_readback"] == bound(GOLDEN / "readback.json"),
            "Wrong solver dump target")
    execution = read(receipt["execution"]["path"])
    require(execution["status"] == "completed" and execution["exit_code"] == 0
            and execution["container_termination"]["status"] == "absent", "Solver dump execution did not close")
    artifacts = [bound(receipt_path), bound(INVENTORY), receipt["request"], receipt["execution"], receipt["log"],
                 *receipt["golden_equal"].values(), *inherited]
    require(artifacts[1]["sha256"] == INVENTORY_SHA and set(receipt["solver_dumps"]) == set(VOLTAGES),
            "Wrong frozen inventory or rail set")
    for rail, dumps in receipt["solver_dumps"].items():
        require(set(dumps) == set(DUMP_NAMES) and all(Path(item["path"]) == directory / rail / name for name, item in dumps.items()),
                "Incomplete solver dump bindings")
        artifacts.extend(dumps.values())
    exact = {Path(item["path"]).name: item["sha256"] for item in golden["artifacts"]
             if Path(item["path"]).name not in {"container.log", "execution.json"}}
    require({name: item["sha256"] for name, item in receipt["golden_equal"].items()} == exact
            and all(Path(item["path"]) == directory / name for name, item in receipt["golden_equal"].items())
            and all(bound(item["path"]) == item for item in artifacts), "Retained solver evidence changed")
    out.mkdir(exist_ok=False)
    inventory = read(INVENTORY)
    rails, loads = {}, {}
    for rail in VOLTAGES:
        loads[rail], rails[rail] = read_rail(out, directory, rail, inventory)
    paired = {name.rsplit("/", 1)[0]: amps for name, amps in loads["VGND"].items()}
    require(all(math.isclose(amps, paired[name.rsplit("/", 1)[0]], rel_tol=1e-13, abs_tol=1e-17)
                for name, amps in loads["VPWR"].items()), "Supply and return instance loads differ")
    require(all(bound(item["path"]) == item for item in artifacts), "Solver evidence changed during readback")
    result = dict(schema=SCHEMA, status="diagnostic", target_odb_sha256=TARGET["odb_sha256"],
                  target_gds_sha256=TARGET["gds_sha256"], dump=bound(receipt_path), producer=bound(__file__), rails=rails,
                  paired_instance_loads=len(paired), kcl_tolerance_a=AMP_TOL,
                  precision="Dumps print 16 significant digits. Currents from voltage differences inherit subtraction and KCL limits.",
                  contact_limit_comparison="Open. The 1 mΩ terminal connection is a solver element without a physical conductor area.",
                  qualified_ir_drop=False, qualified_em=False, artifacts=artifacts)
    write(out / "readback.json", result)
    print(out / "readback.json")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("dump", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    verify(args.dump.resolve(strict=True), args.out.resolve())


if __name__ == "__main__":
    main()
