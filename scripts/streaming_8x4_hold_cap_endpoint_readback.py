"""Reconcile native timing-graph endpoints with the frozen physical graph."""

import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path

import streaming_8x4_hold_cap_timing_coverage as coverage
from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import TOP, read, require, sha
from streaming_8x4_hold_cap_physical import TARGET, setup
from streaming_tt_certificate import eval_boolean, parse_graph
from streaming_tt_simulation import libraries


def pin_support(cell, inputs, constants):
    fixed = {pin: constants[wire] for pin, wire in inputs.items() if wire in constants}
    varying = sorted(inputs.keys() - fixed.keys())
    outcomes = {
        bits: eval_boolean(cell.function, {**fixed, **dict(zip(varying, bits, strict=True))})
        for bits in product((False, True), repeat=len(varying))
    }
    supported = {
        pin for index, pin in enumerate(varying)
        if any(value != outcomes[bits[:index] + (not bits[index],) + bits[index + 1:]]
               for bits, value in outcomes.items())
    }
    return supported, outcomes[next(iter(outcomes))]


def classify(graph, inventory, endpoints):
    constants = {"0": False, "1": True}
    gates = {}
    for gate in graph.gates:
        cell = graph.library.cells[gate.cell]
        inputs = {pin: wire for pin, wire in gate.connections.items() if cell.directions[pin] == "input"}
        supported, fixed_value = pin_support(cell, inputs, constants)
        if not supported:
            constants[gate.output] = fixed_value
        name, = json.loads(gate.name)
        gates[name] = supported

    passive_pins = {
        f"{json.loads(name)[0]}/{pin}"
        for name, _, connections in graph.passive_loads for pin in connections
    }
    loaded_nets = {row["net"] for row in inventory["public_bterms"].values() if row["direction"] == "output"}
    loaded_nets.update(
        term["net"] for inst in inventory["instances"].values() for term in inst["terminals"].values()
        if term["direction"] == "INPUT"
    )
    classified = {}
    for endpoint in endpoints:
        instance, pin = endpoint.rsplit("/", 1)
        terminal = inventory["instances"][instance]["terminals"][pin]
        if endpoint in passive_pins:
            classified[endpoint] = "passive_load"
        elif terminal["direction"] == "OUTPUT" and terminal["net"] is None:
            classified[endpoint] = "open_output"
        elif terminal["direction"] == "OUTPUT" and terminal["net"] not in loaded_nets:
            classified[endpoint] = "sinkless_output_net"
        elif terminal["direction"] == "INPUT" and instance in gates and pin not in gates[instance]:
            classified[endpoint] = "masked_input" if gates[instance] else "input_on_constant_gate"
    require(classified.keys() == endpoints.keys(),
            f"Unexplained timing-graph endpoints: {sorted(endpoints.keys() - classified.keys())}")
    return classified


def reopen(context, coverage_path, expected_sha256):
    coverage_item = bound(coverage_path)
    require(coverage_item["sha256"] == expected_sha256, "Timing coverage receipt differs")
    receipt = read(coverage_path)
    rows, layout, _, expected = coverage.prepare(context)
    require(receipt["schema"] == coverage.SCHEMA and receipt["status"] == "diagnostic"
            and receipt["target_odb_sha256"] == TARGET["odb_sha256"]
            and receipt["target_gds_sha256"] == TARGET["gds_sha256"]
            and len(receipt["cases"]) == len(rows), "Timing coverage receipt refers to another candidate or matrix")
    endpoints = None
    for row, actual in zip(rows, receipt["cases"], strict=True):
        require(all(actual[key] == value for key, value in row.items()), "Coverage row differs from the retained case")
        log_path = coverage_path.parent / f"{row['model']}-{row['corner']}.log"
        require(bound(log_path) == actual["log"], "Raw timing coverage log differs")
        parsed = coverage.parse_coverage(log_path.read_text(), row, expected)
        require(parsed == actual["coverage"], "Timing coverage does not reproduce from the raw log")
        if endpoints is None:
            endpoints = parsed["native_search_other"]
        require(endpoints == parsed["native_search_other"], "Unexpected endpoint variation across timing cases")

    inventory_item = layout["inventory"]
    export_path = Path(inventory_item["path"]).with_name("receipt.json")
    export = read(export_path)
    graph_path = export_path.with_name("connectivity.json")
    graph_item = bound(graph_path)
    require(export["database_sha256"] == TARGET["odb_sha256"]
            and export["artifacts_sha256"] == {"inventory.json": inventory_item["sha256"],
                                              "connectivity.json": graph_item["sha256"]},
            "Timing inventory and graph identify different exports")
    document = read(graph_path)
    used = {cell["type"] for cell in document["modules"][TOP]["cells"].values()}
    corners = {
        row["corner"]: {"path": str(context["pdk"] / path.removeprefix("/work/pdk/")), "sha256": digest}
        for row in rows for path, digest in row["input_sha256"].items() if "/sg13cmos5l_stdcell/" in path
    }
    library, _ = libraries(corners, used)
    graph = parse_graph(document, TOP, library)
    classified = classify(graph, read(inventory_item["path"]), endpoints)
    return dict(status="reconciled", timing_coverage=coverage_item, graph=graph_item,
                inventory=inventory_item, liberty=corners, cases=len(rows),
                counts=dict(Counter(classified.values())), endpoints=classified)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--coverage", type=Path, required=True)
    parser.add_argument("--coverage-sha256", required=True)
    args = parser.parse_args()
    result = reopen(setup(args.history.resolve(strict=True)), args.coverage.resolve(strict=True), args.coverage_sha256)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
