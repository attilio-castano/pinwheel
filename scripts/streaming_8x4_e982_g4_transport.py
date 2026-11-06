"""Reopen f516 proof evidence and transport its Boolean model to exact b7e60."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

import streaming_tt_certificate as certificate
import streaming_tt_simulation as simulation


TOP = simulation.TOP
SCHEMA = "pinwheel.streaming-8x4-e982-g4-transport.v1"
OLD_ODB = "f516ffbca3cd86e5cd214c515ca0be457a91a517dbe715caa47336aec907eee0"
TARGET_ODB = "b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b"
TARGET_GDS = "041ff30708e46be33db330e2f1dcafab889824b689499e931ec9d180a11c1689"
ROUTE_READBACK = "4b23185cbef099e8eef84bfeac39c4ab63461aa5a77b52a3dc4fe516b0513f3b"
OLD_GATE4 = "21249d9175afbf0729e62f03b9fa4370bc248fe48929e10fe5b66286d9fc3558"
REFERENCE = "da19eccfaa31dca8836f40bd693b4f125759470959cb06a0ed9ee3df34a2d1a4"
SDC = "73ce99876d64525e1d62c896f1ce8734edce2b49737898072f1772461c03cbe1"
STATE_PINS = {"Q": "actual_q", "D": "actual_d", "CLK": "actual_clock", "RESET_B": "actual_reset_b"}
PASSIVE_MASTER = "sg13cmos5l_antennanp"
ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), f"Missing regular evidence file: {path}")
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def bind(pins, path, expected=None):
    path = Path(path).absolute()
    actual = sha(path)
    require(expected is None or actual == expected, f"Evidence SHA-256 differs: {path}")
    require(pins.setdefault(str(path), actual) == actual, f"Evidence changed between reads: {path}")
    return {"path": str(path), "sha256": actual}


def reopen(pins, item):
    return bind(pins, item["path"], item["sha256"])


def read_bound(pins, path, expected=None):
    item = bind(pins, path, expected)
    value = certificate.read_json(item["path"])
    reopen(pins, item)
    return value


def emit(path, value):
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write("\n")


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()).hexdigest()


def graph_signature(graph, inventory):
    """Compare every driven node by named identity rather than transient ODB IDs."""
    identities = {item["wire"]: ("net", name, item["signal_type"]) for name, item in inventory["nets"].items()}
    require(len(identities) == len(inventory["nets"]), "OpenDB wire IDs alias distinct named nets")
    for name, wire in inventory["unconnected_signal_outputs"].items():
        require(wire not in identities, "Unconnected output aliases a named wire")
        identities[wire] = ("open-output", name)

    def wire(bit):
        return ("constant", bit) if isinstance(bit, str) else identities[bit]

    def ports(values):
        return {name: tuple(map(wire, bits)) for name, bits in values.items()}

    return {
        "inputs": ports(graph.inputs), "outputs": ports(graph.outputs), "clock": wire(graph.clock),
        "gates": {row.name: (row.cell, wire(row.output), {pin: wire(bit) for pin, bit in row.connections.items()})
                  for row in graph.gates},
        "flipflops": {row.name: (row.cell, wire(row.d), wire(row.q), wire(row.clock), wire(row.reset_b))
                      for row in graph.flipflops},
    }


def state_transport(old_map, old_sampler, old_document, new_document, old_graph, new_graph):
    old = old_document["modules"][TOP]["cells"]
    new = new_document["modules"][TOP]["cells"]
    rows = old_map["rows"]
    require(len(rows) == len({row["semantic"] for row in rows}) == len({row["actual_ff"] for row in rows}) == 6039,
            "Historical semantic state map is not a full bijection")
    old_flops = {row.name for row in old_graph.flipflops}
    new_flops = {row.name for row in new_graph.flipflops}
    require({row["actual_ff"] for row in rows} == old_flops == new_flops,
            "State map does not enumerate both complete parsed FF inventories")
    transported = []
    by_semantic = {}
    for row in rows:
        path = json.loads(row["actual_ff"])
        require(isinstance(path, list) and len(path) == 1 and isinstance(path[0], str)
                and json.dumps(path, separators=(",", ":")) == row["actual_ff"], "Malformed flat FF instance identity")
        name = path[0]
        require(old[name]["type"] == row["actual_cell"] == new[name]["type"], f"State master differs: {name}")
        current = dict(row)
        for pin, key in STATE_PINS.items():
            require(old[name]["connections"][pin] == [row[key]], f"Old state pin readback differs: {name}/{pin}")
            current[key], = new[name]["connections"][pin]
        transported.append(current)
        by_semantic[row["semantic"]] = (row, current, name)

    sampler = {}
    binding_pins = {"q": "actual_q", "d": "actual_d", "clock": "actual_clock", "reset_b": "actual_reset_b"}
    require(set(old_sampler["bindings"]) == {"stage1", "stage2"}, "Incomplete historical sampler")
    for stage, binding in old_sampler["bindings"].items():
        old_row, new_row, name = by_semantic[f"core-d2:r_{stage}:0"]
        require(binding["cell"] == old_row["actual_ff"] and binding["component"] == "core-d2"
                and binding["register"] == "r_" + stage and binding["index"] == 0
                and all(binding[field] == old_row[key] for field, key in binding_pins.items()),
                "Historical sampler witness disagrees with state pairing")
        sampler[stage] = dict(binding, cell=name, **{field: new_row[key] for field, key in binding_pins.items()})
    return transported, sampler


def read_target(pins, route, views, view_sha, export_sha, exporter_sha, reference):
    native = route / "native"
    physical = read_bound(pins, route / "independent-readback.json", ROUTE_READBACK)
    require(physical["physical_checks_pass"] is True and physical["postfill_odb_sha256"] == TARGET_ODB
            and physical["postfill_gds_sha256"] == TARGET_GDS, "Candidate did not bind the verified physical replay")
    fill = native / "flow/09-openroad-fillinsertion"
    database = bind(pins, fill / f"{TOP}.odb", TARGET_ODB)
    gds = bind(pins, native / "design.gds", TARGET_GDS)
    sdc = bind(pins, fill / f"{TOP}.sdc", SDC)

    view_path = views / "signoff-views/report.json"
    view = read_bound(pins, view_path, view_sha)
    require(view["schema"] == "pinwheel.streaming-tt-signoff-export.v1" and view["completed"] is True
            and view["inputs_unchanged"] is True and view["inherited_netlist"] is False
            and view["actual_database_sha256"] == TARGET_ODB and view["top"] == TOP,
            "Candidate view export is not fresh from the exact post-fill ODB")
    view_artifacts = {name: bind(pins, view_path.parent / name, view["artifacts_sha256"][name])
                      for name in ("implemented.v", "implemented.power.v", "implemented.lef", "implemented.cdl")}
    export_dir = views / "actual-signal"
    export_receipt = bind(pins, export_dir / "receipt.json", export_sha)
    document, inventory, _ = simulation.verify_export(export_dir, receipt_sha256=export_sha,
        database=database["path"], reference=reference, exporter_sha256=exporter_sha)
    artifacts = certificate.read_json(export_receipt["path"])["artifacts_sha256"]
    for name, expected in artifacts.items():
        bind(pins, export_dir / name, expected)
    return document, inventory, {
        "database": database, "gds": gds, "sdc": sdc, "view_receipt": bind(pins, view_path, view_sha),
        "view_artifacts": view_artifacts, "connectivity_receipt": export_receipt,
        "export_dir": str(export_dir), "export_artifact_sha256": artifacts,
    }


def run(*, old_gate_path, route, views, view_sha, export_sha, output):
    require(not output.exists(), "Preserve earlier target transport outputs")
    pins = {}
    gate = read_bound(pins, old_gate_path, OLD_GATE4)
    correspondence = gate["final_correspondence"]
    require(gate["canonical_gate4_passed"] is True and correspondence["complete"] is True
            and correspondence["whole_axiom_audit_passed"] is True and correspondence["status"] == "pass"
            and correspondence["target_odb_sha256"] == gate["same_target"]["sha256"] == OLD_ODB,
            "Historical f516 correspondence is unavailable")
    for item in correspondence["evidence"]:
        reopen(pins, item)
    for key in ("same_target", "positive", "private", "semantic_state_map", "sampler_binding", "selected_archive"):
        reopen(pins, gate[key])
    authority = read_bound(pins, gate["authority"]["path"], gate["authority"]["sha256"])
    config_pin = reopen(pins, authority["worker_config"])
    config = certificate.read_json(config_pin["path"])
    exporter_sha = config["source_sha256"]["scripts/streaming_tt_export_odb.py"]
    bind(pins, ROOT / "scripts/streaming_tt_export_odb.py", exporter_sha)
    old_export = config["export"]
    bind(pins, old_export["database"], OLD_ODB)
    bind(pins, old_export["reference"], REFERENCE)
    old_receipt_path = Path(old_export["directory"]) / "receipt.json"
    old_receipt = read_bound(pins, old_receipt_path, old_export["receipt_sha256"])
    for name, expected in old_receipt["artifacts_sha256"].items():
        bind(pins, old_receipt_path.parent / name, expected)
    old_document, old_inventory, _ = simulation.verify_export(**old_export, exporter_sha256=exporter_sha)
    new_document, new_inventory, target = read_target(
        pins, route, views, view_sha, export_sha, exporter_sha, old_export["reference"])
    for item in config["corners"].values():
        reopen(pins, item)
    old_masters = {cell["type"] for cell in old_document["modules"][TOP]["cells"].values()}
    new_masters = {cell["type"] for cell in new_document["modules"][TOP]["cells"].values()}
    require(old_masters == new_masters, "Signal cell master set differs between targets")
    old_library, _ = simulation.libraries(config["corners"], old_masters)
    new_library = old_library
    require(old_library == new_library, "Pinned digital cell library differs between targets")
    old_graph = certificate.parse_graph(old_document, TOP, old_library)
    new_graph = certificate.parse_graph(new_document, TOP, new_library)
    old_passives = Counter(kind for _, kind, _ in old_graph.passive_loads)
    new_passives = Counter(kind for _, kind, _ in new_graph.passive_loads)
    require(old_passives == {PASSIVE_MASTER: 140} and new_passives == {PASSIVE_MASTER: 160},
            "Unexpected passive load population")
    old_signature = graph_signature(old_graph, old_inventory)
    new_signature = graph_signature(new_graph, new_inventory)
    for domain in old_signature:
        require(old_signature[domain] == new_signature[domain], f"Named functional graph differs in {domain}")
    clocks = certificate.clock_cones(old_graph)
    require(clocks == certificate.clock_cones(new_graph), "Actual clock and reset cone semantics differ")
    old_model = certificate.data_model(old_graph)
    require(old_model == certificate.data_model(new_graph), "Canonical complete state/next-state/output model differs")
    old_map = certificate.read_json(gate["semantic_state_map"]["path"])
    old_sampler = certificate.read_json(gate["sampler_binding"]["path"])
    require(old_map["database_sha256"] == OLD_ODB and old_map["connectivity_sha256"] == old_sampler["connectivity_sha256"]
            == old_receipt["artifacts_sha256"]["connectivity.json"], "Historical state and sampler authority targets differ")
    for item in old_sampler["semantic_basis"].values():
        reopen(pins, item)
    rows, sampler = state_transport(old_map, old_sampler, old_document, new_document, old_graph, new_graph)
    output_bits = sum(map(len, new_graph.outputs.values()))
    require(output_bits == 24 and len(clocks) == 6039, "Incomplete public/state scope")

    for name, module in tuple(sys.modules.items()):
        if not name.startswith("streaming_") or name == "streaming_8x4_e982_g4_transport":
            continue
        path = Path(module.__file__).resolve()
        relative = str(path.relative_to(ROOT))
        bind(pins, path, config["source_sha256"][relative])
    bind(pins, Path(__file__).resolve())
    for path, expected in tuple(pins.items()):
        bind(pins, path, expected)

    output.mkdir(parents=True)
    connectivity = target["export_artifact_sha256"]["connectivity.json"]
    state_path = output / "semantic-state-map.json"
    emit(state_path, dict(old_map, database_sha256=TARGET_ODB, connectivity_sha256=connectivity, rows=rows,
                          boundary="All state endpoints transported by exact functional graph equality."))
    sampler_path = output / "sampler-binding.json"
    basis = dict(old_sampler["semantic_basis"], **{
        "accepted-f516-gate4": bind(pins, old_gate_path, OLD_GATE4),
        "candidate-connectivity": target["connectivity_receipt"],
        "actual-state-pairing": bind(pins, state_path),
    })
    emit(sampler_path, dict(old_sampler, connectivity_sha256=connectivity, bindings=sampler, semantic_basis=basis))
    result = {
        "schema": SCHEMA, "passed": True, "target_odb_sha256": TARGET_ODB, "target_gds_sha256": TARGET_GDS,
        "netlist_sha256": target["view_artifacts"]["implemented.v"]["sha256"],
        "powered_netlist_sha256": target["view_artifacts"]["implemented.power.v"]["sha256"],
        "target": target, "historical_gate4": bind(pins, old_gate_path, OLD_GATE4), "historical_worker_config": config_pin,
        "named_functional_graph_equal": True, "state_transition_and_output_model_equal": True,
        "clock_and_reset_cones_equal": True, "functional_correspondence_transported": True,
        "active_gates": len(new_graph.gates), "state_bits": len(rows), "public_output_bits": output_bits,
        "historical_passive_loads": dict(old_passives), "candidate_passive_loads": dict(new_passives),
        "historical_power_only_instances": len(old_inventory["physical_only_instances"]),
        "candidate_power_only_instances": len(new_inventory["physical_only_instances"]),
        "named_graph_sha256": fingerprint(new_signature), "state_and_outputs_sha256": fingerprint(old_model),
        "semantic_state_map": bind(pins, state_path), "sampler_binding": bind(pins, sampler_path),
        "lean_recompiled": False, "fresh_public_wire_passed": False, "full_tapeout_ready": False,
        "boundary": "Transport of the accepted f516 Boolean theorem using independently rederived graph, state, "
                    "clock/reset and output equality. The native export and this comparator are trusted. "
                    "Passive diode and PG-only cell changes remain electrical and physical obligations.",
        "verified_file_sha256": dict(sorted(pins.items())),
    }
    emit(output / "transport.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("old-gate", "route", "views", "output"):
        parser.add_argument("--" + name, type=lambda value: Path(value).absolute(), required=True)
    for name in ("view-sha", "export-sha"):
        parser.add_argument("--" + name, required=True)
    args = parser.parse_args()
    try:
        run(old_gate_path=args.old_gate, route=args.route, views=args.views, view_sha=args.view_sha,
            export_sha=args.export_sha, output=args.output)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(1, f"Transport rejected: {exc}\n")
    print(args.output / "transport.json")


if __name__ == "__main__":
    main()
