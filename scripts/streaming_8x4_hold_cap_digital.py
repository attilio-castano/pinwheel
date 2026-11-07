"""Transport and replay zero-delay correspondence on the exact hold/cap candidate.

Only a comparison copy is normalized. Fresh wire replay retains every actual
cell, including all five stronger buffers and the inserted delay cell.
"""

import argparse
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import time

import process_group
import streaming_8x4_e982_eco_digital as fanout
import streaming_8x4_e982_g4_wire as canonical_wire
from streaming_8x4_e982_g4_transport import (
    ROOT, TOP, REFERENCE, bind, emit, fingerprint, graph_signature, read_bound,
    reopen, require, sha, state_transport,
)
from streaming_8x4_e982_g4_wire import verify_pins
from streaming_8x4_hold_cap_physical import EVIDENCE, TARGET, TRIAL
from streaming_tt_certificate import clock_cones, data_model, eval_boolean, parse_graph
from streaming_tt_simulation import libraries, verify_export


SCHEMA = "pinwheel.streaming-8x4-hold-cap-digital.v1"
WIRE_SCHEMA = "pinwheel.streaming-8x4-hold-cap-public-wire.v1"
BASE_PATH = ROOT / "build/e982-fanout-20261104/digital-02/transport.json"
BASE_SHA = "7b6aaef9a4970e9d3d64a56f7bebce04f30be8e55b407b4367b4ce99578276e1"
PHYSICAL_SHA = "70137eccd434c27864923fa3a9b3114e6fb363008b185822ad9a14e64d05bd72"
EXPORT_SHA = "a00709c7fba629055b6a00886b393d329d6fc4fd49e3e7d0474f1f0142c61da4"
DRIVERS = frozenset(("fanout2219", "fanout1798", "fanout2439", "fanout875", "fanout2425"))
OLD_BUFFER, NEW_BUFFER = "sg13cmos5l_buf_1", "sg13cmos5l_buf_2"
DELAY, DELAY_MASTER = "holdcap_delay", "sg13cmos5l_dlygate4sd2_1"
SOURCE, BRANCH, SINK = "engine.frontend._1956_.Y[1]", "holdcap_delayed_data", "engine.frontend._0230_"
PHYSICAL_MASTERS = frozenset("sg13cmos5l_" + name for name in ("decap_4", "decap_8", "fill_1", "fill_2"))


def bind_software(pins, config):
    """Seal reused host helpers; enforce archive pins for canonical imports."""
    archived_root = Path(config["root"]).resolve()
    for name, module in tuple(sys.modules.items()):
        if not name.startswith("streaming_") or not getattr(module, "__file__", None):
            continue
        path = Path(module.__file__).resolve()
        if path.is_relative_to(ROOT):
            relative = str(path.relative_to(ROOT))
            expected = config["source_sha256"].get(relative)
            require(expected is not None or relative.startswith("scripts/streaming_8x4_"),
                    "Unpinned canonical host helper: " + relative)
        else:
            require(path.is_relative_to(archived_root), "Helper outside selected source roots: " + str(path))
            relative = str(path.relative_to(archived_root))
            require(relative in config["source_sha256"], "Unpinned archived helper: " + relative)
            expected = config["source_sha256"][relative]
        bind(pins, path, expected)
    bind(pins, Path(__file__).resolve())
    bind(pins, Path(process_group.__file__).resolve(), config["source_sha256"]["scripts/process_group.py"])


def source_identity():
    """Record checkout ancestry; byte bindings also cover this new adapter."""
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    relative = str(Path(__file__).resolve().relative_to(ROOT))
    tracked = subprocess.run(["git", "cat-file", "-e", commit + ":" + relative], cwd=ROOT,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    committed = False
    if tracked:
        committed = subprocess.check_output(["git", "show", commit + ":" + relative], cwd=ROOT) == Path(__file__).read_bytes()
    return dict(checkout_commit=commit, adapter_bytes_in_commit=committed, adapter=relative,
                adapter_sha256=sha(Path(__file__).resolve()))


def identity_models(library):
    for master in (OLD_BUFFER, NEW_BUFFER, DELAY_MASTER):
        model = library.cells[master]
        require(not model.sequential and model.output == "X"
                and model.directions == {"A": "input", "X": "output"}
                and [eval_boolean(model.function, {"A": bit}) for bit in (False, True)] == [False, True],
                "Nonidentity or sequential hold/cap cell: " + master)


def normalize(document, baseline, actual, membership, library):
    """Validate the complete inventory delta before undoing exactly six edits."""
    identity_models(library)
    old, new = baseline["instances"], actual["instances"]
    added, removed = new.keys() - old.keys(), old.keys() - new.keys()
    require(len(old) == 98900 and len(new) == 98904
            and len(removed) == 9 and len(added) == 13
            and removed == set(membership["removed_instances"])
            and added == set(membership["added_instances"]), "Unexpected hold/cap instance membership")
    require(baseline["public_bterms"] == actual["public_bterms"]
            and baseline["power_bterms"] == actual["power_bterms"], "Public or power boundary changed")
    require(actual["nets"].keys() == baseline["nets"].keys() | {BRANCH}
            and BRANCH not in baseline["nets"]
            and all(actual["nets"][name]["signal_type"] == net["signal_type"]
                    for name, net in baseline["nets"].items())
            and actual["nets"][SOURCE]["signal_type"] == actual["nets"][BRANCH]["signal_type"] == "SIGNAL",
            "Unexpected named net or net type")
    for name in removed:
        require(old[name]["master"] in PHYSICAL_MASTERS
                and name in baseline["physical_only_instances"] and not fanout.signals(old[name]),
                "Removed cell has signal behavior: " + name)
    for name in added - {DELAY}:
        expected = "sg13cmos5l_decap_4" if name.startswith("holdcap_fill_") else "sg13cmos5l_fill_1"
        require(name.startswith(("holdcap_fill_", "holdcap_tail_"))
                and new[name]["master"] == expected and name in actual["physical_only_instances"]
                and not fanout.signals(new[name]), "Added backfill has signal behavior: " + name)
    require(DELAY in added and new[DELAY]["master"] == DELAY_MASTER
            and fanout.signals(new[DELAY]) == {"A": SOURCE, "X": BRANCH}, "Wrong inserted delay")
    for name in old.keys() & new.keys():
        before, after = old[name], new[name]
        require(before["master_type"] == after["master_type"]
                and before["terminals"].keys() == after["terminals"].keys(), "Changed instance/pin type: " + name)
        expected_master = NEW_BUFFER if name in DRIVERS else before["master"]
        require(after["master"] == expected_master
                and (name not in DRIVERS or before["master"] == OLD_BUFFER), "Unplanned master change: " + name)
        for pin, terminal in before["terminals"].items():
            expected = dict(terminal, net=BRANCH) if (name, pin) == (SINK, "D") else terminal
            require(after["terminals"][pin] == expected, "Unplanned terminal change: " + name + "/" + pin)
    require(DRIVERS <= old.keys() & new.keys()
            and old[SINK]["terminals"]["D"] == dict(direction="INPUT", net=SOURCE, signal_type="SIGNAL"),
            "Wrong original hold leaf or buffer scope")
    for name, instance in new.items():
        rails = {pin: (term["signal_type"], term["direction"], term["net"])
                 for pin, term in instance["terminals"].items() if term["signal_type"] in {"POWER", "GROUND"}}
        require(rails == {"VDD": ("POWER", "INOUT", "VPWR"), "VSS": ("GROUND", "INOUT", "VGND")},
                "Wrong supply pin binding: " + name)

    normalized = deepcopy(document)
    cells = normalized["modules"][TOP]["cells"]
    require(len(cells) == 42210 and set(cells) == set(new) - set(actual["physical_only_instances"]),
            "Incomplete actual functional inventory")
    rules = []
    for name in sorted(DRIVERS):
        require(cells[name]["type"] == NEW_BUFFER and fanout.signals(new[name])
                == fanout.signals(old[name]), "Buffer connectivity changed: " + name)
        cells[name]["type"] = OLD_BUFFER
        rules.append(dict(kind="same_function_master", instance=name, actual_master=NEW_BUFFER,
                          comparison_master=OLD_BUFFER, signal_nets=fanout.signals(new[name])))
    source, branch = actual["nets"][SOURCE]["wire"], actual["nets"][BRANCH]["wire"]
    require(cells[DELAY]["connections"] == {"A": [source], "X": [branch]}
            and cells[SINK]["connections"]["D"] == [branch], "Wrong delay input/output/sink")
    users = {(name, pin) for name, cell in cells.items() for pin, bits in cell["connections"].items() if branch in bits}
    require(users == {(DELAY, "X"), (SINK, "D")}, "Unexpected delayed-net user")
    cells[SINK]["connections"]["D"] = [source]
    del cells[DELAY]
    rules.append(dict(kind="positive_identity_contraction", instance=DELAY, actual_master=DELAY_MASTER,
                      input_net=SOURCE, output_net=BRANCH, sink=[SINK, "D"]))
    return normalized, rules


def read_target(pins, reference, exporter_sha):
    views = TRIAL / "views"
    database = bind(pins, TARGET["odb"], TARGET["odb_sha256"])
    gds = bind(pins, TARGET["gds"], TARGET["gds_sha256"])
    physical = read_bound(pins, TRIAL / "physical-decision.json", PHYSICAL_SHA)
    require(physical["all_four_checks_passed"] is True
            and physical["target_odb_sha256"] == TARGET["odb_sha256"] and physical["gds_sha256"] == TARGET["gds_sha256"],
            "Physical decision identifies another candidate")
    for section in ("main_drc", "enclosure", "lvs"):
        for item in physical[section]["artifacts"]:
            bind(pins, ROOT / item["path"], item["sha256"])
    membership = read_bound(pins, TRIAL / "connectivity-readback.json", EVIDENCE["connectivity-readback.json"])
    require(membership["status"] == "pass" and membership["source_odb_sha256"] == fanout.ECO_ODB
            and membership["target_odb_sha256"] == TARGET["odb_sha256"]
            and membership["all_regular_net_terminals_verified"] is True, "Wrong connectivity scope")
    view = read_bound(pins, views / "rehearsal-view-readback.json", EVIDENCE["views/rehearsal-view-readback.json"])
    require(view["status"] == "pass" and view["target_odb_sha256"] == TARGET["odb_sha256"]
            and view["gds_sha256"] == TARGET["gds_sha256"], "Wrong canonical target views")
    for item in view["artifacts"]:
        bind(pins, ROOT / item["path"], item["sha256"])
    result = read_bound(pins, views / "final-views-native.json")
    signoff = read_bound(pins, views / "signoff-views/report.json", result["canonical_signoff_report_sha256"])
    native = read_bound(pins, views / "execution.json")
    require(result["completed"] is True and result["source_odb_sha256"] == TARGET["odb_sha256"]
            and result["source_odb_unchanged"] is True and signoff["actual_database_sha256"] == TARGET["odb_sha256"]
            and signoff["completed"] is True and signoff["inputs_unchanged"] is True
            and signoff["inherited_netlist"] is False and signoff["top"] == TOP
            and native["status"] == "completed" and native["exit_code"] == 0
            and native["container_termination"]["status"] == "absent"
            and f"type=bind,source={database['path']},target=/work/target.odb,readonly" in native["argv"],
            "Native canonical views did not close on exact read-only ODB")
    netlists = {name: bind(pins, views / "signoff-views" / name, signoff["artifacts_sha256"][name])
                for name in ("implemented.v", "implemented.power.v")}
    require(netlists["implemented.v"]["sha256"] == view["view_sha256"]["verilog"]
            and netlists["implemented.power.v"]["sha256"] == view["view_sha256"]["powered_verilog"]
            and result["canonical_boolean_report_sha256"] == EXPORT_SHA, "Canonical netlist/export hashes differ")
    directory = views / "actual-signal"
    receipt = read_bound(pins, directory / "receipt.json", EXPORT_SHA)
    document, inventory, _ = verify_export(directory, receipt_sha256=EXPORT_SHA, database=database["path"],
                                          reference=reference, exporter_sha256=exporter_sha)
    for name, digest in receipt["artifacts_sha256"].items():
        bind(pins, directory / name, digest)
    target = dict(database=database, gds=gds, export_dir=str(directory),
                  connectivity_receipt=bind(pins, directory / "receipt.json", EXPORT_SHA),
                  export_artifact_sha256=receipt["artifacts_sha256"], view_artifacts=netlists)
    return document, inventory, target, membership


def run_transport(base_path, output):
    require(not output.exists(), "Preserve earlier hold/cap digital evidence")
    pins = {}
    base = read_bound(pins, base_path, BASE_SHA)
    require(base["schema"] == fanout.SCHEMA and base["passed"] is True
            and base["functional_correspondence_transported"] is True
            and base["target_odb_sha256"] == fanout.ECO_ODB and base["target_gds_sha256"] == fanout.ECO_GDS
            and base["base_transport"]["sha256"] == fanout.BASE_TRANSPORT, "Missing sealed fanout correspondence")
    for path, digest in base["verified_file_sha256"].items():
        bind(pins, path, digest)
    reopen(pins, base["base_transport"])
    config_item = reopen(pins, base["historical_worker_config"])
    config = read_bound(pins, config_item["path"], config_item["sha256"])
    bind_software(pins, config)
    reference = bind(pins, config["export"]["reference"], REFERENCE)["path"]
    exporter_sha = config["source_sha256"]["scripts/streaming_tt_export_odb.py"]
    baseline = base["target"]
    old_document, old_inventory, _ = verify_export(baseline["export_dir"],
        receipt_sha256=baseline["connectivity_receipt"]["sha256"], database=baseline["database"]["path"],
        reference=reference, exporter_sha256=exporter_sha)
    document, inventory, target, membership = read_target(pins, reference, exporter_sha)
    old_used = {cell["type"] for cell in old_document["modules"][TOP]["cells"].values()}
    new_used = {cell["type"] for cell in document["modules"][TOP]["cells"].values()}
    require(new_used == old_used | {NEW_BUFFER, DELAY_MASTER} and not {NEW_BUFFER, DELAY_MASTER} & old_used,
            "Unexpected actual signal-cell master set")
    for item in config["corners"].values():
        reopen(pins, item)
    library, library_report = libraries(config["corners"], old_used | new_used)
    normalized, rules = normalize(document, old_inventory, inventory, membership, library)
    old_graph = parse_graph(old_document, TOP, library)
    graph = parse_graph(document, TOP, library)
    normalized_graph = parse_graph(normalized, TOP, library)
    signature = graph_signature(old_graph, old_inventory)
    require(signature == graph_signature(normalized_graph, inventory), "Named gate/state/clock/port graph differs")
    model = data_model(old_graph)
    require(model == data_model(normalized_graph), "Complete next-state/output model differs")
    cones = clock_cones(old_graph)
    require(cones == clock_cones(graph) == clock_cones(normalized_graph) and len(cones) == 6039
            and len(old_graph.gates) == len(normalized_graph.gates) == 36010 and len(graph.gates) == 36011
            and len(graph.flipflops) == 6039 and sum(map(len, graph.outputs.values())) == 24
            and all(Counter(kind for _, kind, _ in g.passive_loads) == {"sg13cmos5l_antennanp": 160}
                    for g in (old_graph, graph, normalized_graph)), "Clock/state/output/passive coverage differs")
    states = read_bound(pins, base["semantic_state_map"]["path"], base["semantic_state_map"]["sha256"])
    sampler = read_bound(pins, base["sampler_binding"]["path"], base["sampler_binding"]["sha256"])
    require(states["database_sha256"] == fanout.ECO_ODB and states["connectivity_sha256"]
            == sampler["connectivity_sha256"] == baseline["export_artifact_sha256"]["connectivity.json"],
            "Accepted state/sampler bindings identify another export")
    for item in sampler["semantic_basis"].values():
        reopen(pins, item)
    sampler["bindings"] = {stage: dict(binding, cell=json.dumps([binding["cell"]], separators=(",", ":")))
                           for stage, binding in sampler["bindings"].items()}
    state_rows, sampler_rows = state_transport(states, sampler, old_document, document, old_graph, graph)
    verify_pins(pins)
    output.mkdir(parents=True)
    connectivity = target["export_artifact_sha256"]["connectivity.json"]
    state_path, sampler_path = output / "semantic-state-map.json", output / "sampler-binding.json"
    emit(state_path, dict(states, database_sha256=TARGET["odb_sha256"], connectivity_sha256=connectivity, rows=state_rows,
                         boundary="Actual hold/cap state pins after five identity master substitutions and one delay contraction."))
    basis = dict(sampler["semantic_basis"], **{"accepted-fanout-transport": bind(pins, base_path, BASE_SHA),
        "candidate-connectivity": target["connectivity_receipt"], "actual-state-pairing": bind(pins, state_path)})
    emit(sampler_path, dict(sampler, bindings=sampler_rows, connectivity_sha256=connectivity, semantic_basis=basis))
    result = dict(schema=SCHEMA, passed=True, target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
        target=target, netlist_sha256=target["view_artifacts"]["implemented.v"]["sha256"],
        powered_netlist_sha256=target["view_artifacts"]["implemented.power.v"]["sha256"],
        base_transport=bind(pins, base_path, BASE_SHA), historical_worker_config=config_item,
        source_identity=source_identity(),
        comparison_basis="Exact raw fanout e40e4 graph; historical fanout receipt hashes describe its contracted b7e60 basis.",
        baseline_raw_named_graph_sha256=fingerprint(signature), baseline_raw_state_and_outputs_sha256=fingerprint(model),
        actual_named_graph_sha256=fingerprint(graph_signature(graph, inventory)), normalized_named_graph_equal=True,
        state_transition_and_output_model_equal=True, clock_and_reset_cones_equal=True,
        baseline_active_gates=36010, actual_active_gates=36011, actual_functional_instances=42210,
        state_bits=len(state_rows), public_output_bits=24, passive_diodes=160,
        physical_only_instances=len(inventory["physical_only_instances"]), identity_transformations=rules,
        added_instances=membership["added_instances"], removed_instances=membership["removed_instances"],
        digital_library=library_report, functional_correspondence_transported=True,
        semantic_state_map=bind(pins, state_path), sampler_binding=bind(pins, sampler_path),
        physical_decision=bind(pins, TRIAL / "physical-decision.json", PHYSICAL_SHA),
        lean_recompiled=False, fresh_public_wire_passed=False, full_tapeout_ready=False,
        boundary="Transported zero-delay Boolean correspondence. Native export/comparator and pinned Liberty digital functions "
                 "remain trusted; delay timing, parasitics, power and shuttle acceptance remain separate.",
        verified_file_sha256=dict(sorted(pins.items())))
    verify_pins(pins)
    emit(output / "transport.json", result)
    return result


def validate_worker(report, worker, config, request, target, pins):
    require(report["schema"] == "pinwheel.streaming-tt-public-wire.v1" and report["passed"] is True
            and report["stage"] == "closed" and report["qualified"] is False and report["physical_acceptance_claim"] is False
            and report["export"]["database_sha256"] == TARGET["odb_sha256"]
            and report["export"]["artifacts_sha256"] == target["export_artifact_sha256"]
            and report["configuration"] == request and report["physical_stage"] == config["physical_stage"]
            and report["inputs_unchanged"] is True and report["generated_inputs_unchanged"] is True
            and report["all_actual_instances_retained"] is True and report["clock_contraction"] is False
            and report["actual_functional_instances"] == 42210 and report["physical_ff_bits"] == 6039
            and report["positive_cases"] == 35 and report["actual_sampler_mutants"] == 1
            and report["native_processes"] == 14, "Full hold/cap wire corpus or actual-cell retention differs")
    source = Path(config["root"])
    worker_reader, owner_reader = canonical_wire.canonical_validators(source, config["source_sha256"])
    traces = worker_reader.validate_native(report, worker, config["tools"])
    journal = owner_reader.native_journal(worker / "native.jsonl", report["native_runs"])
    artifacts = {str(path.relative_to(worker)): sha(path) for path in worker.rglob("*")
                 if path.is_file() and path != worker / "report.json"}
    require(traces == report["traces"] and journal == report["native_journal"]["sha256"]
            and artifacts == report["artifact_sha256"], "Independently reopened wire artifacts differ")
    for path, digest in report["input_sha256_before"].items():
        bind(pins, path, digest)
    bind_software(pins, config)
    verify_pins(pins)
    return traces, artifacts


def run_wire(proof_path, proof_sha, output, timeout):
    require(not output.exists() and 1 <= timeout <= 1800, "Use a fresh bounded hold/cap wire output")
    pins = {}
    proof = read_bound(pins, proof_path, proof_sha)
    require(proof["schema"] == SCHEMA and proof["passed"] is True
            and proof["functional_correspondence_transported"] is True
            and proof["target_odb_sha256"] == TARGET["odb_sha256"] and proof["target_gds_sha256"] == TARGET["gds_sha256"],
            "Missing exact hold/cap digital transport")
    for path, digest in proof["verified_file_sha256"].items():
        bind(pins, path, digest)
    config_item = proof["historical_worker_config"]
    config = read_bound(pins, config_item["path"], config_item["sha256"])
    bind_software(pins, config)
    target = proof["target"]
    config = dict(config, physical_stage="actual-dc654986-hold-cap-canonical-export", sampler_binding=proof["sampler_binding"],
        export=dict(config["export"], directory=target["export_dir"], database=target["database"]["path"],
                    receipt_sha256=target["connectivity_receipt"]["sha256"]))
    source = Path(config["root"])
    entry = bind(pins, source / "scripts/check-streaming-tt-wire.py", config["source_sha256"]["scripts/check-streaming-tt-wire.py"])
    verify_pins(pins)
    output.mkdir(parents=True)
    request_path = output / "request.json"
    emit(request_path, config)
    request = bind(pins, request_path)
    worker = output / "worker"
    argv = [config["tools"]["python"], "-B", entry["path"], "--worker-config", request["path"],
            "--worker-config-sha256", request["sha256"], "--out", str(worker)]
    result = dict(schema=WIRE_SCHEMA, passed=False, fresh_public_wire_passed=False,
        target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
        netlist_sha256=proof["netlist_sha256"], powered_netlist_sha256=proof["powered_netlist_sha256"],
        transport=bind(pins, proof_path, proof_sha), worker_argv=argv, timeout_seconds=timeout,
        full_tapeout_ready=False, boundary="Fresh finite zero-delay wire corpus with all actual cells and sampler fault injection; "
                                         "timing, electrical power and shuttle acceptance remain separate.")
    started = time.monotonic()
    try:
        child = process_group.run_captured(argv, cwd=source, timeout=timeout, log_path=output / "worker.log")
        result["worker_exit_code"] = child.returncode
        require(child.returncode == 0, "Canonical wire worker failed; inspect retained worker logs")
        report = read_bound(pins, worker / "report.json")
        traces, artifacts = validate_worker(report, worker, config, request, target, pins)
        result.update(passed=True, fresh_public_wire_passed=True, actual_functional_instances=42210,
            positive_cases=35, actual_sampler_mutants=1, native_processes=14, physical_edges=report["physical_edges"],
            protocols=["UART", "SPI", "I2C", "JTAG"], traces=traces,
            worker_report=bind(pins, worker / "report.json"), worker_artifact_sha256=artifacts)
    except (OSError, ValueError, KeyError, RuntimeError, TypeError, subprocess.TimeoutExpired) as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        log = output / "worker.log"
        if log.is_file():
            result["worker_log"] = bind(pins, log)
        result.update(elapsed_seconds=time.monotonic() - started, verified_file_sha256=dict(sorted(pins.items())))
        emit(output / "report.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_subparsers(dest="mode", required=True)
    transport, wire = actions.add_parser("transport"), actions.add_parser("wire")
    absolute = lambda value: Path(value).absolute()
    transport.add_argument("--base", type=absolute, default=BASE_PATH)
    for action in (transport, wire):
        action.add_argument("--output", type=absolute, required=True)
    wire.add_argument("--proof", type=absolute, required=True)
    wire.add_argument("--proof-sha", required=True)
    wire.add_argument("--timeout", type=int, default=1800)
    args = parser.parse_args()
    try:
        result = run_transport(args.base, args.output) if args.mode == "transport" else run_wire(
            args.proof, args.proof_sha, args.output, args.timeout)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as exc:
        parser.exit(1, f"Hold/cap digital verification rejected: {exc}\n")
    print(args.output / ("transport.json" if args.mode == "transport" else "report.json"))
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
