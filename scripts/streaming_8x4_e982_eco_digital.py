"""Transport the accepted b7e60 Boolean correspondence through the exact five-net ECO."""

import argparse
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import time

import process_group
import streaming_8x4_e982_g4_wire as canonical_wire
from streaming_8x4_e982_g4_transport import (
    ROOT, TOP, TARGET_ODB as BASE_ODB, TARGET_GDS as BASE_GDS, OLD_GATE4,
    REFERENCE, SCHEMA as BASE_SCHEMA, bind, emit, fingerprint, graph_signature,
    read_bound, reopen, require, sha, state_transport,
)
from streaming_8x4_e982_g4_wire import verify_pins
from streaming_tt_certificate import clock_cones, data_model, eval_boolean, parse_graph
from streaming_tt_simulation import libraries, verify_export


SCHEMA = "pinwheel.streaming-8x4-e982-eco-digital.v1"
WIRE_SCHEMA = "pinwheel.streaming-8x4-e982-eco-public-wire.v1"
BASE_TRANSPORT = "161e7cfee866844d6b242200b0d14828c3ccb29c9ca12de473c4329874bcd9e9"
ECO_ODB = "e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9"
ECO_GDS = "dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82"
PARTITION = "906430380175db7dc7f4cc118d6114a0a6a2352f0dde3c12ccd8b3a3752de215"
SCREEN = "86eff28a562f4d51f3719f146e8529cb10db89c703bb8b87d8b992ab64e94170"
ECO_VIEWS = "f3e019f5d4abf85e7d6f123c9d2f9d8282cca69e29b0e81e1db9ec34f048b045"
ECO_EXPORT = "ea0542e8cb38f331a3a76fcaf7b951132857efeec1bb26fd442f2e04ed215e85"
BUFFER = "sg13cmos5l_buf_1"
DECAP = "sg13cmos5l_decap_4"
NETS = ("net2157", "net2298", "net11223", "net2333", "net840")


def signals(instance):
    return {pin: terminal["net"] for pin, terminal in instance["terminals"].items()
            if terminal["signal_type"] in {"SIGNAL", "CLOCK"}}


def contract(document, baseline, actual, operations, library):
    """Remove only observed positive buffers whose output equals the old branch."""
    old_instances, new_instances = baseline["instances"], actual["instances"]
    added = set(new_instances) - set(old_instances)
    removed = set(old_instances) - set(new_instances)
    require(len(removed) == len(added) == 5 and len(old_instances) == len(new_instances) == 98900
            and all(old_instances[name]["master"] == DECAP and not signals(old_instances[name])
                    for name in removed), "Expected exactly five signal-free decap replacements")
    require(baseline["public_bterms"] == actual["public_bterms"]
            and baseline["power_bterms"] == actual["power_bterms"], "Public or power boundary changed")
    require([op["source_net"] for op in operations] == list(NETS), "Unexpected contraction scope")
    branches = {op["new_net"] for op in operations}
    require(added == {op["new_instance"] for op in operations} and len(branches) == 5
            and not branches & baseline["nets"].keys()
            and actual["nets"].keys() == baseline["nets"].keys() | branches,
            "Unexpected added instances or named nets")

    model = library.cells[BUFFER]
    require(not model.sequential and model.output == "X" and model.directions == {"A": "input", "X": "output"}
            and not eval_boolean(model.function, {"A": False}) and eval_boolean(model.function, {"A": True}),
            "The three-corner pinned buffer is not Boolean identity")
    reverted = deepcopy(document)
    cells = reverted["modules"][TOP]["cells"]
    moves, rules = {}, []
    for op in operations:
        source, upstream, branch = (op[key] for key in ("source_net", "upstream_net", "new_net"))
        name = op["new_instance"]
        require((name, branch) == (f"eco_{source}_buf", f"eco_{source}_branch")
                and op["master"] == new_instances[name]["master"] == BUFFER
                and signals(new_instances[name]) == {"A": upstream, "X": branch}
                and all(actual["nets"][net]["signal_type"] == "SIGNAL" for net in (source, upstream, branch)),
                f"Wrong new buffer, input, output or net type: {source}")
        if source == "net2333":
            require(op["kind"] == "signal_buffer" and upstream == source and op["source_instance"] is None,
                    "The serial insertion does not directly project the original branch")
        else:
            original = op["source_instance"]
            require(op["kind"] == "clone" and original == f"fanout{source[3:]}"
                    and old_instances[original]["master"] == new_instances[original]["master"] == BUFFER
                    and signals(old_instances[original]) == signals(new_instances[original])
                    == {"A": upstream, "X": source}, f"Clone does not share the original positive input: {source}")
        del cells[name]
        for kind, load, pin in op["loads"]:
            old_pin = old_instances[load]["terminals"][pin]
            new_pin = new_instances[load]["terminals"][pin]
            require(kind == "iterm" and (load, pin) not in moves
                    and load not in added | removed and old_pin["signal_type"] == "SIGNAL"
                    and old_pin["direction"] == "INPUT" and old_pin["net"] == source
                    and new_pin == dict(old_pin, net=branch)
                    and cells[load]["connections"][pin] == [actual["nets"][branch]["wire"]],
                    f"Wrong original or ECO sink: {load}/{pin}")
            moves[load, pin] = branch
            cells[load]["connections"][pin] = [actual["nets"][source]["wire"]]
        rules.append(dict(buffer=name, input_net=upstream, output_net=branch, equal_original_net=source,
                          kind=op["kind"], sinks=op["loads"]))

    require(len(moves) == 10, "Unexpected contracted sink count")
    for name in old_instances.keys() - removed:
        old, new = old_instances[name], new_instances[name]
        require(old["master"] == new["master"] and old["master_type"] == new["master_type"]
                and old["terminals"].keys() == new["terminals"].keys(), f"Unplanned cell change: {name}")
        for pin, terminal in old["terminals"].items():
            expected = dict(terminal, net=moves[name, pin]) if (name, pin) in moves else terminal
            require(new["terminals"][pin] == expected, f"Unplanned terminal change: {name}/{pin}")
    return reverted, rules, sorted(removed)


def read_target(pins, trial, views, reference, exporter_sha):
    database = bind(pins, trial / "trial.odb", ECO_ODB)
    gds = bind(pins, trial / "stream/design.gds", ECO_GDS)
    screen = read_bound(pins, trial / "screen.json", SCREEN)
    require(screen["passed"] is True and screen["trial_odb_sha256"] == ECO_ODB
            and screen["gds_sha256"] == ECO_GDS, "Screen identifies another trial")
    view = read_bound(pins, views / "rehearsal-view-readback.json", ECO_VIEWS)
    require(view["status"] == "pass" and view["target_odb_sha256"] == ECO_ODB
            and view["gds_sha256"] == ECO_GDS, "Canonical ECO view readback differs")
    for item in view["artifacts"]:
        bind(pins, ROOT / item["path"], item["sha256"])
    result = read_bound(pins, views / "final-views-native.json")
    signoff = read_bound(pins, views / "signoff-views/report.json", result["canonical_signoff_report_sha256"])
    native = read_bound(pins, views / "execution.json")
    require(result["completed"] is True and result["source_odb_sha256"] == ECO_ODB
            and result["source_odb_unchanged"] is True and signoff["actual_database_sha256"] == ECO_ODB
            and signoff["completed"] is True and signoff["inputs_unchanged"] is True
            and signoff["inherited_netlist"] is False and signoff["top"] == TOP
            and native["status"] == "completed" and native["exit_code"] == 0
            and native["container_termination"]["status"] == "absent"
            and f"type=bind,source={database['path']},target=/work/target.odb,readonly" in native["argv"],
            "Native ECO views did not close on the exact read-only ODB")
    netlists = {name: bind(pins, views / "signoff-views" / name, signoff["artifacts_sha256"][name])
                for name in ("implemented.v", "implemented.power.v")}
    require(netlists["implemented.v"]["sha256"] == view["view_sha256"]["verilog"]
            and netlists["implemented.power.v"]["sha256"] == view["view_sha256"]["powered_verilog"],
            "Canonical ECO Verilog view hashes differ")
    directory = views / "actual-signal"
    require(result["canonical_boolean_report_sha256"] == ECO_EXPORT, "Wrong actual ECO export")
    receipt = read_bound(pins, directory / "receipt.json", ECO_EXPORT)
    document, inventory, _ = verify_export(directory, receipt_sha256=ECO_EXPORT, database=database["path"],
                                          reference=reference, exporter_sha256=exporter_sha)
    for name, digest in receipt["artifacts_sha256"].items():
        bind(pins, directory / name, digest)
    target = dict(database=database, gds=gds, export_dir=str(directory),
                  connectivity_receipt=bind(pins, directory / "receipt.json", ECO_EXPORT),
                  export_artifact_sha256=receipt["artifacts_sha256"], view_artifacts=netlists)
    return document, inventory, target


def run_transport(base_path, trial, views, output):
    require(not output.exists(), "Preserve earlier ECO digital evidence")
    pins = {}
    base = read_bound(pins, base_path, BASE_TRANSPORT)
    require(base["schema"] == BASE_SCHEMA and base["passed"] is True
            and base["functional_correspondence_transported"] is True
            and base["target_odb_sha256"] == BASE_ODB and base["target_gds_sha256"] == BASE_GDS,
            "Missing exact b7e60 correspondence authority")
    for path, digest in base["verified_file_sha256"].items():
        bind(pins, path, digest)
    reopen(pins, base["historical_gate4"])
    require(base["historical_gate4"]["sha256"] == OLD_GATE4, "Historical f516 theorem receipt differs")
    config_item = reopen(pins, base["historical_worker_config"])
    config = read_bound(pins, config_item["path"], config_item["sha256"])
    reference = bind(pins, config["export"]["reference"], REFERENCE)["path"]
    exporter_sha = config["source_sha256"]["scripts/streaming_tt_export_odb.py"]
    baseline = base["target"]
    base_document, base_inventory, _ = verify_export(baseline["export_dir"],
        receipt_sha256=baseline["connectivity_receipt"]["sha256"], database=baseline["database"]["path"],
        reference=reference, exporter_sha256=exporter_sha)
    eco_document, eco_inventory, target = read_target(pins, trial, views, reference, exporter_sha)
    operations = read_bound(pins, trial / "partition.json", PARTITION)["operations"]
    used = {cell["type"] for cell in base_document["modules"][TOP]["cells"].values()}
    require(used == {cell["type"] for cell in eco_document["modules"][TOP]["cells"].values()},
            "Digital library master set differs")
    library, _ = libraries(config["corners"], used)
    base_graph = parse_graph(base_document, TOP, library)
    eco_graph = parse_graph(eco_document, TOP, library)
    contracted_document, rules, removed = contract(eco_document, base_inventory, eco_inventory, operations, library)
    contracted_graph = parse_graph(contracted_document, TOP, library)
    base_signature = graph_signature(base_graph, base_inventory)
    require(fingerprint(base_signature) == base["named_graph_sha256"]
            and base_signature == graph_signature(contracted_graph, eco_inventory),
            "A named original gate, state pin, clock or port differs after contraction")
    base_model = data_model(base_graph)
    require(fingerprint(base_model) == base["state_and_outputs_sha256"] and base_model == data_model(contracted_graph),
            "Complete D/next-state and output model differs after contraction")
    cones = clock_cones(base_graph)
    passive = Counter(kind for _, kind, _ in eco_graph.passive_loads)
    require(cones == clock_cones(eco_graph) == clock_cones(contracted_graph)
            and len(cones) == 6039 and sum(map(len, eco_graph.outputs.values())) == 24
            and len(base_graph.gates) == len(contracted_graph.gates) == 36005 and len(eco_graph.gates) == 36010
            and passive == {"sg13cmos5l_antennanp": 160}, "Full clock, state, output or passive scope differs")
    state_pin, sampler_pin = base["semantic_state_map"], base["sampler_binding"]
    states = read_bound(pins, state_pin["path"], state_pin["sha256"])
    sampler = read_bound(pins, sampler_pin["path"], sampler_pin["sha256"])
    require(states["database_sha256"] == BASE_ODB
            and states["connectivity_sha256"] == sampler["connectivity_sha256"]
            == baseline["export_artifact_sha256"]["connectivity.json"], "Baseline state/sampler binding differs")
    sampler["bindings"] = {stage: dict(binding, cell=json.dumps([binding["cell"]], separators=(",", ":")))
                           for stage, binding in sampler["bindings"].items()}
    state_rows, sampler_rows = state_transport(states, sampler, base_document, eco_document, base_graph, eco_graph)
    bind(pins, Path(__file__).resolve())
    verify_pins(pins)

    output.mkdir(parents=True)
    state_path, sampler_path = output / "semantic-state-map.json", output / "sampler-binding.json"
    connectivity = target["export_artifact_sha256"]["connectivity.json"]
    emit(state_path, dict(states, database_sha256=ECO_ODB, connectivity_sha256=connectivity, rows=state_rows,
                          boundary="State endpoints on exact ECO after verified positive-buffer substitution."))
    basis = dict(sampler["semantic_basis"], **{
        "accepted-b7e60-transport": bind(pins, base_path, BASE_TRANSPORT),
        "candidate-connectivity": target["connectivity_receipt"],
        "actual-state-pairing": bind(pins, state_path),
    })
    emit(sampler_path, dict(sampler, bindings=sampler_rows, connectivity_sha256=connectivity, semantic_basis=basis))
    result = dict(schema=SCHEMA, passed=True, target_odb_sha256=ECO_ODB, target_gds_sha256=ECO_GDS,
        target=target, netlist_sha256=target["view_artifacts"]["implemented.v"]["sha256"],
        powered_netlist_sha256=target["view_artifacts"]["implemented.power.v"]["sha256"],
        base_transport=bind(pins, base_path, BASE_TRANSPORT), historical_worker_config=config_item,
        original_active_gates=36005, eco_active_gates=36010, state_bits=len(state_rows), public_output_bits=24,
        removed_decap_instances=removed, positive_buffer_contractions=rules,
        named_graph_sha256=fingerprint(base_signature), state_and_outputs_sha256=fingerprint(base_model),
        clock_and_reset_cones_equal=True, functional_correspondence_transported=True,
        semantic_state_map=bind(pins, state_path), sampler_binding=bind(pins, sampler_path),
        lean_recompiled=False, fresh_public_wire_passed=False, full_tapeout_ready=False,
        boundary="Zero-delay Boolean correspondence via five verified positive-buffer substitutions. "
                 "Electrical, physical and tapeout acceptance remain separate.",
        verified_file_sha256=dict(sorted(pins.items())))
    emit(output / "transport.json", result)
    return result


def run_wire(proof_path, proof_sha, output, timeout):
    require(not output.exists() and 1 <= timeout <= 1800, "Use a fresh bounded ECO wire output")
    pins = {}
    proof = read_bound(pins, proof_path, proof_sha)
    require(proof["schema"] == SCHEMA and proof["passed"] is True
            and proof["functional_correspondence_transported"] is True
            and proof["target_odb_sha256"] == ECO_ODB and proof["target_gds_sha256"] == ECO_GDS,
            "Missing exact ECO digital transport")
    pins.update(proof["verified_file_sha256"])
    verify_pins(pins)
    item = proof["historical_worker_config"]
    config = read_bound(pins, item["path"], item["sha256"])
    target = proof["target"]
    config = dict(config, physical_stage="actual-e40e4-fanout-eco-canonical-export",
                  sampler_binding=proof["sampler_binding"],
                  export=dict(config["export"], directory=target["export_dir"], database=target["database"]["path"],
                              receipt_sha256=target["connectivity_receipt"]["sha256"]))
    source = Path(config["root"])
    entry = bind(pins, source / "scripts/check-streaming-tt-wire.py",
                 config["source_sha256"]["scripts/check-streaming-tt-wire.py"])
    bind(pins, Path(process_group.__file__).resolve(), config["source_sha256"]["scripts/process_group.py"])
    bind(pins, Path(canonical_wire.__file__).resolve())
    output.mkdir(parents=True)
    request_path = output / "request.json"
    emit(request_path, config)
    request = bind(pins, request_path)
    worker = output / "worker"
    argv = [config["tools"]["python"], "-B", entry["path"], "--worker-config", request["path"],
            "--worker-config-sha256", request["sha256"], "--out", str(worker)]
    result = dict(schema=WIRE_SCHEMA, passed=False, target_odb_sha256=ECO_ODB, target_gds_sha256=ECO_GDS,
                  netlist_sha256=proof["netlist_sha256"], powered_netlist_sha256=proof["powered_netlist_sha256"],
                  transport=bind(pins, proof_path, proof_sha), worker_argv=argv, timeout_seconds=timeout,
                  full_tapeout_ready=False)
    started = time.monotonic()
    try:
        child = process_group.run_captured(argv, cwd=source, timeout=timeout, log_path=output / "worker.log")
        result["worker_exit_code"] = child.returncode
        require(child.returncode == 0, "Canonical wire worker failed; inspect the retained raw logs")
        report = read_bound(pins, worker / "report.json")
        require(report["schema"] == "pinwheel.streaming-tt-public-wire.v1" and report["passed"] is True
                and report["stage"] == "closed" and report["qualified"] is False
                and report["physical_acceptance_claim"] is False
                and report["export"]["database_sha256"] == ECO_ODB
                and report["export"]["artifacts_sha256"] == target["export_artifact_sha256"]
                and report["configuration"] == request and report["physical_stage"] == config["physical_stage"]
                and report["inputs_unchanged"] is True and report["generated_inputs_unchanged"] is True
                and report["all_actual_instances_retained"] is True and report["clock_contraction"] is False
                and report["actual_functional_instances"] == 42209 and report["physical_ff_bits"] == 6039
                and report["positive_cases"] == 35 and report["actual_sampler_mutants"] == 1
                and report["native_processes"] == 14, "Canonical full wire receipt failed to bind the ECO")
        worker_reader, owner_reader = canonical_wire.canonical_validators(source, config["source_sha256"])
        traces = worker_reader.validate_native(report, worker, config["tools"])
        journal = owner_reader.native_journal(worker / "native.jsonl", report["native_runs"])
        artifacts = {str(path.relative_to(worker)): sha(path) for path in worker.rglob("*")
                     if path.is_file() and path != worker / "report.json"}
        require(traces == report["traces"] and journal == report["native_journal"]["sha256"]
                and artifacts == report["artifact_sha256"], "Independently reopened wire artifacts differ")
        for path, digest in report["input_sha256_before"].items():
            bind(pins, path, digest)
        for name, module in tuple(sys.modules.items()):
            if name.startswith("streaming_") and not name.startswith("streaming_8x4_e982_"):
                path = Path(module.__file__).resolve()
                bind(pins, path, config["source_sha256"]["scripts/" + path.name])
        verify_pins(pins)
        result.update(passed=True, fresh_public_wire_passed=True, positive_cases=35, actual_sampler_mutants=1,
                      native_processes=14, physical_edges=report["physical_edges"], traces=traces,
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
    transport = actions.add_parser("transport")
    wire = actions.add_parser("wire")
    for action, paths in ((transport, ("base", "trial", "views", "output")), (wire, ("proof", "output"))):
        for path in paths:
            action.add_argument("--" + path, type=lambda value: Path(value).absolute(), required=True)
    wire.add_argument("--proof-sha", required=True)
    wire.add_argument("--timeout", type=int, default=1800)
    args = parser.parse_args()
    try:
        if args.mode == "transport":
            result = run_transport(args.base, args.trial, args.views, args.output)
        else:
            result = run_wire(args.proof, args.proof_sha, args.output, args.timeout)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(1, f"ECO digital verification rejected: {exc}\n")
    print(args.output / ("transport.json" if args.mode == "transport" else "report.json"))
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
