"""Reopen exact-candidate digital replay and pinned Tiny Tapeout precheck."""

import argparse
import json
from pathlib import Path

import streaming_tt_signoff as signoff
from streaming_8x4_closure24_official_budget import native_journal
from streaming_8x4_e982_native import IMAGE, ROOT, TOP, checked_views
from streaming_8x4_e982_g4_transport import bind, emit, read_bound, require
from streaming_8x4_e982_g4_wire import verify_pins
from streaming_8x4_enclosure_admission import MAIN_GENERATOR, drc_report
from streaming_8x4_hold_cap_digital import SCHEMA, WIRE_SCHEMA, validate_worker
from streaming_8x4_hold_cap_physical import TARGET, TRIAL, setup


def digital(pins):
    out = TRIAL / "digital-02"
    proof = read_bound(pins, out / "transport.json")
    wire = read_bound(pins, out / "wire/report.json")
    for record, schema in ((proof, SCHEMA), (wire, WIRE_SCHEMA)):
        require(record["schema"] == schema and record["passed"] is True
                and record["target_odb_sha256"] == TARGET["odb_sha256"]
                and record["target_gds_sha256"] == TARGET["gds_sha256"], "Wrong digital receipt target")
        for path, digest in record["verified_file_sha256"].items():
            bind(pins, path, digest)
    identity = proof["source_identity"]
    require(identity["adapter_bytes_in_commit"] is True
            and proof["functional_correspondence_transported"] is True
            and proof["normalized_named_graph_equal"] is True
            and proof["state_transition_and_output_model_equal"] is True
            and proof["clock_and_reset_cones_equal"] is True
            and proof["state_bits"] == 6039 and proof["public_output_bits"] == 24
            and len(proof["identity_transformations"]) == 6, "Incomplete correspondence scope")
    bind(pins, ROOT / identity["adapter"], identity["adapter_sha256"])
    require(wire["transport"] == bind(pins, out / "transport.json")
            and wire["fresh_public_wire_passed"] is True and wire["worker_exit_code"] == 0
            and wire["netlist_sha256"] == proof["netlist_sha256"]
            and wire["powered_netlist_sha256"] == proof["powered_netlist_sha256"], "Wire replay misbound")
    request_path = out / "wire/request.json"
    config = read_bound(pins, request_path)
    worker_path = out / "wire/worker"
    worker = read_bound(pins, worker_path / "report.json", wire["worker_report"]["sha256"])
    traces, artifacts = validate_worker(worker, worker_path, config, bind(pins, request_path), proof["target"], pins)
    require(traces == wire["traces"] and artifacts == wire["worker_artifact_sha256"]
            and wire["positive_cases"] == 35 and wire["actual_sampler_mutants"] == 1
            and wire["native_processes"] == 14 and wire["physical_edges"] == sum(t["edges"] for t in traces),
            "Wire result counters or raw traces differ")
    return dict(passed=True, state_bits=6039, public_output_bits=24, actual_functional_instances=42210,
                positive_cases=35, sampler_mutants_detected=1, native_processes=14,
                physical_edges=wire["physical_edges"], correspondence=bind(pins, out / "transport.json"),
                wire=bind(pins, out / "wire/report.json"))


def precheck(context, pins):
    out = TRIAL / "official"
    report = read_bound(pins, out / "rehearsal-tt-precheck-readback.json")
    require(report["status"] == "pass" and report["exit_code"] == 0
            and report["target_odb_sha256"] == TARGET["odb_sha256"]
            and report["gds_sha256"] == TARGET["gds_sha256"]
            and report["cleanup"]["status"] == "absent" and report["frozen_inputs_unchanged"] is True,
            "Incomplete exact-candidate precheck")
    for artifact in report["artifacts"]:
        bind(pins, ROOT / artifact["path"], artifact["sha256"])
    views, view = checked_views(context)
    staged = {"gds": (TARGET["gds"], f"{TOP}.gds"),
              "lef": (views / "official-format.lef", f"{TOP}.lef"),
              "netlist": (views / "signoff-views/implemented.power.v", f"{TOP}.v"),
              "info": (ROOT / "info.yaml", "info.yaml")}
    for source, name in staged.values():
        actual = bind(pins, source)
        bind(pins, out / "design" / name, actual["sha256"])
    require(report["lef_sha256"] == view["view_sha256"]["lef"]
            and report["info_yaml_sha256"] == bind(pins, ROOT / "info.yaml")["sha256"], "Wrong precheck views")
    lock = read_bound(pins, ROOT / "tools/streaming-tt-signoff.json")
    for path, digest in signoff.verify_support(out / "tt", lock).items():
        bind(pins, path, digest)
    source = out / "tt/precheck/precheck.py"
    checks = signoff.selected_checks(source.read_text(), "ihp-sg13cmos5l")
    require(len(checks) == 9 and checks == report["expected_checks"]
            and report["support_revision"] == lock["support_commit"]
            and report["pdk_revision"] == context["prep"]["pdk_identity"]["base"]["revision"]
            and report["pdk_tree_sha256"] == context["prep"]["pdk_identity"]["base"]["tree_sha256"]
            and report["python_version"].startswith(lock["python_version_prefix"])
            and report["packages"] == lock["precheck_python_packages"], "Precheck source/runtime selection differs")
    results = signoff.precheck_result(out / "tt/precheck/reports/results.xml", checks, report["exit_code"])
    require(results == report["result"] and results["passed"], "Precheck XML differs from verdict")
    conf = read_bound(pins, out / "native-config.json")
    journal = native_journal(out / "native-klayout.jsonl", out=out, pdk=context["pdk"],
                             owner=conf["owner"], image_id=IMAGE, gds=out / "design" / f"{TOP}.gds")
    require(conf["image_id"] == IMAGE and conf["out"] == str(out)
            and journal == report["native"] and journal["closed_processes"] == 3 and journal["passed"],
            "Native precheck journal differs")
    raw = [json.loads(line) for line in (out / "native-klayout.jsonl").read_text().splitlines()]
    require(len(raw) == 6, "Incomplete native precheck events")
    geometry = {}
    for index, name in enumerate(("pin_label_purposes_overlapping_drawing", "sg13cmos5l", "zero_area")):
        argv = raw[2 * index]["argv"]
        generator = argv[argv.index("-r") + 1]
        categories, markers = drc_report(out / "tt/precheck/reports" / f"drc_{name}.xml", generator)
        require(not markers, "Precheck DRC markers: " + name)
        geometry[name] = dict(categories=len(categories), markers=0)
        if name == "sg13cmos5l":
            main, _ = drc_report(TRIAL / "main-drc-01/drc_sg13cmos5l.xml", MAIN_GENERATOR)
            require(categories == main and len(categories) == 332 and "NW.b" in categories,
                    "Incomplete precheck main-deck coverage")
    return dict(passed=True, checks=checks, native_klayout_runs=3, geometry=geometry,
                receipt=bind(pins, out / "rehearsal-tt-precheck-readback.json"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    args = parser.parse_args()
    context = setup(args.history.resolve())
    pins = {}
    for role in ("odb", "gds"):
        bind(pins, TARGET[role], TARGET[role + "_sha256"])
    digital_result = digital(pins)
    precheck_result = precheck(context, pins)
    bind(pins, Path(__file__).resolve())
    verify_pins(pins)
    output = TRIAL / "digital-precheck-readback.json"
    emit(output, dict(schema="pinwheel.hold-cap-digital-precheck.v1", passed=True,
         target_odb_sha256=TARGET["odb_sha256"], gds_sha256=TARGET["gds_sha256"],
         digital=digital_result, precheck=precheck_result, qualified_timing=False,
         electrical_power_qualified=False, tapeout_ready=False, verified_file_sha256=dict(sorted(pins.items()))))
    print(output)


if __name__ == "__main__":
    main()
