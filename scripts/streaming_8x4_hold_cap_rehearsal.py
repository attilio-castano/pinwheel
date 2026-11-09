"""Assemble and independently reopen a portable local hold/cap rehearsal.

Verification reads only the bundle and its committed source snapshot. Original
absolute paths are provenance labels resolved through the evidence mirror.
Historical proof/toolchain custody and native reruns are explicitly outside it.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import struct
import subprocess
import sys
from xml.etree.ElementTree import ParseError

from streaming_8x4_bringup import fixture as bringup_fixture
from streaming_8x4_e982_eco_rehearsal import copy_checked, OPEN_GATES
from streaming_8x4_tt_rehearsal import (
    PACKAGE, ROOT, TRACKED_ASSETS, TT_CHECKS, UPSTREAM, digest, file_record, json_object, invalid_constant,
    file_spec, hash_string, local_path, read_json, relative_name, require, revision_label,
)
from streaming_8x4_enclosure_admission import (
    MAIN_GENERATOR, ENCLOSURE_GENERATOR, ENCLOSURE_RULES, drc_report,
)
from streaming_8x4_e982_native import IMAGE, TOP
from streaming_tt_layout import geometry_result
from streaming_tt_signoff import precheck_result, selected_checks, decode
from streaming_tt_quality import inventory_context, logical_power
from streaming_mapped_simulation import check_uart_cases
from streaming_uart_legacy_cases import check_legacy_cases
from streaming_ready_wire_cases import check_i2c_cases
from streaming_8x4_e982_eco_timing_readback import raw_timing, extra_checks
from streaming_8x4_draft_rc_timing_observe import check_observer
from streaming_8x4_e982_parasitics_preflight import annotation_evidence


SCHEMA = "pinwheel.streaming-8x4-hold-cap-rehearsal.v1"
TRIAL = "build/8x4-hold-cap-20261107/trial-02"
ODB = "dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73"
GDS = "d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832"
PINS = {
    "physical-decision.json": "70137eccd434c27864923fa3a9b3114e6fb363008b185822ad9a14e64d05bd72",
    "digital-02/transport.json": "09a71320c29f15ace79151b1fbfd311af06c6796f7274bb2baab77129981d047",
    "digital-02/wire/report.json": "2bfadee2aff5fd8341b0d00772399571e6c64cabec63da714d4462b9ab30183b",
    "digital-precheck-readback.json": "22a9a418a695e20324632d315a0d28c5991a186383bbd79a38d83dd7f0a414e8",
    "official/rehearsal-tt-precheck-readback.json": "fb04e8205dec2f3a8ca7177d42281a64fd3041375dcc59f393421900ee066c81",
    "views/rehearsal-view-readback.json": "1ffd35b51c7367380745356b78aaaeb9ec8b774cdd6723ab51f613b0c7c26729",
    "connectivity-readback.json": "53f9d54453053d7d7f69cda953f012e24c2c062d29d2207915703ab19cc72b7f",
    "rail-readback.json": "fc07bcf4132faa8eac7f4928559cea9b0fae9916612de3d2539435793fb830d5",
    "timing/timing-readback.json": "aaf351d84af3ae653a05999f8d5a402940596e0408abda69089f0e066cdba45c",
    "timing/native-readback.json": "62b5ef3e7735ec4e73c248792fd0476371461adaf9f93f5e7442c3bda2e751e8",
    "layout/inputs/request.json": "867681124a61fe7a07e8e6fdb239b2635d1e0bc3f1fd1831e259ed530d0d19c0",
}
BRINGUP = f"{TRIAL}/rehearsal-bringup-01/receipt.json"
BRINGUP_SOURCE = "scripts/streaming_8x4_hold_cap_bringup.py"
DEMO_ASSETS = {
    "bringup_tool": "scripts/streaming_8x4_bringup.py",
    "host_transport": "scripts/streaming_ready_transport.py",
    "host_demo": "scripts/host_demo.py",
    "wire_protocol": "docs/protocols/streaming-continuation.md",
    "ready_protocol": "docs/protocols/streaming-ready.md",
}
PAYLOAD = {**PACKAGE, "odb": f"database/{TOP}.odb", "cdl": f"cdl/{TOP}.cdl", "sdc": "constraints/core.sdc",
           **{role: "demo/" + name for role, name in DEMO_ASSETS.items()},
           "bringup_fixture": "demo/fixture.json", "bringup_dry_run": "demo/dry-run.json"}
CORNERS = ("nom_fast_1p32V_m40C", "nom_typ_1p20V_25C", "nom_slow_1p08V_125C")
CUSTODY = {
    "portable_selected_evidence": True, "independent_backup_verified": False,
    "historical_proof_archive_complete": False, "native_toolchains_and_full_pdk_included": False,
    "fresh_source_to_gds_rebuild": False, "native_physical_or_simulation_rerun_performed_by_verifier": False,
    "scope": "Selected raw reports, process receipts, traces and exact handoff assets; excluded bindings are provenance labels only.",
}


class Evidence:
    def __init__(self, workspace, origin, source):
        self.workspace, self.origin = Path(workspace), Path(origin)
        require(self.origin.is_absolute() and ".." not in self.origin.parts, "Invalid original workspace label")
        self.files, self.known, self.provenance = {}, {}, {}
        self.source = source
        for name, pin in PINS.items():
            self.known[f"{TRIAL}/{name}"] = pin

    def name(self, value):
        path = Path(value)
        relative = path.relative_to(self.origin).as_posix() if path.is_absolute() else str(value)
        return relative_name(relative).as_posix()

    def record(self, value, expected=None):
        name = self.name(value)
        expected = expected or self.known.get(name) or self.source.get(name)
        require(hash_string(expected), "No sealed digest for selected evidence: " + name)
        record = file_record(self.workspace, name, expected)
        require(self.files.setdefault(name, record) == record, "Conflicting selected evidence: " + name)
        self.known[name] = expected
        return record

    def path(self, value, expected=None):
        return local_path(self.workspace, self.record(value, expected)["path"])

    def read(self, value, expected=None):
        return read_json(self.path(value, expected))

    def array(self, value, expected=None):
        result = json.loads(self.path(value, expected).read_bytes(), object_pairs_hook=json_object,
                            parse_constant=invalid_constant)
        require(type(result) is list, "Expected a JSON array")
        return result

    def link(self, item):
        return self.record(item["path"], item["sha256"])

    def artifacts(self, record):
        return [self.link(item) for item in record["artifacts"]]

    def register(self, values):
        """Remember receipt bindings without opening their historical targets."""
        for path, pin in values.items():
            require(hash_string(pin), "Malformed provenance digest")
            require(self.provenance.setdefault(path, pin) == pin, "Conflicting provenance digest")
            try:
                name = self.name(path)
            except ValueError:
                continue
            require(self.known.setdefault(name, pin) == pin, "Conflicting local provenance digest")

    def excluded(self):
        return {path: dict(sha256=pin, scope="Recorded provenance; bytes not included or reopened")
                for path, pin in sorted(self.provenance.items())
                if not (Path(path).is_relative_to(self.origin)
                        and (Path(path).relative_to(self.origin).as_posix() in self.files
                             or self.source.get(Path(path).relative_to(self.origin).as_posix()) == pin))}


def exact(record, gds_key="gds_sha256"):
    require(record["target_odb_sha256"] == ODB and record[gds_key] == GDS, "Mixed or stale layout evidence")


def closed(record):
    require(record["status"] == "completed" and type(record["exit_code"]) is int and record["exit_code"] == 0
            and record["container_termination"]["status"] == "absent"
            and record["container_termination"]["remaining"] == []
            and 0 < record["elapsed_seconds"] <= record["timeout_seconds"]
            and math.isfinite(record["timeout_seconds"]), "Incomplete native execution or cleanup")
    argv = record["argv"]
    require(argv.count(IMAGE) == 1 and argv[argv.index("--network") + 1] == "none"
            and "--read-only" in argv and argv[argv.index("--pull") + 1] == "never", "Wrong native runtime policy")
    return argv


def mounted(e, argv, relative, target):
    require(f"type=bind,source={e.origin / relative},target={target},readonly" in argv,
            "Wrong read-only native input: " + relative)


def reopen_views(e):
    view = e.read(f"{TRIAL}/views/rehearsal-view-readback.json")
    exact(view)
    require(view["status"] == "pass", "Canonical views failed")
    e.artifacts(view)
    assets = {"odb": e.record(f"{TRIAL}/trial.odb", ODB), "gds": e.record(f"{TRIAL}/stream/design.gds", GDS)}
    for role, name, key in (("lef", "official-format.lef", "lef"), ("cdl", "complete-reference.cdl", "cdl"),
                            ("nl", "signoff-views/implemented.v", "verilog"),
                            ("pnl", "signoff-views/implemented.power.v", "powered_verilog"), ("def", "design.def", "def")):
        assets[role] = e.record(f"{TRIAL}/views/{name}", view["view_sha256"][key])
    mounted(e, closed(e.read(f"{TRIAL}/views/execution.json")), assets["odb"]["path"], "/work/target.odb")
    export = e.read(f"{TRIAL}/views/actual-signal/receipt.json")
    require(export["database_sha256"] == ODB and export["read_only_database"] is True and export["top"] == TOP,
            "Wrong actual connectivity export")
    for name, pin in export["artifacts_sha256"].items():
        e.record(f"{TRIAL}/views/actual-signal/{name}", pin)
    inventory = e.read(f"{TRIAL}/views/actual-signal/inventory.json")
    context, disconnected = inventory_context(inventory)
    power = logical_power(inventory)
    require(len(inventory["instances"]) == 98904 and len(inventory["physical_only_instances"]) == 56694
            and power["passed"] is True, "Incomplete actual inventory or logical supply binding")
    membership = e.read(f"{TRIAL}/connectivity-readback.json")
    rails = e.read(f"{TRIAL}/rail-readback.json")
    require(membership["status"] == rails["status"] == "pass" and membership["target_odb_sha256"] == ODB
            and membership["all_regular_net_terminals_verified"] is True
            and len(membership["added_instances"]) == 13 and len(membership["removed_instances"]) == 9
            and rails["target_odb_sha256"] == ODB and rails["instances"] == 98904
            and rails["inventory_sha256"] == export["artifacts_sha256"]["inventory.json"], "Route/inventory receipt differs")
    geometry = e.read(f"{TRIAL}/views/native-geometry.json")
    require(geometry["completed"] is True and geometry["input_sha256"]["/work/target.odb"] == ODB
            and geometry["die_dbu"] == [0, 0, 1724160, 710640] and len(geometry["public_pins_dbu"]) == 43
            and geometry["instance_count"] == 98904, "Candidate outline or public pin inventory differs")
    return assets, inventory, context, disconnected


def reopen_physical(e, assets):
    decision = e.read(f"{TRIAL}/physical-decision.json")
    exact(decision)
    require(decision["all_four_checks_passed"] is True and decision["carry_forward_for_qualification"] is True
            and all(decision[key] is False for key in ("qualified_timing", "electrical_power_qualified", "tapeout_ready")),
            "Wrong physical decision scope")
    categories = {}
    for role, folder, report, generator, count in (
            ("main_drc", "main-drc-01", "drc_sg13cmos5l.xml", MAIN_GENERATOR, 332),
            ("enclosure", "enclosure-01", "enclosure.xml", ENCLOSURE_GENERATOR, 11)):
        row = decision[role]
        exact(row)
        require(row["status"] == "pass" and row["markers"] == {}, "Nonpassing physical rule receipt")
        e.artifacts(row)
        argv = closed(e.read(f"{TRIAL}/{folder}/execution.json"))
        mounted(e, argv, assets["gds"]["path"], "/work/export/design.gds")
        require(argv[argv.index("-r") + 1] == generator, "Wrong physical deck invocation")
        names, items = drc_report(e.path(f"{TRIAL}/{folder}/{report}"), generator)
        require(not items and len(names) == count and names == set(row["categories"]), "Incomplete physical rule report")
        log = e.path(f"{TRIAL}/{folder}/container.log").read_text()
        require(not re.search(r"\b(?:WARNING|ERROR|FATAL)\b|Traceback", log), "Unexpected physical checker diagnostic")
        if role == "main_drc":
            require("NW.b" in names and log.count("KLayout DRC run for tables 'main' completed") == 1
                    and "Executing rule NW.b\n" in log, "Main-deck completion missing")
        else:
            require(names == set(ENCLOSURE_RULES)
                    and re.findall(r"^Rule (\S+): (\d+) error\(s\)$", log, re.M)
                    == [(rule, "0") for rule in ENCLOSURE_RULES], "Enclosure rule execution missing")
        categories[role] = count
    lvs = decision["lvs"]
    exact(lvs)
    e.artifacts(lvs)
    execution = e.read(f"{TRIAL}/layout/execution.json")
    argv = closed(execution)
    mounted(e, argv, assets["gds"]["path"], "/input/actual.gds")
    mounted(e, argv, assets["cdl"]["path"], "/input/actual.cdl")
    request = e.read(f"{TRIAL}/layout/inputs/request.json")
    require(request["source_odb_sha256"] == ODB
            and request["input_sha256"]["/input/actual.gds"] == GDS
            and request["input_sha256"]["/input/actual.cdl"] == assets["cdl"]["sha256"], "Wrong native layout request inputs")
    for name, pin in request["producer_sha256"].items():
        require(e.source[name] == pin, "Native report worker differs from committed source")
    native = e.read(f"{TRIAL}/layout/native-result.json")
    journal = e.array(f"{TRIAL}/layout/native-journal.json")
    require(native["completed"] is True and native["inputs_unchanged"] is True
            and native["source_odb_sha256"] == ODB and native["events"] == journal
            and [row["kind"] for row in journal] == ["antenna", "lvs"] and all(row["exit_code"] == 0 for row in journal),
            "Native LVS/antenna journal differs")
    actual = e.read(f"{TRIAL}/layout/lvs-result.json")
    e.record(f"{TRIAL}/layout/lvs.lvsdb", actual["report_sha256"])
    result = actual["result"]
    require(lvs["status"] == "pass" and result["passed"] is True and result["top"] == TOP
            and len(result["circuits"]) == lvs["circuit_pairs"] == 39
            and result["layout_devices"] == result["schematic_devices"] == 256
            and all(row["status"] == "Match" and row["layout"] and row["schematic"] for row in result["circuits"])
            and lvs["reference_cdl_sha256"] == assets["cdl"]["sha256"], "Incomplete transistor LVS")
    log = e.path(f"{TRIAL}/layout/lvs.native.log").read_text()
    require(all(text in log for text in ("Selected NET_ONLY option: false", "Comparison in strict port mode",
                                         "Congratulations! Netlists match.")), "Strict transistor LVS success missing")
    antenna = e.read(f"{TRIAL}/layout/antenna-result.json")
    expected = [["Ant.a"], ["Ant.c"], *[[f"Ant.{rule}_{layer}"] for layer in
        ("Metal1", "Metal2", "Metal3", "Metal4", "TopMetal1") for rule in ("b", "e")],
        *[[f"Ant.{rule}_{layer}"] for layer in ("Via1", "Via2", "Via3", "TopVia1") for rule in ("d", "f")],
        ["Ant.g"], ["Ant.h"], ["Ant.i"]]
    fresh = geometry_result(e.path(f"{TRIAL}/layout/antenna.xml", antenna["report_sha256"]), TOP, expected_categories=expected)
    require(fresh == antenna["result"] == decision["foundry_antenna"] and fresh["passed"] is True,
            "Foundry antenna XML differs")
    return dict(main_categories=332, enclosure_categories=11, markers=0, lvs_pairs=39, lvs_devices_per_side=256,
                rail_terminal_bindings_instances=98904, rail_scope="Logical inventory bindings only; no fresh PSM or dynamic power analysis",
                die_micrometres=[1724.16, 710.64], public_pins=43,
                antenna_categories=23, antenna_violations=0, lvs_database_interpretation="Sealed pinned native reader; not rerun")


def trace_file(e, item):
    entry = e.link(item)
    require(type(item["edges"]) is int and item["edges"] > 0 and item["bytes"] == entry["bytes"] == item["edges"] * 20,
            "Incomplete or truncated wire trace")
    count = 0
    with e.path(entry["path"]).open("rb") as stream:
        while block := stream.read(20 * 8192):
            require(len(block) % 20 == 0, "Partial wire trace edge")
            for offset in range(0, len(block), 20):
                count += 1
                require(struct.unpack_from("<I", block, offset)[0] == count, "Reordered or missing wire trace edge")
    require(count == item["edges"], "Wrong complete wire edge count")
    return entry


def reopen_digital(e, assets):
    proof = e.read(f"{TRIAL}/digital-02/transport.json")
    wire = e.read(f"{TRIAL}/digital-02/wire/report.json")
    for row in (proof, wire):
        exact(row, "target_gds_sha256")
        require(row["passed"] is True and row["full_tapeout_ready"] is False
                and row["netlist_sha256"] == assets["nl"]["sha256"]
                and row["powered_netlist_sha256"] == assets["pnl"]["sha256"], "Mixed digital candidate views")
        e.register(row["verified_file_sha256"])
    require(proof["schema"] == "pinwheel.streaming-8x4-hold-cap-digital.v1"
            and all(proof[key] is True for key in ("functional_correspondence_transported", "normalized_named_graph_equal",
                "state_transition_and_output_model_equal", "clock_and_reset_cones_equal"))
            and proof["source_identity"]["adapter_bytes_in_commit"] is True
            and len(proof["identity_transformations"]) == 6 and proof["state_bits"] == 6039
            and proof["public_output_bits"] == 24 and proof["actual_functional_instances"] == 42210,
            "Incomplete exact-candidate correspondence")
    for role in ("base_transport", "semantic_state_map", "sampler_binding", "physical_decision"):
        e.link(proof[role])
    state = e.read(proof["semantic_state_map"]["path"])
    document = e.read(f"{TRIAL}/views/actual-signal/connectivity.json")
    cells = document["modules"][TOP]["cells"]
    rows = state["rows"]
    require(state["database_sha256"] == ODB and len(rows) == len({r["semantic"] for r in rows})
            == len({r["actual_ff"] for r in rows}) == 6039, "Incomplete semantic state bijection")
    actual_ff = {name for name, cell in cells.items() if {"Q", "D", "CLK", "RESET_B"} <= cell["connections"].keys()}
    require({json.loads(row["actual_ff"])[0] for row in rows} == actual_ff, "State map omits actual flip-flops")
    for row in rows:
        names = json.loads(row["actual_ff"])
        require(type(names) is list and len(names) == 1 and json.dumps(names, separators=(",", ":")) == row["actual_ff"],
                "Malformed actual state identity")
        cell = cells[names[0]]
        require(cell["type"] == row["actual_cell"] and all(cell["connections"][pin] == [row[key]] for pin, key in
                (("Q", "actual_q"), ("D", "actual_d"), ("CLK", "actual_clock"), ("RESET_B", "actual_reset_b"))),
                "Actual candidate state pin differs")
    sampler = e.read(proof["sampler_binding"]["path"])
    require(sampler["connectivity_sha256"] == state["connectivity_sha256"]
            == e.record(f"{TRIAL}/views/actual-signal/connectivity.json")["sha256"]
            and set(sampler["bindings"]) == {"stage1", "stage2"}, "Wrong actual sampler binding")
    for stage, binding in sampler["bindings"].items():
        paired, = [row for row in rows if row["semantic"] == "core-d2:r_" + stage + ":0"]
        require(binding["cell"] == json.loads(paired["actual_ff"])[0] and all(binding[key] == paired[value] for key, value in
            (("q", "actual_q"), ("d", "actual_d"), ("clock", "actual_clock"), ("reset_b", "actual_reset_b"))),
                "Sampler witness disagrees with complete actual state map")
    require(wire["schema"] == "pinwheel.streaming-8x4-hold-cap-public-wire.v1"
            and wire["fresh_public_wire_passed"] is True and wire["worker_exit_code"] == 0
            and e.link(wire["transport"])["sha256"] == PINS["digital-02/transport.json"], "Wire transport misbound")
    worker_item = e.link(wire["worker_report"])
    worker = e.read(worker_item["path"])
    worker_dir = relative_name(worker_item["path"]).parent
    request = e.read(worker["configuration"]["path"], worker["configuration"]["sha256"])
    for name, module in tuple(sys.modules.items()):
        if name.startswith("streaming_") and not name.startswith("streaming_8x4_") and getattr(module, "__file__", None):
            path = Path(module.__file__).resolve()
            require(path.is_relative_to(ROOT), "Reader loaded outside the committed source root")
            relative = path.relative_to(ROOT).as_posix()
            if relative in request["source_sha256"]:
                require(e.source[relative] == request["source_sha256"][relative],
                        "Canonical reader differs from pinned worker source: " + relative)
    require(worker["passed"] is True and worker["stage"] == "closed" and worker["qualified"] is False
            and worker["inputs_unchanged"] is True and worker["generated_inputs_unchanged"] is True
            and worker["all_actual_instances_retained"] is True and worker["clock_contraction"] is False
            and worker["export"]["database_sha256"] == ODB and worker["physical_ff_bits"] == 6039
            and worker["actual_functional_instances"] == 42210 and worker["positive_cases"] == wire["positive_cases"] == 35
            and worker["actual_sampler_mutants"] == wire["actual_sampler_mutants"] == 1
            and worker["native_processes"] == wire["native_processes"] == 14
            and worker["physical_edges"] == wire["physical_edges"] == 513297
            and worker["artifact_sha256"] == wire["worker_artifact_sha256"], "Incomplete full public-wire worker")
    for name, pin in worker["artifact_sha256"].items():
        e.record((worker_dir / relative_name(name)).as_posix(), pin)
    check_uart_cases(worker["uart"])
    check_legacy_cases(worker["legacy"])
    check_i2c_cases(worker["i2c"])
    require(all(worker[key]["depth"] == 2 for key in ("uart", "legacy", "i2c"))
            and worker["uart"]["cases"][-1]["mutation"] == worker["sampler_mutation"]
            and worker["traces"] == wire["traces"] and len(wire["traces"]) == 14
            and sum(trace["edges"] for trace in wire["traces"]) == 513297, "Protocol/mutant/trace aggregate differs")
    for trace in wire["traces"]:
        trace_file(e, trace)
    journal = [decode(line) for line in e.path(worker["native_journal"]["path"], worker["native_journal"]["sha256"]).read_text().splitlines()]
    require(len(journal) == 28 and len(worker["native_runs"]) == 14, "Missing wire native process journal")
    for index, record in enumerate(worker["native_runs"]):
        intent, result = journal[2 * index:2 * index + 2]
        expected = {key: record[key] for key in ("index", "scope", "argv", "executable_sha256_before")}
        require(intent == dict(event="intent", **expected) and result == dict(event="result", **record)
                and record["index"] == index and record["native_exit_code"] == 0 and record["client_succeeded"] is True
                and record["argv"] == record["actual_argv"] and record["argv"][0] == request["tools"]["vvp"],
                "Wire native journal/actual invocation differs")
        model = e.record(record["argv"][1], record["executable_sha256_before"])
        require(model["sha256"] == record["executable_sha256_after"], "Executed model changed")
    e.link(wire["worker_log"])
    return worker, wire, dict(state_bits=6039, public_output_bits=24, actual_functional_instances=42210,
        positive_cases=35, sampler_faults_detected=1, native_processes=14, sampled_wire_edges=513297,
        scope="Reopened state pins, protocol verdicts, complete raw traces and native journal; theorem/compiler not rerun")


def reopen_precheck(e, assets):
    aggregate = e.read(f"{TRIAL}/digital-precheck-readback.json")
    exact(aggregate)
    require(aggregate["passed"] is True, "Fresh precheck readback failed")
    e.register(aggregate["verified_file_sha256"])
    report = e.read(f"{TRIAL}/official/rehearsal-tt-precheck-readback.json")
    exact(report)
    require(report["status"] == "pass" and report["exit_code"] == 0 and report["cleanup"]["status"] == "absent"
            and report["frozen_inputs_unchanged"] is True, "Precheck did not close")
    e.artifacts(report)
    lock = e.read("tools/streaming-tt-signoff.json")
    for name, item in lock["support_files"].items():
        e.record(f"{TRIAL}/official/tt/{name}", item["sha256"])
    source = e.path(f"{TRIAL}/official/tt/precheck/precheck.py").read_text()
    require(selected_checks(source, UPSTREAM["pdk"]) == report["expected_checks"] == TT_CHECKS
            and report["support_revision"] == lock["support_commit"]
            and report["pdk_revision"] == lock["pdk_completion_revision"]
            and report["packages"] == lock["precheck_python_packages"]
            and report["python_version"].startswith(lock["python_version_prefix"]), "Pinned official check/runtime inventory differs")
    results = precheck_result(e.path(f"{TRIAL}/official/tt/precheck/reports/results.xml"), TT_CHECKS, 0)
    require(results == report["result"] and results["passed"] is True and results["executed_checks"] == 9,
            "Official JUnit checks differ")
    for role, name in (("gds", f"{TOP}.gds"), ("lef", f"{TOP}.lef"), ("pnl", f"{TOP}.v"), ("info_yaml", "info.yaml")):
        e.record(f"{TRIAL}/official/design/{name}", assets[role]["sha256"])
    conf = e.read(f"{TRIAL}/official/native-config.json")
    native = [decode(line) for line in e.path(f"{TRIAL}/official/native-klayout.jsonl").read_text().splitlines()]
    require(conf["image_id"] == IMAGE and conf["out"] == str(e.origin / TRIAL / "official") and len(native) == 6,
            "Wrong precheck native runtime/journal")
    identities = set()
    for index, name in enumerate(("pin_label_purposes_overlapping_drawing", "sg13cmos5l", "zero_area")):
        intent, result = native[2 * index:2 * index + 2]
        argv = intent["argv"]
        require(intent["event"] == "intent" and result["event"] == "result" and intent["identity"] == result["identity"]
                and intent["identity"] not in identities and result["exit_code"] == 0 and argv.count(IMAGE) == 1
                and argv[argv.index("--network") + 1] == "none" and f"org.pinwheel.signoff_owner={conf['owner']}" in argv
                and f"input={e.origin / TRIAL / 'official/design' / (TOP + '.gds')}" in argv and f"{name}=true" in argv,
                "Wrong native precheck process")
        identities.add(intent["identity"])
        generator = argv[argv.index("-r") + 1]
        categories, markers = drc_report(e.path(f"{TRIAL}/official/tt/precheck/reports/drc_{name}.xml"), generator)
        require(not markers, "Native precheck geometry has markers")
        if name == "sg13cmos5l":
            main, _ = drc_report(e.path(f"{TRIAL}/main-drc-01/drc_sg13cmos5l.xml"), MAIN_GENERATOR)
            require(categories == main and len(categories) == 332, "Native precheck main coverage differs")
    allocation = e.read("physical/streaming_8x4/allocation.json")
    e.record(f"{TRIAL}/official/tt/{allocation['template_path']}", allocation["template_sha256"])
    return dict(checks=9, native_klayout_runs=3, support_revision=report["support_revision"],
                provider_acceptance=False, scope="Pinned local CMOS5L 8x4 tooling rehearsal")


def reopen_timing(e, inventory, context, disconnected):
    timing = e.read(f"{TRIAL}/timing/timing-readback.json")
    exact(timing, "target_gds_sha256")
    e.register(timing["verified_file_sha256"])
    require(timing["status"] == "diagnostic" and timing["model_qualified"] is False and timing["qualified_timing"] is False
            and timing["tapeout_ready"] is False and timing["parasitics_preflight_passed"] is True
            and timing["native_execution_completed"] is True and set(timing["model_matrix"]) == {"MIN", "TYP", "MAX"},
            "Draft timing scope differs")
    native = e.read(f"{TRIAL}/timing/native-readback.json")
    exact(native)
    closed(e.read(native["execution"]["path"], native["execution"]["sha256"]))
    passes = e.array(native["passes"]["path"], native["passes"]["sha256"])
    request = e.read(timing["request"]["path"], timing["request"]["sha256"])
    require(request["source_odb_sha256"] == ODB and request["observer_expectation"]["inventory_sha256"]
            == e.record(f"{TRIAL}/views/actual-signal/inventory.json")["sha256"], "Timing observer identifies another inventory")
    require(timing["target"]["sdc"]["sha256"] == request["layout"]["sdc"]["sha256"]
            == e.record("physical/streaming-tt.sdc")["sha256"], "Selected rehearsal SDC assumptions differ")
    require(passes == timing["native_passes"], "Timing native passes differ")
    summaries = {}
    for model, row in sorted(timing["model_matrix"].items()):
        require(row["assessment"]["status"] == "passed" and row["assessment"]["failures"] == []
                and set(row["cases"]) == set(CORNERS) and row["spef_validation"]["status"] == "pass", "Incomplete draft timing matrix")
        e.link(row["spef"])
        model_summaries = {}
        for corner in CORNERS:
            case, counts = row["cases"][corner], row["assessment"]["corners"][corner]
            directory = f"{TRIAL}/timing/run/{model}/flow/02-openroad-stapostpnr/{corner}"
            names = ["sta.log", "checks.rpt", "clock.rpt", "unpropagated.rpt", "violator_list.rpt",
                     *(f"{kind}.{mode}.rpt" for mode in ("min", "max") for kind in ("ws", "wns", "tns")), "min.rpt", "max.rpt"]
            raw = {name: e.path(f"{directory}/{name}").read_text() for name in names}
            metrics = {f"timing__{purpose}__{kind}__corner:{corner}": case[f"{purpose}_{kind}_ns"]
                       for purpose in ("hold", "setup") for kind in ("ws", "wns", "tns")}
            observed = raw_timing(e.path(f"{directory}/sta.log").parent, corner, metrics, {})
            require(all(observed[key] == case[key] for key in observed)
                    and all(counts[key] == 0 for key in ("hold_violations", "setup_violations", "capacitance_violations",
                                                       "slew_violations", "fanout_violations"))
                    and case["hold_ws_ns"] > 0 and case["setup_ws_ns"] > 0, "Draft raw timing/counters differ")
            require(extra_checks(raw["checks.rpt"], raw["violator_list.rpt"], counts) == case["ancillary_checks"]
                    and check_observer(raw["sta.log"], request["observer_expectation"], corner,
                                       raw["clock.rpt"], raw["unpropagated.rpt"]) == case["clock"], "Draft check/clock context differs")
            annotation = dict(status="pass", **annotation_evidence(raw["checks.rpt"], corner, context, disconnected))
            require(annotation == case["annotation"] and annotation["complete_for_consumed_nets"] is True,
                    "Consumed-net annotation differs")
            model_summaries[corner] = dict(hold_ns=case["hold_ws_ns"], setup_ns=case["setup_ws_ns"],
                hold_setup_slew_cap_fanout_violations=0, consumed_net_annotation_complete=True)
        summaries[model] = model_summaries
    return dict(scenarios=9, matrix=summaries, model_qualified=False, qualified_timing=False,
                dedicated_recovery_removal_pulse_width="open_no_dedicated_reports",
                full_unconstrained_endpoint_inventory="open_check_setup_diagnostic_only",
                scope="Draft RC sensitivity and 20ns rehearsal constraints; selected raw timing/annotation reports, not qualified STA")


def reopen_bringup(e, expected, worker, wire, source):
    receipt = e.read(BRINGUP, expected)
    e.register(receipt["verified_file_sha256"])
    exact(receipt, "target_gds_sha256")
    require(receipt["schema"] == "pinwheel.streaming-8x4-hold-cap-bringup.v1" and receipt["passed"] is True
            and receipt["exit_code"] == 0 and receipt["board_exercised"] is False and receipt["positive_cases"] == 4
            and 0 < receipt["elapsed_seconds"] <= receipt["timeout_seconds"] <= 300
            and e.link(receipt["wire"])["sha256"] == PINS["digital-02/wire/report.json"]
            and receipt["worker"] == wire["worker_report"]
            and e.name(receipt["producer"]["path"]) == BRINGUP_SOURCE
            and e.link(receipt["producer"])["sha256"] == source[BRINGUP_SOURCE], "Bring-up target/source/worker differs")
    model = e.link(receipt["model"])
    require(model["sha256"] == worker["artifact_sha256"]["unchanged.vvp"]
            and receipt["model"]["path"] == worker["executables"]["unchanged"]
            and worker["input_sha256_before"][receipt["vvp"]["path"]] == receipt["vvp"]["sha256"], "Bring-up model/runtime differs")
    fixture_item, dry_item = e.link(receipt["fixture"]), e.link(receipt["dry_run"])
    fixture, dry = e.read(fixture_item["path"]), e.read(dry_item["path"])
    require(e.link(receipt["log"])["sha256"] == dry_item["sha256"] and fixture == bringup_fixture()
            and dry["schema"] == "pinwheel.streaming-ready-pin-dry-run.v1" and dry["passed"] is True
            and dry["board_exercised"] is False and dry["scope"] == "Local public-pin simulation"
            and dry["model_sha256"] == model["sha256"] and dry["cases"] == receipt["cases"], "Bring-up fixture/raw stdout differs")
    cases = dry["cases"]
    require(set(cases) == {"uart_rx", "spi_duplex", "i2c_read", "i2c_write"}
            and all(row["matching_release"] is True and type(row["edges"]) is int and row["edges"] > 0 for row in cases.values()),
            "Incomplete bring-up cases")
    for name in ("uart_rx", "spi_duplex"):
        require(cases[name]["rx_hex"] == fixture[name]["expected_rx_hex"], "Bring-up received bytes differ")
    require(cases["spi_duplex"]["tx_hex"] == fixture["spi_duplex"]["tx_hex"], "SPI transmit bytes differ")
    for name, field in (("i2c_read", "expected_rx_hex"), ("i2c_write", "tx_hex")):
        require(cases[name]["data_hex"] == fixture[name][field]
                and cases[name]["address_7bit"] == fixture[name]["address_7bit"]
                and cases[name]["stream_cells"] == fixture[name]["start_cells"], "I2C bring-up differs")
    require(cases["i2c_read"]["target_stretch_edges"] > 0 and cases["i2c_write"]["target_stretch_edges"] == 0,
            "I2C stretch/clean-write evidence differs")
    return dict(cases=4, model_sha256=model["sha256"], board_exercised=False), fixture_item, dry_item


def source_files(root, names):
    return {name: file_record(root, name, digest(local_path(root, name)))["sha256"] for name in sorted(names)}


def validate_source_map(source):
    required = {"scripts/streaming_8x4_hold_cap_rehearsal.py", BRINGUP_SOURCE, "physical/streaming-tt.sdc",
                *TRACKED_ASSETS.values(), *DEMO_ASSETS.values()}
    require(type(source) is dict and required <= source.keys(), "Missing mandatory committed source bindings")
    for name, pin in source.items():
        path = relative_name(name)
        require(hash_string(pin) and (path.parts[0] in {"scripts", "physical", "tools"} or name in required),
                "Unsafe or unexpected source snapshot member")
    # A resealed manifest must not omit the code that interprets its evidence.
    # Derive this set from loaded modules too, rather than trusting its file list.
    for module in tuple(sys.modules.values()):
        value = getattr(module, "__file__", None)
        if value:
            path = Path(value).absolute()
            if path.is_relative_to(ROOT) and path.suffix == ".py" and path.is_file():
                relative = path.relative_to(ROOT).as_posix()
                if path.parts[len(ROOT.parts)] in {"scripts", "physical", "tools"}:
                    require(relative in source, "Loaded verifier helper omitted from source snapshot: " + relative)


def committed_sources(root, commit):
    require(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip() == commit,
            "Assemble from the selected committed HEAD")
    # Include the complete tracked Python/physical/tool source roots. This avoids
    # guessing dynamically selected helper imports and remains a bounded source snapshot.
    names = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", commit, "--", "scripts", "physical", "tools",
        *TRACKED_ASSETS.values(), *DEMO_ASSETS.values(), "LICENSE"], cwd=root, text=True).splitlines()
    require(str(Path(__file__).resolve().relative_to(ROOT)) in names and BRINGUP_SOURCE in names,
            "Commit the actual assembler and bring-up producer first")
    source = source_files(root, names)
    validate_source_map(source)
    for name, expected in source.items():
        blob = subprocess.check_output(["git", "show", f"{commit}:{name}"], cwd=root, timeout=15)
        require(hashlib.sha256(blob).hexdigest() == expected, "Source differs from selected HEAD: " + name)
    return source


def manifest_for(workspace, origin, commit, source, bringup_sha):
    revision_label(commit)
    e = Evidence(workspace, origin, source)
    assets, inventory, context, disconnected = reopen_views(e)
    for role, name in {**TRACKED_ASSETS, **DEMO_ASSETS}.items():
        assets[role] = e.record(name, source[name])
    assets["sdc"] = e.record("physical/streaming-tt.sdc", source["physical/streaming-tt.sdc"])
    require(re.search(r"(?m)^  clock_hz: 0\s*$", e.path("info.yaml").read_text()), "Qualified clock must remain unset")
    physical = reopen_physical(e, assets)
    worker, wire, digital = reopen_digital(e, assets)
    precheck = reopen_precheck(e, assets)
    timing = reopen_timing(e, inventory, context, disconnected)
    bringup, assets["bringup_fixture"], assets["bringup_dry_run"] = reopen_bringup(e, bringup_sha, worker, wire, source)
    payload = {role: dict(assets[role], path="package/" + target) for role, target in PAYLOAD.items()}
    for name, row in e.files.items():
        file_record(workspace, name, row["sha256"])
    return dict(schema=SCHEMA, source_commit=commit, source_sha256=source, origin_workspace=str(origin),
        target_odb_sha256=ODB, gds_sha256=GDS, bringup_receipt_sha256=bringup_sha, upstream=UPSTREAM,
        assets=assets, payload=payload, evidence=dict(sorted(e.files.items())), excluded_provenance=e.excluded(),
        checks=dict(physical=physical, digital=digital, tt_precheck=precheck, draft_timing=timing, bringup=bringup),
        rehearsal_decision="go", fabrication_decision="no-go", open_gates=list(OPEN_GATES),
        tapeout_ready=False, shuttle_submission_performed=False, provider_acceptance=False, custody=CUSTODY)


def assemble(workspace, bundle, source_commit, bringup_sha):
    require(hash_string(bringup_sha), "Exact bring-up receipt SHA-256 required")
    source_commit = revision_label(source_commit)
    relative = bundle.relative_to(workspace).as_posix()
    require(relative_name(relative).is_relative_to(relative_name(TRIAL)) and local_path(workspace, relative) == bundle
            and not bundle.exists(), "Use a fresh ignored candidate bundle path")
    source = committed_sources(ROOT, source_commit)
    manifest = manifest_for(workspace, workspace, source_commit, source, bringup_sha)
    bundle.mkdir(parents=True, exist_ok=False)
    for entry in manifest["evidence"].values():
        copy_checked(local_path(workspace, entry["path"]), local_path(bundle / "evidence", entry["path"]), entry)
    for role, entry in manifest["payload"].items():
        copy_checked(local_path(workspace, manifest["assets"][role]["path"]), local_path(bundle, entry["path"]), entry)
    for name, expected in source.items():
        entry = file_record(ROOT, name, expected)
        copy_checked(local_path(ROOT, name), local_path(bundle / "source", name), entry)
    path = bundle / "manifest.json"
    with path.open("x") as stream:
        json.dump(manifest, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write("\n")
    return verify(bundle, digest(path))


def verify(bundle, expected):
    require(bundle.is_dir() and not bundle.is_symlink() and hash_string(expected), "Invalid bundle or manifest SHA-256")
    file_record(bundle, "manifest.json", expected)
    manifest = read_json(local_path(bundle, "manifest.json"))
    require(manifest["schema"] == SCHEMA, "Wrong candidate rehearsal schema")
    source = manifest["source_sha256"]
    validate_source_map(source)
    require(source_files(ROOT, source) == source, "Running verifier/source differs from committed snapshot")
    require(source_files(local_path(bundle, "source"), source) == source, "Packaged committed source differs")
    reopened = manifest_for(local_path(bundle, "evidence"), Path(manifest["origin_workspace"]), manifest["source_commit"],
                            source, manifest["bringup_receipt_sha256"])
    require(manifest == reopened, "Manifest differs from independently reopened portable evidence")
    validate_source_map(source)
    for entry in manifest["payload"].values():
        require(file_spec(bundle, entry) == entry, "Packaged handoff asset differs")
    files = {"manifest.json", *(item["path"] for item in manifest["payload"].values()),
             *("evidence/" + name for name in manifest["evidence"]), *("source/" + name for name in source)}
    dirs = {parent.as_posix() for name in files for parent in relative_name(name).parents if parent.parts}
    members = {path.relative_to(bundle).as_posix(): path for path in bundle.rglob("*")}
    require(members.keys() == files | dirs and all(not path.is_symlink()
            and (path.is_file() if name in files else path.is_dir()) for name, path in members.items()),
            "Unexpected, missing or unsafe bundle members")
    return dict(verified=True, source_commit=manifest["source_commit"], manifest_sha256=expected,
        target_odb_sha256=ODB, gds_sha256=GDS, rehearsal_decision="go", fabrication_decision="no-go",
        open_gates=list(OPEN_GATES), tapeout_ready=False, evidence_files=len(manifest["evidence"]),
        payload_files=len(manifest["payload"]), source_files=len(source), custody=CUSTODY)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_subparsers(dest="command", required=True)
    build = actions.add_parser("assemble")
    build.add_argument("bundle", type=Path)
    build.add_argument("--source-commit", required=True)
    build.add_argument("--bringup-sha256", required=True)
    check = actions.add_parser("verify")
    check.add_argument("bundle", type=Path)
    check.add_argument("--manifest-sha256", required=True)
    args = parser.parse_args()
    try:
        bundle = args.bundle.absolute()
        result = assemble(ROOT, bundle, args.source_commit, args.bringup_sha256) if args.command == "assemble" else verify(
            bundle, args.manifest_sha256)
    except (OSError, ValueError, TypeError, KeyError, ParseError, subprocess.SubprocessError) as exc:
        parser.exit(2, f"Hold/cap rehearsal rejected: {exc}\n")
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
