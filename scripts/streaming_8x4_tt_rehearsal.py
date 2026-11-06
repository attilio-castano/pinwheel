"""Assemble and reopen the local Pinwheel Tiny Tapeout rehearsal package."""

import argparse
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
from xml.etree import ElementTree

import streaming_8x4_enclosure_admission as physical_reader
import streaming_tt_signoff as tt_reader
from streaming_8x4_enclosure_admission import (
    ENCLOSURE_GENERATOR, ENCLOSURE_RULES, MAIN_DECK, MAIN_GENERATOR,
    PREFILL_ODB, TOP, drc_report, validate_antenna,
)


ROOT = Path(__file__).resolve().parents[1]
INPUT_SCHEMA = "pinwheel.streaming-8x4-tt-rehearsal-input.v1"
MANIFEST_SCHEMA = "pinwheel.streaming-8x4-tt-rehearsal.v1"
PACKAGE = {
    "gds": f"gds/{TOP}.gds", "lef": f"lef/{TOP}.lef",
    "nl": f"verilog/{TOP}.v", "pnl": f"verilog/{TOP}.power.v",
    "info_yaml": "info.yaml", "docs_info_md": "docs/info.md", "license": "LICENSE",
}
TRACKED_ASSETS = {
    "info_yaml": "info.yaml", "docs_info_md": "docs/info.md", "license": "LICENSE",
    "workflow": ".github/workflows/tt-rehearsal.yml", "allocation": "physical/streaming_8x4/allocation.json",
}
UPSTREAM = {
    "shuttle": "ttihp27a", "pdk": "ihp-sg13cmos5l", "tiles": "8x4", "top": TOP,
    "action_revision": "e7a50f8f46f9f8df4b2c9935bfeb1cbc6b6ae4f6",
    "support_revision": "37f5534aa57beaa6f079847b2c7fcbd9a75b2392",
    "rehearsal_support_revision": "d66cf179e7bc4d296362ab7e2e3b344dc3c4f665",
}
REQUIRED_ASSETS = {*PACKAGE, "odb", "workflow"}
OPTIONAL_ASSETS = {"def", "cdl", "sdc", "allocation"}
VIEW_KEYS = {"lef": "lef", "def": "def", "nl": "verilog", "pnl": "powered_verilog", "cdl": "cdl", "sdc": "sdc"}
RECEIPT_ROLES = {"route", "route_execution", "native", "g4_transport", "g4_wire",
                 "bringup_fixture", "bringup_dry_run", "release_decision"}
NATIVE_CHECKS = ("views", "transistor_lvs", "pg_connectivity", "pin_geometry", "tt_precheck")
NATIVE_SCHEMA = "pinwheel.e982-tt-native-rehearsal.v1"
NATIVE_LEAVES = dict(zip(NATIVE_CHECKS, (
    "rehearsal-view-readback.json", "rehearsal-lvs-readback.json", "rehearsal-pg-readback.json",
    "rehearsal-pin-readback.json", "rehearsal-tt-precheck-readback.json",
)))
TT_CHECKS = ["KLayout pin label overlapping drawing", "KLayout SG13CMOS5L DRC", "KLayout zero area",
             "KLayout Checks", "Pin check", "Boundary check", "Layer check", "Cell name check", "Analog pin check"]
G4_SCHEMAS = {
    "g4_transport": "pinwheel.streaming-8x4-e982-g4-transport.v1",
    "g4_wire": "pinwheel.streaming-8x4-e982-g4-wire.v1",
}
BRINGUP_CASES = ("uart_rx", "spi_duplex", "i2c_read", "i2c_write")
RELEASE_BLOCKERS = {"qualified_cmos5l_timing", "shuttle_8x4_custom_gds_admission"}
OUTSIDE_REHEARSAL = (
    "qualified_extraction", "qualified_timing", "fresh_source_to_gds_rebuild", "shuttle_allocation",
    "live_shuttle_precheck", "shuttle_submission", "fabrication_acceptance",
)
SCOPE = {
    "physical": "Exact post-fill candidate and the named deck scopes",
    "digital": "Local transport and finite wire receipts, with separate sealed historical proof provenance",
    "precheck": "Historical support-tools rehearsal; current shuttle tooling is identified separately",
    "bringup": "Local public-pin simulation on the current G4 model; no board result",
    "package": "Local handoff copies; inspect the sealed evidence from the original workspace",
}
ROUTE_REPORTS = {
    "main_drc": ("drc_sg13cmos5l.xml", "drc_report_sha256"),
    "enclosure_subset": ("enclosure.xml", "enclosure_report_sha256"),
    "foundry_antenna": ("antenna.xml", "foundry-antenna_report_sha256"),
    "openroad_antenna": ("openroad-antenna.log", "openroad_antenna_sha256"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def json_object(pairs):
    value = dict(pairs)
    require(len(value) == len(pairs), "Duplicate JSON key")
    return value


def invalid_constant(value):
    raise ValueError(f"Nonfinite JSON constant: {value}")


def decode_json(data):
    value = json.loads(data, object_pairs_hook=json_object, parse_constant=invalid_constant)
    require(type(value) is dict, "Expected JSON object")
    return value


def read_json(path):
    return decode_json(path.read_bytes())


def relative_name(value):
    require(type(value) is str and value and "\\" not in value
            and all(ord(char) >= 32 and ord(char) != 127 for char in value), "Invalid relative path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and path.as_posix() == value and path.parts
            and ".." not in path.parts, f"Noncanonical relative path: {value}")
    return path


def local_path(root, relative):
    path = root
    for name in relative_name(relative).parts:
        path = path / name
        require(not path.is_symlink(), f"Symbolic link is outside the package contract: {relative}")
    return path


def hash_string(value):
    return type(value) is str and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def stat_identity(info):
    return info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def file_record(root, relative, expected):
    path = local_path(root, relative)
    require(path.is_file() and hash_string(expected), f"Missing regular file or SHA-256: {relative}")
    before = path.stat()
    actual = digest(path)
    require(stat_identity(path.stat()) == stat_identity(before) and actual == expected,
            f"File changed or SHA-256 differs: {relative}")
    return {"path": relative, "sha256": actual, "bytes": before.st_size}


def file_spec(root, entry):
    require(type(entry) is dict and set(entry) in ({"path", "sha256"}, {"path", "sha256", "bytes"}),
            "Each file binding requires path and SHA-256")
    actual = file_record(root, entry["path"], entry["sha256"])
    require("bytes" not in entry or type(entry["bytes"]) is int and entry["bytes"] == actual["bytes"],
            f"File byte count differs: {entry['path']}")
    return actual


def receipt_record(workspace, entry):
    """Normalize exact producer paths inside this worktree to relative paths."""
    require(type(entry) is dict and type(entry.get("path")) is str, "Invalid receipt artifact binding")
    path = Path(entry["path"])
    if path.is_absolute():
        entry = dict(entry, path=path.relative_to(workspace).as_posix())
    return file_spec(workspace, entry)


def role_records(root, entries, required, optional):
    require(type(entries) is dict and required <= entries.keys() <= required | optional,
            f"Unknown or missing file roles: {required}")
    result = {role: file_spec(root, entry) for role, entry in sorted(entries.items())}
    require(len({entry["path"] for entry in result.values()}) == len(result), "Aliased file roles")
    return result


def check_state(status, evidence=()):
    return {"status": status, "evidence": list(evidence)}


def integer_zero(value):
    return type(value) is int and value == 0


def route_checks(workspace, assets, receipts):
    names = ("route", *ROUTE_REPORTS)
    if "route" not in receipts and "route_execution" not in receipts:
        return {name: check_state("open") for name in names}
    require({"route", "route_execution"} <= receipts.keys(), "Route readback and native execution must be joined")
    readback = read_json(local_path(workspace, receipts["route"]["path"]))
    execution = read_json(local_path(workspace, receipts["route_execution"]["path"]))
    target, gds = (assets[role]["sha256"] for role in ("odb", "gds"))
    require(readback["postfill_odb_sha256"] == execution["postfill_odb"]["sha256"] == target
            and readback["postfill_gds_sha256"] == execution["gds_sha256"] == gds,
            "Route evidence is for another post-fill ODB or GDS")
    require(readback["target_odb_sha256"] == execution["target_odb_sha256"] == PREFILL_ODB
            and execution["frozen_inputs_unchanged"] is True and execution["deck_sha256"] == MAIN_DECK
            and execution["route_stops_at"] == "OpenROAD.FillInsertion",
            "Wrong route scope, source, or deck custody")
    if "def" in assets:
        require(execution["def_sha256"] == assets["def"]["sha256"], "Route DEF and release DEF differ")
    phases = execution["phases"]
    require([phase["phase"] for phase in phases] == ["route", "streamout", "enclosure", "foundry-antenna", "drc"]
            and all(phase["status"] == "completed" and integer_zero(phase["exit_code"])
                    and phase["container_absent"] is True
                    and 0 < phase["elapsed_seconds"] <= phase["timeout_seconds"]
                    and math.isfinite(phase["timeout_seconds"]) for phase in phases),
            "Incomplete route or physical execution")
    require(integer_zero(readback["route_exit_code"]) and readback["physical_checks_pass"] is True
            and readback["fixed_net840_DEF_preserved"] is True
            and readback["route_diagnostics_match_seven_known_warnings"] is True
            and not readback["other_route_diagnostics"]
            and integer_zero(readback["route_metrics"]["route__drc_errors"]), "Route readback did not close")

    report_dir = relative_name(receipts["route_execution"]["path"]).parent
    reports = {role: file_record(workspace, (report_dir / filename).as_posix(), execution[digest_key])
               for role, (filename, digest_key) in ROUTE_REPORTS.items()}
    main = local_path(workspace, reports["main_drc"]["path"])
    enclosure = local_path(workspace, reports["enclosure_subset"]["path"])
    antenna = local_path(workspace, reports["foundry_antenna"]["path"])
    main_names, main_items = drc_report(main, MAIN_GENERATOR)
    enclosure_names, enclosure_items = drc_report(enclosure, ENCLOSURE_GENERATOR)
    antenna_names, antenna_items = drc_report(
        antenna, "/work/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/drc/rule_decks/antenna.drc")
    require(len(main_names) == 332 and not main_items and enclosure_names == set(ENCLOSURE_RULES)
            and not enclosure_items and len(antenna_names) == 23 and not antenna_items,
            "Raw layout reports have missing coverage or nonzero violations")
    log = local_path(workspace, reports["openroad_antenna"]["path"]).read_text()
    validate_antenna(log, explicit=True, count=2)
    require("\nNET840_WIRE_TYPE FIXED\n" in log
            and log.endswith("ARC_WHOLE 0\nARC_NET840 0\nANTENNA_COMPLETE\n"),
            "Raw antenna target or terminal result differs")
    return {"route": check_state("passed", [receipts["route"], receipts["route_execution"]]),
            **{name: check_state("passed", [receipts["route_execution"], report])
               for name, report in reports.items()}}


def status(value):
    names = {"pass": "passed", "passed": "passed", "fail": "failed", "failed": "failed", "open": "open",
             "missing": "open", "blocked": "open", "not_run": "open", "diagnostic": "diagnostic"}
    require(type(value) is str and value in names, "Unknown receipt check status")
    return names[value]


def named_file(workspace, records, filename):
    files = [entry["path"] for entry in records if PurePosixPath(entry["path"]).name == filename]
    require(len(files) == 1, f"Expected one sealed {filename}")
    return local_path(workspace, files[0])


def native_scope(workspace, name, check, records, assets, upstream):
    if name == "views":
        views = check["view_sha256"]
        keys = {entry["sha256"] for entry in records}
        for role, view in VIEW_KEYS.items():
            if role in assets and (role != "sdc" or view in views):
                require(views.get(view) == assets[role]["sha256"]
                        and (role == "def" or assets[role]["sha256"] in keys),
                        f"Release {role} differs from the native view receipt")
        final = read_json(named_file(workspace, records, "final-views-native.json"))
        require(final["completed"] is True and final["source_odb_unchanged"] is True
                and final["source_odb_sha256"] == assets["odb"]["sha256"], "Native views are not from the sealed ODB")
    elif name == "transistor_lvs":
        result = read_json(named_file(workspace, records, "lvs-result.json"))
        native = read_json(named_file(workspace, records, "native-result.json"))
        log = named_file(workspace, records, "lvs.native.log").read_text()
        require("cdl" in assets and check["reference_cdl_sha256"] == assets["cdl"]["sha256"]
                and native["completed"] is True and native["inputs_unchanged"] is True
                and native["source_odb_sha256"] == assets["odb"]["sha256"]
                and check["top"] == result["result"]["top"] == TOP and result["result"]["passed"] is True
                and result["report_sha256"] == digest(named_file(workspace, records, "lvs.lvsdb"))
                and check["circuit_pairs"] == len(result["result"]["circuits"]) > 0
                and "Selected NET_ONLY option: false" in log and "Congratulations! Netlists match." in log,
                "LVS evidence lacks exact transistor top/reference/results")
    elif name == "pg_connectivity":
        native = read_json(named_file(workspace, records, "native.json"))
        require(native["completed"] is True and native["canonical_inventory_rederived"] is True
                and native["geometric_open_path_connectivity"] is True and native["source_odb_unchanged"] is True
                and native["inventory_totals"] == check["census_totals"]
                and set(check["rails"]) == {"VPWR", "VGND"} and all(
                    rail["bterms"] == 1 and rail["iterms"] == check["census_totals"]["instances"]
                    for rail in check["rails"].values()), "Incomplete geometric PG connectivity")
        require(check["shorts_checked"] is False and check["ir_drop_qualified"] is False,
                "PG observation exceeds geometric open-path scope")
    elif name == "pin_geometry":
        geom = check["measurement"]["geometry"]
        require(all(geom[key] is True for key in ("exact_top_bbox_8x4", "exact_rectangular_prBoundary_189_4",
                    "all43_exact_Metal4_pin_rectangles_and_50_25_labels")) and len(geom["pins"]) == 43,
                "Incomplete public pin geometry")
        if "allocation" in assets:
            allocation = read_json(local_path(workspace, assets["allocation"]["path"]))
            require(check["allocation_sha256"] == assets["allocation"]["sha256"]
                    and check["template_sha256"] == allocation["template_sha256"]
                    and allocation["tiles"] == upstream["tiles"]
                    and allocation["support_commit"] == upstream["rehearsal_support_revision"],
                    "Pin geometry and allocation template differ")
    elif name == "tt_precheck":
        keys = {entry["sha256"] for entry in records}
        require(all(assets[role]["sha256"] in keys for role in ("gds", "lef", "info_yaml", "pnl"))
                and check.get("support_revision") == upstream["rehearsal_support_revision"],
                "TT precheck does not consume the release views, metadata or pinned rehearsal revision")
        result = tt_reader.precheck_result(named_file(workspace, records, "results.xml"), TT_CHECKS, check["exit_code"])
        require(check["expected_checks"] == TT_CHECKS and result == check["result"] and result["passed"] is True
                and check["lef_sha256"] == assets["lef"]["sha256"] and check["info_yaml_sha256"] == assets["info_yaml"]["sha256"]
                and check["action_revision"] is None
                and check["frozen_inputs_unchanged"] is True and check["cleanup"]["status"] == "absent"
                and check["native"]["closed_processes"] == 3 and check["native"]["passed"] is True
                and set(check["native"]["reports"]) == {"pin_label_purposes_overlapping_drawing", "sg13cmos5l", "zero_area"}
                and check["native"]["journal_sha256"] == digest(named_file(workspace, records, "native-klayout.jsonl")),
                "Incomplete or failing raw TT precheck evidence")
        for label, report in check["native"]["reports"].items():
            path = named_file(workspace, records, f"drc_{label}.xml")
            xml = ElementTree.parse(path).getroot()
            require(integer_zero(report["exit_code"]) and report["report_sha256"] == digest(path)
                    and xml.tag == "report-database" and xml.findtext("top-cell") == TOP
                    and xml.find("items") is not None and not list(xml.find("items")),
                    f"Missing or failing native precheck XML: {label}")


def native_checks(workspace, assets, receipts, upstream):
    if "native" not in receipts:
        return {name: check_state("open") for name in NATIVE_CHECKS}
    receipt = receipts["native"]
    raw = read_json(local_path(workspace, receipt["path"]))
    require(raw["schema"] == NATIVE_SCHEMA and raw["target_odb_sha256"] == assets["odb"]["sha256"]
            and raw["gds_sha256"] == assets["gds"]["sha256"], "Native receipt target differs")
    require(type(raw["checks"]) is dict and raw["checks"].keys() <= set(NATIVE_CHECKS), "Unknown native checks")
    results = {}
    for name in NATIVE_CHECKS:
        if name not in raw["checks"]:
            results[name] = check_state("open", [receipt])
            continue
        check = raw["checks"][name]
        state = status(check["status"])
        for key, role in (("target_odb_sha256", "odb"), ("gds_sha256", "gds")):
            require(key not in check or check[key] == assets[role]["sha256"], f"Stale native check: {name}")
        records = [receipt_record(workspace, entry) for entry in check.get("artifacts", [])]
        if state == "passed":
            require(records and len({entry["path"] for entry in records}) == len(records),
                    f"Passing native check lacks unique sealed artifacts: {name}")
            native_scope(workspace, name, check, records, assets, upstream)
            leaf = named_file(workspace, records, NATIVE_LEAVES[name])
            original = read_json(leaf)
            require({key: value for key, value in original.items() if key != "artifacts"}
                    == {key: value for key, value in check.items() if key != "artifacts"},
                    f"Native check summary differs from sealed primary receipt: {name}")
            require([record for record in records if record["path"] != leaf.relative_to(workspace).as_posix()]
                    == [receipt_record(workspace, entry) for entry in original.get("artifacts", [])],
                    f"Native check artifact list differs from primary receipt: {name}")
        results[name] = check_state(state, [receipt, *records])
    return results


def digital_checks(workspace, assets, receipts):
    results = {}
    for name, schema in G4_SCHEMAS.items():
        if name not in receipts:
            results[name] = check_state("open")
            continue
        receipt = receipts[name]
        raw = read_json(local_path(workspace, receipt["path"]))
        require(raw["schema"] == schema and raw["target_odb_sha256"] == assets["odb"]["sha256"]
                and raw["target_gds_sha256"] == assets["gds"]["sha256"]
                and raw["netlist_sha256"] == assets["nl"]["sha256"]
                and raw["powered_netlist_sha256"] == assets["pnl"]["sha256"],
                f"Stale digital receipt: {name}")
        require(type(raw["passed"]) is bool and raw["full_tapeout_ready"] is False,
                f"Invalid actual digital outcome: {name}")
        pins = raw["verified_file_sha256"]
        require(type(pins) is dict and pins, f"Missing digital receipt custody: {name}")
        local = []
        for path, expected in sorted(pins.items()):
            # The old proof remains a separately sealed historical authority.
            # Reopen current-worktree files without traversing its absolute paths.
            if Path(path).is_relative_to(workspace):
                local.append(receipt_record(workspace, {"path": path, "sha256": expected}))
        keys = {entry["sha256"] for entry in local}
        if raw["passed"]:
            require(all(assets[role]["sha256"] in keys for role in ("odb", "gds", "nl", "pnl"))
                    and ("sdc" not in assets or assets["sdc"]["sha256"] in keys),
                    f"Digital receipt lacks local candidate view seals: {name}")
            if name == "g4_transport":
                require(all(raw[key] is True for key in ("functional_correspondence_transported",
                            "named_functional_graph_equal", "state_transition_and_output_model_equal",
                            "clock_and_reset_cones_equal")) and raw["state_bits"] == 6039
                        and raw["public_output_bits"] == 24, "Incomplete functional transport scope")
            else:
                require("g4_transport" in receipts and results["g4_transport"]["status"] == "passed"
                        and receipt_record(workspace, raw["transport"]) == receipts["g4_transport"],
                        "Wire evidence uses a different functional transport receipt")
                require(raw["fresh_public_wire_passed"] is True and integer_zero(raw["worker_exit_code"])
                        and raw["positive_cases"] == 35 and raw["actual_sampler_mutants"] == 1
                        and raw["native_processes"] == 14 and set(raw["protocols"]) == {"UART", "SPI", "I2C", "JTAG"},
                        "Incomplete finite public-wire scope")
                worker = receipt_record(workspace, raw["worker_report"])
                worker_dir = relative_name(worker["path"]).parent
                report = read_json(local_path(workspace, worker["path"]))
                require(report["schema"] == "pinwheel.streaming-tt-public-wire.v1"
                        and report["stage"] == "closed" and report["passed"] is True
                        and report["qualified"] is False and report["physical_acceptance_claim"] is False
                        and report["export"]["database_sha256"] == assets["odb"]["sha256"]
                        and report["artifact_sha256"] == raw["worker_artifact_sha256"],
                        "Fresh wire worker differs from the sealed wrapper result")
                local.extend(file_record(workspace, (worker_dir / relative_name(path)).as_posix(), expected)
                             for path, expected in sorted(report["artifact_sha256"].items()))
        results[name] = check_state("passed" if raw["passed"] else "failed", [receipt, *local])
    return results


def bringup_checks(workspace, receipts, checks):
    names = ("bringup_fixture", "bringup_dry_run")
    results = {name: check_state("open") for name in names}
    if "bringup_fixture" not in receipts:
        require("bringup_dry_run" not in receipts, "Bring-up model result requires its fixture")
        return results
    fixture_record = receipts["bringup_fixture"]
    fixture = read_json(local_path(workspace, fixture_record["path"]))
    require(fixture["schema"] == "pinwheel.streaming-ready-board-bringup.v1" and fixture["top_module"] == TOP
            and fixture["queue_depth"] == 2 and fixture["warm_reset_request_hex"] == "a7270000000000000000000000000000000000009859"
            and all(fixture[name]["words_hex"] and all(re.fullmatch(r"[0-9a-f]{16}", word)
                    for word in fixture[name]["words_hex"]) for name in BRINGUP_CASES), "Wrong depth-two bring-up fixture")
    results["bringup_fixture"] = check_state("passed", [fixture_record])
    if "bringup_dry_run" not in receipts:
        return results

    dry_record = receipts["bringup_dry_run"]
    dry = read_json(local_path(workspace, dry_record["path"]))
    require(checks["g4_wire"]["status"] == "passed", "Bring-up requires the fresh passing G4 wire model")
    wire = read_json(local_path(workspace, receipts["g4_wire"]["path"]))
    worker_record = receipt_record(workspace, wire["worker_report"])
    worker = read_json(local_path(workspace, worker_record["path"]))
    model_path = (relative_name(worker_record["path"]).parent / "unchanged.vvp").as_posix()
    model = file_record(workspace, model_path, wire["worker_artifact_sha256"]["unchanged.vvp"])
    require(worker["artifact_sha256"]["unchanged.vvp"] == model["sha256"] == dry["model_sha256"],
            "Bring-up simulator differs from the current G4 worker")
    require(dry["schema"] == "pinwheel.streaming-ready-pin-dry-run.v1" and dry["passed"] is True
            and dry["board_exercised"] is False and dry["scope"] == "Local public-pin simulation",
            "Bring-up report exceeds the observed simulator scope")
    cases = dry["cases"]
    require(set(cases) == set(BRINGUP_CASES) and all(row["matching_release"] is True
            and type(row["edges"]) is int and row["edges"] > 0 for row in cases.values()), "Incomplete bring-up cases")
    require(cases["uart_rx"]["rx_hex"] == fixture["uart_rx"]["expected_rx_hex"]
            and cases["spi_duplex"]["tx_hex"] == fixture["spi_duplex"]["tx_hex"]
            and cases["spi_duplex"]["rx_hex"] == fixture["spi_duplex"]["expected_rx_hex"],
            "UART or SPI observed payload differs from the board fixture")
    for name, payload in (("i2c_read", "expected_rx_hex"), ("i2c_write", "tx_hex")):
        case = cases[name]
        require(case["address_7bit"] == fixture[name]["address_7bit"] and case["data_hex"] == fixture[name][payload]
                and case["stream_cells"] == fixture[name]["start_cells"], "I2C observed fixture differs")
    results["bringup_dry_run"] = check_state("passed", [fixture_record, dry_record, worker_record, model])
    return results


def release_decision(workspace, assets, receipts, checks):
    if "release_decision" not in receipts:
        return check_state("open"), None
    receipt = receipts["release_decision"]
    value = read_json(local_path(workspace, receipt["path"]))
    require(value["schema"] == "pinwheel.tt-rehearsal-decision.v1"
            and value["target_odb_sha256"] == assets["odb"]["sha256"]
            and value["gds_sha256"] == assets["gds"]["sha256"], "Release decision target differs")
    blockers = value["open_gates"]
    require(value["fabrication_decision"] == "no-go" and value["rehearsal_decision"] in ("go", "no-go")
            and type(blockers) is dict and blockers.keys() == RELEASE_BLOCKERS
            and all(row["status"] == "open" and type(row["reason"]) is str and row["reason"].strip()
                    for row in blockers.values()), "Release decision must preserve the two open authorization gates")
    go = value["rehearsal_decision"] == "go"
    require(not go or all(check["status"] == "passed" for check in checks.values()),
            "A rehearsal go requires all local evidence lanes")
    return check_state("passed" if go else "failed", [receipt]), {
        "rehearsal": value["rehearsal_decision"], "fabrication": value["fabrication_decision"], "open_gates": blockers}


def target_upstream(upstream):
    require(upstream == UPSTREAM, "Shuttle, allocation, or exact support/action revisions differ")
    return upstream


def revision_label(value):
    require(type(value) is str and re.fullmatch(r"[0-9a-f]{40}", value), "Require reviewed source commit label")
    return value


def observed_file(workspace, relative):
    path = local_path(workspace, relative)
    require(path.is_file(), f"Missing rehearsal source: {relative}")
    return {"path": relative, "sha256": digest(path)}


def draft_spec(workspace, source_commit, decision_path):
    """Generate the reviewable spec for the November 4 rehearsal without copying evidence."""
    revision_label(source_commit)
    work = "build/tt-rehearsal-20261104"
    route = "build/e982-whole-route-20261104"
    g4 = "build/e982-g4-20261104"
    views = f"{work}/views"
    postfill = f"{route}/native/flow/09-openroad-fillinsertion"
    source_paths = {**TRACKED_ASSETS, "odb": f"{postfill}/{TOP}.odb", "gds": f"{route}/native/design.gds",
                    "lef": f"{views}/official-format.lef", "def": f"{views}/design.def",
                    "nl": f"{views}/signoff-views/implemented.v", "pnl": f"{views}/signoff-views/implemented.power.v",
                    "cdl": f"{views}/complete-reference.cdl", "sdc": f"{postfill}/{TOP}.sdc"}
    assets = {name: observed_file(workspace, path) for name, path in source_paths.items()}
    for path in (*TRACKED_ASSETS.values(), "scripts/streaming_8x4_tt_rehearsal.py",
                 "scripts/streaming_8x4_enclosure_admission.py", "scripts/streaming_tt_signoff.py"):
        raw = subprocess.check_output(["git", "show", f"{source_commit}:{path}"], cwd=workspace, timeout=15)
        require(hashlib.sha256(raw).hexdigest() == observed_file(workspace, path)["sha256"],
                f"Rehearsal tracked input differs from the reviewed source commit: {path}")

    receipt_paths = {"route": f"{route}/independent-readback.json", "route_execution": f"{route}/native/execution.json",
                     "native": f"{work}/native-receipt.json", "g4_transport": f"{g4}/transport.json",
                     "g4_wire": f"{g4}/wire/report.json", "bringup_fixture": f"{work}/bringup/fixture.json",
                     "bringup_dry_run": f"{work}/bringup/dry-run.json", "release_decision": decision_path}
    receipts = {name: observed_file(workspace, path) for name, path in receipt_paths.items()
                if local_path(workspace, path).is_file()}
    return {"schema": INPUT_SCHEMA, "source_commit": source_commit, "target_odb_sha256": assets["odb"]["sha256"],
            "assets": assets, "receipts": receipts, "upstream": dict(UPSTREAM)}


def manifest_for(workspace, spec):
    require(spec.get("schema") == INPUT_SCHEMA
            and set(spec) == {"schema", "source_commit", "target_odb_sha256", "assets", "receipts", "upstream"},
            "Unknown rehearsal input schema")
    source_commit = revision_label(spec["source_commit"])
    assets = role_records(workspace, spec["assets"], REQUIRED_ASSETS, OPTIONAL_ASSETS)
    receipts = role_records(workspace, spec["receipts"], set(), RECEIPT_ROLES)
    require(len({entry["path"] for entry in (*assets.values(), *receipts.values())}) == len(assets) + len(receipts),
            "Asset and receipt paths may not alias")
    require(assets["odb"]["sha256"] == spec["target_odb_sha256"], "Rehearsal target ODB SHA-256 differs")
    upstream = target_upstream(spec["upstream"])
    checks = {**route_checks(workspace, assets, receipts), **native_checks(workspace, assets, receipts, upstream),
              **digital_checks(workspace, assets, receipts)}
    checks.update(bringup_checks(workspace, receipts, checks))
    checks["release_decision"], decision = release_decision(workspace, assets, receipts, checks)
    payload = {role: dict(assets[role], path=f"package/{path}") for role, path in PACKAGE.items()}
    return {"schema": MANIFEST_SCHEMA, "source_commit": source_commit,
            "target_odb_sha256": spec["target_odb_sha256"], "upstream": upstream,
            "reader_sha256": {"rehearsal": digest(Path(__file__)),
                              "layout_report": digest(Path(physical_reader.__file__)),
                              "tt_precheck": digest(Path(tt_reader.__file__))},
            "assets": assets, "receipts": receipts, "payload": payload, "checks": checks, "scope": SCOPE,
            "release_decision": decision,
            "open_gates": [name for name, check in checks.items() if check["status"] != "passed"] + list(OUTSIDE_REHEARSAL),
            "local_checks_passed": all(check["status"] == "passed" for check in checks.values()),
            "tapeout_ready": False, "shuttle_precheck_performed": False, "submission_performed": False}


def assemble(workspace, spec, destination):
    manifest = manifest_for(workspace, spec)
    relative = destination.relative_to(workspace).as_posix()
    require(relative_name(relative).parts[0] == "build" and len(relative_name(relative).parts) > 1,
            "Rehearsal packages belong under the ignored build directory")
    require(local_path(workspace, relative) == destination, "Invalid bundle destination")
    destination.mkdir()
    for role, entry in manifest["payload"].items():
        source = local_path(workspace, manifest["assets"][role]["path"])
        target = local_path(destination, entry["path"])
        target.parent.mkdir(parents=True, exist_ok=True)
        with source.open("rb") as input_stream, target.open("xb") as output_stream:
            shutil.copyfileobj(input_stream, output_stream, length=1024 * 1024)
        require(file_spec(destination, entry) == entry, f"Copied package view differs: {role}")
    manifest_path = destination / "manifest.json"
    with manifest_path.open("x", encoding="utf-8") as stream:
        json.dump(manifest, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write("\n")
    return verify(workspace, destination, digest(manifest_path))


def verify(workspace, bundle, expected, *, source_archive=None):
    require(local_path(workspace, bundle.relative_to(workspace).as_posix()) == bundle, "Invalid bundle path")
    path = local_path(bundle, "manifest.json")
    require(bundle.is_dir() and path.is_file() and hash_string(expected), "Missing bundle or manifest SHA-256")
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == expected, "Bundle manifest does not match its reviewed SHA-256")
    manifest = decode_json(data)
    require(manifest.get("schema") == MANIFEST_SCHEMA, "Unsupported rehearsal manifest")
    spec = {key: manifest[key] for key in ("source_commit", "target_odb_sha256", "assets", "receipts", "upstream")}
    require(manifest == manifest_for(workspace, dict(spec, schema=INPUT_SCHEMA)),
            "Manifest evidence, targets or derived checks differ")
    if source_archive is not None:
        for role, relative in TRACKED_ASSETS.items():
            require(role in manifest["assets"], f"Missing archived asset role: {role}")
            file_record(source_archive, relative, manifest["assets"][role]["sha256"])
    for entry in manifest["payload"].values():
        require(file_spec(bundle, entry) == entry, "Packaged asset differs from its evidence")
    files = {"manifest.json", *(entry["path"] for entry in manifest["payload"].values())}
    dirs = {parent.as_posix() for name in files for parent in relative_name(name).parents if parent.parts}
    members = {entry.relative_to(bundle).as_posix(): entry for entry in bundle.rglob("*")}
    require(members.keys() == files | dirs and all(not entry.is_symlink()
            and (entry.is_file() if name in files else entry.is_dir()) for name, entry in members.items()),
            "Unexpected bundle members")
    return {"verified": True, "manifest_sha256": expected, "target_odb_sha256": manifest["target_odb_sha256"],
            "local_checks_passed": manifest["local_checks_passed"], "open_gates": manifest["open_gates"],
            "tapeout_ready": False, "shuttle_precheck_performed": False, "submission_performed": False}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, default=ROOT)
    actions = parser.add_subparsers(dest="command", required=True)
    prepare = actions.add_parser("spec", help="Print the reviewable spec for the exact November 4 workspace")
    prepare.add_argument("--source-commit", required=True)
    prepare.add_argument("--release-decision", default="build/tt-rehearsal-20261104/release-decision.json")
    build = actions.add_parser("assemble")
    build.add_argument("--input", type=Path, required=True)
    build.add_argument("--output", type=Path, required=True)
    check = actions.add_parser("verify")
    check.add_argument("bundle", type=Path)
    check.add_argument("--manifest-sha256", required=True)
    args = parser.parse_args(argv)
    try:
        workspace = args.workspace.resolve(strict=True)
        if args.command == "spec":
            result = draft_spec(workspace, args.source_commit, args.release_decision)
        elif args.command == "assemble":
            result = assemble(workspace, read_json(args.input), args.output.absolute())
        else:
            result = verify(workspace, args.bundle.absolute(), args.manifest_sha256,
                            source_archive=ROOT if ROOT != workspace else None)
    except (OSError, ValueError, TypeError, KeyError, ElementTree.ParseError, subprocess.SubprocessError) as error:
        print(f"Rehearsal rejected: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
