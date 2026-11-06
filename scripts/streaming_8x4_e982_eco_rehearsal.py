"""Seal and reopen the local rehearsal of the exact routed fanout ECO."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
from xml.etree.ElementTree import ParseError

from streaming_8x4_bringup import fixture as bringup_fixture
from streaming_8x4_e982_eco_rehearsal_evidence import reopen_evidence
from streaming_8x4_tt_rehearsal import (
    BRINGUP_CASES, PACKAGE, ROOT, TRACKED_ASSETS, UPSTREAM, digest, file_record, file_spec,
    hash_string, local_path, observed_file, read_json, relative_name, require, revision_label,
)
from streaming_tt_intake import dependency_closure


SCHEMA = "pinwheel.streaming-8x4-e982-eco-rehearsal.v1"
ECO = "build/e982-fanout-20261104"
ODB = "e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9"
GDS = "dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82"
TRANSPORT = "7b6aaef9a4970e9d3d64a56f7bebce04f30be8e55b407b4367b4ce99578276e1"
WIRE = "eb1975a2b5bcb047d0453ef6b5086a4bec92d59ee511cecf790e6b311d92116c"
BRINGUP = "9c40c96518285c2f30f88170a4548297eaabdff46a619ad879ee93705c30c43e"
BRINGUP_SOURCE = "scripts/streaming_8x4_e982_eco_bringup.py"
TT_LOCK = "tools/streaming-tt-signoff.json"
TIMING = "a42c09b64dc2721cbdf7e224b8b228caaa3cbcb82497ccba52972a78471a48ae"
ELECTRICAL = "cc452dd0c004af4b125cf47839e097893ca91d66245b5ed2cf57b57afefc4baf"
POWER = "c0133860e060ca4221048b9e5156efeb1a213421f7250bf2a763cdc47d0f470a"
OPEN_GATES = (
    "qualified_cmos5l_extraction_and_timing",
    "qualified_electrical_power",
    "shuttle_allocation_and_custom_gds_acceptance",
)


def require_target(data):
    require(data["target_odb_sha256"] == ODB and data["target_gds_sha256"] == GDS,
            "Receipt is for a different layout")


def binding_name(binding, origin):
    path = Path(binding["path"])
    name = path.relative_to(origin).as_posix() if path.is_absolute() else binding["path"]
    return relative_name(name).as_posix()


def reopen_digital(workspace, origin, pins, assets, source):
    def collect(path, expected):
        row = file_record(workspace, path, expected)
        require(pins.setdefault(path, expected) == expected, f"Conflicting evidence for {path}")
        return row

    def load(path, expected):
        collect(path, expected)
        return read_json(local_path(workspace, path))

    def linked(item):
        return collect(binding_name(item, origin), item["sha256"])

    transport = load(f"{ECO}/digital-02/transport.json", TRANSPORT)
    wire = load(f"{ECO}/digital-02/wire/report.json", WIRE)
    for receipt in (transport, wire):
        require_target(receipt)
        require(receipt["passed"] is True and receipt["full_tapeout_ready"] is False
                and receipt["netlist_sha256"] == assets["nl"]["sha256"]
                and receipt["powered_netlist_sha256"] == assets["pnl"]["sha256"], "Wrong exact ECO digital views")
    require(transport["schema"] == "pinwheel.streaming-8x4-e982-eco-digital.v1"
            and transport["functional_correspondence_transported"] is True
            and transport["clock_and_reset_cones_equal"] is True
            and len(transport["positive_buffer_contractions"]) == 5
            and transport["state_bits"] == 6039 and transport["public_output_bits"] == 24,
            "Incomplete ECO correspondence")
    for role in ("base_transport", "semantic_state_map", "sampler_binding"):
        linked(transport[role])
    require(wire["schema"] == "pinwheel.streaming-8x4-e982-eco-public-wire.v1"
            and wire["fresh_public_wire_passed"] is True and wire["worker_exit_code"] == 0
            and linked(wire["transport"])["sha256"] == TRANSPORT, "Incomplete exact ECO public-wire replay")
    worker_file = linked(wire["worker_report"])
    worker = read_json(local_path(workspace, worker_file["path"]))
    worker_dir = relative_name(worker_file["path"]).parent
    require(worker["stage"] == "closed" and worker["passed"] is True and worker["inputs_unchanged"] is True
            and worker["generated_inputs_unchanged"] is True and worker["clock_contraction"] is False
            and worker["export"]["database_sha256"] == ODB and worker["physical_ff_bits"] == 6039
            and worker["artifact_sha256"] == wire["worker_artifact_sha256"]
            and worker["positive_cases"] == wire["positive_cases"] == 35
            and worker["actual_sampler_mutants"] == wire["actual_sampler_mutants"] == 1
            and worker["native_processes"] == wire["native_processes"] == 14
            and worker["physical_edges"] == wire["physical_edges"] == 513297, "Incomplete public-wire worker")
    for name, pin in worker["artifact_sha256"].items():
        collect((worker_dir / relative_name(name)).as_posix(), pin)
    require(worker["traces"] == wire["traces"] and len(wire["traces"]) == 14
            and sum(trace["edges"] for trace in wire["traces"]) == 513297
            and all(linked(trace)["bytes"] == trace["bytes"] == trace["edges"] * 20
                    for trace in wire["traces"]), "Raw ECO traces differ")
    linked(worker["native_journal"])
    linked(worker["configuration"])
    linked(wire["worker_log"])
    model = collect((worker_dir / "unchanged.vvp").as_posix(), worker["artifact_sha256"]["unchanged.vvp"])

    path = f"{ECO}/rehearsal-bringup-01/receipt.json"
    receipt = load(path, BRINGUP)
    require_target(receipt)
    require(receipt["schema"] == "pinwheel.streaming-8x4-e982-eco-bringup.v1"
            and receipt["passed"] is True and receipt["exit_code"] == 0
            and 0 <= receipt["elapsed_seconds"] <= receipt["timeout_seconds"] <= 900
            and linked(receipt["wire"])["sha256"] == WIRE
            and linked(receipt["worker"]) == worker_file and linked(receipt["model"]) == model
            and worker["input_sha256_before"][receipt["vvp"]["path"]] == receipt["vvp"]["sha256"]
            and binding_name(receipt["producer"], origin) == BRINGUP_SOURCE
            and receipt["producer"]["sha256"] == source[BRINGUP_SOURCE],
            "Bring-up model or worker differs from the exact ECO")
    fixture = read_json(local_path(workspace, linked(receipt["fixture"])["path"]))
    dry = read_json(local_path(workspace, linked(receipt["dry_run"])["path"]))
    require(linked(receipt["log"])["sha256"] == receipt["dry_run"]["sha256"],
            "Bring-up dry run differs from simulator output")
    require(fixture == bringup_fixture() and dry["schema"] == "pinwheel.streaming-ready-pin-dry-run.v1"
            and dry["passed"] is True and dry["board_exercised"] is False and dry["model_sha256"] == model["sha256"]
            and dry["scope"] == "Local public-pin simulation", "Bring-up fixture or scope differs")
    cases = dry["cases"]
    require(cases == receipt["cases"] and set(cases) == set(BRINGUP_CASES)
            and all(row["matching_release"] is True and type(row["edges"]) is int and row["edges"] > 0
                    for row in cases.values()), "Incomplete bring-up cases")
    require(cases["uart_rx"]["rx_hex"] == fixture["uart_rx"]["expected_rx_hex"]
            and cases["spi_duplex"]["tx_hex"] == fixture["spi_duplex"]["tx_hex"]
            and cases["spi_duplex"]["rx_hex"] == fixture["spi_duplex"]["expected_rx_hex"],
            "UART or SPI bring-up payload differs")
    for name, payload in (("i2c_read", "expected_rx_hex"), ("i2c_write", "tx_hex")):
        require(cases[name]["address_7bit"] == fixture[name]["address_7bit"]
                and cases[name]["data_hex"] == fixture[name][payload]
                and cases[name]["stream_cells"] == fixture[name]["start_cells"], "I2C bring-up payload differs")
    return dict(positive_wire_cases=35, sampler_faults_detected=1, sampled_wire_edges=513297,
                bringup_cases=cases, board_exercised=False)


def reopen_diagnostics(workspace, pins):
    for relative, pin in (("timing-eco-02/timing-readback.json", TIMING),
                          ("electrical-01/readback.json", ELECTRICAL),
                          ("signoff-01/eco-power-observation.json", POWER)):
        path = f"{ECO}/{relative}"
        file_record(workspace, path, pin)
        pins[path] = pin
    timing = read_json(workspace / ECO / "timing-eco-02/timing-readback.json")
    electrical = read_json(workspace / ECO / "electrical-01/readback.json")
    power = read_json(workspace / ECO / "signoff-01/eco-power-observation.json")
    require_target(timing)
    require_target(electrical)
    require(timing["status"] == "diagnostic" and timing["parasitics_preflight_passed"] is True
            and timing["qualified_timing"] is False and timing["model_qualified"] is False
            and electrical["qualified_timing"] is False and power["power_qualified"] is False
            and power["inputs_sha256"][f"{ECO}/five-01/trial.odb"] == ODB
            and power["inputs_sha256"][f"{ECO}/five-01/stream/design.gds"] == GDS,
            "Diagnostic scope or target differs")
    return dict(timing_scenarios=9, timing_qualified=False, power_qualified=False)


def source_files(root):
    entry = Path(__file__).resolve().relative_to(ROOT).as_posix()
    names = sorted(set(dependency_closure(root, (*TRACKED_ASSETS.values(), entry))["files"])
                   | {BRINGUP_SOURCE, TT_LOCK})
    return {name: observed_file(root, name)["sha256"] for name in names}


def manifest_for(workspace, origin, source_commit, source):
    physical = reopen_evidence(workspace, origin=origin)
    require(physical["target_odb_sha256"] == ODB and physical["gds_sha256"] == GDS,
            "Physical evidence belongs to a different layout")
    pins = dict(physical["verified_file_sha256"])
    require(pins[TT_LOCK] == source[TT_LOCK], "Precheck lock differs from the reviewed source")
    assets = {role: file_spec(workspace, item) for role, item in physical["views"].items()}
    for role, path in TRACKED_ASSETS.items():
        assets[role] = file_record(workspace, path, source[path])
    require(assets["odb"]["sha256"] == ODB and assets["gds"]["sha256"] == GDS
            and re.search(r"(?m)^  clock_hz: 0\s*$", (workspace / "info.yaml").read_text()),
            "Exact ECO package or unqualified clock field differs")
    digital = reopen_digital(workspace, origin, pins, assets, source)
    diagnostics = reopen_diagnostics(workspace, pins)
    for item in assets.values():
        require(pins.setdefault(item["path"], item["sha256"]) == item["sha256"],
                "Packaged asset disagrees with observed evidence")
    evidence = {name: file_record(workspace, name, expected) for name, expected in sorted(pins.items())}
    payload = {role: dict(assets[role], path=f"package/{path}") for role, path in PACKAGE.items()}
    return dict(schema=SCHEMA, source_commit=revision_label(source_commit), source_sha256=source,
                origin_workspace=str(origin), target_odb_sha256=ODB, gds_sha256=GDS,
                upstream=UPSTREAM, assets=assets, payload=payload, evidence=evidence,
                checks=dict(physical=physical["checks"], digital=digital, diagnostics=diagnostics),
                rehearsal_decision="go", fabrication_decision="no-go", open_gates=list(OPEN_GATES),
                tapeout_ready=False, shuttle_precheck_performed=False, submission_performed=False,
                scope="Local packaged views and selected raw reports. Historical toolchains and full CAD replay "
                      "inputs are retained separately.")


def copy_checked(source, destination, entry):
    destination.parent.mkdir(parents=True, exist_ok=True)
    with source.open("rb") as reader, destination.open("xb") as writer:
        shutil.copyfileobj(reader, writer, length=1024 * 1024)
    require(digest(destination) == entry["sha256"] and destination.stat().st_size == entry["bytes"],
            f"Copied evidence differs: {destination.name}")


def assemble(workspace, bundle, source_commit):
    revision_label(source_commit)
    relative = bundle.relative_to(workspace).as_posix()
    require(relative_name(relative).is_relative_to(relative_name(ECO))
            and local_path(workspace, relative) == bundle, "Use a fresh ignored ECO bundle path")
    source = source_files(ROOT)
    for path, expected in source.items():
        blob = subprocess.check_output(["git", "show", f"{source_commit}:{path}"], cwd=ROOT, timeout=15)
        require(hashlib.sha256(blob).hexdigest() == expected, f"Source file differs from {source_commit}: {path}")
    manifest = manifest_for(workspace, workspace, source_commit, source)
    bundle.mkdir(parents=True, exist_ok=False)
    for entry in manifest["evidence"].values():
        copy_checked(local_path(workspace, entry["path"]), local_path(bundle / "evidence", entry["path"]), entry)
    for role, entry in manifest["payload"].items():
        copy_checked(local_path(workspace, manifest["assets"][role]["path"]), local_path(bundle, entry["path"]), entry)
    path = bundle / "manifest.json"
    with path.open("x", encoding="utf-8") as stream:
        json.dump(manifest, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write("\n")
    return verify(bundle, digest(path))


def verify(bundle, expected):
    require(bundle.is_dir() and not bundle.is_symlink() and hash_string(expected), "Invalid ECO bundle or manifest SHA")
    path = local_path(bundle, "manifest.json")
    file_record(bundle, "manifest.json", expected)
    manifest = read_json(path)
    require(manifest["schema"] == SCHEMA, "Expected the ECO-specific rehearsal manifest")
    origin = Path(manifest["origin_workspace"])
    require(origin.is_absolute() and ".." not in origin.parts, "Invalid original workspace label")
    source = source_files(ROOT)
    require(source == manifest["source_sha256"], "Verifier or tracked inputs differ from the reviewed source")
    evidence = local_path(bundle, "evidence")
    require(manifest == manifest_for(evidence, origin, manifest["source_commit"], source),
            "Manifest differs from independently reopened ECO evidence")
    for entry in manifest["payload"].values():
        require(file_spec(bundle, entry) == entry, "Packaged payload differs from the exact ECO evidence")
    files = {"manifest.json", *(entry["path"] for entry in manifest["payload"].values()),
             *(f"evidence/{name}" for name in manifest["evidence"])}
    dirs = {parent.as_posix() for name in files for parent in relative_name(name).parents if parent.parts}
    members = {entry.relative_to(bundle).as_posix(): entry for entry in bundle.rglob("*")}
    require(members.keys() == files | dirs and all(not entry.is_symlink()
            and (entry.is_file() if name in files else entry.is_dir()) for name, entry in members.items()),
            "Unexpected ECO bundle members")
    return {**{key: manifest[key] for key in ("source_commit", "target_odb_sha256", "gds_sha256",
                                              "rehearsal_decision", "fabrication_decision", "open_gates")},
            "verified": True, "manifest_sha256": expected, "evidence_files": len(manifest["evidence"]),
            "payload_files": len(manifest["payload"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_subparsers(dest="command", required=True)
    build = actions.add_parser("assemble")
    build.add_argument("bundle", type=Path)
    build.add_argument("--source-commit", required=True)
    check = actions.add_parser("verify")
    check.add_argument("bundle", type=Path)
    check.add_argument("--manifest-sha256", required=True)
    args = parser.parse_args()
    try:
        bundle = args.bundle.absolute()
        result = (assemble(ROOT, bundle, args.source_commit) if args.command == "assemble"
                  else verify(bundle, args.manifest_sha256))
    except (OSError, ValueError, TypeError, KeyError, ParseError, subprocess.SubprocessError) as error:
        parser.exit(2, f"ECO rehearsal rejected: {error}\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
