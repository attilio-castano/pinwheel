"""Replay the depth-two bring-up fixture on the exact ECO wire executable."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import time

import process_group
import streaming_8x4_bringup as bench
from streaming_8x4_e982_eco_digital import ECO_GDS, ECO_ODB, WIRE_SCHEMA
from streaming_8x4_e982_g4_transport import ROOT, bind, emit, read_bound, reopen, require
from streaming_tt_wire_binding import dependency_closure


SCHEMA = "pinwheel.streaming-8x4-e982-eco-bringup.v1"
WIRE = "eb1975a2b5bcb047d0453ef6b5086a4bec92d59ee511cecf790e6b311d92116c"
MODEL = "1a05eba9d709845b56ffa51b63d72e8a3cd3d02af770adbfbe82d9e48c76ba05"
VVP = "0be7cf5374b78d3e8c8044338b3a2b4998f66c07cf8f6075e623b1e0001f596d"
CASES = ("uart_rx", "spi_duplex", "i2c_read", "i2c_write")


def checked_cases(fixture, dry_run):
    require(dry_run["schema"] == "pinwheel.streaming-ready-pin-dry-run.v1" and dry_run["passed"] is True
            and dry_run["board_exercised"] is False and dry_run["scope"] == "Local public-pin simulation"
            and dry_run["model_sha256"] == MODEL, "Dry run does not bind the exact local pin simulation")
    cases = dry_run["cases"]
    require(set(cases) == set(CASES) and all(row["matching_release"] is True and type(row["edges"]) is int
                                          and row["edges"] > 0 for row in cases.values()), "Incomplete bench cases")
    for name in ("uart_rx", "spi_duplex"):
        require(cases[name]["rx_hex"] == fixture[name]["expected_rx_hex"], f"Wrong {name} received bytes")
    require(cases["spi_duplex"]["tx_hex"] == fixture["spi_duplex"]["tx_hex"], "Wrong SPI transmitted bytes")
    for name, payload in (("i2c_read", "expected_rx_hex"), ("i2c_write", "tx_hex")):
        require(cases[name]["data_hex"] == fixture[name][payload]
                and cases[name]["address_7bit"] == fixture[name]["address_7bit"]
                and cases[name]["stream_cells"] == fixture[name]["start_cells"], f"Wrong {name} fixture")
    require(cases["i2c_read"]["target_stretch_edges"] > 0 and cases["i2c_write"]["target_stretch_edges"] == 0,
            "I²C stretch or clean-write evidence differs")
    return cases


def run(wire_path, output, timeout):
    require(1 <= timeout <= 300 and not output.exists()
            and output.is_relative_to(ROOT / "build/e982-fanout-20261104"),
            "Use a fresh local ECO output path and a timeout no greater than 300 seconds")
    pins = {}
    wire = read_bound(pins, wire_path, WIRE)
    require(wire["schema"] == WIRE_SCHEMA and wire["passed"] is True and wire["fresh_public_wire_passed"] is True
            and wire["target_odb_sha256"] == ECO_ODB and wire["target_gds_sha256"] == ECO_GDS
            and wire["positive_cases"] == 35, "Missing the exact successful ECO wire report")
    worker_item = reopen(pins, wire["worker_report"])
    worker = read_bound(pins, worker_item["path"], worker_item["sha256"])
    require(worker["passed"] is True and worker["stage"] == "closed" and worker["inputs_unchanged"] is True
            and worker["export"]["database_sha256"] == ECO_ODB
            and worker["all_actual_instances_retained"] is True and worker["clock_contraction"] is False
            and worker["tool_identity_before"] == worker["tool_identity_after"],
            "Wire worker evidence is incomplete")
    model_path = Path(worker_item["path"]).parent / "unchanged.vvp"
    require(str(model_path) == worker["executables"]["unchanged"]
            and wire["worker_artifact_sha256"]["unchanged.vvp"] == worker["artifact_sha256"]["unchanged.vvp"] == MODEL,
            "Wrong unchanged ECO model")
    model = bind(pins, model_path, MODEL)
    request_item = reopen(pins, worker["configuration"])
    require(wire["verified_file_sha256"][request_item["path"]] == request_item["sha256"],
            "Wire configuration does not bind the closed worker")
    request = read_bound(pins, request_item["path"], request_item["sha256"])
    vvp_path = Path(request["tools"]["vvp"])
    require(worker["input_sha256_before"][str(vvp_path.resolve())] == VVP
            and worker["native_runs"][0]["actual_argv"] == [str(vvp_path), str(model_path)],
            "VVP differs from the actual ECO replay runtime")
    vvp = bind(pins, vvp_path, VVP)
    runtime = worker["tool_identity_before"]["files"]
    suite = vvp_path.parent.parent
    with model_path.open() as stream:
        header = stream.read(16384)
    plugins = [Path(item) for item in re.findall(r'^:vpi_module "([^"]+)";$', header, re.M)]
    require(header.splitlines()[0] == f"#! {vvp_path}" and len(set(plugins)) == len(plugins) == 6
            and all(path.is_relative_to(suite / "lib/ivl") for path in plugins), "Unexpected compiled VVP loader context")
    runtime_files = [vvp_path, suite / "libexec/vvp", suite / "libexec/realpath",
                     suite / "lib/libvvp.1.14.0.dylib", *plugins]
    for path in runtime_files:
        item = runtime[str(path)]
        require(str(path.resolve(strict=True)) == item["resolved"], f"Runtime path target changed: {path}")
        bind(pins, item["resolved"], item["sha256"])
    python = Path(request["tools"]["python"]).resolve(strict=True)
    bind(pins, python, worker["input_sha256_before"][str(python)])
    script = Path(bench.__file__).resolve()
    for relative in dependency_closure(ROOT, [str(script.relative_to(ROOT))])["files"]:
        bind(pins, ROOT / relative)
    bind(pins, Path(process_group.__file__).resolve(), request["source_sha256"]["scripts/process_group.py"])
    producer = bind(pins, Path(__file__).resolve())

    output.mkdir(parents=True)
    fixture_path, dry_path = output / "fixture.json", output / "dry-run.json"
    fixture = bench.fixture()
    emit(fixture_path, fixture)
    fixture_item = bind(pins, fixture_path)
    argv = [str(python), "-B", str(script), "simulate", "--vvp", vvp["path"], "--executable", model["path"],
            "--executable-sha256", MODEL]
    log = output / "simulate.log"
    result = dict(schema=SCHEMA, passed=False, target_odb_sha256=ECO_ODB, target_gds_sha256=ECO_GDS,
                  fixture=fixture_item, wire=bind(pins, wire_path, WIRE), worker=worker_item, model=model, vvp=vvp,
                  producer=producer, argv=argv, timeout_seconds=timeout, board_exercised=False)
    start = time.monotonic()
    try:
        completed = process_group.run_captured(argv, cwd=ROOT, timeout=timeout, log_path=log)
        result["exit_code"] = completed.returncode
        require(completed.returncode == 0 and not completed.stderr, "Bring-up simulator child did not close cleanly")
        dry = json.loads(completed.stdout)
        cases = checked_cases(fixture, dry)
        for path, digest in tuple(pins.items()):
            bind(pins, path, digest)
        emit(dry_path, dry)
        require(dry_path.read_bytes() == log.read_bytes(), "Raw process JSON differs from reopened dry run")
        result.update(passed=True, cases=cases, positive_cases=len(cases), dry_run=bind(pins, dry_path))
    except subprocess.TimeoutExpired as exc:
        result.update(exit_code=None, process_group_stopped=getattr(exc, "process_group_stopped", False),
                      error=str(exc))
    except (OSError, ValueError, KeyError, TypeError) as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        if log.is_file():
            result["log"] = bind(pins, log)
        result.update(elapsed_seconds=time.monotonic() - start, verified_file_sha256=dict(sorted(pins.items())))
        emit(output / "receipt.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wire", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    try:
        result = run(args.wire.absolute(), args.output.absolute(), args.timeout)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(2, f"ECO bring-up rejected: {exc}\n")
    print(args.output / "receipt.json")
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
