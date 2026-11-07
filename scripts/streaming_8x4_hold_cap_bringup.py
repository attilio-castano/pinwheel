"""Replay the depth-two bring-up fixture on the exact hold/cap wire model."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import time

import process_group
import streaming_8x4_bringup as bench
from streaming_8x4_e982_g4_transport import ROOT, bind, emit, read_bound, reopen, require
from streaming_8x4_hold_cap_digital import WIRE_SCHEMA
from streaming_8x4_hold_cap_physical import TARGET, TRIAL
from streaming_tt_wire_binding import dependency_closure

SCHEMA = "pinwheel.streaming-8x4-hold-cap-bringup.v1"
WIRE = "2bfadee2aff5fd8341b0d00772399571e6c64cabec63da714d4462b9ab30183b"
CASES = ("uart_rx", "spi_duplex", "i2c_read", "i2c_write")


def checked_cases(fixture, dry, model_sha):
    require(dry["schema"] == "pinwheel.streaming-ready-pin-dry-run.v1" and dry["passed"] is True
            and dry["board_exercised"] is False and dry["scope"] == "Local public-pin simulation"
            and dry["model_sha256"] == model_sha, "Wrong bring-up model or scope")
    cases = dry["cases"]
    require(set(cases) == set(CASES)
            and all(row["matching_release"] is True and type(row["edges"]) is int and row["edges"] > 0
                    for row in cases.values()), "Incomplete bring-up cases")
    for name in ("uart_rx", "spi_duplex"):
        require(cases[name]["rx_hex"] == fixture[name]["expected_rx_hex"], "Wrong received bytes: " + name)
    require(cases["spi_duplex"]["tx_hex"] == fixture["spi_duplex"]["tx_hex"], "Wrong SPI transmitted bytes")
    for name, payload in (("i2c_read", "expected_rx_hex"), ("i2c_write", "tx_hex")):
        require(cases[name]["data_hex"] == fixture[name][payload]
                and cases[name]["address_7bit"] == fixture[name]["address_7bit"]
                and cases[name]["stream_cells"] == fixture[name]["start_cells"], "Wrong I2C fixture: " + name)
    require(cases["i2c_read"]["target_stretch_edges"] > 0 and cases["i2c_write"]["target_stretch_edges"] == 0,
            "I2C stretch or clean-write observation differs")
    return cases


def run(output, timeout):
    require(not output.exists() and output.is_relative_to(TRIAL) and 1 <= timeout <= 300,
            "Use a fresh candidate output and a timeout of at most 300 seconds")
    pins = {}
    wire_path = TRIAL / "digital-02/wire/report.json"
    wire = read_bound(pins, wire_path, WIRE)
    require(wire["schema"] == WIRE_SCHEMA and wire["passed"] is True and wire["fresh_public_wire_passed"] is True
            and wire["target_odb_sha256"] == TARGET["odb_sha256"]
            and wire["target_gds_sha256"] == TARGET["gds_sha256"]
            and wire["positive_cases"] == 35, "Missing exact-candidate fresh wire replay")
    worker_item = reopen(pins, wire["worker_report"])
    worker = read_bound(pins, worker_item["path"], worker_item["sha256"])
    require(worker["passed"] is True and worker["stage"] == "closed" and worker["inputs_unchanged"] is True
            and worker["export"]["database_sha256"] == TARGET["odb_sha256"]
            and worker["all_actual_instances_retained"] is True and worker["clock_contraction"] is False
            and worker["tool_identity_before"] == worker["tool_identity_after"], "Unclosed wire worker")
    model_path = Path(worker_item["path"]).parent / "unchanged.vvp"
    model_sha = worker["artifact_sha256"]["unchanged.vvp"]
    require(str(model_path) == worker["executables"]["unchanged"]
            and wire["worker_artifact_sha256"]["unchanged.vvp"] == model_sha, "Wrong unchanged model")
    model = bind(pins, model_path, model_sha)
    request_item = reopen(pins, worker["configuration"])
    require(wire["verified_file_sha256"][request_item["path"]] == request_item["sha256"], "Wire request misbound")
    request = read_bound(pins, request_item["path"], request_item["sha256"])
    vvp_path = Path(request["tools"]["vvp"])
    vvp_sha = worker["input_sha256_before"][str(vvp_path.resolve())]
    require(worker["native_runs"][0]["actual_argv"] == [str(vvp_path), str(model_path)], "Wrong simulator selection")
    vvp = bind(pins, vvp_path, vvp_sha)
    runtime = worker["tool_identity_before"]["files"]
    suite = vvp_path.parent.parent
    with model_path.open() as stream:
        header = stream.read(16384)
    plugins = [Path(item) for item in re.findall(r'^:vpi_module "([^"]+)";$', header, re.M)]
    require(header.splitlines()[0] == f"#! {vvp_path}" and len(set(plugins)) == len(plugins) == 6
            and all(path.is_relative_to(suite / "lib/ivl") for path in plugins), "Wrong VVP loader context")
    for path in [vvp_path, suite / "libexec/vvp", suite / "libexec/realpath",
                 suite / "lib/libvvp.1.14.0.dylib", *plugins]:
        item = runtime[str(path)]
        require(str(path.resolve(strict=True)) == item["resolved"], "Runtime path changed: " + str(path))
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
            "--executable-sha256", model_sha]
    log = output / "simulate.log"
    result = dict(schema=SCHEMA, passed=False, target_odb_sha256=TARGET["odb_sha256"],
                  target_gds_sha256=TARGET["gds_sha256"], fixture=fixture_item,
                  wire=bind(pins, wire_path, WIRE), worker=worker_item, model=model, vvp=vvp,
                  producer=producer, argv=argv, timeout_seconds=timeout, board_exercised=False)
    start = time.monotonic()
    try:
        child = process_group.run_captured(argv, cwd=ROOT, timeout=timeout, log_path=log)
        result["exit_code"] = child.returncode
        require(child.returncode == 0 and not child.stderr, "Bring-up child failed")
        dry = json.loads(child.stdout)
        cases = checked_cases(fixture, dry, model_sha)
        for path, digest in tuple(pins.items()):
            bind(pins, path, digest)
        emit(dry_path, dry)
        require(dry_path.read_bytes() == log.read_bytes(), "Dry-run JSON differs from process output")
        result.update(passed=True, cases=cases, positive_cases=4, dry_run=bind(pins, dry_path))
    except subprocess.TimeoutExpired as exc:
        result.update(exit_code=None, process_group_stopped=getattr(exc, "process_group_stopped", False), error=str(exc))
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
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    result = run(args.output.absolute(), args.timeout)
    print(args.output / "receipt.json")
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
