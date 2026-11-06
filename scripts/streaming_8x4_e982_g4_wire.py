"""Run the original 35-case public-wire corpus on the exact e982 successor."""

import argparse
import importlib.util
from pathlib import Path
import subprocess
import sys
import time

import process_group
import streaming_8x4_e982_g4_transport as transport


SCHEMA = "pinwheel.streaming-8x4-e982-g4-wire.v1"


def verify_pins(pins):
    for path, pin in tuple(pins.items()):
        transport.bind(pins, path, pin)


def canonical_validators(source, source_pins):
    sys.path.insert(0, str(source / "scripts"))
    readers = []
    for name in ("check-streaming-tt-wire.py", "run-streaming-tt-wire.py"):
        path = source / "scripts" / name
        transport.bind({}, path, source_pins["scripts/" + name])
        spec = importlib.util.spec_from_file_location("_pinwheel_e982_" + name, path)
        reader = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(reader)
        readers.append(reader)
    return readers


def validate_worker(report, worker, config, request, target):
    transport.require(report["schema"] == "pinwheel.streaming-tt-public-wire.v1" and report["passed"] is True
        and report["stage"] == "closed" and report["qualified"] is False and report["physical_acceptance_claim"] is False
        and report["export"]["database_sha256"] == transport.TARGET_ODB
        and report["export"]["artifacts_sha256"] == target["export_artifact_sha256"]
        and report["configuration"] == request and report["physical_stage"] == config["physical_stage"]
        and report["inputs_unchanged"] is True and report["generated_inputs_unchanged"] is True
        and report["all_actual_instances_retained"] is True and report["clock_contraction"] is False
        and report["physical_ff_bits"] == 6039 and report["positive_cases"] == 35
        and report["actual_sampler_mutants"] == 1 and report["native_processes"] == 14,
        "Candidate worker receipt did not close the full public-wire corpus")
    source = Path(config["root"])
    worker_reader, owner_reader = canonical_validators(source, config["source_sha256"])
    traces = worker_reader.validate_native(report, worker, config["tools"])
    transport.require(traces == report["traces"], "Independently reopened raw traces differ from worker receipt")
    journal = owner_reader.native_journal(worker / "native.jsonl", report["native_runs"])
    transport.require(journal == report["native_journal"]["sha256"], "Canonical process journal differs")
    artifacts = {str(path.relative_to(worker)): transport.sha(path) for path in worker.rglob("*")
                 if path.is_file() and path != worker / "report.json"}
    transport.require(artifacts == report["artifact_sha256"], "Worker artifact membership or bytes changed")
    for path, pin in report["input_sha256_before"].items():
        transport.bind({}, path, pin)
    # The caller imports the current transport and the archived validator in one
    # process. Require exact selected archive bytes for any reused helper import.
    for name, module in tuple(sys.modules.items()):
        if name.startswith("streaming_") and not name.startswith("streaming_8x4_e982_g4_"):
            path = Path(module.__file__).resolve()
            transport.bind({}, path, config["source_sha256"]["scripts/" + path.name])
    return traces


def run(transport_path, transport_sha, out, timeout):
    transport.require(not out.exists(), "Preserve earlier candidate wire attempts")
    transport.require(1 <= timeout <= 7200, "Wire timeout must be explicitly bounded")
    pins = {}
    proof = transport.read_bound(pins, transport_path, transport_sha)
    transport.require(proof["schema"] == transport.SCHEMA and proof["passed"] is True
            and proof["functional_correspondence_transported"] is True
            and proof["target_odb_sha256"] == transport.TARGET_ODB and proof["target_gds_sha256"] == transport.TARGET_GDS,
            "Candidate is not bound to a completed transport")
    pins.update(proof["verified_file_sha256"])
    verify_pins(pins)
    config_item = proof["historical_worker_config"]
    config = transport.read_bound(pins, config_item["path"], config_item["sha256"])
    target = proof["target"]
    config = dict(config, physical_stage="actual-b7e60-postfill-canonical-export", sampler_binding=proof["sampler_binding"],
        export=dict(config["export"], directory=target["export_dir"],
                    receipt_sha256=target["connectivity_receipt"]["sha256"], database=target["database"]["path"]))
    source = Path(config["root"])
    entrypoint = source / "scripts/check-streaming-tt-wire.py"
    transport.bind(pins, entrypoint, config["source_sha256"]["scripts/check-streaming-tt-wire.py"])
    transport.bind(pins, Path(__file__).resolve())
    transport.bind(pins, Path(process_group.__file__).resolve(), config["source_sha256"]["scripts/process_group.py"])

    out.mkdir(parents=True)
    request_path = out / "request.json"
    transport.emit(request_path, config)
    request = transport.bind(pins, request_path)
    worker = out / "worker"
    argv = [config["tools"]["python"], "-B", str(entrypoint), "--worker-config", request["path"],
            "--worker-config-sha256", request["sha256"], "--out", str(worker)]
    result = {
        "schema": SCHEMA, "passed": False, "target_odb_sha256": transport.TARGET_ODB,
        "target_gds_sha256": transport.TARGET_GDS, "netlist_sha256": proof["netlist_sha256"],
        "powered_netlist_sha256": proof["powered_netlist_sha256"], "transport": transport.bind(pins, transport_path, transport_sha),
        "worker_argv": argv, "timeout_seconds": timeout,
        "boundary": "Fresh finite zero-delay protocol and sampler-mutant evidence on actual ODB connectivity "
                    "with pinned Liberty digital functions. Timing, analog, power and tapeout remain separate.",
        "full_tapeout_ready": False,
    }
    started = time.monotonic()
    try:
        child = process_group.run_captured(argv, cwd=source, timeout=timeout, log_path=out / "worker.log")
        result["worker_exit_code"] = child.returncode
        transport.require(child.returncode == 0, "Canonical host wire worker failed; inspect worker.log and retained receipts")
        worker_report = transport.read_bound(pins, worker / "report.json")
        traces = validate_worker(worker_report, worker, config, request, target)
        verify_pins(pins)
        result.update(passed=True, fresh_public_wire_passed=True, positive_cases=35, actual_sampler_mutants=1,
            native_processes=14, physical_edges=worker_report["physical_edges"], protocols=["UART", "SPI", "I2C", "JTAG"],
            traces=traces, worker_report=transport.bind(pins, worker / "report.json"),
            worker_artifact_sha256=worker_report["artifact_sha256"])
    except (OSError, ValueError, KeyError, RuntimeError, TypeError, subprocess.TimeoutExpired) as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        log = out / "worker.log"
        if log.is_file():
            result["worker_log"] = transport.bind(pins, log)
        result["verified_file_sha256"] = dict(sorted(pins.items()))
        result["elapsed_seconds"] = time.monotonic() - started
        transport.emit(out / "report.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--transport", type=lambda value: Path(value).absolute(), required=True)
    parser.add_argument("--transport-sha", required=True)
    parser.add_argument("--out", type=lambda value: Path(value).absolute(), required=True)
    parser.add_argument("--timeout", type=int, default=1800)
    args = parser.parse_args()
    try:
        result = run(args.transport, args.transport_sha, args.out, args.timeout)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(1, f"Wire verification rejected: {exc}\n")
    print(args.out / "report.json")
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
