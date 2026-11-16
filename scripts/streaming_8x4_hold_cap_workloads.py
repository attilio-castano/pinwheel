"""Produce checked zero-delay activity for four finite frozen 8×4 workloads."""

import argparse
from pathlib import Path
import time

import process_group
import streaming_8x4_bringup as bench
from streaming_8x4_e982_g4_transport import ROOT, bind, emit, read_bound, require
from streaming_8x4_hold_cap_activity import BRIDGE, EDGE, INPUT_WIDTHS, selected_inputs, vcd_activity
from streaming_8x4_hold_cap_bringup import WIRE
from streaming_8x4_hold_cap_physical import TARGET, TRIAL
from streaming_ready_compile import i2c_image
from streaming_ready_transport import ReadyHost
from streaming_rtl import QuadRTL
from streaming_transport import Opcode, QuadTransport
from streaming_tt_wire_binding import dependency_closure
from streaming_uart_compile import uart_image
from streaming_wire_cases import EdgeTrace, run_stream


SCHEMA = "pinwheel.streaming-8x4-hold-cap-workload-suite.v1"
CASES = ("i2c-write", "spi", "uart", "reset-upload")


def retained_write(pins, directory):
    wire = read_bound(pins, TRIAL / "digital-02/wire/report.json", WIRE)
    worker = wire["worker_artifact_sha256"]
    prefix = "i2c/write-varying/"
    report = read_bound(pins, directory / prefix / "report.json", worker[prefix + "report.json"])
    trace = bind(pins, directory / prefix / "wire.bin", worker[prefix + "wire.bin"])
    record = report["trace"]
    require(report["passed"] is True and (report["direction"], report["profile"], report["depth"]) == ("write", "varying", 2)
            and report["physical_edges"] == record["edges"] and report["payload_bytes"] == 64
            and report["projection"]["complete"] and report["projection"]["payload_valid"]
            and report["cleanup"]["matching_release"] and report["peer"]["target_stretch_edges"] > 0
            and any(item == dict(trace, edges=record["edges"], bytes=record["bytes"]) for item in wire["traces"]),
            "Incomplete frozen I2C write evidence")
    return trace, record, dict(payload_bytes=report["payload_bytes"], address_7bit=report["address"],
                               target_stretch_edges=report["peer"]["target_stretch_edges"], matching_release=True)


def reset_upload(vvp, executable, trace):
    phases = {}
    with QuadRTL(vvp, executable, record_sink=trace) as rtl:
        transport = QuadTransport(rtl)
        host = ReadyHost(transport, depth=2)
        host.initialize()
        phases["after_cold_reset"] = rtl.cycle
        reset = host.warm_reset()
        require(reset.sequence == 0 and not (reset.tag or reset.valid or reset.busy or reset.retained or reset.fault),
                "Warm reset failed to establish empty ownership")
        phases["after_warm_reset"] = rtl.cycle
        first = host.load(uart_image(4))
        phases["after_first_commit"] = rtl.cycle
        transport.idle(512)
        phases["after_first_idle"] = rtl.cycle
        replacement = host.load(i2c_image())
        phases["after_replacement_commit"] = rtl.cycle
        transport.idle(512)
        phases["after_replacement_idle"] = rtl.cycle
        counts = {op.name: transport.opcode_counts[op] for op in (Opcode.WARM_RESET, Opcode.WRITE, Opcode.COMMIT)}
        require(first.image.words != replacement.image.words and replacement.generation == first.generation + 1
                and counts == dict(WARM_RESET=1, WRITE=len(first.image.words) + len(replacement.image.words), COMMIT=2),
                "Incomplete checked replacement-upload sequence")
    return dict(phases_at_edge=phases, opcodes=counts, upload_words=[len(first.image.words), len(replacement.image.words)],
                committed_generations=[first.generation, replacement.generation])


def checked_trace(case, pins, directory, output, vvp):
    if case == "i2c-write":
        return retained_write(pins, directory)
    executable = directory / "unchanged.vvp"
    if case == "spi":
        bits = 1024
        report = run_stream(vvp, executable, output / "spi", protocol="spi", bits=bits, depth=2)
        emit(output / "spi/report.json", report)
        bind(pins, output / "spi/report.json")
        require(report["passed"] is True and report["bits"] == bits and report["start_count"] == 1
                and report["release"]["tag"] == report["owner_tag"], "SPI public transfer or release failed")
        return bind(pins, output / "spi/wire.bin"), report["trace"], {
            key: report[key] for key in ("bits", "tx_sha256", "rx_sha256", "opcode_counts", "peer", "release")}
    path = output / "wire.bin"
    if case == "uart":
        measured = bench.simulate_uart(vvp, executable, path)
        prior = read_bound(pins, TRIAL / "rehearsal-bringup-01/receipt.json")
        require(prior["passed"] is True and prior["target_odb_sha256"] == TARGET["odb_sha256"]
                and prior["target_gds_sha256"] == TARGET["gds_sha256"]
                and prior["model"] == bind(pins, executable) and measured == prior["cases"]["uart_rx"],
                "UART public fixture differs from the exact bring-up evidence")
        recording = dict(edges=measured["edges"], bytes=measured["edges"] * EDGE.size, format=EdgeTrace.FORMAT)
    else:
        recorder = EdgeTrace(path)
        try:
            measured = reset_upload(vvp, executable, recorder)
        finally:
            recording = recorder.close()
    trace = bind(pins, path)
    return trace, dict(recording, sha256=trace["sha256"]), measured


def restore_stimulus(path, trace, record):
    source = Path(trace["path"])
    require(record["format"] == EdgeTrace.FORMAT and record["sha256"] == trace["sha256"]
            and 0 < record["edges"] <= 100000 and record["bytes"] == record["edges"] * EDGE.size == source.stat().st_size,
            "Bad workload trace identity or extent")
    observations = []
    with path.open("x") as drives:
        for expected_cycle, (cycle, *fields) in enumerate(EDGE.iter_unpack(source.read_bytes()), 1):
            require(cycle == expected_cycle and all(value < 1 << width for value, width in zip(fields[:8], INPUT_WIDTHS)),
                    "Noncontiguous trace or invalid drive fields")
            drives.write(" ".join(map(str, fields[:8])) + "\n")
            observations.append(tuple(fields[8:]))
    require(len(observations) == record["edges"], "Wrong recorded workload duration")
    return observations


def run(case, output, timeout):
    require(output.parent == TRIAL and not output.exists() and 1 <= timeout <= 300,
            "Use a fresh candidate output and a timeout of at most 300 seconds")
    start, pins = time.monotonic(), {}
    directory, compiler, vvp, _, inventory = selected_inputs(pins)
    producer = bind(pins, Path(__file__).resolve())
    for source in dependency_closure(ROOT, [str(Path(bench.__file__).resolve().relative_to(ROOT))])["files"]:
        bind(pins, ROOT / source)
    bind(pins, Path(selected_inputs.__code__.co_filename))
    bind(pins, Path(process_group.__file__))
    output.mkdir(exist_ok=False)
    trace, record, protocol = checked_trace(case, pins, directory, output, vvp)
    stimulus = output / "stimulus.txt"
    expected = restore_stimulus(stimulus, trace, record)
    bridge = output / "bridge.sv"
    original = (directory / "bridge.sv").read_text()
    anchor = '    fd=$fopen("/dev/stdin","r");'
    require(original.count(anchor) == 1 and original.count("#10;") == 2, "Wrong frozen bridge")
    bridge.write_text(original.replace(anchor, '    $dumpfile("activity.vcd");\n    $dumpvars(0,dut);\n'
                                      '    fd=$fopen("stimulus.txt","r");'))
    model = output / "activity.vvp"
    compile_argv = [str(compiler), "-g2012", "-s", BRIDGE, "-o", str(model),
                    str(directory / "unchanged.sv"), str(directory / "cells.sv"), str(bridge)]
    compile_log = output / "compile.log"
    child = process_group.run_captured(compile_argv, cwd=output, timeout=timeout, log_path=compile_log)
    require(child.returncode == 0 and not child.stderr, "Instrumented Icarus compile failed")
    model_item = bind(pins, model)
    replay_argv = [str(vvp), str(model)]
    replay_log = output / "replay.log"
    child = process_group.run_captured(replay_argv, cwd=output, timeout=timeout, log_path=replay_log)
    require(child.returncode == 0 and not child.stderr, "Instrumented trace replay failed")
    observed = [tuple(map(int, line.split()[1:])) for line in child.stdout.splitlines() if line.startswith("STREAM_QUAD ")]
    require(observed == expected, "Instrumented replay differed from an exact uninstrumented public observation")
    vcd = output / "activity.vcd"
    waveform = vcd_activity(vcd, inventory, len(expected))
    artifacts = {path.name: bind(pins, path) for path in (bridge, stimulus, compile_log, replay_log, vcd)}
    for path, digest in tuple(pins.items()):
        bind(pins, path, digest)
    emit(output / "receipt.json", dict(
        schema=SCHEMA, status="diagnostic", workload=case, workload_cycles=len(expected), protocol_checks=protocol,
        target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
        all_public_observations_replayed=True, uninstrumented_trace=trace, trace_record=record,
        producer=producer, compile_argv=compile_argv, replay_argv=replay_argv, compiled_model=model_item, waveform=waveform,
        artifacts=artifacts, verified_file_sha256=dict(sorted(pins.items())), elapsed_seconds=time.monotonic() - start,
        actual_simulation_activity=True, hardware_measured=False, extracted_timing_simulation=False,
        opensta_annotation_verified=False, power_qualified=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=CASES, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    run(args.case, args.out.resolve(), args.timeout)
    print(args.out / "receipt.json")


if __name__ == "__main__":
    main()
