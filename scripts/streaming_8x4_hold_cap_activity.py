"""Measure zero-delay activity on the frozen 8x4 positive I2C trace."""

import argparse
from collections import defaultdict
from pathlib import Path
import struct
import time

import process_group
from streaming_8x4_e982_g4_transport import ROOT, bind, emit, read_bound, require
from streaming_8x4_hold_cap_bringup import WIRE
from streaming_8x4_hold_cap_physical import TARGET, TRIAL
from streaming_wire_cases import EdgeTrace


SCHEMA = "pinwheel.streaming-8x4-hold-cap-workload-activity.v1"
BRIDGE = "streaming_quad_host_bridge"
SCOPE = (BRIDGE, "dut")
CYCLE_PS = 20000
EDGE = struct.Struct("<I16B")
INPUT_WIDTHS = (1, 1, 1, 4, 8, 8, 2, 8)
PORT_WIDTHS = {"clk": 1, "ena": 1, "rst_n": 1, "ui_in": 8, "uio_in": 8,
               "uio_oe": 8, "uio_out": 8, "uo_out": 8}


def selected_inputs(pins):
    wire = read_bound(pins, TRIAL / "digital-02/wire/report.json", WIRE)
    require(wire["passed"] is True and wire["fresh_public_wire_passed"] is True
            and wire["target_odb_sha256"] == TARGET["odb_sha256"] and wire["target_gds_sha256"] == TARGET["gds_sha256"],
            "Wrong candidate wire authority")
    for role in ("odb", "gds"):
        bind(pins, TARGET[role], TARGET[role + "_sha256"])
    item = wire["worker_report"]
    worker = read_bound(pins, item["path"], item["sha256"])
    directory = Path(item["path"]).parent
    require(worker["passed"] is True and worker["stage"] == "closed"
            and worker["all_actual_instances_retained"] is True and worker["clock_contraction"] is False
            and worker["actual_functional_instances"] == 42210 and worker["physical_ff_bits"] == 6039
            and worker["export"]["database_sha256"] == TARGET["odb_sha256"]
            and worker["tool_identity_before"] == worker["tool_identity_after"], "Wrong retained worker")
    request = read_bound(pins, worker["configuration"]["path"], worker["configuration"]["sha256"])
    require(wire["verified_file_sha256"][worker["configuration"]["path"]] == worker["configuration"]["sha256"],
            "Wire request differs")
    case, = [row for row in worker["i2c"]["cases"] if (row["direction"], row["profile"]) == ("read", "varying")]
    require(case["passed"] is True and case["physical_edges"] == 10419 and case["trace"]["format"] == EdgeTrace.FORMAT,
            "Wrong I2C workload or trace format")
    trace = directory / "i2c/read-varying/wire.bin"
    trace_item = bind(pins, trace, case["trace"]["sha256"])
    require(case["trace"]["edges"] == 10419 and case["trace"]["bytes"] == trace.stat().st_size == 10419 * EDGE.size
            and wire["worker_artifact_sha256"]["i2c/read-varying/wire.bin"] == trace_item["sha256"]
            and any(row == dict(trace_item, edges=10419, bytes=10419 * EDGE.size) for row in wire["traces"]),
            "Incomplete wire trace binding")

    for name in ("unchanged.sv", "cells.sv", "bridge.sv", "unchanged.vvp"):
        bind(pins, directory / name, wire["worker_artifact_sha256"][name])
    command, = [row for row in worker["commands"] if row["label"] == "unchanged"]
    compiler, vvp = (Path(request["tools"][name]) for name in ("iverilog", "vvp"))
    require(command["argv"] == [str(compiler), "-g2012", "-s", BRIDGE, "-o", str(directory / "unchanged.vvp"),
                                *[str(directory / name) for name in ("unchanged.sv", "cells.sv", "bridge.sv")]]
            and command["exit_code"] == 0
            and command["executable_sha256"] == wire["worker_artifact_sha256"]["unchanged.vvp"],
            "Wrong retained compile invocation")
    runtime = worker["tool_identity_before"]["files"]
    for path, item in runtime.items():
        require(str(Path(path).resolve(strict=True)) == item["resolved"], "Pinned Icarus runtime alias changed")
        bind(pins, item["resolved"], item["sha256"])
    require(bind(pins, compiler, command["compiler_sha256_before"])["sha256"] == command["compiler_sha256_after"],
            "Pinned Icarus compiler changed")
    bind(pins, vvp, worker["input_sha256_before"][str(vvp.resolve())])

    export = worker["export"]
    inventory_path = Path(export["receipt"]).with_name("inventory.json")
    inventory = read_bound(pins, inventory_path, export["artifacts_sha256"]["inventory.json"])
    receipt = read_bound(pins, export["receipt"], export["receipt_sha256"])
    require(receipt["database_sha256"] == TARGET["odb_sha256"] and receipt["read_only_database"] is True
            and receipt["artifacts_sha256"] == export["artifacts_sha256"], "Wrong actual pin inventory")
    return directory, compiler, vvp, trace_item, inventory


def stimulus_and_expected(trace):
    drives, observations = [], []
    for expected_cycle, (cycle, *fields) in enumerate(EDGE.iter_unpack(trace.read_bytes()), 1):
        require(cycle == expected_cycle and all(value < 1 << width for value, width in zip(fields[:8], INPUT_WIDTHS)),
                "Malformed retained trace sequence or drive")
        drives.append(" ".join(map(str, fields[:8])))
        observations.append(tuple(fields[8:]))
    require(len(drives) == 10419, "Wrong replay duration")
    return "\n".join(drives) + "\n", observations


def observed_pins(inventory):
    instances = inventory["instances"]
    signal = set(instances) - inventory["physical_only_instances"].keys()
    pins = {(name, pin) for name in signal for pin, row in instances[name]["terminals"].items()
            if row["signal_type"] in ("SIGNAL", "CLOCK")}
    ff = {(name, pin) for name in signal if instances[name]["master"] == "sg13cmos5l_dfrbpq_1"
          for pin in ("D", "CLK", "Q", "RESET_B")}
    require(len(signal) == 42210 and len(ff) == 6039 * 4 and ff <= pins, "Wrong candidate signal/FF inventory")
    return pins, ff


def vcd_activity(path, inventory, cycles):
    expected, ff = observed_pins(inventory)
    declarations, ports, scopes, timescale = set(), {}, [], []
    with path.open("rb") as stream:
        in_timescale = False
        for raw in stream:
            words = raw.decode("ascii").split()
            if not words:
                continue
            keyword = words[0]
            if keyword == "$timescale":
                in_timescale = True
                words = words[1:]
            if in_timescale:
                timescale.extend(word for word in words if word != "$end")
                in_timescale = "$end" not in words
            elif keyword == "$scope":
                require(len(words) == 4 and words[-1] == "$end", "Malformed waveform scope")
                scopes.append(words[2].removeprefix("\\"))
            elif keyword == "$upscope":
                require(scopes, "Unbalanced waveform scope")
                scopes.pop()
            elif keyword == "$var" and tuple(scopes[:2]) == SCOPE:
                name = words[4].removeprefix("\\")
                if len(scopes) == 2 and name in PORT_WIDTHS:
                    require(name not in ports and int(words[2]) == PORT_WIDTHS[name], "Wrong waveform port shape")
                    ports[name] = words[3].encode("ascii")
                elif len(scopes) == 3:
                    declarations.add((scopes[2], name))
            elif keyword == "$enddefinitions":
                require(not scopes, "Unclosed waveform scopes")
                break
        require(timescale == ["1ps"] and set(ports) == set(PORT_WIDTHS), "Unexpected waveform timescale or ports")
        require(expected <= declarations, "Waveform omitted actual DUT pins: " + str(sorted(expected - declarations)[:10]))
        aliases = defaultdict(list)
        for name, identifier in ports.items():
            aliases[identifier].append(name)
        last = {name: [b"x" * width, 0] for name, width in PORT_WIDTHS.items()}
        high = {name: [0] * width for name, width in PORT_WIDTHS.items()}
        unknown = {name: [0] * width for name, width in PORT_WIDTHS.items()}
        transitions = {name: [0] * width for name, width in PORT_WIDTHS.items()}
        clock_changes = []
        now = 0

        def advance(name, value, timestamp):
            previous, before = last[name]
            for index, bit in enumerate(reversed(previous)):
                if bit == ord("1"):
                    high[name][index] += timestamp - before
                elif bit != ord("0"):
                    unknown[name][index] += timestamp - before
            for index, (old, new) in enumerate(zip(reversed(previous), reversed(value))):
                if old in b"01" and new in b"01" and old != new:
                    transitions[name][index] += 1
            if name == "clk" and value != previous:
                clock_changes.append((timestamp, value))
            last[name] = [value, timestamp]

        for raw in stream:
            kind = raw[:1]
            if kind == b"#":
                timestamp = int(raw[1:])
                require(timestamp >= now, "Waveform time moved backward")
                now = timestamp
            elif kind in (b"0", b"1", b"x", b"z"):
                identifier = raw[1:-1]
                if identifier in aliases:
                    for name in aliases[identifier]:
                        advance(name, kind, now)
            elif kind == b"b":
                value, identifier = raw[1:].split()
                if identifier in aliases:
                    for name in aliases[identifier]:
                        width = PORT_WIDTHS[name]
                        require(len(value) <= width and all(bit in b"01xz" for bit in value), "Malformed public waveform bus")
                        advance(name, value.rjust(width, value[:1] if value[:1] in (b"x", b"z") else b"0"), now)
    require(now == cycles * CYCLE_PS and clock_changes == [(edge * CYCLE_PS // 2, b"1" if edge % 2 else b"0")
            for edge in range(2 * cycles + 1)], "Waveform clock or duration differs from the exact replay")
    for name in PORT_WIDTHS:
        advance(name, last[name][0], now)
    return dict(scope="/".join(SCOPE), timescale_ps=1, duration_ps=now, clock_period_ps=CYCLE_PS,
                clock_rising_edges=cycles, actual_signal_pins_declared=len(expected), ff_signal_pins_declared=len(ff),
                public_port_activity={name: [dict(bit=index, transitions=transitions[name][index], high_time_ps=high[name][index],
                                             unknown_time_ps=unknown[name][index]) for index in range(width)]
                                      for name, width in PORT_WIDTHS.items()})


def run(output, timeout):
    require(output.parent == TRIAL and not output.exists() and 1 <= timeout <= 300,
            "Use a fresh candidate output and a timeout of at most 300 seconds")
    start = time.monotonic()
    pins = {}
    directory, compiler, vvp, trace, inventory = selected_inputs(pins)
    producer = bind(pins, Path(__file__).resolve())
    stimulus, expected = stimulus_and_expected(Path(trace["path"]))
    original = (directory / "bridge.sv").read_text()
    anchor = '    fd=$fopen("/dev/stdin","r");'
    require(original.count(anchor) == 1 and original.count("#10;") == 2, "Retained bridge input or clock changed")
    instrumented = original.replace(anchor, '    $dumpfile("activity.vcd");\n    $dumpvars(0,dut);\n'
                                    '    fd=$fopen("stimulus.txt","r");')
    output.mkdir(exist_ok=False)
    bridge = output / "bridge.sv"
    bridge.write_text(instrumented)
    stimulus_path = output / "stimulus.txt"
    stimulus_path.write_text(stimulus)
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
    observations = [tuple(map(int, line.split()[1:])) for line in child.stdout.splitlines() if line.startswith("STREAM_QUAD ")]
    require(observations == expected, "Instrumented replay differed from an exact retained public observation")
    vcd = output / "activity.vcd"
    activity = vcd_activity(vcd, inventory, len(expected))
    artifacts = {path.name: bind(pins, path) for path in (bridge, stimulus_path, compile_log, replay_log, vcd)}
    for path, digest in tuple(pins.items()):
        bind(pins, path, digest)
    result = dict(schema=SCHEMA, status="diagnostic", target_odb_sha256=TARGET["odb_sha256"],
                  target_gds_sha256=TARGET["gds_sha256"], workload="I2C read, varying payload and clock stretch",
                  workload_cycles=len(expected), all_public_observations_replayed=True, retained_trace=trace,
                  producer=producer, compile_argv=compile_argv, replay_argv=replay_argv, compiled_model=model_item,
                  timeout_per_process_seconds=timeout, elapsed_seconds=time.monotonic() - start,
                  waveform=activity, artifacts=artifacts, verified_file_sha256=dict(sorted(pins.items())),
                  actual_simulation_activity=True, hardware_measured=False, extracted_timing_simulation=False,
                  opensta_annotation_verified=False, power_qualified=False,
                  scope="Complete retained trace replay on zero-delay pinned Liberty functions at 50 MHz, including reset.")
    emit(output / "receipt.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    run(args.out.resolve(), args.timeout)
    print(args.out / "receipt.json")


if __name__ == "__main__":
    main()
