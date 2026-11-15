"""Run the public-pin corpus on the exact logical Tiny Tapeout release netlist."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import struct
import time

from pad_io import PadDrive
from process_group import run_captured
from streaming_8x4_bringup import DEPTH, TOP
from streaming_8x4_e982_native import require, sha, write
from streaming_8x4_jane_street_source import RTL
from streaming_mapped_simulation import run_uart_cases
from streaming_peers import StreamingJTAGPeer, StreamingSPIPeer
from streaming_ready_compile import i2c_image
from streaming_ready_peers import StreamingI2cPeer, expected_rx, payloads as i2c_payloads
from streaming_ready_transport import ReadyHost, pack_read, project
from streaming_ready_wire_cases import run_i2c_cases
from streaming_ready_wrapper import bridge_source
from streaming_rtl import QuadRTL
from streaming_transport import Opcode, QuadTransport
from streaming_uart_compile import uart_image
from streaming_uart_legacy_cases import SCHEMA as LEGACY_SCHEMA, WORKLOADS, check_legacy_cases, ready_image
from streaming_uart_wire_cases import Recording, receive_frame
from streaming_wire_cases import EdgeTrace, packed_bits, payloads, run_stream


GDS = "d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832"
NETLIST = "6b50411924e8bcd369137c0187b25d08e2b0f1f1c5baafbce700a657d893d90e"
PDK_REVISION = "89d42ee6d2fd9b50b86a1aada6fee6673c3e6008"
PDK_MODELS = {
    "sg13cmos5l_udp.v": "5491a3edf7468792b5222e7abe057e0583a407c01b2086d4fd44a55b6cf88055",
    "sg13cmos5l_stdcell.v": "485945f1b167daa68354548f46c95bdbff7d931516fc5b4edd47f2e2cd555735",
}
SCHEMA = "pinwheel.streaming-8x4-jane-street-behavior.v1"
EDGE = struct.Struct("<I16B")
BRIDGE = "streaming_quad_host_bridge"
OBSERVATIONS = ("miso", "ready", "busy", "levels", "enabled", "wires", "known", "edge_inputs")
# SHA-256 receipts from the frozen candidate's ODB-connectivity public-wire replay.
HISTORICAL = {
    "uart/unchanged.bin": "24b7de005c177684ef914a83416feae048a3288d392b0a5ab4288cfe8969ebd7",
    "uart/sampler-ff-pin.bin": "fc1ed5963dd565691c6603fcfbaec29989232e6b18b30114cd88ac02f45e6a35",
    "legacy/spi/wire.bin": "f23b3c973d897c27ff9e516405aeeb3d2d8567b4c542b7dace02b6d239aef99c",
    "legacy/jtag/wire.bin": "ac4a14b65aba6d0d3f1b23f41e6ae760ee04848a8547573ece9fc27682e7e8b0",
    "i2c/read-address_nack/wire.bin": "7766284b2c94494ea6cbd87fe9347bfe9d4a6595b9f582a263c18b6232817b42",
    "i2c/read-clean/wire.bin": "e84d71c963e058ed8a039de6f8e6a1675d1fcb27a73c30206bb04354342a696e",
    "i2c/read-lastpoll/wire.bin": "3985a58e00615634a6f29aec316cff6bbe285ea995fde017323a29a7cd672236",
    "i2c/read-timeout/wire.bin": "3d318362dc8f88ad99f2818b787691080d310cc85f5d81d3549a37e0f232df1e",
    "i2c/read-varying/wire.bin": "c4eab37e9e5c7d78196ee739782189ff21c211ace308da8b405cfeba0d0eb690",
    "i2c/write-address_nack/wire.bin": "0ca2ec3a9eb0408159b5b0ec09a2d70032c08339099fa40feeab342ba4c7baa4",
    "i2c/write-clean/wire.bin": "49c9fdfb959dc1b7c58aa97f8b61d7a4685c40614bedbb08399a3335b7042da8",
    "i2c/write-lastpoll/wire.bin": "2a3d6e9058654eaf57ad6892c0a462b21b51589d87e761e87e162f18520490cf",
    "i2c/write-timeout/wire.bin": "b5b3a2dc24709538640c65625ec9ff22ae00acb00092aa4174e59e6f052b9acd",
    "i2c/write-varying/wire.bin": "6752e9178f5bc22bc4e79bfa2ad900465449f47a84626352ea63f26e32abafe5",
}
MUTANT_TRACE = "uart/sampler-ff-pin.bin"


def artifact(path):
    return {"sha256": sha(path), "bytes": path.stat().st_size}


def sampler_mutant(netlist, destination):
    original = netlist.read_text()
    names = (r"\engine.core._2263_", r"\engine.core._2265_")
    pins = []
    for stage, name in enumerate(names, 1):
        pattern = re.compile(r"^ sg13cmos5l_dfrbpq_1 " + re.escape(name) + r" +\(([^;]+)\);$", re.M)
        instance, = tuple(pattern.finditer(original))
        require(r".Q(\engine.core.stage" + str(stage) + " [0])" in instance[1],
                "Sampler instance lost its bound Q bit")
        pin, = tuple(re.finditer(r"\.D\(([^)]+)\)", instance[1]))
        pins.append((instance.start(1) + pin.start(1), instance.start(1) + pin.end(1), pin[1]))
    start, end, before = pins[1]
    after = pins[0][2]
    require(before == r"\engine.core._5797_.Y [0]" and after == r"\engine.core._5796_.Y [0]",
            "Sampler D roots differ from the frozen connectivity")
    with destination.open("x") as stream:
        stream.write(original[:start] + after + original[end:])
    return dict(pin="D", changed_ff_pins=1, before=before, after=after,
                source_cell=names[0][1:], changed_cell=names[1][1:], **artifact(destination))


def run_corpus(vvp, exact, mutant, mutation, out):
    uart = run_uart_cases(vvp, exact, out / "uart", depth=DEPTH, mutant=mutant, mutation=mutation)
    legacy = dict(schema=LEGACY_SCHEMA, passed=True, depth=DEPTH, cases=[])
    for protocol, count in WORKLOADS:
        directory = out / "legacy" / protocol
        row = run_stream(vvp, exact, directory, protocol=protocol, bits=count, depth=DEPTH)
        write(directory / "report.json", row)
        require(row["passed"], f"{protocol} public-wire case failed: {row.get('error')}")
        legacy["cases"].append(row)
    legacy["physical_edges"] = sum(row["physical_edges"] for row in legacy["cases"])
    check_legacy_cases(legacy)
    write(out / "legacy/report.json", legacy)
    i2c = run_i2c_cases(vvp, exact, out / "i2c", depth=DEPTH)
    require(i2c["passed"], "An I2C public-wire case failed")
    control = uart["cases"][-1]
    require(control["oracle_rejected"] is True and control["observation"]["terminal_delta"] == -1,
            "UART oracle missed the sampler pin mutation")
    require(len(uart["cases"]) + len(legacy["cases"]) + len(i2c["cases"]) == 36, "Incomplete wire corpus")
    return {"positive_cases": 35, "negative_cases": 1, "sampler_terminal_delta_edges": -1,
            "native_runs": 14, "physical_edges": sum(row["physical_edges"] for row in (uart, legacy, i2c))}


def replay_rtl(vvp, rtl, path):
    comparison = hashlib.sha256()
    with QuadRTL(vvp, rtl, record_limit=0) as simulation:
        for cycle, *fields in EDGE.iter_unpack(path.read_bytes()):
            require(cycle == simulation.cycle + 1, "Wire trace edge count is discontinuous")
            initialize, csn, sck, mosi, *drive = fields[:8]
            result = simulation.tick(csn=csn, sck=sck, mosi=mosi, initialize=initialize, drive=PadDrive(*drive))
            observed = [result[name] for name in OBSERVATIONS]
            require(observed == fields[8:], f"RTL observations differ at edge {cycle} of {path.parent.name}")
            comparison.update(EDGE.pack(cycle, *fields[:8], *observed))
    return comparison.hexdigest()


def duplex(rtl, host, protocol, count):
    tx, expected, tx_bits, expected_bits = payloads(protocol, count)
    loaded = host.load(ready_image(protocol))
    peer = (StreamingSPIPeer(tx, expected) if protocol == "spi" else
            StreamingJTAGPeer(int.from_bytes(tx, "little"), int.from_bytes(expected, "little"), count))
    rtl.device = peer
    pending = loaded.submit(tx_bits, bit_count=count)
    terminal = pending.wait(max_exchanges=32)
    require(not terminal.fault and pending.tx_accepted == count and pending.rx_bits == expected_bits,
            f"{protocol} transaction differs from external stimulus")
    peer.check(pending.rx_bits)
    observed = packed_bits(pending.rx_bits, msb_first=protocol == "spi")
    require(observed == expected, f"{protocol} payload differs")
    released = pending.release()
    require(released.tag == pending.tag and not released.busy and not released.retained,
            f"{protocol} owner was not released")
    rtl.device = None
    return dict(case=protocol, generation=loaded.generation, owner_tag=pending.tag,
                image=list(loaded.image.words), tx_hex=tx.hex(), rx_hex=observed.hex(), end_edge=rtl.cycle)


def succession(vvp, executable, path):
    recording = Recording(path)
    try:
        with QuadRTL(vvp, executable, record_sink=recording) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=DEPTH)
            host.initialize()
            loaded = host.load(uart_image(4))
            uart = receive_frame(rtl, transport, host, loaded, recording, q=4, profile="valid", payload=0x96)
            require(uart["projection"]["payload_valid"] and uart["projection"]["value"] == 0x96
                    and uart["cleanup"] == "matching-release", "Unexpected UART succession case")
            cases = [dict(case="uart", generation=loaded.generation, owner_tag=uart["owner_tag"],
                          image=list(loaded.image.words), rx_hex="96", end_edge=rtl.cycle)]
            rtl.device = None
            # Attach the I2C peer while UART's idle output enables are all off.
            loaded = host.load(i2c_image())
            _, payload = i2c_payloads()
            plan = pack_read(0x52, len(payload))
            rtl.device = StreamingI2cPeer(plan, payload, profile="varying")
            pending = loaded.submit(plan.tx_bits, bit_count=plan.bit_count)
            terminal = pending.wait(max_exchanges=96)
            require(not terminal.fault and pending.tx_accepted == plan.bit_count
                    and pending.rx_bits == expected_rx(plan, payload), "I2C succession case differs from its target")
            observed = project(plan, pending.rx_bits, fault=terminal.fault)
            require(observed.payload_valid and observed.data == payload, "I2C succession payload differs")
            peer_result = rtl.device.check(pending.rx_bits)
            require(peer_result["target_stretch_edges"] > 0, "I2C target did not stretch SCL")
            released = pending.release()
            require(released.tag == pending.tag and not released.busy and not released.retained,
                    "I2C succession owner was not released")
            cases.append(dict(case="i2c_read", generation=loaded.generation, image=list(loaded.image.words),
                              owner_tag=pending.tag, rx_hex=observed.data.hex(), end_edge=rtl.cycle,
                              target_stretch_edges=peer_result["target_stretch_edges"]))
            rtl.device = None
            cases.append(duplex(rtl, host, "spi", 64))
            cases.append(duplex(rtl, host, "jtag", 65))
            require(len({tuple(case["image"]) for case in cases}) == 4 and
                    [case["generation"] for case in cases] == [1, 2, 3, 4] and
                    len({case["owner_tag"] for case in cases}) == 4 and
                    all(transport.opcode_counts[opcode] == 4 for opcode in (Opcode.COMMIT, Opcode.START, Opcode.RELEASE))
                    and transport.opcode_counts[Opcode.WARM_RESET] == 0,
                    "Successive protocol images did not execute on one uninterrupted instance")
        return dict(cases=cases, trace=recording.trace.close(), exit_code=rtl.process.returncode,
                    native_processes=1, cold_resets=1, warm_resets=0)
    finally:
        recording.trace.close()


def compile_model(compiler, out, name, sources):
    result = out / (name + ".vvp")
    argv = [str(compiler), "-g2012", "-DGL_TEST", "-DFUNCTIONAL", "-DSIM", "-s", BRIDGE,
            "-o", str(result), *map(str, sources)]
    run = run_captured(argv, cwd=out, timeout=300, log_path=out / (name + "-compile.log"))
    require(run.returncode == 0, f"Compilation failed for {name}: see its compile log")
    return result, dict(argv=argv, output=artifact(result), exit_code=run.returncode)


def run(release, models, compiler, vvp, out, suite):
    paths = {release / f"release/{TOP}.gds": GDS, release / f"release/{TOP}.v": NETLIST}
    paths.update({release / "src" / name: digest for name, digest in RTL.items()})
    paths.update({models / name: digest for name, digest in PDK_MODELS.items()})
    require(all(sha(path) == digest for path, digest in paths.items()), "Release or vendor model hash differs")
    sources = [release / "src" / name for name in RTL]
    vendor = [models / name for name in PDK_MODELS]
    netlist = release / f"release/{TOP}.v"
    out.mkdir(parents=True, exist_ok=False)
    result = dict(schema=SCHEMA, passed=False, scope="Finite functional public-pin simulation",
                  target_gds_sha256=GDS, netlist_sha256=NETLIST, pdk_revision=PDK_REVISION,
                  inputs={str(path): artifact(path) for path in [*paths, compiler, vvp, Path(__file__)]},
                  stages={}, suite=suite, board_exercised=False)
    started = time.monotonic()
    try:
        bridge = out / "bridge.sv"
        bridge.write_text(bridge_source(DEPTH))
        result["bridge"] = artifact(bridge)
        compiled = {}
        for name, files in {"exact": [*vendor, netlist], "rtl": sources}.items():
            compiled[name], result["stages"][name] = compile_model(compiler, out, name, [*files, bridge])
        write(out / "progress.json", result)
        result["succession"] = {}
        for name in ("exact", "rtl"):
            result["succession"][name] = succession(vvp, compiled[name], out / (name + "-succession.bin"))
        require(result["succession"]["exact"] == result["succession"]["rtl"], "Succession public observations differ")
        write(out / "progress.json", result)
        if suite == "all":
            mutant_source = out / "sampler-mutant.v"
            result["mutation"] = sampler_mutant(netlist, mutant_source)
            mutant, result["stages"]["mutant"] = compile_model(compiler, out, "mutant", [*vendor, mutant_source, bridge])
            result["corpus"] = run_corpus(vvp, compiled["exact"], mutant, result["mutation"], out)
            require(result["corpus"]["physical_edges"] == 513297, "Unexpected complete physical edge count")
            result["historical_traces"] = {path: artifact(out / path) for path in HISTORICAL}
            require(all(row["sha256"] == HISTORICAL[path] for path, row in result["historical_traces"].items()),
                    "A public-pin trace differs from the historical physical replay")
            write(out / "progress.json", result)
            result["rtl_trace_replays"] = {}
            for path, expected in HISTORICAL.items():
                if path != MUTANT_TRACE:
                    observed = replay_rtl(vvp, compiled["rtl"], out / path)
                    require(observed == expected, f"RTL public-pin trace hash differs for {path}")
                    result["rtl_trace_replays"][path] = observed
        require(result["inputs"] == {str(path): artifact(path) for path in [*paths, compiler, vvp, Path(__file__)]},
                "Release or vendor model changed during simulation")
        result["passed"] = True
    except BaseException as error:
        result["error"] = repr(error)
        raise
    finally:
        result["elapsed_seconds"] = time.monotonic() - started
        write(out / "receipt.json", result)
    print(json.dumps(dict(passed=True, corpus=result.get("corpus"), succession=result["succession"]["exact"],
                          elapsed_seconds=result["elapsed_seconds"]), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("release", "models", "iverilog", "vvp", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--suite", choices=("all", "demo"), default="all",
                        help="Run the complete regression or just the four-protocol succession fixture")
    args = parser.parse_args()
    run(args.release.resolve(strict=True), args.models.resolve(strict=True), args.iverilog.resolve(strict=True),
        args.vvp.resolve(strict=True), args.out.resolve(), args.suite)


if __name__ == "__main__":
    main()
