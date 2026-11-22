#!/usr/bin/env python3
"""Run the GPIO-host RV32I firmware and a public-pin SPI peer on emitted RTL."""
import argparse
import importlib.util
import json
from pathlib import Path
import re

from streaming_ready_compile import spi_image
from streaming_transport import Code, Opcode, command, decode_response
from typed_module_checks import tool_config
from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("ready_segments", ROOT / "scripts/check-ready-segments.py")
segments = importlib.util.module_from_spec(spec)
spec.loader.exec_module(segments)

TRANSMIT = 0xD31C65AE
REPLIES = (0xA53CD872, 0x719B06E4)


def session():
    image = spi_image(mode=0)
    queue = [(Opcode.WRITE, dict(address=i, word=word)) for i, word in enumerate(image.words)]
    queue.extend([
        (Opcode.COMMIT, dict(count=len(image.words), idle_enabled=image.idle_enabled, idle_levels=image.idle_levels)),
        (Opcode.START, dict(expected_generation=1, bit_count=32)),
        (Opcode.EXCHANGE32, dict(tag=0x10001, tx_offset=0, rx_ack=0, data=TRANSMIT << 32)),
        (Opcode.EXCHANGE0, dict(tag=0x10001, tx_offset=32, rx_ack=0)),
        (Opcode.EXCHANGE0, dict(tag=0x10001, tx_offset=32, rx_ack=32)),
        (Opcode.RELEASE, dict(tag=0x10001)),
    ])
    return [command(i, op, **fields) for i, (op, fields) in enumerate(queue)]


def check(trace, frames, collect, reply):
    nibbles = ''.join(re.findall(r'^NIBBLE ([0-9a-f])$', trace, re.M))
    if len(nibbles) != 52 * len(frames):
        raise ValueError("Missing firmware response reads")
    receipts = [decode_response(int(nibbles[i*52:(i+1)*52], 16), i) for i in range(len(frames))]
    if any(r.code != Code.ACCEPTED or r.fault for r in receipts):
        raise ValueError("Command failed: " + str(receipts))
    capture, ack, release = receipts[collect:]
    if (capture.tag, capture.tx_accepted, capture.rx_start, capture.rx_valid, capture.data) != (
            0x10001, 32, 0, 32, reply):
        raise ValueError("Receipt differs from independent SPI reply")
    if not ack.retained or ack.rx_start != 32 or ack.rx_valid or release.tag != capture.tag or release.busy or release.retained:
        raise ValueError("Incomplete acknowledgement or release")
    if re.findall(r'^RESULT ([0-9a-f]{8})$', trace, re.M) != [f'{reply:08x}']:
        raise ValueError("Firmware did not retire the peer word to x25")
    done = re.findall(r'^DONE (\d+) ([0-9a-f]{8})$', trace, re.M)
    if len(done) != 1 or int(done[0][1], 16) != TRANSMIT:
        raise ValueError("Peer captured a different MOSI word")
    return dict(edges=int(done[0][0]), frames=len(frames), transmitted=TRANSMIT,
                firmware_x25=reply, acknowledged=ack.rx_start, released=True)


def sources(tb):
    return {**segments.source_hashes(), str(tb.relative_to(ROOT)): sha(tb)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    out = fresh_directory(ROOT / "build/processor-ready-spi", parser.parse_args().tag)
    report = dict(passed=False, commands=[], cases={})
    run = Commands(ROOT, out, report["commands"])
    tb = ROOT / "test/processor_ready_spi_tb.sv"
    try:
        manifest, tools, paths = tool_config()
        report.update(toolchain=manifest, tools={str(p): sha(p) for p in paths}, source_commit=segments.source_commit())
        report['source_sha256'] = sources(tb)
        lean = ["lake", "env", "lean", "-DwarningAsError=true"]
        run(["lake", "build", "Pinwheel.Hardware.Processor.Examples.ReadySPIExchange",
             "Pinwheel.Hardware.Processor.Examples.ReadySPISampling", "Pinwheel.Hardware.Processor.LoadableSystemExport",
             "Pinwheel.Hardware.StreamingReady.SegmentExport"], "build")
        requests = session()
        collect = len(requests)-3
        table = out / "requests.bin"
        table.write_bytes(bytes(int(n, 16) for frame in requests for n in frame.bytes.hex()))
        system = out / "system"
        run([*lean, "--run", "test/ProcessorReadySPIEmit.lean", system, table, collect], "emit-cpu")
        cpu = [system / "top.sv"]
        for name in ("core", "mmio", "ram", "bus"):
            rtl = system / (name + ".sv")
            rtl.write_text(run([tools["circt"], system / (name + ".mlir"), "--canonicalize", "--lower-seq-to-sv",
                                "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"],
                               "lower-cpu-" + name))
            cpu.append(rtl)
        stores = segments.build_rtl(run, lean, tools, out)
        shell = out / "shell"
        for store in stores:
            exe = out / store / "firmware.vvp"
            run([tools["iverilog"], "-g2012", "-s", "tb", "-o", exe, *cpu, out / store / "core.sv",
                 shell / "frontend.sv", shell / "package.sv", shell / "tt.sv", tb], "compile-firmware-" + store)
            for reply in REPLIES:
                label = f"{store}-{reply:08x}"
                trace = run([tools["vvp"], exe, f"+reply={reply:x}"], label, timeout=180)
                report["cases"][label] = check(trace, requests, collect, reply)
                rows = re.findall(r'^EDGE ([0-9a-f]{8}) ([0-9a-f]{2})$', trace, re.M)
                if len(rows) + 6 != report["cases"][label]["edges"]:
                    raise ValueError("Incomplete post-loader GPIO history")
                edges = out / (label + ".bin")
                edges.write_bytes(bytes(int(x, 16) for row in rows for x in row))
                run([*lean, "--run", "test/ProcessorReadySPIReplay.lean", table, edges, collect, reply],
                    "model-" + label, timeout=180)
                if store == "registered" and edges.read_bytes() != (out / f"direct-{reply:08x}.bin").read_bytes():
                    raise ValueError("Store variants disagree on the timed GPIO exchange")
            control = run([tools["vvp"], exe, f"+reply={REPLIES[0]:x}", "+invert-peer"], "inverted-" + store)
            try:
                check(control, requests, collect, REPLIES[0])
            except ValueError as error:
                if str(error) != "Receipt differs from independent SPI reply":
                    raise
            else:
                raise ValueError("Inverted peer escaped detection")
            # Verify the changed receipt, writeback and RELEASE actually completed.
            check(control, requests, collect, REPLIES[0] ^ 0xffffffff)
        if report["source_sha256"] != sources(tb) or report["tools"] != {str(p): sha(p) for p in paths}:
            raise ValueError("Source or tool inputs changed during replay")
        report['passed'] = True
    finally:
        report['artifact_sha256'] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
