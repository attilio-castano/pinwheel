"""Emit Pinwheel depth-two bench fixtures or run them on a local pin simulator."""

import argparse
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from streaming_peers import StreamingSPIPeer
from streaming_ready_compile import i2c_image
from streaming_ready_peers import payloads as i2c_payloads
from streaming_ready_transport import ReadyHost, pack_read, pack_write
from streaming_ready_wire_cases import run_i2c_case
from streaming_rtl import QuadRTL
from streaming_transport import Opcode, QuadTransport, command
from streaming_uart_compile import uart_image
from streaming_uart_legacy_cases import ready_image
from streaming_uart_wire_cases import Recording, receive_frame
from streaming_wire_cases import packed_bits, payloads as stream_payloads


DEPTH = 2
TOP = "tt_um_pinwheel_streaming_ready_d2"
UART_QUARTERS = 4
UART_BYTE = 0x96
SPI_BITS = 64
I2C_ADDRESS = 0x52
# I2C timing (low_cycles, high_cycles, wait_budget) by bus mode at a 4 MHz core
# clock, from the board clock guide (docs/board-clock-guide.md, Lean `guide`).
# "default" keeps the frozen bring-up program, which meets only Fast-mode Plus.
# The mode-specific programs use the largest poll budget: a target may then
# stretch SCL for 252 core clocks (63 us), since slower modes stretch longer.
I2C_MODES = {"default": (4, 4, 31), "fast": (5, 3, 255), "standard": (18, 18, 255)}


def fixture(i2c_mode="default"):
    low_cycles, high_cycles, wait_budget = I2C_MODES[i2c_mode]
    i2c = i2c_image(low_cycles, high_cycles, wait_budget)
    # Non-default modes say which timing they carry; the default output stays byte-identical.
    timing = {} if i2c_mode == "default" else {"i2c_mode": i2c_mode, "low_cycles": low_cycles,
                                                "high_cycles": high_cycles, "wait_budget": wait_budget,
                                                "core_hz": 4_000_000}

    spi_tx, spi_rx, _, _ = stream_payloads("spi", SPI_BITS)
    i2c_write, i2c_read = i2c_payloads()

    def program(image, **fields):
        return {"words_hex": [f"{word:016x}" for word in image.words],
                "idle_levels": image.idle_levels, "idle_enabled": image.idle_enabled, **fields}

    return {
        "schema": "pinwheel.streaming-ready-board-bringup.v1",
        "top_module": TOP,
        "queue_depth": DEPTH,
        "cold_reset": "Select the project, hold CSn high and SCK/MOSI low, then clock rst_n low and high.",
        "warm_reset_request_hex": command(0, Opcode.WARM_RESET).bytes.hex(),
        "uart_rx": program(uart_image(UART_QUARTERS), start_cells=8, quarter_cycles=UART_QUARTERS,
                           protocol_input=0, expected_rx_hex=f"{UART_BYTE:02x}"),
        "spi_duplex": program(ready_image("spi"), start_cells=SPI_BITS, half_cycles=4,
                              tx_hex=spi_tx.hex(), expected_rx_hex=spi_rx.hex()),
        "i2c_read": program(i2c, address_7bit=I2C_ADDRESS, **timing,
                            start_cells=pack_read(I2C_ADDRESS, len(i2c_read)).bit_count,
                            expected_rx_hex=i2c_read.hex()),
        "i2c_write": program(i2c, address_7bit=I2C_ADDRESS, **timing,
                             start_cells=pack_write(I2C_ADDRESS, i2c_write).bit_count,
                             tx_hex=i2c_write.hex()),
    }


def simulate_uart(vvp, executable, trace):
    recording = Recording(trace)
    try:
        with QuadRTL(vvp, executable, record_sink=recording) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=DEPTH)
            host.initialize()
            reset = host.warm_reset()
            if reset.sequence != 0 or reset.tag or reset.valid or reset.busy or reset.retained or reset.fault:
                raise RuntimeError("Cold start did not admit the empty sequence-zero warm reset")
            loaded = host.load(uart_image(UART_QUARTERS))
            report = receive_frame(rtl, transport, host, loaded, recording,
                                   q=UART_QUARTERS, profile="valid", payload=UART_BYTE)
            projected = report["projection"]
            if not projected["payload_valid"] or projected["value"] != UART_BYTE:
                raise RuntimeError("UART received the wrong 8N1 byte")
            return {"rx_hex": f"{projected['value']:02x}", "matching_release": True, "edges": rtl.cycle}
    finally:
        recording.trace.close()


def simulate_spi(vvp, executable):
    tx, rx, tx_bits, _ = stream_payloads("spi", SPI_BITS)
    peer = StreamingSPIPeer(tx, rx)
    with QuadRTL(vvp, executable) as rtl:
        host = ReadyHost(QuadTransport(rtl), depth=DEPTH)
        host.initialize()
        loaded = host.load(ready_image("spi"))
        rtl.device = peer
        pending = loaded.submit(tx_bits, bit_count=SPI_BITS)
        terminal = pending.wait(max_exchanges=16)
        if terminal.fault or pending.tx_accepted != SPI_BITS:
            raise RuntimeError("SPI did not transmit the complete fixture")
        peer.check(pending.rx_bits)
        observed = packed_bits(pending.rx_bits, msb_first=True)
        released = pending.release()
        if observed != rx or released.tag != pending.tag or released.busy or released.retained:
            raise RuntimeError("SPI response or matching release differed from the fixture")
        return {"tx_hex": tx.hex(), "rx_hex": observed.hex(), "matching_release": True, "edges": rtl.cycle}


def digest(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError("Use a regular, explicitly selected pin simulator model")
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def simulate(vvp, executable, expected_digest, i2c_mode="default"):
    if digest(executable) != expected_digest:
        raise ValueError("Pin simulator model differs from the supplied SHA-256")
    profiles = fixture(i2c_mode)
    # The default leaves image=None so the frozen run is unchanged.
    i2c = None if i2c_mode == "default" else i2c_image(*I2C_MODES[i2c_mode])
    with TemporaryDirectory(prefix="pinwheel-bringup-") as temporary:
        scratch = Path(temporary)
        cases = {"uart_rx": simulate_uart(vvp, executable, scratch / "uart-wire.bin"),
                 "spi_duplex": simulate_spi(vvp, executable)}
        for direction, profile in (("read", "varying"), ("write", "clean")):
            key = f"i2c_{direction}"
            row = run_i2c_case(vvp, executable, scratch / key, depth=DEPTH, direction=direction, profile=profile,
                               image=i2c)
            if not row["passed"]:
                raise RuntimeError(f"{key} did not pass: {row['error']}")
            expected = profiles[key].get("expected_rx_hex", profiles[key].get("tx_hex"))
            if row["projection"]["data_hex"] != expected:
                raise RuntimeError(f"{key} payload differs from the bench fixture")
            cases[key] = {"data_hex": expected, "address_7bit": row["address"],
                          "stream_cells": row["stream_cells"], "matching_release": row["cleanup"]["matching_release"],
                          "target_stretch_edges": row["peer"]["target_stretch_edges"], "edges": row["physical_edges"]}
    if digest(executable) != expected_digest:
        raise ValueError("Pin simulator model changed during the dry run")
    result = {"schema": "pinwheel.streaming-ready-pin-dry-run.v1", "passed": True,
              "scope": "Local public-pin simulation", "board_exercised": False,
              "model_sha256": expected_digest, "cases": cases}
    if i2c_mode != "default":
        low_cycles, high_cycles, wait_budget = I2C_MODES[i2c_mode]
        result.update(i2c_mode=i2c_mode, i2c_low_cycles=low_cycles, i2c_high_cycles=high_cycles,
                      i2c_wait_budget=wait_budget)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    vectors = commands.add_parser("fixture", help="Print the deterministic board bring-up vectors")
    vectors.add_argument("--i2c-mode", choices=sorted(I2C_MODES), default="default",
                         help="I2C SCL timing for a 4 MHz core clock (default: the frozen bring-up program)")
    dry_run = commands.add_parser("simulate", help="Exercise the vectors with Icarus and a public-pin model")
    dry_run.add_argument("--vvp", type=Path, required=True)
    dry_run.add_argument("--executable", type=Path, required=True)
    dry_run.add_argument("--executable-sha256", required=True)
    dry_run.add_argument("--i2c-mode", choices=sorted(I2C_MODES), default="default",
                         help="Run the I2C cases with this fixture mode (default: the frozen program)")
    args = parser.parse_args()
    try:
        result = (fixture(args.i2c_mode) if args.command == "fixture" else
                  simulate(args.vvp.resolve(strict=True), args.executable.absolute(), args.executable_sha256,
                           args.i2c_mode))
    except (OSError, RuntimeError, ValueError) as error:
        parser.exit(1, f"Pinwheel bring-up check failed: {error}\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
