#!/usr/bin/env python3
"""Replay a checked Ready register read on both emitted instruction stores."""

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import struct
import subprocess

from i2c_read_peers import I2CReadPeer
from streaming_8x4_spi_modes import exchange
from streaming_ready_artifacts import LOWERING_PASSES, lowering_copy
from streaming_ready_compile import spi_image
from streaming_ready_transport import ReadyHost, byte_bits
from streaming_ready_wrapper import bridge_source, package_source, tt_source
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport, require_accepted
from streaming_wire_cases import EdgeTrace, require
from typed_module_checks import tool_config
from typed_ready_engine import legacy_assembly
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
STORES = {"direct": "0", "registered": "1"}
ADDRESS, REGISTER, PAYLOAD = 0x53, 0xA6, 0x96
BUDGET = 36
DEADLINE_SLOT = 13
CASES = {"read": None, "write-address-nack": 0, "register-nack": 1, "read-address-nack": 2}
STATUS = ("phase", "tx_accepted", "tx_consumed", "tx_queued", "tx_free", "rx_produced", "rx_popped", "rx_queued")


def lower(run, circt, source, directory, label):
    directory.mkdir(parents=True, exist_ok=True)
    prepared = directory / f"{source.stem}-lowering.mlir"
    lowering_copy(source, prepared)
    rtl = directory / f"{source.stem}.sv"
    rtl.write_text(run([circt, prepared, *LOWERING_PASSES], label, timeout=180))
    return rtl


def diagnostic_bridge():
    """Record core accounting ports alongside, and separate from, public pads."""
    bridge = bridge_source(2)
    token = '      $display("STREAM_QUAD '
    require(bridge.count(token) == 1, "Expected one physical-edge reply in the Ready bridge")
    fields = ", ".join(f"dut.engine.status_{name}" for name in STATUS)
    probe = f'      $display("SEGMENT_STATUS{" %0d" * len(STATUS)}", {fields});\n'
    return bridge.replace(token, probe + token)


def build_rtl(run, lean, tools, out):
    emitted = {}
    for store, registered in STORES.items():
        directory = out / (store + "-emitted")
        run([*lean, "--run", "test/StreamingReadySegmentEmit.lean", directory, registered], f"emit-{store}")
        emitted[store] = directory
    direct, registered = emitted.values()
    for path in ("frontend.mlir", "frontend-interface.json"):
        require((direct / path).read_bytes() == (registered / path).read_bytes(), f"Stores disagree on {path}")
    core = legacy_assembly(direct / "core-interface.json", addr_bits=1)
    cached = legacy_assembly(registered / "core-interface.json", addr_bits=1)
    require({k: v for k, v in core.items() if k != "registers"} ==
            {k: v for k, v in cached.items() if k != "registers"}, "Stores disagree on core ports")
    require((direct / "core.mlir").read_bytes() != (registered / "core.mlir").read_bytes(),
            "Expected two distinct store circuits")
    frontend = legacy_assembly(direct / "frontend-interface.json")
    shell = out / "shell"
    frontend_rtl = lower(run, tools["circt"], direct / "frontend.mlir", shell, "lower-frontend")
    package, tt, bridge = (shell / f"{name}.sv" for name in ("package", "tt", "bridge"))
    package.write_text(package_source(core, frontend))
    tt.write_text(tt_source(2))
    bridge.write_text(diagnostic_bridge())
    builds = {}
    for store, directory in emitted.items():
        rtl = lower(run, tools["circt"], directory / "core.mlir", out / store, f"lower-{store}")
        executable = rtl.parent / "bridge.vvp"
        run([tools["iverilog"], "-g2012", "-s", "streaming_quad_host_bridge", "-o", executable,
             rtl, frontend_rtl, package, tt, bridge], f"compile-{store}")
        builds[store] = executable
    require((out / "direct/core.sv").read_bytes() != (out / "registered/core.sv").read_bytes(),
            "Lowering erased the store distinction")
    return builds


def wire_tx():
    """Independent host bit plan for target-owned ACK/data and final NACK."""
    return tuple(bit for byte in (ADDRESS << 1, REGISTER, (ADDRESS << 1) | 1)
                 for bit in (*byte_bits(byte), True)) + (True,) * 9


def read_image(run, lean, out):
    text = run([*lean, "--run", "test/StreamingReadySegmentImages.lean"], "compile-read-image")
    image = json.loads(text)
    require(image["tx_budget"] == BUDGET and tuple(image["tx_bits"]) == wire_tx(),
            "Lean image and manual wire plan disagree")
    require(0 < len(image["words"]) <= 64 and all(type(word) is int and 0 <= word < 2**64
            for word in image["words"]), "Invalid segmented image words")
    (out / "register-read-image.json").write_text(json.dumps(image, indent=2) + "\n")
    return image


def load(transport, image):
    for addr, word in enumerate(image["words"]):
        require_accepted(transport.request(Opcode.WRITE, address=addr, word=word))
    cm = require_accepted(transport.request(Opcode.COMMIT, count=len(image["words"]),
        idle_levels=image["idle_levels"], idle_enabled=image["idle_enabled"]))
    require(cm.valid and cm.tag == 0x10000 and not cm.busy and not cm.retained,
            "Cold image did not commit to the free first generation")
    return cm.generation


def status(rtl):
    words = rtl.log[-2].split()
    require(len(words) == len(STATUS) + 1 and words[0] == "SEGMENT_STATUS", "Missing core status observation")
    return dict(zip(STATUS, map(int, words[1:]), strict=True))


def deadline_aperture(edges, held_at, budget):
    # The drive releases before the first eligible poll. Each later edge
    # supplies a raw pin observation to the fixed two-stage sampler.
    released = next(row[0] for row in edges if row[0] > held_at and not row[13] & 1)
    stopped = next(row[0] for row in edges if row[0] > released and not row[11])
    require(stopped == released + budget and all(not row[16] & 1 for row in edges
            if released <= row[0] <= stopped), "SCL did not stay low through the last sampled poll")
    return dict(master_released=released, last_poll=stopped, eligible_polls=budget)


def drain(transport, owner, first, expected):
    """Collect each disjoint chunk, then send one empty acknowledgment."""
    prefix = ()
    reply = first
    for _ in range(20):
        require_accepted(reply)
        require(reply.tag == owner and reply.tx_accepted == BUDGET and reply.rx_start == len(prefix),
                "Ready receipt changed owner, accepted TX or RX prefix")
        prefix += reply.rx_bits
        require(len(prefix) <= expected, "Ready exposed a receive bit beyond the observed prefix")
        if reply.retained and not reply.rx_queued and reply.rx_valid == 0:
            require(len(prefix) == expected, "Ready terminal receive prefix is incomplete")
            return prefix, reply
        reply = transport.exchange(owner, BUDGET, len(prefix))
    raise RuntimeError("Segmented transfer did not reach a drained receive prefix")


def read_outcome(rx, terminal):
    if terminal.fault:
        return {"outcome": "deadline"}
    for slot, kind in zip((8, 17, 26), tuple(CASES)[1:], strict=True):
        if slot < len(rx) and rx[slot]:
            return {"outcome": kind}
    require(len(rx) == BUDGET, "Completed ACK path did not return a full byte")
    return {"outcome": "read", "byte": sum(bit << k for k, bit in enumerate(reversed(rx[27:35])))}


def warm_spi(rtl, transport, generation):
    spi = spi_image(mode=0)
    loaded = ReadyHost(transport, depth=2).load(spi)
    require(loaded.generation == generation + 1, "Warm reload did not increment the image generation")
    stale = transport.request(Opcode.START, expected_generation=generation, bit_count=33)
    require(stale.code is Code.REJECTED and stale.valid and not stale.busy and not stale.retained and
            stale.tag == ((generation + 1) << 16) | 1, "Stale START changed generation or acquired ownership")
    result = exchange(rtl, transport, loaded, 0, 33)
    require(result["owner_tag"] == ((generation + 1) << 16) | 2, "Warm SPI did not acquire the next transfer ID")
    return dict(image_words=list(spi.words), stale_start=asdict(stale), exchange=result)


def replay(vvp, executable, path, image, *, nack=None, deadline=False, reload=False):
    expected_slots = DEADLINE_SLOT if deadline else 36 if nack is None else 9 * (nack + 1)
    if deadline:
        stretches = (0,) * DEADLINE_SLOT + (4096,)
    else:
        stretches = (11, 0, 0, 0, 0, 0, 0, 0, 13)
    ack = tuple(int(i == nack) for i in range(3))
    peer = I2CReadPeer(ADDRESS, REGISTER, (PAYLOAD,), ack, fall_stretches=stretches)
    trace = EdgeTrace(path)
    try:
        with QuadRTL(vvp, executable, record_limit=0, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            transport.cold_reset()
            generation = load(transport, image)
            rtl.device = peer
            start = require_accepted(transport.request(Opcode.START, expected_generation=generation, bit_count=BUDGET))
            require(start.tag == 0x10001 and start.busy and not start.tx_accepted, "Unexpected START receipt")
            first = transport.exchange(start.tag, 0, 0, wire_tx())
            require(first.tx_accepted == BUDGET, "Host did not queue the full path before any branch decision")
            rx, terminal = drain(transport, start.tag, first, expected_slots)
            counters = status(rtl)
            require(counters["tx_accepted"] == BUDGET and counters["rx_produced"] == expected_slots and
                    counters["rx_popped"] == expected_slots and counters["rx_queued"] == 0,
                    "Ready changed the accepted TX count or captured/acknowledged RX ledger")
            require(terminal.fault == deadline and (counters["phase"] == (6 if deadline else 5)),
                    "NACK must complete and an unresolved data guard must time out")
            expected = tuple(map(bool, peer.expected()[:expected_slots]))
            require(rx == expected, "Sampled RX prefix differs from independently resolved public bits")
            result = read_outcome(rx, terminal)
            case = "deadline" if deadline else next(name for name, stage in CASES.items() if stage == nack)
            require(result["outcome"] == case and (case != "read" or result["byte"] == PAYLOAD),
                    "Host decoded the wrong register-read outcome")
            if deadline:
                require(peer.bits == peer.expected()[:expected_slots] and not peer.stopped and peer.starts == 1 and
                        peer.fall_stretch_arms[-1]["fall_index"] == DEADLINE_SLOT and not rtl.observation.bit(0),
                        "Missed deadline was not a real held-low data clock")
                require(counters["tx_consumed"] == expected_slots + 1,
                        "Data timeout failed to keep the TX reservation for the unqualified slot")
                wire = dict(starts=peer.starts, stopped=peer.stopped, observed_bits=peer.bits,
                            fall_stretch_arms=peer.fall_stretch_arms)
                held = transport.request(Opcode.RELEASE, tag=start.tag)
                require(held.code is Code.REJECTED and held.retained and held.fault and held.tag == start.tag and
                        held.tx_accepted == BUDGET, "Timeout unexpectedly discarded unsent TX or released custody")
                released = require_accepted(transport.request(Opcode.WARM_RESET))
                require(not released.retained and not released.valid and released.tag == start.tag,
                        "Explicit warm cancellation did not clear timeout custody")
            else:
                wire = peer.check()
                require(counters["tx_consumed"] == expected_slots and counters["tx_queued"] == 0 and
                        counters["tx_free"] == 2, "Ready early halt consumed or retained skipped TX")
                released = require_accepted(transport.request(Opcode.RELEASE, tag=start.tag))
                require(released.tag == start.tag and not released.retained and not released.busy,
                        "Exact acknowledgment did not allow owner RELEASE")
            rtl.device = None
            following = warm_spi(rtl, transport, generation) if reload else None
            commands = transport.opcode_counts
            require(commands[Opcode.WARM_RESET] == int(deadline), "Unexpected reset during segmented session")
    finally:
        recorded = trace.close()
    edges = list(struct.iter_unpack("<I16B", path.read_bytes()))
    require([row[0] for row in edges if row[1]] == [1] and len(edges) == rtl.cycle,
            "Replay did not retain every physical edge or exactly one cold reset")
    if deadline:
        wire["aperture"] = deadline_aperture(edges, peer.fall_stretch_arms[-1]["fall_edge"], image["wait_budget"])
    return dict(nack_stage=nack, missed_deadline=deadline, result=result, wire=wire, rx_bits=rx, counters=counters,
                discarded_tx=0 if deadline else BUDGET - counters["tx_consumed"], receipt=asdict(terminal),
                release=asdict(released), subsequent_spi=following, trace=recorded)


def source_hashes():
    paths = [*ROOT.glob("Pinwheel/**/*.lean"), *ROOT.glob("test/*.lean"), *ROOT.glob("scripts/*.py"),
             *(ROOT / name for name in ("Pinwheel.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
                                         "tools/hardware-toolchain.json"))]
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def source_commit():
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def check_readback(run, lean, out, cases):
    outcomes = {"read": f"some (.success {PAYLOAD})", "write-address-nack": "some .writeAddressNack",
                "register-nack": "some .registerNack", "read-address-nack": "some .readAddressNack",
                "deadline": "none"}
    source = ["import Pinwheel.Program.StreamingReadySegmentReadback",
              "open Pinwheel.Program.StreamingReadySegments", ""]
    for name, outcome in outcomes.items():
        bits = ", ".join("true" if bit else "false" for bit in cases[name]["rx_bits"])
        source.append(f"example : projectRegisterRead ⟨{ADDRESS}, {REGISTER}⟩ [{bits}] = {outcome} := by decide +kernel")
    witness = out / "ObservedSegmentReadback.lean"
    witness.write_text("\n".join(source) + "\n")
    run([*lean, witness], "check-observed-readback")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    out = fresh_directory(ROOT / "build/ready-segments", parser.parse_args().tag)
    logs = out / "logs"
    logs.mkdir()
    report = dict(schema="pinwheel.ready-segments.v1", passed=False, commands=[], source_commit=source_commit(),
                  source_sha256=source_hashes(), stores={})
    run = Commands(ROOT, logs, report["commands"])
    try:
        report["toolchain"], tools, _ = tool_config()
        lean = ["lake", "env", "lean", "-DwarningAsError=true"]
        run(["lake", "--no-cache", "build"], "build-library", timeout=1800)
        run([*lean, "test/ProofAudit.lean"], "audit-library")
        image = read_image(run, lean, out)
        report["image"] = image
        builds = build_rtl(run, lean, tools, out)
        frozen = {path: sha(path) for path in out.rglob("*") if path.is_file() and path.parent != logs}
        for store, executable in builds.items():
            directory = out / (store + "-replay")
            directory.mkdir()
            cases = {name: replay(tools["vvp"], executable, directory / f"{name}.bin", image,
                                  nack=stage, reload=stage == 0) for name, stage in CASES.items()}
            cases["deadline"] = replay(tools["vvp"], executable, directory / "deadline.bin", image, deadline=True)
            report["stores"][store] = cases
        require(report["stores"]["direct"] == report["stores"]["registered"],
                "Instruction stores changed the segmented read, custody, or warm SPI receipts")
        for name in report["stores"]["direct"]:
            direct = (out / "direct-replay" / f"{name}.bin").read_bytes()
            cached = (out / "registered-replay" / f"{name}.bin").read_bytes()
            require(direct == cached and direct and len(direct) % 20 == 0, f"Changed public pin trace: {name}")
        check_readback(run, lean, out, report["stores"]["direct"])
        require(source_commit() == report["source_commit"] and source_hashes() == report["source_sha256"],
                "Source inputs changed during replay")
        require(all(sha(path) == expected for path, expected in frozen.items()), "Emitted inputs changed during replay")
        report["artifact_sha256"] = {str(path.relative_to(out)): sha(path)
                                     for path in sorted(out.rglob("*")) if path.is_file()}
        report["passed"] = True
    except BaseException as error:
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified Ready segmented replay. Report at {out / 'report.json'}")


if __name__ == "__main__":
    main()
