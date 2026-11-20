#!/usr/bin/env python3
"""Replay I2C, SPI, and timed Ethernet on both Ready instruction stores."""

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import struct
import subprocess

from i2c_read_peers import I2CReadPeer
import streaming_8x4_ethernet as ethernet_replay
from streaming_peers import StreamingSPIPeer
from streaming_ready_artifacts import LOWERING_PASSES, lowering_copy
from streaming_ready_compile import spi_image
from streaming_ready_transport import CombinedI2cRead, ReadyHost, byte_bits
from streaming_ready_wrapper import bridge_source, package_source, tt_source
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport, Receipt, StreamProtocolError, StreamRejected
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
STATUS = ("phase", "generation", "transfer", "tx_accepted", "tx_consumed", "tx_queued", "tx_free",
          "rx_produced", "rx_popped", "rx_queued")
PRE_EDGE = {
    "frontend_phase": "dut.engine.frontend.r_phase",
    "tx_push": "dut.engine.core_tx_push",
    "tx_push_bits": "dut.engine.core_tx_bits",
    "pre_phase": "dut.engine.status_phase",
    "pre_tx_accepted": "dut.engine.status_tx_accepted",
    "pre_tx_consumed": "dut.engine.status_tx_consumed",
    "pre_tx_queued": "dut.engine.status_tx_queued",
    "pre_tx_free": "dut.engine.status_tx_free",
    "pre_tx_valid": "dut.engine.core.r_tx_valid",
    "pre_stream_flags": "{dut.engine.core.r_current_word[35:34], dut.engine.core.r_current_word[2:0]}",
}


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
    clock = "      clk=1;#10;clk=0;"
    require(bridge.count(token) == bridge.count(clock) == 1, "Expected one clock and reply per Ready edge")
    fields = ", ".join(f"dut.engine.status_{name}" for name in STATUS)
    probe = f'      $display("SEGMENT_STATUS{" %0d" * len(STATUS)}", {fields});\n'
    pre_fields = ", ".join(PRE_EDGE.values())
    before = f'      $display("SEGMENT_PRE{" %0d" * len(PRE_EDGE)}", {pre_fields});\n'
    return bridge.replace(clock, before + clock).replace(token, probe + token)


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


def status(rtl):
    words = rtl.log[-2].split()
    require(len(words) == len(STATUS) + 1 and words[0] == "SEGMENT_STATUS", "Missing core status observation")
    return dict(zip(STATUS, map(int, words[1:]), strict=True))


def timing_status(rtl):
    words = rtl.log[-3].split()
    require(len(words) == len(PRE_EDGE) + 1 and words[0] == "SEGMENT_PRE", "Missing pre-edge Ready observation")
    return {**status(rtl), **dict(zip(PRE_EDGE, map(int, words[1:]), strict=True))}


def deadline_aperture(edges, held_at, budget):
    # The drive releases before the first eligible poll. Each later edge
    # supplies a raw pin observation to the fixed two-stage sampler.
    released = next(row[0] for row in edges if row[0] > held_at and not row[13] & 1)
    stopped = next(row[0] for row in edges if row[0] > released and not row[11])
    require(stopped == released + budget and all(not row[16] & 1 for row in edges
            if released <= row[0] <= stopped), "SCL did not stay low through the last sampled poll")
    return dict(master_released=released, last_poll=stopped, eligible_polls=budget)


def ownership(counters, terminal, ending, exit_kind, closure):
    """Bind the public acknowledgement to the engine's independent counters."""
    owner = (counters["generation"] << 16) | counters["transfer"]
    require(terminal.retained and not terminal.busy and terminal.tag == ending.tag == owner and
            terminal.tx_accepted == counters["tx_accepted"] and terminal.rx_valid == 0 and
            terminal.rx_start == counters["rx_produced"] == counters["rx_popped"] and
            not terminal.rx_queued and not counters["rx_queued"],
            "Ready finished without the exact owner and captured RX acknowledgement")
    require(counters["tx_accepted"] >= counters["tx_consumed"], "TX consumption exceeded acceptance")
    remaining = counters["tx_accepted"] - counters["tx_consumed"]
    return dict(exit=exit_kind, closure=closure, tag=owner, ending_tag=ending.tag,
                tx_accepted=counters["tx_accepted"], tx_reserved=counters["tx_consumed"],
                tx_cancelled=remaining if exit_kind == "earlyExit" else 0,
                tx_owned=remaining if exit_kind == "timeout" else 0,
                rx_captured=counters["rx_produced"], rx_acknowledged=terminal.rx_start)


def spi_exchange(rtl, loaded, mode, count, *, stalled=False):
    size = (count + 7) // 8
    tx = bytes((0xD3 + 73 * i) & 255 for i in range(size))
    rx = bytes((0xA5 + 151 * i) & 255 for i in range(size))
    peer = StreamingSPIPeer(tx, rx, mode=mode, bit_count=count)
    rtl.device = peer
    pending = loaded.submit(peer.expected, bit_count=count)
    if stalled:
        pending.pump(max_bits=32)
        loaded.host.transport.idle(600)
        require(pending.tx_accepted == 32 and peer.selected and len(peer.bits) == 32,
                "SPI advanced during a deliberate TX credit stall")
    pending.wait(max_exchanges=20)
    counters = status(rtl)
    completed = pending.finish(max_exchanges=20)
    require(completed.release is not None and not completed.terminal.fault and
            counters["phase"] == 5 and counters["tx_accepted"] == counters["tx_consumed"] == count and
            not counters["tx_queued"] and counters["tx_free"] == 2 and
            len(completed.rx_bits) == count and completed.result == completed.rx_bits and
            completed.tx_consumed == count and completed.tx_cancelled == 0,
            "Shared runner changed the exact SPI exchange")
    observation = peer.check(completed.rx_bits, require_stall=stalled)
    require(rtl.observation.bit(4) and rtl.observation.bit(3) == int(mode == 2),
            "SPI RELEASE did not restore the idle pads")
    rtl.device = None
    return dict(mode=mode, count=count, owner_tag=pending.tag, tx_bytes=tx.hex(), rx_bytes=rx.hex(),
                end_edge=rtl.cycle, peer=observation, rx_bits=completed.rx_bits,
                counters=counters, receipt=asdict(completed.terminal), release=asdict(completed.release),
                ownership=ownership(counters, completed.terminal, completed.release, "completed", "released"))


def warm_spi(rtl, host, generation):
    spi = spi_image(mode=0)
    loaded = host.load(spi)
    require(loaded.generation == generation + 1, "Warm reload did not increment the image generation")
    stale = host.transport.request(Opcode.START, expected_generation=generation, bit_count=33)
    require(stale.code is Code.REJECTED and stale.valid and not stale.busy and not stale.retained and
            stale.tag == ((generation + 1) << 16) | 1, "Stale START changed generation or acquired ownership")
    result = spi_exchange(rtl, loaded, 0, 33)
    require(result["owner_tag"] == ((generation + 1) << 16) | 2, "Warm SPI did not acquire the next transfer ID")
    return dict(image_words=list(spi.words), stale_start=asdict(stale), exchange=result)


def replay_spi(vvp, executable, path):
    """Credit starvation and a one-bit tail exercise the fixed exchange case."""
    spi = spi_image(mode=2)
    trace = EdgeTrace(path)
    try:
        with QuadRTL(vvp, executable, record_limit=0, record_sink=trace) as rtl:
            host = ReadyHost(QuadTransport(rtl), depth=2)
            host.initialize()
            result = spi_exchange(rtl, host.load(spi), 2, 65, stalled=True)
            require(result["owner_tag"] == 0x10001 and host.transport.opcode_counts[Opcode.WARM_RESET] == 0,
                    "SPI did not finish under its original owner")
    finally:
        recorded = trace.close()
    require(recorded["edges"] == rtl.cycle, "SPI replay did not retain every physical edge")
    return dict(image_words=list(spi.words), exchange=result, trace=recorded)


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
            host = ReadyHost(transport, depth=2)
            host.initialize()
            loaded = host.load(CombinedI2cRead.from_manifest(image))
            require(loaded.generation == 1, "Cold image did not commit to the first generation")
            rtl.device = peer
            pending = loaded.submit()
            start = pending.last
            require(start.tag == 0x10001 and start.busy and not start.tx_accepted, "Unexpected START receipt")
            first = pending.pump()
            require(first.tx_accepted == BUDGET, "Host did not queue the full path before any branch decision")
            pending.wait(max_exchanges=20)
            counters = status(rtl)
            completed = pending.finish(max_exchanges=20)
            rx, terminal, released = completed.rx_bits, completed.terminal, completed.release
            require(counters["tx_accepted"] == BUDGET and counters["rx_produced"] == expected_slots and
                    counters["rx_popped"] == expected_slots and counters["rx_queued"] == 0,
                    "Ready changed the accepted TX count or captured/acknowledged RX ledger")
            require(terminal.fault == deadline and (counters["phase"] == (6 if deadline else 5)),
                    "NACK must complete and an unresolved data guard must time out")
            expected = tuple(map(bool, peer.expected()[:expected_slots]))
            require(rx == expected, "Sampled RX prefix differs from independently resolved public bits")
            result = asdict(completed.result)
            case = "deadline" if deadline else next(name for name, stage in CASES.items() if stage == nack)
            require(result == dict(outcome=case, byte=PAYLOAD if case == "read" else None),
                    "Host decoded the wrong register-read outcome")
            held = None
            if deadline:
                require(released is None and transport.opcode_counts[Opcode.WARM_RESET] == 0 and
                        transport.opcode_counts[Opcode.RELEASE] == 0,
                        "Finishing a timeout must return a live owner without sending RELEASE or WARM_RESET")
                require(peer.bits == peer.expected()[:expected_slots] and not peer.stopped and peer.starts == 1 and
                        peer.fall_stretch_arms[-1]["fall_index"] == DEADLINE_SLOT and not rtl.observation.bit(0),
                        "Missed deadline was not a real held-low data clock")
                require(counters["tx_consumed"] == expected_slots + 1,
                        "Data timeout failed to keep the TX reservation for the unqualified slot")
                wire = dict(starts=peer.starts, stopped=peer.stopped, observed_bits=peer.bits,
                            fall_stretch_arms=peer.fall_stretch_arms)
                prior_commands = transport.transactions
                try:
                    host.load(spi_image())
                except StreamProtocolError:
                    require(transport.transactions == prior_commands,
                            "Runner tried to replace a blocked image at the transport")
                else:
                    raise RuntimeError("Timed-out owner must fence the runner's next upload")
                try:
                    pending.release()
                except StreamRejected as error:
                    held = error.receipt
                else:
                    raise RuntimeError("The normal RELEASE path accepted an owner with unspent TX")
                require(held.code is Code.REJECTED and held.retained and held.fault and held.tag == start.tag and
                        held.tx_accepted == BUDGET, "Timeout unexpectedly discarded unsent TX or released custody")
                require(completed.tx_consumed is None and completed.tx_cancelled is None,
                        "Runner inferred a timeout TX disposition without a fixed terminal path")
                cancelled = pending.cancel()
                require(not cancelled.retained and not cancelled.valid and cancelled.tag == start.tag,
                        "Explicit warm cancellation did not clear timeout custody")
                ledger = (ownership(counters, terminal, held, "timeout", "retained"),
                          ownership(counters, terminal, cancelled, "timeout", "cancelled"))
            else:
                wire = peer.check()
                require(counters["tx_consumed"] == expected_slots and counters["tx_queued"] == 0 and
                        counters["tx_free"] == 2, "Ready early halt consumed or retained skipped TX")
                require(completed.tx_consumed == counters["tx_consumed"] and
                        completed.tx_cancelled == BUDGET - counters["tx_consumed"],
                        "Runner's completed TX disposition disagrees with the hardware counters")
                require(released is not None and released.tag == start.tag and not released.retained and not released.busy,
                        "Exact acknowledgment did not allow owner RELEASE")
                ledger = (ownership(counters, terminal, released,
                                    "completed" if nack is None else "earlyExit", "released"),)
                cancelled = None
            rtl.device = None
            following = warm_spi(rtl, host, loaded.generation) if reload else None
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
                release=asdict(released) if released else None, rejected_release=asdict(held) if held else None,
                cancellation=asdict(cancelled) if cancelled else None, ownership=ledger,
                subsequent_spi=following, trace=recorded)


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
    source = ["import Pinwheel.Program.StreamingSPI", "import Pinwheel.Program.StreamingReadySegmentReadback",
              "open Pinwheel.Program.StreamingReadySegments", ""]
    for name, outcome in outcomes.items():
        bits = ", ".join("true" if bit else "false" for bit in cases[name]["rx_bits"])
        source.append(f"example : projectRegisterRead ⟨{ADDRESS}, {REGISTER}⟩ [{bits}] = {outcome} := by decide +kernel")
    for mode, record in (("mode0", cases["write-address-nack"]["subsequent_spi"]), ("mode2", cases["spi"])):
        words = ", ".join(map(str, record["image_words"]))
        source.append(f"example : (Pinwheel.Program.StreamingSPI.image .{mode} 3).words = [{words}] := by decide +kernel")
    witness = out / "ObservedSegmentReadback.lean"
    witness.write_text("\n".join(source) + "\n")
    run([*lean, witness], "check-observed-readback")


def check_ownership(run, lean, out, cases, ethernet):
    reports = {name.replace("-", "_") + "_" + summary["closure"]: summary
               for name in (*CASES.keys(), "deadline") for summary in cases[name]["ownership"]}
    reports["spi_released"] = cases["spi"]["exchange"]["ownership"]
    reports["warm_spi_released"] = cases["write-address-nack"]["subsequent_spi"]["exchange"]["ownership"]
    for name, replayed in ethernet.items():
        (case,) = replayed["cases"]
        evidence = case["ownership"]
        terminal, released = (Receipt(**evidence[key]) for key in ("terminal", "release"))
        reports[f"ethernet_{name}_released"] = ownership(
            evidence["terminal_counters"], terminal, released, "completed", "released")
    source = ["import Pinwheel.Hardware.StreamingReady.ProtocolOwnership",
              "open Pinwheel.Hardware.StreamingReady.ProtocolOwnership", ""]
    for name, record in reports.items():
        source.extend([
            f"def {name} : Report :=",
            f"  {{ exit := .{record['exit']}, closure := .{record['closure']},",
            f"    tag := {record['tag']}, endingTag := {record['ending_tag']},",
            f"    txAccepted := {record['tx_accepted']}, txReserved := {record['tx_reserved']},",
            f"    txCancelled := {record['tx_cancelled']}, txOwned := {record['tx_owned']},",
            f"    rxCaptured := {record['rx_captured']}, rxAcknowledged := {record['rx_acknowledged']} }}",
            f"example : {name}.Valid := by decide +kernel", "",
        ])
    source.extend([
        "example : ¬ ({write_address_nack_released with txCancelled := 0}).Valid := by decide +kernel",
        "example : ¬ ({spi_released with endingTag := 0}).Valid := by decide +kernel",
        "example : ¬ ({spi_released with rxAcknowledged := 0}).Valid := by decide +kernel",
        "example : ¬ ({deadline_retained with closure := .released}).Valid := by decide +kernel",
    ])
    witness = out / "ObservedReadyOwnership.lean"
    witness.write_text("\n".join(source) + "\n")
    run([*lean, witness], "check-observed-ownership")


def check_ethernet_timing(run, lean, out, ethernet):
    """Match the measured host cuts and first reservation miss to Lean execution."""
    source = [
        "import Pinwheel.Hardware.StreamingReady.EthernetRefill",
        "open Pinwheel.Program",
        "open StreamingEthernetSchedule StreamingEthernetRefill",
        "set_option maxRecDepth 30000",
        "set_option maxHeartbeats 20000000",
    ]
    for name, replayed in ethernet.items():
        (case,) = replayed["cases"]
        phy = case["phy"]
        width = phy["high_ticks"]
        first = phy["first_rise"]
        require(case["name"] == name and phy["accepted"] == (name != "late"),
                "The Ethernet PHY returned the wrong verdict for its schedule")
        source.append(f"""
example : (StreamingEthernetCore.image.words, StreamingEthernetCore.idlePins) =
  ({replayed['words']}, ⟨{replayed['idle_levels']}, {replayed['idle_enabled']}⟩) := by decide +kernel

example : (List.finRange 8).map {name} = {case['refill_delays']} := by decide +kernel
""")
        bursts = case["bursts"][1:]
        launches = [burst["start"] - first for burst in bursts]
        measured_cuts = [tuple(edge - first for edge in (burst["grant"], *burst["tx_push"], burst["visible"]))
                         for burst in bursts]
        timing = case["timing"]
        missed = timing["first_missing_reservation"]
        verdict = "none" if missed is None else f"(some {missed})"
        cuts = [cut["edge"] for cut in timing["reservations"]]
        visibility = "late_visibility" if name == "late" else f"{name}_visibility (by decide)"
        reservation = "late_reservationMiss" if name == "late" else f"{name}_noReservationMiss (by decide)"
        source.append(f"""
example : (List.finRange 8).map (fun i => launch {name} i - (firstSample + 1)) =
  {launches} := by decide +kernel

example : (List.finRange 8).map (fun i =>
    let (grant, firstPush, secondPush, visible) := refillCuts {name} i
    (grant - (firstSample + 1), firstPush - (firstSample + 1),
     secondPush - (firstSample + 1), visible - (firstSample + 1))) =
  {measured_cuts} := by decide +kernel

example : checkRefillVisibility {name} {width} = true := {visibility}

example : (List.range {case['tx_bits']}).map (fun bit => ({first} + reservationCut bit) - firstSample) =
  {cuts} := by decide +kernel

example : firstReservationMiss {name} {width} = .ok {verdict} := {reservation}
""")
        if name != "late":
            payload = ", ".join(f"{byte}#8" for byte in bytes.fromhex(phy["sampled_hex"]))
            source.append(f"""
example : checkCredit {name} {width} = true := {name}_credit (by decide)

example : StreamingEthernetFrame.frameBytes = [{payload}] := by decide +kernel
""")
        else:
            require(missed is not None, "The late PHY result lacks a missed reservation")
            miss = timing["reservations"][missed]
            counters = case["ownership"]["terminal_counters"]
            code = int(case["ownership"]["release"]["code"])
            source.append(f"""
example :
  let core := (bodyAt late {width} (reservationCut {missed})).core
  core.phase = .boundary ∧ core.txConsumed = {miss['reserved_before']} ∧ core.canReserve = false :=
  late_noCreditAtMiss

example :
  let settled := (complete late {width}).run StreamingEthernetCore.program false
    ((releaseClocked {width}).take {phy['completion_delay']})
  settled.core.phase = .completed ∧ settled.core.txAccepted = {counters['tx_accepted']} ∧
    settled.core.txConsumed = {counters['tx_consumed']} ∧ settled.core.drained = true ∧
    (StreamingEthernetRefill.released late {width}).core.phase = .free ∧
    (StreamingEthernetRefill.released late {width}).host.code = {code} :=
  late_settles
""")
    witness = out / "ObservedEthernetTiming.lean"
    witness.write_text("\n".join(source) + "\n")
    run([*lean, witness], "check-observed-ethernet-timing", timeout=300)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    out = fresh_directory(ROOT / "build/ready-segments", parser.parse_args().tag)
    logs = out / "logs"
    logs.mkdir()
    report = dict(schema="pinwheel.ready-segments.v3", passed=False, commands=[], source_commit=source_commit(),
                  source_sha256=source_hashes(), stores={}, ethernet={})
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
            cases["spi"] = replay_spi(tools["vvp"], executable, directory / "spi.bin")
            report["stores"][store] = cases
            report["ethernet"][store] = {
                name: ethernet_replay.replay_timed_runner(tools["vvp"], executable,
                    directory / f"ethernet-{name}.bin", schedule=name, observe=timing_status)
                for name in ethernet_replay.REFILL_POLICIES
            }
        require(report["stores"]["direct"] == report["stores"]["registered"],
                "Instruction stores changed the segmented read, custody, or warm SPI receipts")
        require(report["ethernet"]["direct"] == report["ethernet"]["registered"],
                "Instruction stores changed the Ethernet timing or ownership receipts")
        traces = (*report["stores"]["direct"], *(f"ethernet-{name}" for name in ethernet_replay.REFILL_POLICIES))
        for name in traces:
            direct = (out / "direct-replay" / f"{name}.bin").read_bytes()
            cached = (out / "registered-replay" / f"{name}.bin").read_bytes()
            require(direct == cached and direct and len(direct) % 20 == 0, f"Changed public pin trace: {name}")
        check_readback(run, lean, out, report["stores"]["direct"])
        check_ownership(run, lean, out, report["stores"]["direct"], report["ethernet"]["direct"])
        check_ethernet_timing(run, lean, out, report["ethernet"]["direct"])
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
    print(f"Verified shared Ready protocol runner. Report at {out / 'report.json'}")


if __name__ == "__main__":
    main()
