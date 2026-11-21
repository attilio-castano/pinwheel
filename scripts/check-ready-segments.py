#!/usr/bin/env python3
"""Replay segmented protocols on both source-emitted Ready instruction stores."""

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import struct
import subprocess

from i2c_read_peers import I2CReadPeer, I2CReadWireError
import streaming_8x4_ethernet as ethernet_replay
import streaming_8x4_swd_dpidr as dpidr_replay
from streaming_peers import StreamingSPIPeer
from streaming_ready_artifacts import LOWERING_PASSES, lowering_copy
from streaming_ready_compile import spi_image
import streaming_ready_swd_branching_replay as swd_replay
from streaming_ready_switch_replay import replay_switch
from streaming_ready_transport import BranchingSwdRead, CombinedI2cRead, ReadyHost, byte_bits
from streaming_ready_wrapper import bridge_source, package_source, tt_source
from streaming_rtl import QuadRTL
from streaming_transport import (Code, Opcode, QuadTransport, Receipt, StreamProtocolError, StreamRejected,
                                 StreamTransportError)
from streaming_wire_cases import EdgeTrace, require
from typed_module_checks import tool_config
from typed_ready_engine import legacy_assembly
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
STORES = {"direct": "0", "registered": "1"}
ADDRESS, REGISTER, PAYLOAD = 0x53, 0xA6, 0x96
BUDGET = 36
DEADLINE_SLOT = 13
# This controller-owned slot already releases SDA, so idle takeover after
# the fault leaves the visible late SCL rise without creating a wire STOP.
LATE_DEADLINE_SLOT = 14
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
    "command": "dut.engine.core_command",
    "command_initialize": "dut.engine.core_initialize",
    "command_address": "dut.engine.core_address",
    "command_word": "dut.engine.core_word",
    "command_count": "dut.engine.core_count",
    "command_idle_levels": "dut.engine.core_idle_levels",
    "command_idle_enabled": "dut.engine.core_idle_enabled",
    "command_generation": "dut.engine.core_expected_generation",
    "command_start_count": "dut.engine.core_start_count",
    "pc": "dut.engine.status_pc",
    "stage2": "dut.engine.status_stage2",
    "countdown": "dut.engine.core.r_countdown",
    "capture_valid": "dut.engine.core.r_capture_valid",
    "capture_bit": "dut.engine.core.r_last_capture",
    "cell_bit": "dut.engine.core.r_cell_bit",
}


def lower(run, circt, source, directory, label):
    directory.mkdir(parents=True, exist_ok=True)
    prepared = directory / f"{source.stem}-lowering.mlir"
    lowering_copy(source, prepared)
    rtl = directory / f"{source.stem}.sv"
    rtl.write_text(run([circt, prepared, *LOWERING_PASSES], label, timeout=180))
    return rtl


def diagnostic_bridge(*, swdio_link=False):
    """Record core accounting ports alongside, and separate from, public pads."""
    bridge = bridge_source(2, swdio_link=swdio_link)
    token = '      $display("STREAM_QUAD '
    clock = "      clk=1;#10;clk=0;"
    require(bridge.count(token) == bridge.count(clock) == 1, "Expected one clock and reply per Ready edge")
    fields = ", ".join(f"dut.engine.status_{name}" for name in STATUS)
    probe = f'      $display("SEGMENT_STATUS{" %0d" * len(STATUS)}", {fields});\n'
    pre_fields = ", ".join(PRE_EDGE.values())
    before = f'      $display("SEGMENT_PRE{" %0d" * len(PRE_EDGE)}", {pre_fields});\n'
    return bridge.replace(clock, before + clock).replace(token, probe + token)


def compile_bridge(run, tools, core, frontend, package, tt, bridge, label):
    executable = core.parent / f"{bridge.stem}.vvp"
    run([tools["iverilog"], "-g2012", "-s", "streaming_quad_host_bridge", "-o", executable,
         core, frontend, package, tt, bridge], label)
    return executable


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
        builds[store] = compile_bridge(run, tools, rtl, frontend_rtl, package, tt, bridge, f"compile-{store}")
    require((out / "direct/core.sv").read_bytes() != (out / "registered/core.sv").read_bytes(),
            "Lowering erased the store distinction")
    return builds


def build_swd_bridges(run, tools, out):
    shell = out / "shell"
    bridge = shell / "swd-bridge.sv"
    bridge.write_text(diagnostic_bridge(swdio_link=True))
    return {store: compile_bridge(run, tools, out / store / "core.sv", shell / "frontend.sv",
                                  shell / "package.sv", shell / "tt.sv", bridge, f"compile-swd-{store}")
            for store in STORES}


def wire_tx():
    """Independent host bit plan for target-owned ACK/data and final NACK."""
    return tuple(bit for byte in (ADDRESS << 1, REGISTER, (ADDRESS << 1) | 1)
                 for bit in (*byte_bits(byte), True)) + (True,) * 9


def read_image(run, lean, out, variant="standard"):
    arguments = [] if variant == "standard" else [variant]
    text = run([*lean, "--run", "test/StreamingReadySegmentImages.lean", *arguments], f"compile-read-{variant}")
    image = json.loads(text)
    require(image["tx_budget"] == BUDGET and tuple(image["tx_bits"]) == wire_tx(),
            "Lean image and manual wire plan disagree")
    require(0 < len(image["words"]) <= 64 and all(type(word) is int and 0 <= word < 2**64
            for word in image["words"]), "Invalid segmented image words")
    path = "register-read-image.json" if variant == "standard" else f"register-read-{variant}.json"
    (out / path).write_text(json.dumps(image, indent=2) + "\n")
    return image


def read_swd_images(run, lean, out):
    manifests = {}
    for name in ("standard", "inverted-ack", "short-turnaround"):
        raw = run([*lean, "--run", "test/StreamingReadySWDImages.lean", name], f"compile-swd-{name}-image")
        manifest = json.loads(raw)
        (out / f"swd-{name}-image.json").write_text(json.dumps(manifest, indent=2) + "\n")
        manifests[name] = manifest
    return manifests


def replay_swd(vvp, executable, directory, manifests):
    images = {name: BranchingSwdRead.from_manifest(manifest) for name, manifest in manifests.items()}
    reports = {"standard": swd_replay.replay(vvp, executable, directory / "swd-standard.bin", images["standard"],
                                             observe=timing_status, execution=segment_execution)}
    for name in ("inverted-ack", "short-turnaround"):
        reports[name] = swd_replay.replay_negative(vvp, executable, directory / f"swd-{name}.bin",
                                                   images[name], name, observe=timing_status)
    reports["dpidr"] = dpidr_replay.replay(vvp, executable, directory / "swd-dpidr.bin")
    return reports


def status(rtl):
    words = rtl.log[-2].split()
    require(len(words) == len(STATUS) + 1 and words[0] == "SEGMENT_STATUS", "Missing core status observation")
    return dict(zip(STATUS, map(int, words[1:]), strict=True))


def timing_status(rtl):
    words = rtl.log[-3].split()
    require(len(words) == len(PRE_EDGE) + 1 and words[0] == "SEGMENT_PRE", "Missing pre-edge Ready observation")
    return {**status(rtl), **dict(zip(PRE_EDGE, map(int, words[1:]), strict=True))}


def observe_core(rtl, trace, observations):
    def record(edge):
        trace(edge)
        observations.append(clock_observation(edge, timing_status(rtl)))
    rtl.record_sink = record


def clock_observation(edge, core):
    return {"edge": edge["cycle"], "raw": edge["observation"]["edge_inputs"], **core}


def segment_execution(edges, words):
    """Resolve service windows from public raw pins at the actual clock cuts."""
    start = next(index for index, cut in enumerate(edges)
                 if cut["command"] == 3 and cut["pre_phase"] == 0 and cut["phase"] == 1)
    fetches, supplies, branches, tx_bits, rx_bits = [], [], [], [], []
    polls, parked, slots, terminal = [], 0, 0, None
    require(start >= 1, "Clock trace must start before the START aperture")
    for index in range(start + 1, len(edges) - 1):
        cut, following = edges[index], edges[index + 1]
        before, middle = edges[index - 2:index]
        require((before["edge"], middle["edge"]) == (cut["edge"] - 2, cut["edge"] - 1) and
                not any(step["command_initialize"] or step["command"] == 15 for step in (before, middle)),
                "Ordinary consecutive clocks required at the sampler aperture")
        raw_sample = before["raw"]
        require(cut["stage2"] == raw_sample, "Second sampler differs from the public pins two clocks earlier")
        phase = cut["pre_phase"]
        kind = cut["pre_stream_flags"] & 7
        if phase == 1:
            pc = cut["pc"]
            require(pc < len(words), "Fetched outside the uploaded segmented image")
            fetches.append(pc)
            slots = 0
            if words[pc] & 7 == 6:
                require(cut["capture_valid"] == 1 and following["capture_valid"] == 0 and cut["phase"] == 1,
                        "Branch did not consume a qualified latched sample")
                branches.append({"pc": pc, "bit": bool(cut["capture_bit"]), "next_pc": following["pc"]})
        if phase == 2 and kind == 1:
            transmits = bool(cut["pre_stream_flags"] & 8)
            receives = bool(cut["pre_stream_flags"] & 16)
            tx_available = bool(cut["pre_tx_valid"] or cut["pre_tx_queued"])
            # The preceding clock's result is the input to this reservation.
            # A concurrent pop or offer supplies credit on the following edge.
            rx_room = middle["rx_queued"] < 2
            credit = (not transmits or tx_available) and (not receives or rx_room)
            require(cut["phase"] == (3 if credit else 2),
                    "Segmented stream did not reserve from pre-edge host credit")
            if cut["phase"] == 2:
                parked += 1
            else:
                require(cut["tx_consumed"] == cut["pre_tx_consumed"] + int(transmits),
                        "Segmented stream left its boundary with the wrong TX reservation")
                if transmits:
                    tx_bits.append(bool(following["cell_bit"]))
        if phase == 3 and kind == 1 and cut["phase"] == 4:
            supplies.append({"kind": "cell", "parked": parked, "samples": [raw_sample]})
            parked = 0
            slots += 1
        if phase == 7:
            polls.append(raw_sample)
            if cut["phase"] != 7:
                if kind == 1:
                    supplies.append({"kind": "cell", "parked": parked, "samples": polls})
                    parked = 0
                    slots += 1
                else:
                    require(kind == 4, "Unexpected word at a standalone guard poll")
                    supplies.append({"kind": "wait", "samples": polls})
                polls = []
        if phase in (3, 7) and cut["phase"] == 4 and kind == 1 and cut["pre_stream_flags"] & 16:
            source = (words[cut["pc"]] >> 33) & 1
            rx_bits.append(bool((raw_sample >> source) & 1))
        if cut["phase"] in (5, 6):
            terminal = {"pc": cut["pc"], "phase": cut["phase"],
                        "edge": cut["edge"], "clocks": cut["edge"] - edges[start]["edge"],
                        "slot": slots - 1 if phase == 7 and kind == 1 else 0,
                        "poll_countdown": cut["countdown"], "tx_reserved": cut["tx_consumed"],
                        "rx_produced": cut["rx_produced"]}
            break
    if terminal is not None:
        require((len(tx_bits), len(rx_bits)) == (terminal["tx_reserved"], terminal["rx_produced"]),
                "Trace lost a reservation or capture")
    return {"fetches": fetches, "supplies": supplies, "branches": branches,
            "tx_bits": tx_bits, "rx_bits": rx_bits, "terminal": terminal}


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


def i2c_exchange(rtl, host, loaded, image, *, nack=None, deadline=False, blocked_image=None, aperture_stretch=None):
    """Run one read on the current owner generation and the existing pin trace."""
    transport = host.transport
    prior_counts = transport.opcode_counts.copy()
    late = deadline and aperture_stretch is not None
    stretch_slot, stretch_duration = aperture_stretch or (DEADLINE_SLOT, 4096)
    expected_slots = stretch_slot if deadline else 36 if nack is None else 9 * (nack + 1)
    if deadline or aperture_stretch is not None:
        stretches = (0,) * stretch_slot + (stretch_duration,)
    else:
        stretches = (11, 0, 0, 0, 0, 0, 0, 0, 13)
    ack = tuple(int(i == nack) for i in range(3))
    peer = I2CReadPeer(ADDRESS, REGISTER, (PAYLOAD,), ack, fall_stretches=stretches)
    trace, observations = rtl.record_sink, []
    observe_core(rtl, trace, observations)
    rtl.device = peer
    try:
        pending = loaded.submit()
        start = pending.last
        require(start.generation == loaded.generation and start.busy and not start.tx_accepted,
                "Unexpected START receipt")
        first = pending.pump()
        require(first.tx_accepted == BUDGET, "Host did not queue the full path before any branch decision")
        pending.wait(max_exchanges=20)
        counters = status(rtl)
        execution = segment_execution(observations, image["words"])
        require(execution["terminal"] is not None, "Did not observe the I2C terminal cut")
    finally:
        rtl.record_sink = trace
    completed = pending.finish(max_exchanges=20)
    rx, terminal, released = completed.rx_bits, completed.terminal, completed.release
    require(list(rx) == execution["rx_bits"], "Host RX differs from chronological raw-pin captures")
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
    fences = {}
    if deadline:
        require(released is None and
                transport.opcode_counts[Opcode.WARM_RESET] == prior_counts[Opcode.WARM_RESET] and
                transport.opcode_counts[Opcode.RELEASE] == prior_counts[Opcode.RELEASE],
                "Finishing a timeout must return a live owner without sending RELEASE or WARM_RESET")
        wire_slots = expected_slots + int(late)
        require(peer.bits == peer.expected()[:wire_slots] and not peer.stopped and peer.starts == 1 and
                peer.fall_stretch_arms[-1]["fall_index"] == stretch_slot and bool(rtl.observation.bit(0)) == late,
                "Missed deadline did not preserve the physical clock prefix")
        require(counters["tx_consumed"] == expected_slots + 1,
                "Data timeout failed to keep the TX reservation for the unqualified slot")
        wire = dict(starts=peer.starts, stopped=peer.stopped, observed_bits=peer.bits,
                    fall_stretch_arms=peer.fall_stretch_arms)
        prior_commands = transport.transactions
        try:
            host.load(spi_image() if blocked_image is None else blocked_image)
        except StreamProtocolError:
            require(transport.transactions == prior_commands,
                    "Runner tried to replace a blocked image at the transport")
        else:
            raise RuntimeError("Timed-out owner must fence the runner's next upload")
        if blocked_image is not None:
            for opcode, fields in (
                (Opcode.WRITE, dict(address=0, word=blocked_image.words[0])),
                (Opcode.COMMIT, dict(count=len(blocked_image.words), idle_levels=blocked_image.idle_levels,
                                     idle_enabled=blocked_image.idle_enabled)),
                (Opcode.START, dict(expected_generation=loaded.generation, bit_count=64)),
            ):
                denied = transport.request(opcode, **fields)
                require(denied.code is Code.REJECTED and denied.tag == start.tag and denied.retained and
                        denied.fault and status(rtl) == counters,
                        f"Fault owner did not fence {opcode.name} at the hardware")
                fences[opcode.name] = asdict(denied)
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
    require(transport.opcode_counts[Opcode.WARM_RESET] - prior_counts[Opcode.WARM_RESET] == int(deadline),
            "Unexpected reset during segmented session")
    wire["rising_cycles"] = peer.rising_cycles
    result = dict(nack_stage=nack, missed_deadline=deadline, result=result, wire=wire, rx_bits=rx, counters=counters,
                discarded_tx=0 if deadline else BUDGET - counters["tx_consumed"], receipt=asdict(terminal),
                release=asdict(released) if released else None, rejected_release=asdict(held) if held else None,
                cancellation=asdict(cancelled) if cancelled else None, ownership=ledger,
                execution=execution)
    if blocked_image is not None:
        result.update(start=asdict(start), fault_fences=fences, settled_cut=status(rtl))
    return result


def replay(vvp, executable, path, image, *, nack=None, deadline=False, reload=False, aperture_stretch=None):
    trace = EdgeTrace(path)
    try:
        with QuadRTL(vvp, executable, record_limit=0, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=2)
            host.initialize()
            loaded = host.load(CombinedI2cRead.from_manifest(image))
            require(loaded.generation == 1, "Cold image did not commit to the first generation")
            result = i2c_exchange(rtl, host, loaded, image, nack=nack, deadline=deadline,
                                  aperture_stretch=aperture_stretch)
            require(result["receipt"]["tag"] == 0x10001, "Unexpected first I2C owner tag")
            result["subsequent_spi"] = warm_spi(rtl, host, loaded.generation) if reload else None
    finally:
        recorded = trace.close()
    edges = list(struct.iter_unpack("<I16B", path.read_bytes()))
    require([row[0] for row in edges if row[1]] == [1] and len(edges) == rtl.cycle,
            "Replay did not retain every physical edge or exactly one cold reset")
    if deadline and aperture_stretch is None:
        wire = result["wire"]
        wire["aperture"] = deadline_aperture(edges, wire["fall_stretch_arms"][-1]["fall_edge"], image["wait_budget"])
    return {**result, "trace": recorded}


def replay_deadline_edge(vvp, executable, path, image, deadline, *, late=False):
    """Release target SCL at or just after the final raw sample."""
    fault_wire = deadline["wire"]
    fault_arm = fault_wire["fall_stretch_arms"][-1]
    fault_cut = fault_wire["aperture"]
    # The stalled replay locates the final poll. The Ready sampler reads the
    # raw pin two clocks earlier, so shorten the target's stretch to that edge.
    slot = LATE_DEADLINE_SLOT if late else DEADLINE_SLOT
    stretch = fault_cut["last_poll"] - 2 + int(late) - fault_arm["fall_edge"]
    require(stretch > 0, "The timeout fixture has no stretched last-sample aperture")
    result = replay(vvp, executable, path, image, deadline=late, aperture_stretch=(slot, stretch))
    wire = result["wire"]
    (arm,) = wire["fall_stretch_arms"]
    edges = list(struct.iter_unpack("<I16B", path.read_bytes()))
    master_released = next(row[0] for row in edges if row[0] > arm["fall_edge"] and not row[13] & 1)
    raw_release = next(row[0] for row in edges if row[0] > master_released and row[16] & 1)
    budget = image["wait_budget"]
    last_poll = master_released + budget
    samples = [supply["samples"] for supply in result["execution"]["supplies"]
               if supply["kind"] == "cell"][slot]
    require(arm["fall_index"] == slot and
            raw_release == arm["first_target_release_edge"] == wire["rising_cycles"][slot] and
            raw_release + 2 == last_poll + int(late) and len(samples) == budget and
            all(not sample & 1 for sample in samples[:-1]) and bool(samples[-1] & 1) != late,
            "I2C did not distinguish the final eligible sample from a late SCL rise")
    if late:
        require(result["execution"]["terminal"]["edge"] == last_poll,
                "A physically visible late rise deferred expiry")
    wire["aperture"] = dict(master_released=master_released, target_released=raw_release,
                           last_poll=last_poll, eligible_polls=budget)
    return result


def replay_inverted_ack(vvp, executable, path, image, reference):
    """The structural checker permits the image. A success peer exposes its wrong branch."""
    trace = EdgeTrace(path)
    peer = I2CReadPeer(ADDRESS, REGISTER, (PAYLOAD,))
    observations = []
    try:
        with QuadRTL(vvp, executable, record_limit=0, record_sink=trace) as rtl:
            host = ReadyHost(QuadTransport(rtl), depth=2)
            host.initialize()
            loaded = host.load(CombinedI2cRead.from_manifest(image))
            observe_core(rtl, trace, observations)
            rtl.device = peer
            pending = loaded.submit()
            try:
                pending.pump()
                pending.wait(max_exchanges=20)
            except StreamTransportError as error:
                cause = error.cause
                if not isinstance(cause, I2CReadWireError):
                    raise
                require(str(cause) == "I2C read STOP before requested prefix/data finished",
                        f"Inverted ACK failed for a different wire reason: {cause}")
                rejection = {"category": cause.category, "message": str(cause)}
            else:
                raise RuntimeError("Inverted ACK branch passed the independent I2C wire oracle")
    finally:
        recorded = trace.close()
    execution = segment_execution(observations, image["words"])
    (branch,) = execution["branches"]
    normal = reference["execution"]["branches"][0]
    target = (image["words"][branch["pc"]] >> 3) & 63
    require(branch["pc"] == normal["pc"] and not branch["bit"] and not normal["bit"] and
            branch["next_pc"] == target and normal["next_pc"] == normal["pc"] + 1 and
            len(execution["tx_bits"]) == 9 and peer.bits[:9] == peer.expected()[:9],
            "Wire rejection did not follow the inverted branch on the first qualified ACK")
    return {"rejection": rejection, "execution": execution, "trace": recorded}


def source_hashes():
    paths = [*ROOT.glob("Pinwheel/**/*.lean"), *ROOT.glob("test/*.lean"), *ROOT.glob("scripts/*.py"),
             *(ROOT / name for name in ("Pinwheel.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
                                         "tools/hardware-toolchain.json"))]
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def source_commit():
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def check_readback(run, lean, out, cases):
    outcomes = {"read": f"some (.success {PAYLOAD})", "last-poll": f"some (.success {PAYLOAD})",
                "write-address-nack": "some .writeAddressNack",
                "register-nack": "some .registerNack", "read-address-nack": "some .readAddressNack",
                "deadline": "none", "late-poll": "none"}
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


def check_ownership(run, lean, out, cases, ethernet, split, switches, swd):
    reports = {name.replace("-", "_") + "_" + summary["closure"]: summary
               for name in (*CASES.keys(), "deadline", "last-poll", "late-poll")
               for summary in cases[name]["ownership"]}
    reports["spi_released"] = cases["spi"]["exchange"]["ownership"]
    reports["warm_spi_released"] = cases["write-address-nack"]["subsequent_spi"]["exchange"]["ownership"]
    reports.update({"split_" + name.replace("-", "_") + "_" + summary["closure"]: summary
                    for name, case in split.items() for summary in case["ownership"]})
    for name, replayed in switches.items():
        for stage in ("initial_can", "crc_control", "final_can"):
            if replayed[stage] is not None:
                reports[f"switch_{name}_{stage}"] = replayed[stage]["ownership"]
        for summary in replayed["i2c"]["ownership"]:
            reports[f"switch_{name}_i2c_{summary['closure']}"] = summary
    for name, replayed in ethernet.items():
        (case,) = replayed["cases"]
        evidence = case["ownership"]
        terminal, released = (Receipt(**evidence[key]) for key in ("terminal", "release"))
        reports[f"ethernet_{name}_released"] = ownership(
            evidence["terminal_counters"], terminal, released, "completed", "released")
    for entry in swd["standard"]["cases"]:
        reports["swd_" + entry["name"].replace("-", "_") + "_released"] = ownership(
            entry["counters"], Receipt(**entry["receipt"]), Receipt(**entry["release"]), "completed", "released")
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


def lean_bits(bits):
    return "[" + ", ".join("true" if bit else "false" for bit in bits) + "]"


def lean_samples(samples):
    return "[" + ", ".join(f"{sample}#2" for sample in samples) + "]"


def lean_observations(items):
    supplied = []
    for item in items:
        samples = lean_samples(item["samples"])
        supplied.append(f".cell {item['parked']} {samples}" if item["kind"] == "cell" else f".wait {samples}")
    return "[" + ", ".join(supplied) + "]"


def lean_branches(edges):
    branches = [(edge["bit"], edge["next_pc"] != edge["pc"] + 1) for edge in edges]
    return "[" + ", ".join(f"({str(bit).lower()}, {str(taken).lower()})" for bit, taken in branches) + "]"


def check_i2c_execution(run, lean, out, images, original, split, switches):
    """Feed sampler events observed on both stores to the branch-sensitive semantics."""
    source = [
        "import Pinwheel.Program.StreamingReadyRegisterReadVariants",
        "import Pinwheel.Program.StreamingReadySegmentExecution",
        "open Pinwheel.Program.StreamingReadySegments",
        "open Pinwheel.Program.StreamingReadySegments.Execution",
        "open Pinwheel.Program.StreamingReadyRegisterReadVariants",
        "set_option maxRecDepth 8192",
        "",
    ]
    switched = {name: replayed["i2c"] for name, replayed in switches.items()}
    variants = (("standard", "registerReadImage", "(registerReadRows .standard)", images["standard"], original),
                ("split", "splitImage", "(splitRows .standard)", images["split"], split),
                ("switch", "splitImage", "(splitRows .standard)", images["split"], switched))
    for variant, image_name, rows, manifest, cases in variants:
        source.append(f"example : {image_name}.words.map BitVec.toNat = {manifest['words']} := by decide +kernel")
        for name, case in cases.items():
            if name == "spi":
                continue
            executed = case["execution"]
            terminal = executed["terminal"]
            tx, rx = terminal["tx_reserved"], terminal["rx_produced"]
            if case["missed_deadline"]:
                require(terminal["poll_countdown"] == 0, "Fault did not expire at the final poll")
                outcome = f".timeout {terminal['pc']} {terminal['slot']}"
            else:
                kind = "complete" if case["nack_stage"] is None else "discard"
                path, = (path for path in manifest["exits"] if (path["kind"], path["tx"], path["rx"])
                         == (kind, tx, rx))
                parked = sum(item.get("parked", 0) for item in executed["supplies"])
                require(terminal["clocks"] <= path["core_clocks"] + parked,
                        "Observed execution exceeded the checked path bound plus measured credit delay")
                outcome = f".planned ⟨.{kind}, {tx}, {rx}, {path['core_clocks']}⟩"
            label = variant + "_" + name.replace("-", "_")
            if name in ("last-poll", "late-poll"):
                slot = LATE_DEADLINE_SLOT if case["missed_deadline"] else DEADLINE_SLOT
                samples = [supply["samples"] for supply in executed["supplies"]
                           if supply["kind"] == "cell"][slot]
                verdict = "none" if case["missed_deadline"] else f"(some {samples[-1]}#2)"
                source.append(f"""
example : pollWindow (Pinwheel.Program.StreamingReady.i2cGuard .standard 1 1)
    {lean_samples(samples)} = some {verdict} := by decide +kernel
""")
            source.append(f"""
def {label} := run {rows} {BUDGET} {lean_bits(manifest['tx_bits'])}
  {lean_observations(executed['supplies'])}

example : {label}.any (fun r =>
    decide (r.terminal = {outcome}) &&
    decide (r.fetchPCs = {executed['fetches']}) &&
    decide (r.branches = {lean_branches(executed['branches'])}) &&
    decide (r.txBits = {lean_bits(executed['tx_bits'])}) &&
    decide (r.rxBits = {lean_bits(case['rx_bits'])}) &&
    r.remainingObservations.isEmpty) = true := by decide +kernel
""")
    witness = out / "ObservedReadyRowExecution.lean"
    witness.write_text("\n".join(source) + "\n")
    run([*lean, witness], "check-observed-row-execution", timeout=300)


def check_swd_execution(run, lean, out, swd, manifests):
    variants = {"standard": "standard", "inverted-ack": "invertedAck", "short-turnaround": "shortTurnaround"}
    outcomes = {"wait": ".wait", "fault": ".fault", "bad-parity": ".badParity", "invalid-ack": ".invalidAck"}
    source = [
        "import Pinwheel.Hardware.StreamingReady.SWDSession",
        "import Pinwheel.Program.StreamingSWDBranching",
        "open Pinwheel.Program.StreamingSWDBranching",
        "open Pinwheel.Program.StreamingReadySegments.Execution",
        "set_option maxRecDepth 8192",
    ]
    for name, variant in variants.items():
        source.append(f"example : (image .{variant}).words.map BitVec.toNat = {swd[name]['words']} := by decide +kernel")
    source.append("example : Pinwheel.Hardware.StreamingReady.SWDSession.readImage.words.map BitVec.toNat = "
                  f"{swd['dpidr']['words']} := by decide +kernel")
    for entry in swd["standard"]["cases"]:
        name = entry["name"]
        label = "swd_" + name.replace("-", "_")
        executed = entry["execution"]
        require(list(entry["rx_bits"]) == executed["rx_bits"], "SWD RX differs from chronological raw-pin captures")
        terminal = executed["terminal"]
        parked = sum(item.get("parked", 0) for item in executed["supplies"])
        clocks = terminal["clocks"] - parked
        rx = terminal["rx_produced"]
        require(terminal["phase"] == 5 and entry["receipt"]["rx_start"] == rx and
                any((path["kind"], path["tx"], path["rx"], path["core_clocks"]) == ("complete", 0, rx, clocks)
                    for path in manifests["standard"]["exits"]),
                "SWD measured execution disagreed with its exact serviced path clocks")
        outcome = f".ok {entry['result']['word']}#32" if name == "ok" else outcomes[name]
        source.append(f"""
def {label} := run (rows 3 .standard) 0 [] {lean_observations(executed['supplies'])} idlePins
example : {label}.any (fun r =>
    decide (r.terminal = .planned ⟨.complete, 0, {rx}, {clocks}⟩) &&
    decide (r.fetchPCs = {executed['fetches']}) &&
    decide (r.branches = {lean_branches(executed['branches'])}) &&
    decide (r.rxBits = {lean_bits(entry['rx_bits'])}) &&
    decide (decode r.rxBits = {outcome}) &&
    r.txBits.isEmpty && r.remainingObservations.isEmpty) = true := by decide +kernel
""")
    witness = out / "ObservedBranchingSWD.lean"
    witness.write_text("\n".join(source) + "\n")
    run([*lean, witness], "check-observed-swd-execution")


def check_can_handoff(run, lean, out, switches):
    """Bind the installed words, measured generations, and CAN captures to Lean."""
    source = [
        "import Pinwheel.Hardware.StreamingReady.CANSession",
        "import Pinwheel.Hardware.StreamingReady.ProtocolOwnership",
        "import Pinwheel.Program.StreamingReadyRegisterReadVariants",
        "open Pinwheel.Hardware.StreamingReady.CANSession",
        "open Pinwheel.Hardware.StreamingReady.ProtocolOwnership",
        "open Pinwheel.Program.StreamingCAN Pinwheel.Program.StreamingCANCore",
        "open Pinwheel.Program.StreamingReadyRegisterReadVariants",
        "set_option maxRecDepth 8192",
    ]
    for replayed in switches.values():
        stages = (
            ("first_install", {"generation": 0, "transfer": 0}, replayed["initial_can"]["start"]),
            ("to_i2c", replayed["initial_can"]["settled_cut"], replayed["i2c"]["start"]),
            ("to_can", replayed["i2c"]["settled_cut"], (replayed["crc_control"] or replayed["final_can"])["start"]),
        )
        for name, settled, started in stages:
            handoff = replayed[name]
            image, cut = handoff["image_words"], handoff["commit_cut"]
            compiled = "splitImage.words" if name == "to_i2c" else "receiveImage.words"
            generation, transfer = cut["generation"], cut["transfer"]
            source.append(f"""
example : {compiled}.map BitVec.toNat = {image} := by decide +kernel
example : (List.range {compiled}.length) = {[write['address'] for write in handoff['writes']]} :=
  by decide +kernel
example : ({generation}#16 = {settled['generation']}#16 + 1 ∧
    {transfer}#16 = {settled['transfer']}#16 ∧
    ownerTag {generation}#16 ({transfer}#16 + 1) = {started['tag']}) := by decide +kernel
""")
            if handoff["stale_start"] is not None:
                stale = handoff["stale_cut"]
                source.append(f"""
example : ({generation}#16 ≠ {settled['generation']}#16 ∧
    ownerTag {stale['generation']}#16 {stale['transfer']}#16 = {handoff['stale_start']['tag']} ∧
    {stale['generation']}#16 = {generation}#16 ∧ {stale['transfer']}#16 = {transfer}#16) := by decide +kernel
""")
        for stage in ("initial_can", "crc_control", "final_can"):
            case = replayed[stage]
            if case is None:
                continue
            identifier, payload = case["source_identifier"], case["source_byte"]
            kind = "badCRC" if case["corrupt"] == "crc" else "valid"
            observed = lean_bits(case["captured"])
            cuts = [sample["edge"] for sample in case["capture_cuts"]]
            decoded = "none" if case["decoded"] is None else f"some ({identifier}#11, {payload}#8)"
            source.append(f"""
example : FrameCase.symbols {identifier}#11 {payload}#8 .{kind} = {observed} := by decide +kernel
example : decodeFrame {observed} = {decoded} := by decide +kernel
example : (apertures {case['wire']['sof']}).map (· + 2) = {cuts} := by decide +kernel
""")
    witness = out / "ObservedReadyHandoff.lean"
    witness.write_text("\n".join(source) + "\n")
    run([*lean, witness], "check-observed-handoff")


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


def check_causal_policies(run, lean, out):
    source = out / "causal-policies.c"
    executable = out / "causal-policies"
    run(["lake", "build", "Pinwheel:static"], "build-causal-library", timeout=1800)
    run([*lean, "-c", source, "test/StreamingReadyCausalPolicies.lean"], "compile-causal-policies")
    run(["lake", "env", "leanc", "-O3", "-o", executable, source,
         ROOT / ".lake/build/lib/libpinwheel_Pinwheel.a"], "link-causal-policies")
    return json.loads(run([executable], "check-causal-policies", timeout=300))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    out = fresh_directory(ROOT / "build/ready-segments", parser.parse_args().tag)
    logs = out / "logs"
    logs.mkdir()
    report = dict(schema="pinwheel.ready-segments.v9", passed=False, commands=[], source_commit=source_commit(),
                  source_sha256=source_hashes(), stores={}, ethernet={}, split={}, inverted_ack={}, switches={}, swd={})
    run = Commands(ROOT, logs, report["commands"])
    try:
        report["toolchain"], tools, _ = tool_config()
        lean = ["lake", "env", "lean", "-DwarningAsError=true"]
        run(["lake", "--no-cache", "build"], "build-library", timeout=1800)
        run([*lean, "test/ProofAudit.lean"], "audit-library")
        run([*lean, "test/StreamingReadyTraceContract.lean"], "check-flat-trace-deadline")
        run([*lean, "test/StreamingReadyTimingAdmission.lean"], "check-timing-admission")
        report["causal_source"] = check_causal_policies(run, lean, out)
        run([*lean, "test/StreamingReadySegmentBehavior.lean"], "check-register-read-behavior")
        images = {name: read_image(run, lean, out, name) for name in ("standard", "split", "inverted-ack")}
        image = images["standard"]
        report["image"] = image
        report["variants"] = {name: images[name] for name in ("split", "inverted-ack")}
        report["swd_images"] = read_swd_images(run, lean, out)
        builds = build_rtl(run, lean, tools, out)
        swd_builds = build_swd_bridges(run, tools, out)
        frozen = {path: sha(path) for path in out.rglob("*") if path.is_file() and path.parent != logs}
        for store, executable in builds.items():
            directory = out / (store + "-replay")
            directory.mkdir()
            cases = {name: replay(tools["vvp"], executable, directory / f"{name}.bin", image,
                                  nack=stage, reload=stage == 0) for name, stage in CASES.items()}
            cases["deadline"] = replay(tools["vvp"], executable, directory / "deadline.bin", image, deadline=True)
            for name, late in (("last-poll", False), ("late-poll", True)):
                cases[name] = replay_deadline_edge(tools["vvp"], executable, directory / f"{name}.bin",
                                                   image, cases["deadline"], late=late)
            cases["spi"] = replay_spi(tools["vvp"], executable, directory / "spi.bin")
            report["stores"][store] = cases
            split = {name: replay(tools["vvp"], executable, directory / f"split-{name}.bin",
                                  images["split"], nack=stage) for name, stage in CASES.items()}
            split["deadline"] = replay(tools["vvp"], executable, directory / "split-deadline.bin",
                                       images["split"], deadline=True)
            report["split"][store] = split
            for name, candidate in split.items():
                original = cases[name]
                require(candidate["result"] == original["result"] and candidate["rx_bits"] == original["rx_bits"]
                        and all(candidate["wire"][key] == original["wire"][key]
                                for key in ("starts", "stopped", "observed_bits"))
                        and candidate["ownership"] == original["ownership"],
                        f"Splitting the address row changed the protocol outcome: {name}")
            before = cases["deadline"]["wire"]["rising_cycles"]
            after = split["deadline"]["wire"]["rising_cycles"]
            require((after[8] - after[7]) - (before[8] - before[7]) == 2,
                    "Unstretched address ACK did not gain the two split instruction clocks")
            report["inverted_ack"][store] = replay_inverted_ack(
                tools["vvp"], executable, directory / "inverted-ack.bin", images["inverted-ack"], cases["read"])
            report["ethernet"][store] = {
                name: ethernet_replay.replay_timed_runner(tools["vvp"], executable,
                    directory / f"ethernet-{name}.bin", schedule=name, observe=timing_status)
                for name in ethernet_replay.REFILL_POLICIES
            }
            switches = {}
            for name, deadline in (("early_exit", False), ("timeout", True)):
                path = directory / f"switch-{name}.bin"
                result = replay_switch(tools["vvp"], executable, path, images["split"],
                                       i2c_exchange, timing_status, ownership, deadline=deadline)
                if deadline:
                    wire = result["i2c"]["wire"]
                    edges = list(struct.iter_unpack("<I16B", path.read_bytes()))
                    wire["aperture"] = deadline_aperture(edges, wire["fall_stretch_arms"][-1]["fall_edge"],
                                                         images["split"]["wait_budget"])
                switches[name] = result
            report["switches"][store] = switches
            report["swd"][store] = replay_swd(tools["vvp"], swd_builds[store], directory, report["swd_images"])
        require(report["stores"]["direct"] == report["stores"]["registered"],
                "Instruction stores changed the segmented read, custody, or warm SPI receipts")
        require(report["ethernet"]["direct"] == report["ethernet"]["registered"],
                "Instruction stores changed the Ethernet timing or ownership receipts")
        require(all(report[key]["direct"] == report[key]["registered"] for key in ("split", "inverted_ack")),
                "Instruction stores changed the split or inverted-ACK execution")
        require(report["switches"]["direct"] == report["switches"]["registered"],
                "Instruction stores changed the protocol handoff")
        require(report["swd"]["direct"] == report["swd"]["registered"],
                "Instruction stores changed the SWD wire events or ownership receipts")
        switches = report["switches"]["direct"]
        swd = report["swd"]["direct"]
        traces = (*report["stores"]["direct"], *(f"ethernet-{name}" for name in ethernet_replay.REFILL_POLICIES),
                  *(f"split-{name}" for name in report["split"]["direct"]), "inverted-ack",
                  *(f"switch-{name}" for name in switches), *(f"swd-{name}" for name in swd))
        for name in traces:
            direct = (out / "direct-replay" / f"{name}.bin").read_bytes()
            cached = (out / "registered-replay" / f"{name}.bin").read_bytes()
            require(direct == cached and direct and len(direct) % 20 == 0, f"Changed public pin trace: {name}")
        check_readback(run, lean, out, report["stores"]["direct"])
        check_ownership(run, lean, out, report["stores"]["direct"], report["ethernet"]["direct"],
                        report["split"]["direct"], switches, swd)
        check_i2c_execution(run, lean, out, images, report["stores"]["direct"], report["split"]["direct"], switches)
        check_swd_execution(run, lean, out, swd, report["swd_images"])
        check_ethernet_timing(run, lean, out, report["ethernet"]["direct"])
        check_can_handoff(run, lean, out, switches)
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
