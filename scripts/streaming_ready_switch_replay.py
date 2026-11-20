"""Reprogram one sampled-ready engine between two independently driven wire peers."""
from dataclasses import asdict
from pathlib import Path
import struct

import streaming_8x4_can as can
from streaming_ready_transport import CombinedI2cRead, ReadyHost
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport, Receipt
from streaming_wire_cases import EdgeTrace, require


FRESH_IDENTIFIER = 0x2D4
FRESH_BYTE = 0x69


def free_cut(rtl, observe, generation, transfer):
    state = observe(rtl)
    require(state["phase"] == 0 and state["generation"] == generation and state["transfer"] == transfer and
            state["tx_free"] == can.DEPTH and all(state[field] == 0 for field in (
                "tx_accepted", "tx_consumed", "tx_queued", "rx_produced", "rx_popped", "rx_queued")) and
            not rtl.observation.status and not rtl.observation.logical.enabled,
            "Protocol handoff did not leave a released, empty engine with the same transfer counter")
    return state


def install(rtl, host, image, observe, *, previous_generation, transfer, start_count):
    generation = previous_generation + 1
    sink, commands = rtl.record_sink, []

    def record(edge):
        sink(edge)
        state = observe(rtl)
        require(not state["command_initialize"], "Core reset while installing a protocol")
        if state["command"]:
            commands.append((edge["cycle"], state))

    rtl.record_sink = record
    try:
        loaded = host.load(image)
        require(loaded.generation == generation, "COMMIT did not establish the next generation")
        committed = free_cut(rtl, observe, generation, transfer)
        stale = None
        stale_cut = None
        if previous_generation:
            receipt = host.transport.request(Opcode.START, expected_generation=previous_generation,
                                             bit_count=start_count)
            require(receipt.code is Code.REJECTED and receipt.valid and not receipt.busy and not receipt.retained and
                    not receipt.fault and receipt.tag == ((generation << 16) | transfer) and
                    receipt.tx_accepted == receipt.rx_start == receipt.rx_valid == receipt.rx_queued == 0 and
                    receipt.tx_free == can.DEPTH,
                    "Stale START changed the freshly installed image or acquired custody")
            stale = asdict(receipt)
            stale_cut = free_cut(rtl, observe, generation, transfer)
    finally:
        rtl.record_sink = sink

    count = len(image.words)
    require([state["command"] for _, state in commands] == [1] * count + [2] + ([3] if stale else []),
            "Core did not receive the ordered WRITE, COMMIT, and stale START commands")
    writes = [{"edge": edge, "address": state["command_address"], "word": state["command_word"]}
              for edge, state in commands[:count]]
    words = [write["word"] for write in writes]
    commit_edge, commit = commands[count]
    require([write["address"] for write in writes] == list(range(count)) and words == list(image.words) and
            commit["command_count"] == count and commit["command_idle_levels"] == image.idle_levels and
            commit["command_idle_enabled"] == image.idle_enabled and commit["generation"] == generation,
            "Core upload did not commit the expected words and pad descriptor")
    if stale:
        _, attempted = commands[-1]
        require(attempted["command_generation"] == previous_generation and
                attempted["command_start_count"] == start_count and attempted["phase"] == 0,
                "Stale START did not deliver the old generation at the free cut")
    return loaded, dict(previous_generation=previous_generation, generation=generation, transfer=transfer,
                        image_words=words, writes=writes, idle_levels=commit["command_idle_levels"],
                        idle_enabled=commit["command_idle_enabled"], commit_edge=commit_edge, commit_cut=committed,
                        stale_start=stale, stale_cut=stale_cut)


def capture(rtl, host, loaded, observe, ownership, *, transfer, name, corrupt, delay, skew,
            identifier=can.IDENTIFIER, byte=can.PAYLOAD):
    result = can.exchange(rtl, host.transport, loaded, name, corrupt, delay, skew,
                          identifier=identifier, byte=byte, observe=observe)
    started, terminal, released = (Receipt(**result[key]) for key in ("start", "receipt", "release"))
    require(started.tag == result["owner_tag"] == (loaded.generation << 16) | transfer and
            started.code is Code.ACCEPTED and started.valid and started.busy and not started.retained and
            started.tx_free == can.DEPTH and started.rx_queued == 0,
            "CAN did not start with a fresh, empty receive-only owner")
    require(result["counters"]["phase"] == 5 and not result["counters"]["tx_consumed"] and
            terminal.rx_start == can.CAPTURE_BITS and not terminal.fault and
            released.code is Code.ACCEPTED and released.valid,
            "CAN decode incorrectly changed hardware completion or custody")
    result["ownership"] = ownership(result["counters"], terminal, released, "completed", "released")
    result["settled_cut"] = free_cut(rtl, observe, loaded.generation, transfer)
    return result


def replay_switch(vvp, executable, trace_path, split_manifest, i2c_exchange, observe, ownership, *, deadline=False):
    """Exercise both image changes with independent peers and one host lifetime.

    The ordinary path also settles a corrupt CAN frame after its decoder
    rejects it. The deadline path takes an explicit warm cancellation before
    the final install. The observation callback provides the same accounting
    and pre-edge sampler signals as the standalone source gate.
    """
    can_image = can.can_receive_image()
    i2c_image = CombinedI2cRead.from_manifest(split_manifest)
    trace = EdgeTrace(trace_path)
    try:
        with QuadRTL(vvp, executable, record_limit=can.SOF_TO_COMPLETION + 250, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=can.DEPTH)
            host.initialize()
            loaded, first_install = install(rtl, host, can_image, observe, previous_generation=0,
                                            transfer=0, start_count=can.CAPTURE_BITS)
            initial = capture(rtl, host, loaded, observe, ownership, transfer=1, name="initial-can", corrupt=None,
                              delay=192, skew=0)
            loaded, to_i2c = install(rtl, host, i2c_image, observe, previous_generation=1,
                                     transfer=1, start_count=i2c_image.tx_budget)
            i2c = i2c_exchange(rtl, host, loaded, split_manifest, nack=None if deadline else 1,
                               deadline=deadline, blocked_image=can_image)
            require(i2c["start"]["tag"] == 0x20002 and i2c["receipt"]["tag"] == 0x20002 and
                    i2c["result"]["outcome"] == ("deadline" if deadline else "register-nack"),
                    "I2C did not establish its own image, transfer, and outcome")
            ending = i2c["cancellation"] if deadline else i2c["release"]
            require(ending is not None and ending["tag"] == 0x20002, "I2C settled a different owner")
            free_cut(rtl, observe, 2, 2)
            loaded, to_can = install(rtl, host, can_image, observe, previous_generation=2,
                                     transfer=2, start_count=can.CAPTURE_BITS)

            crc_control = None
            final_transfer = 3
            if not deadline:
                crc_control = capture(rtl, host, loaded, observe, ownership, transfer=3,
                                      name="bad-crc", corrupt="crc", delay=249, skew=7)
                require(crc_control["decoded"] is None and crc_control["rx_acknowledged"] == can.CAPTURE_BITS,
                        "Bad wire CRC did not reject the application frame and settle its capture")
                final_transfer += 1
            final_can = capture(rtl, host, loaded, observe, ownership, transfer=final_transfer, name="fresh-can",
                                corrupt=None, delay=211, skew=2, identifier=FRESH_IDENTIFIER, byte=FRESH_BYTE)
            require(final_can["captured"] != initial["captured"], "Fresh CAN frame duplicated the initial payload")

            counts = transport.opcode_counts
            session_count = 3 if deadline else 4
            require(counts[Opcode.START] == session_count + 2 + int(deadline) and
                    counts[Opcode.COMMIT] == 3 + int(deadline) and
                    counts[Opcode.RELEASE] == session_count and counts[Opcode.WARM_RESET] == int(deadline),
                    "Protocol sequence made an unexpected START, COMMIT, RELEASE, or cancellation")
    finally:
        streamed = trace.close()
    edges = struct.iter_unpack("<I16B", Path(trace_path).read_bytes())
    require([row[0] for row in edges if row[1]] == [1] and streamed["edges"] == rtl.cycle,
            "Protocol switch replay did not retain every edge from exactly one cold reset")
    return dict(deadline=deadline, first_install=first_install, initial_can=initial, to_i2c=to_i2c, i2c=i2c,
                to_can=to_can, crc_control=crc_control, final_can=final_can, trace=streamed,
                command_counts={opcode.name: count for opcode, count in sorted(counts.items())})
