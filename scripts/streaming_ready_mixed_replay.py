"""Warm-load independent protocol peers on one segmented Ready core and host."""
from dataclasses import asdict, replace
from pathlib import Path
import struct

from pad_io import SWDIO_LINK
import streaming_8x4_can as can
import streaming_8x4_ethernet as ethernet
import streaming_8x4_ps2 as ps2
from streaming_compile import jtag_image
from streaming_peers import StreamingJTAGPeer
from streaming_ready_compile import Instruction, lower, spi_image
import streaming_ready_swd_branching_replay as swd
from streaming_ready_switch_replay import free_cut, install
from streaming_ready_transport import BranchingSwdRead, CheckedReadyImage, CombinedI2cRead, ReadyHost
from streaming_rtl import QuadRTL
from streaming_transport import Opcode, QuadTransport
from streaming_uart_wire_cases import Recording, receive_frame
from streaming_wire_cases import require


class LinkedSwdPeer(swd.RdbuffPeer):
    def drive(self, cycle, pads, ui=0):
        # The bench changes only external wiring. The same RTL ports still
        # drive and sense SWDIO, with both strong drivers checked per edge.
        return replace(super().drive(cycle, pads, ui), links=SWDIO_LINK)


def ready_jtag_image():
    original = jtag_image()
    compiled = lower((Instruction(row.operation, row.cell) for row in original.source.instructions),
                     idle_levels=original.idle_levels, idle_enabled=original.idle_enabled)
    require(compiled.words == original.words, 'The Ready wrapper changed a JTAG instruction word')
    return compiled


JTAG_BITS = 37


def jtag_exchange(rtl, loaded, observe):
    sent, reply = 0x159FC421DA, 0x0EB763C815
    peer = StreamingJTAGPeer(sent, reply, JTAG_BITS)
    tx = tuple(bool(sent >> position & 1) for position in range(JTAG_BITS))
    rtl.device = peer
    try:
        pending = loaded.submit(tx, bit_count=JTAG_BITS)
        pending.pump(max_bits=32)
        loaded.host.transport.idle(650)
        require(len(peer.bits) == 32 and rtl.snapshot.busy and pending.tx_accepted == 32,
                'JTAG did not hold Shift-DR when its transmit queue ran out')
        pending.wait(max_exchanges=20)
        counters = observe(rtl)
        finished = pending.finish(max_exchanges=20)
        terminal, release = finished.terminal, finished.release
        require(release is not None and release.tag == terminal.tag == pending.tag and
                finished.tx_consumed == counters['tx_consumed'] == JTAG_BITS and
                finished.tx_cancelled == 0 and terminal.rx_start == JTAG_BITS and
                terminal.rx_valid == terminal.rx_queued == counters['tx_queued'] == 0,
                'JTAG scan did not settle one full-duplex owner')
        wire = peer.check(finished.rx_bits, require_stall=True)
        return dict(owner_tag=pending.tag, receipt=asdict(terminal), release=asdict(release),
                    rx_bits=finished.rx_bits, wire=wire)
    finally:
        rtl.device = None


def ethernet_exchange(rtl, transport, loaded, observe):
    sink, timing = rtl.record_sink, {}

    def record(edge):
        sink(edge)
        timing[edge['cycle']] = observe(rtl)

    rtl.record_sink = record
    try:
        return ethernet.exchange(rtl, transport, loaded, 'mixed-uniform', 1, False,
                                 ethernet.REFILL_POLICIES['uniform'], timing=timing)
    finally:
        rtl.record_sink = sink


def check_leg(events, generation, count, *, fault):
    starts = [cut for cut in events if cut['command'] == 3 and
              cut['pre_phase'] == 0 and cut['phase'] == 1]
    terminals = [cut for cut in events if cut['pre_phase'] in (1, 2, 3, 4, 7) and cut['phase'] in (5, 6)]
    settlements = [cut for cut in events if cut['pre_phase'] in (5, 6) and cut['phase'] == 0]
    require(len(starts) == len(terminals) == len(settlements) == 1,
            'A protocol session did not acquire, retain and settle exactly one owner')
    start, terminal, settle = starts[0], terminals[0], settlements[0]
    require(all(cut['generation'] == cut['transfer'] == generation for cut in (start, terminal, settle)) and
            start['command_generation'] == generation and start['command_start_count'] == count and
            start['edge'] < terminal['edge'] < settle['edge'] and terminal['phase'] == (6 if fault else 5) and
            settle['command'] == (15 if fault else 4),
            'Actual START, first retained result or settlement selected a different owner or transition')
    return dict(start=start['edge'], terminal=terminal['edge'], settlement=settle['edge'],
                start_count=start['command_start_count'],
                clocks_through_terminal=terminal['edge'] - start['edge'],
                owner_tag=(generation << 16) | generation,
                terminal_tx_accepted=terminal['tx_accepted'], terminal_tx_reserved=terminal['tx_consumed'],
                terminal_rx_captured=terminal['rx_produced'])


def check_receive_cuts(name, result, captured, cuts):
    if name == 'can':
        expected = [(point['capture_edge'], point['bit']) for point in result['wire']['apertures']]
        mask = can.CAN_RX
    elif name == 'ps2':
        expected = [(point['expected_capture_edge'], point['data']) for point in result['wire']['apertures']]
        mask = ps2.DATA
    else:
        observation = result['observation']
        expected = [(edge + 2, bit) for edge, bit in
                    zip(observation['raw_sample_edges'], observation['raw_center_bits'], strict=True)]
        mask = 1 << result['waveform']['rx_input']
    actual = [dict(edge=edge, rx_produced=count, bit=bool(stage2 & mask)) for edge, count, stage2 in captured]
    require(cuts['start_count'] == cuts['terminal_tx_accepted'] == cuts['terminal_tx_reserved'] == 0 and
            cuts['terminal_rx_captured'] == len(expected) and
            [cut['rx_produced'] for cut in actual] == list(range(1, len(expected) + 1)) and
            [(cut['edge'], cut['bit']) for cut in actual] == expected,
            f'{name} checked receive did not follow the independent capture apertures and zero-TX plan')
    return actual


def replay_mixed(vvp, executable, trace_path, i2c_manifest, swd_manifest, *,
                 receive_manifests, observe, execution, spi_exchange, i2c_exchange):
    """Exercise one physical tape with eight protocols and a cancelled I²C timeout."""
    can_image, ps2_image, uart_image = (CheckedReadyImage.from_manifest(receive_manifests[name])
                                       for name in ('can', 'ps2', 'uart-rx'))
    i2c_image = CombinedI2cRead.from_manifest(i2c_manifest)
    swd_image = BranchingSwdRead.from_manifest(swd_manifest)
    tape = Recording(trace_path)
    events, captures, results = [], [], []
    previous_rx = 0

    def observe_edge(edge):
        nonlocal previous_rx
        tape(edge)
        if edge['pins']['initialize']:
            return
        cut = observe(rtl)
        if cut['rx_produced'] > previous_rx:
            captures.append((edge['cycle'], cut['rx_produced'], cut['stage2']))
        previous_rx = cut['rx_produced']
        if cut['command'] or cut['pre_phase'] != cut['phase']:
            events.append(dict(edge=edge['cycle'], **cut))

    try:
        with QuadRTL(vvp, executable, record_limit=6500, record_sink=observe_edge) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=2)
            host.initialize()
            legs = (
                ('can', can_image, can_image.path_plan.start_count,
                 # The explicit COUNT row keeps the first aperture and extends the final dwell one clock.
                 lambda loaded: can.exchange(rtl, transport, loaded, 'mixed-can', None, 380, 3,
                                             observe=observe, bit_count=None, completion_delta=1)),
                ('ps2', ps2_image, ps2_image.path_plan.start_count,
                 lambda loaded: ps2.exchange(rtl, transport, loaded, 'mixed-ps2', 0xB2, None, 770,
                                             ps2.MIXED_LOW, ps2.MIXED_HIGH, bit_count=None)),
                ('uart-rx', uart_image, uart_image.path_plan.start_count,
                 lambda loaded: receive_frame(rtl, transport, host, loaded, tape, q=12,
                                              profile='valid', payload=0x96, bit_count=None)),
                ('i2c-timeout', i2c_image, i2c_image.tx_budget,
                 lambda loaded: i2c_exchange(rtl, host, loaded, i2c_manifest, deadline=True, blocked_image=can_image)),
                ('i2c-read', i2c_image, i2c_image.tx_budget,
                 lambda loaded: i2c_exchange(rtl, host, loaded, i2c_manifest)),
                ('swd', swd_image, swd_image.path_plan.start_count,
                 lambda loaded: swd.exchange(rtl, loaded, swd.CASES[0], observe=observe, execution=execution,
                                             peer_factory=LinkedSwdPeer)),
                ('spi', spi_image(mode=2), 65,
                 lambda loaded: spi_exchange(rtl, loaded, 2, 65, stalled=True)),
                ('jtag', ready_jtag_image(), JTAG_BITS,
                 lambda loaded: jtag_exchange(rtl, loaded, observe)),
                ('ethernet', ethernet.ethernet_sni_image(), ethernet.WIRE_BITS,
                 lambda loaded: ethernet_exchange(rtl, transport, loaded, observe)),
            )
            for generation, (name, image, count, run_session) in enumerate(legs, 1):
                loaded, uploaded = install(rtl, host, image, observe, previous_generation=generation - 1,
                                           transfer=generation - 1, start_count=count)
                first = len(events)
                first_capture = len(captures)
                try:
                    result = run_session(loaded)
                except Exception as error:
                    error.add_note(f'Mixed Ready protocol {name}, generation {generation}')
                    raise
                fault = name == 'i2c-timeout'
                cuts = check_leg(events[first:], generation, count, fault=fault)
                if type(image) is CheckedReadyImage:
                    cuts['capture_cuts'] = check_receive_cuts(name, result, captures[first_capture:], cuts)
                settled = free_cut(rtl, observe, generation, generation, idle=(image.idle_levels, image.idle_enabled))
                rtl.device = None
                results.append(dict(protocol=name, upload=uploaded, cuts=cuts, session=result, settled=settled))

            counts = transport.opcode_counts
            sessions = len(legs)
            require(counts[Opcode.START] == 2 * sessions and counts[Opcode.COMMIT] == sessions + 1 and
                    counts[Opcode.RELEASE] == sessions and counts[Opcode.WARM_RESET] == 1,
                    'Mixed replay used an unexpected START, COMMIT, RELEASE or warm cancellation')
    finally:
        recorded = tape.trace.close()
    resets = [edge[0] for edge in struct.iter_unpack('<I16B', Path(trace_path).read_bytes()) if edge[1]]
    require(resets == [1] and recorded['edges'] == rtl.cycle,
            'Mixed replay did not preserve every edge from one cold reset')
    return dict(cold_resets=resets, sessions=results, trace=recorded,
                command_counts={opcode.name: count for opcode, count in sorted(counts.items())})
