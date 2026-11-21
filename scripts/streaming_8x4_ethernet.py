"""Replay a minimum Ethernet frame at a digital SNI PHY interface."""
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import time

from pad_io import PadDrive
from streaming_8x4_bringup import DEPTH, TOP
from streaming_8x4_e982_native import require, sha, write
from streaming_8x4_jane_street_behavior import GDS, NETLIST, PDK_MODELS, RTL, artifact, compile_model
from streaming_ready_ethernet import BIT_CYCLES, BIT_RATE, CORE_HZ, WIRE_BITS, ethernet_sni_image, minimum_frame, serial_bits
from streaming_ready_transport import ReadyHost
from streaming_ready_wrapper import bridge_source
from streaming_rtl import QuadRTL
from streaming_transport import Opcode, QuadTransport, require_accepted
from streaming_wire_cases import EdgeTrace


TX_CLK, GO = 1, 2
TXD, TX_EN = 1, 2
SETUP = 2
GO_TO_FIRST = 18
FIRST_REFILL = 115
BURST_BITS = 64
REQUEST_CLOSE = 90
GRANT = 91
READY = 143
RESPONSE_CLOSE = 248
CORE_BOUNDARY, CORE_COMPLETED, CORE_FREE = 2, 5, 0
TX_STREAM_FLAGS = 9
CASES = (('valid-width-1', 1, False), ('valid-width-2', 2, False), ('bad-fcs', 2, True))
REFILL_POLICIES = {
    'uniform': (0,) * 8,
    'staggered': (0, 24) * 4,
    'late': (180, 64) + (0,) * 6,
}
DEADLINE_REFILLS = (0, 173, 64, 173, 64, 160, 28, 128)
SAME_EDGE_REFILLS = (175, 64) + (0,) * 6


def fixture_frame():
    return minimum_frame(bytes.fromhex('020000000001'), bytes.fromhex('020000000002'),
                         0x88b5, bytes(range(46)))


def phy_accepts(bits):
    """Check minimum length, preamble/SFD and CRC residue directly on serial bits."""
    if len(bits) != 576 or tuple(bits[:64]) != (True, False) * 31 + (True, True):
        return False
    remainder = 0xffffffff
    for bit in bits[64:]:
        feedback = (remainder & 1) ^ bit
        remainder >>= 1
        if feedback:
            remainder ^= 0xedb88320
    return remainder == 0xdebb20e3


class SerialPHY:
    """Independent 10 MHz clock with an explicit sampled high width and GO edge."""

    def __init__(self, high_ticks):
        self.high_ticks = high_ticks
        self.go = None

    def drive(self, cycle, pads, _ui=0):
        edge = cycle + 1
        clock = TX_CLK if edge % BIT_CYCLES < self.high_ticks else 0
        go = GO if self.go is not None and edge >= self.go else 0
        return PadDrive(levels=clock | go, enabled=TX_CLK | GO, pullups=0)

    def arm(self, cycle):
        # The next callback must already know GO's edge, so leave a full period.
        self.go = (cycle // BIT_CYCLES + 2) * BIT_CYCLES
        return self.go + GO_TO_FIRST

    def check(self, records, first, bits, corrupt):
        by_cycle = {record['cycle']: record for record in records}
        busy_start = next(record['cycle'] for record in records if record['observation']['busy'])
        last = first + BIT_CYCLES * (len(bits) - 1)
        stop = last + 4
        expected_rises = list(range(first, last + 1, BIT_CYCLES))
        sampled, rises = [], []
        for cycle in range(busy_start, max(by_cycle) + 1):
            observed = by_cycle[cycle]['observation']
            drive = by_cycle[cycle]['drive']
            require(drive['enabled'] == TX_CLK | GO and drive['links'] == 0 and
                    observed['edge_inputs'] == drive['levels'] == observed['wires'] & (TX_CLK | GO),
                    'SNI fixture changed its resolved raw inputs')
            require(observed['enabled'] == TXD | TX_EN and
                    observed['levels'] & (TXD | TX_EN) == observed['wires'] >> 2 & (TXD | TX_EN),
                    'SNI TXD/TX_EN were not driven on the advertised function pads')
            require(bool(observed['levels'] & TX_EN) == (first - 3 <= cycle < stop) and
                    bool(observed['busy']) == (cycle < stop),
                    'SNI TX_EN or BUSY diverged from the uninterrupted frame window')
            previous = by_cycle[cycle - 1]['observation']
            raw_rise = observed['edge_inputs'] & TX_CLK and not previous['edge_inputs'] & TX_CLK
            if raw_rise and previous['levels'] & TX_EN:
                rises.append(cycle)
                bit = bool(previous['levels'] & TXD)
                valid = TX_EN | int(bit)
                require(all(by_cycle[setup]['observation']['levels'] == valid
                            for setup in range(cycle - SETUP, cycle + 1)),
                        'SNI data/enable changed inside modeled setup and sampling aperture')
                sampled.append(bit)
        require(rises == expected_rises and tuple(sampled) == bits,
                'PHY did not observe exactly 576 gapless supplied bits')
        valid = phy_accepts(sampled)
        require(valid == (not corrupt), 'Independent PHY preamble/FCS verdict differs')
        sampled_bytes = bytes(sum(int(bit) << index for index, bit in enumerate(sampled[pos:pos + 8]))
                              for pos in range(0, len(sampled), 8))
        return dict(go=self.go, first_rise=first, last_rise=last, tx_en_off=stop, busy_start=busy_start,
                    high_ticks=self.high_ticks, setup_ticks=SETUP, sampled_rises=rises,
                    sampled_hex=sampled_bytes.hex(), accepted=valid)

    def check_missed_deadline(self, records, first, bits, completion_delay):
        try:
            self.check(records, first, bits, False)
        except ValueError as error:
            require(str(error) == 'SNI TX_EN or BUSY diverged from the uninterrupted frame window',
                    'The late refill did not fail the PHY frame deadline check')
        else:
            raise ValueError('The PHY unexpectedly accepted the late refill')

        by_cycle = {record['cycle']: record['observation'] for record in records}
        sampled = []
        for bit in range(len(bits)):
            cycle = first + BIT_CYCLES * bit
            before, edge = by_cycle[cycle - 1], by_cycle[cycle]
            require(edge['edge_inputs'] & TX_CLK and not before['edge_inputs'] & TX_CLK,
                    'The late fixture did not supply the expected PHY clock')
            require(before['enabled'] == TXD | TX_EN and before['levels'] & TX_EN,
                    'TXD/TX_EN were not driven on the late fixture sampling edge')
            sampled.append(bool(before['levels'] & TXD))
        first_mismatch = next((i for i, (expected, observed) in enumerate(zip(bits, sampled, strict=True))
                               if expected != observed), None)
        require(first_mismatch == BURST_BITS + 1 and completion_delay == BIT_CYCLES and
                not phy_accepts(sampled), 'Missed reservation did not produce the expected one-cell slip')
        return dict(go=self.go, first_rise=first, high_ticks=self.high_ticks, accepted=False,
                    first_mismatch_bit=first_mismatch, expected_bit=bits[first_mismatch],
                    observed_bit=sampled[first_mismatch],
                    mismatch_rise=first + BIT_CYCLES * first_mismatch,
                    completion_delay=completion_delay)


def burst_timing(timing, records, start, close, offset):
    request_close = next(record['cycle'] for record in records
                         if start + 1 < record['cycle'] and record['pins']['csn'])
    grant = next(edge for edge in range(request_close + 1, close)
                 if timing[edge]['frontend_phase'] == 1 and timing[edge + 1]['frontend_phase'] == 2)
    pushes = [edge for edge in range(grant, close) if timing[edge]['tx_push']]
    grant_state = timing[grant]
    require(request_close == start + REQUEST_CLOSE and grant == start + GRANT and
            grant_state['pre_tx_free'] >= 2 and grant_state['pre_tx_accepted'] == offset and
            pushes == [grant + 1, grant + 2], 'SNI did not reserve the two FIFO beats at the observed grant')
    for beat, edge in enumerate(pushes, start=1):
        accepted = offset + 32 * beat
        require(timing[edge]['tx_push_bits'] == 32 and timing[edge]['tx_accepted'] == accepted and
                timing[edge + 1]['pre_tx_accepted'] == accepted and
                timing[edge + 1]['pre_tx_queued'] > 0,
                'SNI FIFO push was not visible to the following edge')
    return dict(request_close=request_close, grant=grant, tx_push=pushes,
                first_visible=pushes[0] + 1, visible=pushes[-1] + 1,
                push_bits=[timing[edge]['tx_push_bits'] for edge in pushes],
                grant_tx_free=grant_state['pre_tx_free'], grant_tx_consumed=grant_state['pre_tx_consumed'],
                grant_tx_queued=grant_state['pre_tx_queued'], grant_tx_valid=grant_state['pre_tx_valid'])


def push_burst(rtl, send, tag, offset, timing):
    start = rtl.cycle
    reply = send(offset)
    ready = next(record['cycle'] for record in rtl.records
                 if record['cycle'] > start and record['observation']['ready'])
    require((ready, rtl.cycle) == (start + READY, start + RESPONSE_CLOSE),
            'SNI host refill response timing changed')
    require(reply.tag == tag and reply.busy and not reply.fault and not reply.retained and
            reply.tx_accepted == offset + BURST_BITS and reply.rx_start == reply.rx_valid == 0,
            'SNI host did not accept the exact requested 64-bit burst')
    result = dict(offset=offset, start=start, request_close=start + REQUEST_CLOSE, grant=start + GRANT,
                  tx_push=[start + GRANT + 1, start + GRANT + 2], ready=ready, response_close=rtl.cycle)
    if timing is not None:
        result.update(burst_timing(timing, rtl.records, start, rtl.cycle, offset))
    return result


def check_reservations(timing, first, missed_deadline):
    reservations = []
    first_missing = None
    for bit in range(WIRE_BITS):
        edge = first - SETUP + BIT_CYCLES * bit
        state = timing[edge]
        available = bool(state['pre_tx_valid'] or state['pre_tx_queued'])
        reserved_before, reserved_after = state['pre_tx_consumed'], state['tx_consumed']
        phase = state['pre_phase']
        if first_missing is None:
            require(phase == CORE_BOUNDARY and state['pre_stream_flags'] == TX_STREAM_FLAGS and
                    reserved_before == bit and reserved_after == bit + int(available),
                    'SNI reservation cut did not match the core TX boundary and offset')
            if not available:
                first_missing = bit
        reservations.append(dict(bit=bit, edge=edge, phase=phase, available=available,
                                 reserved_before=reserved_before, reserved_after=reserved_after))
    require(first_missing == (BURST_BITS if missed_deadline else None),
            'SNI reservation availability differed from its schedule')
    return dict(reservations=reservations, first_missing_reservation=first_missing)


def finish_owner(rtl, pending, timing):
    terminal_counters = timing[rtl.cycle]
    completed = pending.finish(max_exchanges=3)
    released_counters = timing[rtl.cycle]
    terminal, release = completed.terminal, completed.release
    tag = pending.tag
    require(terminal.retained and not terminal.busy and not terminal.fault and release is not None and
            terminal.tag == release.tag == tag and terminal.tx_accepted == WIRE_BITS and
            completed.result == completed.rx_bits == () and completed.tx_consumed == WIRE_BITS and
            completed.tx_cancelled == 0 and pending.terminal_retries == [],
            'Shared runner did not finish the same SNI owner with the exact TX prefix')
    for counters, phase, count in ((terminal_counters, CORE_COMPLETED, WIRE_BITS),
                                   (released_counters, CORE_FREE, 0)):
        require(counters['phase'] == phase and (counters['generation'] << 16 | counters['transfer']) == tag and
                counters['tx_accepted'] == counters['tx_consumed'] == count and
                counters['tx_free'] == DEPTH and
                not any(counters[name] for name in ('tx_queued', 'rx_produced', 'rx_popped', 'rx_queued')),
                'Observed SNI ownership counters differ from the runner settlement')
    return dict(terminal=asdict(terminal), release=asdict(release), terminal_counters=terminal_counters,
                released_counters=released_counters, tx_consumed=completed.tx_consumed,
                tx_cancelled=completed.tx_cancelled, terminal_retries=pending.terminal_retries)


def exchange(rtl, transport, loaded, name, high_ticks, corrupt, refill_delays=None, missed_deadline=False,
             missed_reservation=False, *, timing=None):
    peer = SerialPHY(high_ticks)
    rtl.device = peer
    start = rtl.cycle
    frame = fixture_frame()
    if corrupt:
        frame = frame[:-1] + bytes([frame[-1] ^ 1])
    bits = serial_bits(frame)
    if timing is None:
        started = require_accepted(transport.request(Opcode.START, expected_generation=loaded.generation,
                                                     bit_count=WIRE_BITS))

        def send(offset):
            return require_accepted(transport.exchange(started.tag, offset, 0, bits[offset:offset + BURST_BITS]))
    else:
        timing.clear()
        pending = loaded.submit(bits, bit_count=WIRE_BITS)
        started = pending.last

        def send(offset):
            require(pending.tx_accepted == offset, 'SNI refill began at a different accepted TX offset')
            return pending.pump(scheduled_bits=BURST_BITS)
    require(started.busy and started.tx_free == DEPTH and started.tx_accepted == 0,
            'SNI START did not create an empty armed owner')
    bursts = [push_burst(rtl, send, started.tag, 0, timing)]
    first = peer.arm(rtl.cycle)
    for index, offset in enumerate(range(BURST_BITS, WIRE_BITS, BURST_BITS)):
        delay = refill_delays[index] if refill_delays is not None else 0
        launch = first + FIRST_REFILL + (offset - BURST_BITS) * BIT_CYCLES + delay
        require(rtl.cycle < launch, 'A previous refill exceeded the next host launch deadline')
        transport.idle(launch - rtl.cycle)
        bursts.append(push_burst(rtl, send, started.tag, offset, timing))
    done = first + BIT_CYCLES * (WIRE_BITS - 1) + 4
    transport.idle(done - rtl.cycle)
    if missed_deadline:
        require(rtl.snapshot.busy, 'SNI late refill unexpectedly met the original completion deadline')
        while rtl.snapshot.busy and rtl.cycle < done + BIT_CYCLES:
            transport.idle(1)
    require(not rtl.snapshot.busy, 'SNI program did not finish at the exact final deadline')
    completion_delay = rtl.cycle - done
    if timing is None:
        released = require_accepted(transport.request(Opcode.RELEASE, tag=started.tag))
        require(released.tag == started.tag and not released.busy and not released.retained,
                'SNI owner did not release after consuming the frame')
    else:
        ownership = finish_owner(rtl, pending, timing)
    records = [record for record in rtl.records if record['cycle'] > start]
    if missed_deadline:
        trace = peer.check_missed_deadline(records, first, bits, completion_delay)
    else:
        trace = peer.check(records, first, bits, corrupt)
    rtl.device = None
    result = dict(name=name, owner_tag=started.tag, tx_bits=bursts[-1]['offset'] + BURST_BITS,
                  bursts=bursts, phy=trace)
    if timing is not None:
        result['ownership'] = ownership
        result['timing'] = check_reservations(timing, first, missed_deadline or missed_reservation)
    if refill_delays is not None:
        result['refill_delays'] = [burst['start'] - first - FIRST_REFILL - index * BURST_BITS * BIT_CYCLES
                                   for index, burst in enumerate(bursts[1:])]
        require(tuple(result['refill_delays']) == refill_delays, 'SNI refill launch differed from its schedule')
    return result


def replay(vvp, executable, trace_path, *, cases=CASES, observe=None):
    trace = EdgeTrace(trace_path)
    try:
        with QuadRTL(vvp, executable, record_limit=6000, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=DEPTH)
            host.initialize()
            loaded = host.load(ethernet_sni_image())
            timing = None
            if observe is not None:
                timing = {}

                def record_edge(record):
                    trace(record)
                    timing[record['cycle']] = observe(rtl)

                rtl.record_sink = record_edge
            results = [exchange(rtl, transport, loaded, *case, timing=timing) for case in cases]
            require(transport.opcode_counts[Opcode.COMMIT] == 1 and
                    transport.opcode_counts[Opcode.EXCHANGE64] == len(cases) * (WIRE_BITS // BURST_BITS) and
                    transport.opcode_counts[Opcode.EXCHANGE0] == (2 * len(cases) if observe else 0) and
                    all(transport.opcode_counts[op] == len(cases) for op in (Opcode.START, Opcode.RELEASE)) and
                    transport.opcode_counts[Opcode.WARM_RESET] == 0 and
                    len({case['owner_tag'] for case in results}) == len(cases),
                    'SNI cases changed image or reused an owner')
    finally:
        recorded = trace.close()
    return dict(cases=results, words=list(loaded.image.words), idle_levels=loaded.image.idle_levels,
                idle_enabled=loaded.image.idle_enabled, image_certificate=asdict(loaded.image.certificate),
                trace=recorded, exit_code=rtl.process.returncode)

def replay_schedules(vvp, executable, trace_path):
    """Use the independent PHY to check two refill policies and one missed reservation."""
    cases = tuple((name, 1, False, delays, name == 'late') for name, delays in REFILL_POLICIES.items())
    return replay(vvp, executable, trace_path, cases=cases)


def replay_timed_runner(vvp, executable, trace_path, *, observe, schedule=None):
    """Drive Ethernet with the common Ready owner and sample pre/post-edge RTL accounting.

    ``grant`` and ``tx_push`` name execution edges. ``first_visible`` and
    ``visible`` name the first pre-edge cuts with one and both committed beats.
    """
    if not callable(observe):
        raise ValueError('Timed SNI replay requires an RTL accounting observer')
    if schedule is not None and schedule not in REFILL_POLICIES:
        raise ValueError('Unknown SNI refill schedule')
    cases = tuple((name, 1, False, delays, name == 'late') for name, delays in REFILL_POLICIES.items()
                  if schedule is None or name == schedule)
    return replay(vvp, executable, trace_path, cases=cases, observe=observe)


def replay_refill_boundary(vvp, executable, trace_path, *, observe):
    """Contrast both legal PHY widths with a push on the first missed reservation edge."""
    cases = (('on-deadline-1', 1, False, DEADLINE_REFILLS, False),
             ('on-deadline-2', 2, False, DEADLINE_REFILLS, False),
             ('same-edge-late', 1, False, SAME_EDGE_REFILLS, False, True))
    result = replay(vvp, executable, trace_path, cases=cases, observe=observe)
    _, _, same_edge = result['cases']
    missed = same_edge['timing']['reservations'][BURST_BITS]
    require(same_edge['bursts'][1]['tx_push'][0] == missed['edge'] and
            same_edge['bursts'][1]['first_visible'] == missed['edge'] + 1 and
            missed['reserved_before'] == missed['reserved_after'] == BURST_BITS,
            'A same-edge SNI push incorrectly supplied pre-edge credit')
    return result


def run(release, models, iverilog, vvp, out):
    netlist = release / 'release' / (TOP + '.v')
    inputs = {netlist: NETLIST, release / 'release' / (TOP + '.gds'): GDS}
    inputs.update({release / 'src' / name: digest for name, digest in RTL.items()})
    inputs.update({models / name: digest for name, digest in PDK_MODELS.items()})
    for path, expected in inputs.items():
        require(sha(path) == expected, f'Frozen release or vendor model hash differs for {path}')

    out.mkdir(parents=True, exist_ok=False)
    scripts = Path(__file__).resolve().parent
    files = [*inputs, iverilog, vvp, Path(__file__).resolve(),
             *(scripts / name for name in ('streaming_ready_ethernet.py', 'streaming_ready_compile.py',
                'streaming_compile.py', 'streaming_8x4_jane_street_behavior.py',
                'streaming_ready_wrapper.py', 'streaming_ready_transport.py', 'streaming_transport.py',
                'streaming_rtl.py', 'streaming_wire_cases.py', 'pad_io.py', 'pinwheel_host.py'))]
    result = dict(schema='pinwheel.streaming-8x4-ethernet.v1', passed=False, core_hz=CORE_HZ, bit_rate=BIT_RATE,
                  inputs={str(path): artifact(path) for path in files}, stages={}, backends={})
    started = time.monotonic()
    try:
        bridge = out / 'bridge.sv'
        bridge.write_text(bridge_source(DEPTH))
        result['bridge'] = artifact(bridge)
        sources = {'rtl': [release / 'src' / name for name in RTL],
                   'gate': [*(models / name for name in PDK_MODELS), netlist]}
        for name, paths in sources.items():
            executable, result['stages'][name] = compile_model(iverilog, out, name, [*paths, bridge])
            result['backends'][name] = replay(vvp, executable, out / (name + '-wire.bin'))
            print(f'{name}: {len(CASES)} Ethernet SNI frame cases passed', flush=True)
        require(result['backends']['rtl'] == result['backends']['gate'] and
                (out / 'rtl-wire.bin').read_bytes() == (out / 'gate-wire.bin').read_bytes(),
                'Frozen RTL and gate results or public-edge traces differ')
        require(result['inputs'] == {str(path): artifact(path) for path in files},
                'An Ethernet replay input changed while running')
        result['passed'] = True
    except BaseException as error:
        result['error'] = repr(error)
        raise
    finally:
        result['elapsed_seconds'] = time.monotonic() - started
        write(out / 'receipt.json', result)
    print(json.dumps(dict(passed=True, trace=result['backends']['rtl']['trace'],
                          receipt=str(out / 'receipt.json')), indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('release', 'models', 'iverilog', 'vvp', 'out'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    run(args.release.resolve(strict=True), args.models.resolve(strict=True),
        args.iverilog.resolve(strict=True), args.vvp.resolve(strict=True), args.out.resolve())


if __name__ == '__main__':
    main()
