"""Replay a passive Classical CAN observer on the frozen 8×4 RTL and gate netlist."""
import argparse
from bisect import bisect_right
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import time

from pad_io import PadDrive
from streaming_8x4_bringup import DEPTH, TOP
from streaming_8x4_e982_native import require, sha, write
from streaming_8x4_jane_street_behavior import GDS, NETLIST, PDK_MODELS, RTL, artifact, compile_model
from streaming_ready_can import BIT_CYCLES, BIT_RATE, CAPTURE_BITS, CORE_HZ, can_receive_image, decode_can_frame
from streaming_ready_transport import ReadyHost
from streaming_ready_wrapper import bridge_source
from streaming_rtl import QuadRTL
from streaming_transport import Opcode, QuadTransport
from streaming_wire_cases import EdgeTrace


CAN_RX = 1
CENTER = 16
SAMPLER_DELAY = 2
SKEW = 4
SOF_TO_COMPLETION = 2052
IDENTIFIER, PAYLOAD = 0x012, 0xB2
CASES = (('valid', None, 192, 0), ('bad-stuffing', 'stuffing', 211, 2), ('bad-crc', 'crc', 249, 7))


def _msb_bits(value, width):
    return tuple(bool(value & (1 << bit)) for bit in range(width - 1, -1, -1))


def _reference_crc15(message, width):
    """Append 15 zero coefficients, then divide over GF(2)."""
    dividend = message << 15
    polynomial = (1 << 15) | 0x4599
    for bit in range(width - 1, -1, -1):
        if dividend & (1 << (bit + 15)):
            dividend ^= polynomial << bit
    return dividend


@dataclass(frozen=True)
class PeerFrame:
    sender: tuple[bool, ...]
    ack_slot: int
    stuff_slots: tuple[int, ...]
    crc: int

    @property
    def samples(self):
        # The transmitter sends recessive in the ACK slot. The independent
        # fixture receiver resolves that slot dominant, including in controls.
        return self.sender[:self.ack_slot] + (False,) + self.sender[self.ack_slot + 1:]


def peer_frame(identifier, byte, corrupt=None):
    """Serialize a one-byte base frame independently of the host decoder."""
    message = (identifier << 15) | (1 << 8) | byte  # SOF, ID, RTR/IDE/r0, DLC=1, DATA
    crc = _reference_crc15(message, 27) ^ int(corrupt == 'crc')
    wire, stuff_slots = [], []
    for bit in _msb_bits((message << 15) | crc, 42):
        wire.append(bit)
        if len(wire) >= 5 and wire[-5:] == [bit] * 5:
            stuff_slots.append(len(wire))
            wire.append(not bit)
    ack_slot = len(wire) + 1
    wire += [True] * (CAPTURE_BITS - len(wire))  # CRC delimiter, ACK field, EOF, idle.
    if corrupt == 'stuffing':
        first = stuff_slots[0]
        wire[first] = wire[first - 1]
    return PeerFrame(tuple(wire), ack_slot, tuple(stuff_slots), crc)


class ObserverPeer:
    """Resolve transmitter and external ACK drives on the digital CAN sense input."""

    def __init__(self, frame, delay, skew_seed, *, completion_delta=0):
        self.frame = frame
        self.delay = delay
        self.completion_delta = completion_delta
        self.starts = (0, *(BIT_CYCLES * index + (13 * index + skew_seed) % (2 * SKEW + 1) - SKEW
                            for index in range(1, CAPTURE_BITS)))
        self.busy_start = None

    @property
    def sof(self):
        return self.busy_start + self.delay

    @property
    def completion(self):
        return self.sof + SOF_TO_COMPLETION + self.completion_delta

    def drive(self, cycle, pads, _ui=0):
        require(pads.logical.enabled == 0, 'Passive CAN observer enabled a protocol output')
        if self.busy_start is None and pads.status:
            self.busy_start = cycle
        if self.busy_start is None:
            return PadDrive()
        slot = bisect_right(self.starts, cycle + 1 - self.sof) - 1
        dominant = slot >= 0 and (not self.frame.sender[slot] or slot == self.frame.ack_slot)
        return PadDrive(enabled=CAN_RX if dominant else 0)

    def check(self, records, captured):
        expected = self.frame.samples
        require(captured == expected, 'Host did not drain the exact 64 resolved bus samples')
        active = [record for record in records if record['cycle'] >= self.busy_start]
        require([record['cycle'] for record in active] == list(range(self.busy_start, self.completion + 1)),
                'Incomplete CAN wire trace')
        observed = {}
        for record in active:
            cycle, pins, drive, snapshot = (record[key] for key in ('cycle', 'pins', 'drive', 'observation'))
            require(snapshot['busy'] == (cycle < self.completion), 'CAN BUSY interval changed')
            require(snapshot['enabled'] == drive['levels'] == drive['links'] == 0 and
                    drive['enabled'] in (0, CAN_RX) and drive['pullups'] & CAN_RX,
                    'CAN fixture violated released outputs or dominant/recessive resolution')
            raw = snapshot['edge_inputs'] & CAN_RX
            require(raw == snapshot['wires'] & CAN_RX == CAN_RX ^ drive['enabled'],
                    'Raw CAN input differs from the resolved peer drivers')
            slot = bisect_right(self.starts, cycle - self.sof) - 1
            require(bool(raw) == (slot < 0 or expected[slot]), 'CAN bit timing differs from the peer schedule')
            if cycle >= self.sof:
                require(pins['csn'] and not pins['sck'], 'Host clocked the quad link during the CAN capture')
            observed[cycle] = bool(raw)
        apertures = []
        for index, bit in enumerate(captured):
            raw_sample = self.sof + CENTER + BIT_CYCLES * index
            start = self.sof + self.starts[index]
            end = self.sof + self.starts[index + 1] if index + 1 < CAPTURE_BITS else self.completion
            require(start <= raw_sample < end and observed[raw_sample] == bit,
                    'CAN capture differs from its raw sample aperture')
            apertures.append(dict(raw_sample=raw_sample, capture_edge=raw_sample + SAMPLER_DELAY, bit=bit))
        return dict(busy_start=self.busy_start, busy_end=self.completion, sof=self.sof,
                    slot_starts=[self.sof + start for start in self.starts], apertures=apertures)


def exchange(rtl, transport, loaded, name, corrupt, delay, skew_seed,
             *, identifier=IDENTIFIER, byte=PAYLOAD, observe=None, bit_count=CAPTURE_BITS,
             completion_delta=0):
    frame = peer_frame(identifier, byte, corrupt)
    peer = ObserverPeer(frame, delay, skew_seed, completion_delta=completion_delta)
    rtl.device = peer
    exchanges = (Opcode.EXCHANGE32, Opcode.EXCHANGE64)
    before = tuple(transport.opcode_counts[op] for op in exchanges)
    wire_sink = rtl.record_sink
    capture_cuts = []
    if observe is not None:
        produced = observe(rtl)['rx_produced']
        require(produced == 0, 'CAN capture inherited RX custody before START')

        def observe_edge(record):
            nonlocal produced
            if wire_sink is not None:
                wire_sink(record)
            state = observe(rtl)
            captured = state['rx_produced']
            if captured != produced:
                require(captured == produced + 1, 'CAN capture skipped an RX prefix position')
                capture_cuts.append(dict(edge=record['cycle'], rx_produced=captured,
                                         bit=bool(state['stage2'] & CAN_RX)))
                produced = captured

        rtl.record_sink = observe_edge
    try:
        pending = loaded.submit(bit_count=bit_count)
        started = pending.last
        require(peer.busy_start is not None and rtl.snapshot.busy and rtl.cycle < peer.sof,
                'CAN START did not arm the observer before the peer SOF')
        transport.idle(peer.completion - rtl.cycle)
        require(not rtl.snapshot.busy and before == tuple(transport.opcode_counts[op] for op in exchanges),
                'CAN observer did not reach completion without host queue service')
    finally:
        rtl.record_sink = wire_sink
    wire_records = tuple(rtl.records)
    terminal = pending.wait(max_exchanges=6)
    require(terminal.retained and not terminal.fault and pending.tx_accepted == 0,
            'CAN observer did not retain the complete receive-only owner')
    counters = observe(rtl) if observe is not None else None
    wire = peer.check(wire_records, pending.rx_bits)
    decoded = decode_can_frame(pending.rx_bits)
    require(decoded == ((identifier, byte) if corrupt is None else None), 'CAN decoder verdict differs')
    completed = pending.finish(max_exchanges=6)
    terminal, released = completed.terminal, completed.release
    require(released is not None and released.tag == pending.tag and not released.busy and not released.retained and
            terminal.rx_start == CAPTURE_BITS and terminal.rx_valid == 0 and completed.result == pending.rx_bits and
            completed.tx_consumed == completed.tx_cancelled == 0,
            'CAN observer did not release after acknowledging the exact captured interval')
    rtl.device = None
    evidence = dict(name=name, corrupt=corrupt, source_identifier=identifier, source_byte=byte, decoded=decoded,
                    peer_crc=frame.crc, peer_stuff_slots=frame.stuff_slots, external_ack_slot=frame.ack_slot,
                    captured=list(pending.rx_bits), owner_tag=pending.tag, rx_acknowledged=terminal.rx_start,
                    wire=wire)
    if counters is not None:
        require([(cut['edge'], cut['bit']) for cut in capture_cuts] ==
                [(aperture['capture_edge'], aperture['bit']) for aperture in wire['apertures']],
                'CAN hardware capture edges or sampler values diverged from the peer apertures')
        evidence.update(start=asdict(started), receipt=asdict(terminal), release=asdict(released), counters=counters,
                        capture_cuts=capture_cuts)
    return evidence


def replay(vvp, executable, trace_path):
    trace = EdgeTrace(trace_path)
    record_limit = max(delay for _, _, delay, _ in CASES) + SOF_TO_COMPLETION + 1
    try:
        with QuadRTL(vvp, executable, record_limit=record_limit, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=DEPTH)
            host.initialize()
            loaded = host.load(can_receive_image())
            cases = [exchange(rtl, transport, loaded, *case) for case in CASES]
            require(transport.opcode_counts[Opcode.COMMIT] == 1 and
                    all(transport.opcode_counts[opcode] == len(CASES)
                        for opcode in (Opcode.START, Opcode.RELEASE)) and
                    transport.opcode_counts[Opcode.WARM_RESET] == 0 and
                    len({case['owner_tag'] for case in cases}) == len(CASES),
                    'CAN cases did not reuse one image under distinct owners')
    finally:
        recorded = trace.close()
    return dict(cases=cases, words=list(loaded.image.words), idle_levels=loaded.image.idle_levels,
                idle_enabled=loaded.image.idle_enabled, image_certificate=asdict(loaded.image.certificate),
                trace=recorded, exit_code=rtl.process.returncode)


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
             *(scripts / name for name in ('streaming_ready_can.py', 'streaming_ready_compile.py',
                'streaming_compile.py', 'streaming_8x4_jane_street_behavior.py',
                'streaming_ready_wrapper.py', 'streaming_ready_transport.py', 'streaming_transport.py',
                'streaming_rtl.py', 'streaming_wire_cases.py', 'pad_io.py', 'pinwheel_host.py'))]
    result = dict(schema='pinwheel.streaming-8x4-can.v1', passed=False, core_hz=CORE_HZ, bit_rate=BIT_RATE,
                  max_slot_skew=SKEW, inputs={str(path): artifact(path) for path in files}, stages={}, backends={})
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
            print(f'{name}: {len(CASES)} CAN frame cases passed', flush=True)
        require(result['backends']['rtl'] == result['backends']['gate'] and
                (out / 'rtl-wire.bin').read_bytes() == (out / 'gate-wire.bin').read_bytes(),
                'Frozen RTL and gate results or public-edge traces differ')
        require(result['inputs'] == {str(path): artifact(path) for path in files},
                'A CAN replay input changed while running')
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
    run(args.release.resolve(strict=True), args.models.resolve(strict=True), args.iverilog.resolve(strict=True),
        args.vvp.resolve(strict=True), args.out.resolve())


if __name__ == '__main__':
    main()
