"""Replay keyboard-to-host PS/2 receive on the frozen 8×4 RTL and gate netlist."""
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import time

from pad_io import PadDrive
from streaming_8x4_bringup import DEPTH, TOP
from streaming_8x4_e982_native import require, sha, write
from streaming_8x4_jane_street_behavior import GDS, NETLIST, PDK_MODELS, RTL, artifact, compile_model
from streaming_ready_ps2 import CORE_HZ, FRAME_BITS, decode_ps2_frame, ps2_receive_image
from streaming_ready_transport import ReadyHost
from streaming_ready_wrapper import bridge_source
from streaming_rtl import QuadRTL
from streaming_transport import Opcode, QuadTransport
from streaming_wire_cases import EdgeTrace


CLOCK = 1
DATA = 2
BUS = CLOCK | DATA
MIN_HALF = 120
MAX_HALF = 200
DATA_SETUP = 22
SAMPLER_DELAY = 2
FINAL_FALL_TO_TERMINAL = 220
MIXED_LOW = (120, 200, 160, 120, 200, 183, 122, 197, 120, 200, 137)
MIXED_HIGH = (120, 200, 200, 200, 120, 121, 199, 163, 200, 120)
CASES = (
    ('valid', 0xB2, None, 48, MIXED_LOW, MIXED_HIGH),
    ('bad-start', 0x96, 0, 26, (MIN_HALF,) * FRAME_BITS, (MIN_HALF,) * (FRAME_BITS - 1)),
    ('bad-parity', 0xA7, 9, 767, (MAX_HALF,) * FRAME_BITS, (MAX_HALF,) * (FRAME_BITS - 1)),
    ('bad-stop', 0x69, 10, 89, MIXED_LOW[::-1], MIXED_HIGH[::-1]),
)


class KeyboardPeer:
    """Schedule open-drain clock and data independently after observing BUSY."""

    def __init__(self, byte, bad_field, delay, low, high):
        parity = 1 ^ (byte.bit_count() & 1)
        frame = (byte << 1) | (parity << 9) | (1 << 10)
        if bad_field is not None:
            frame ^= 1 << bad_field
        self.bits = tuple(bool(frame & (1 << index)) for index in range(FRAME_BITS))
        require(len(low) == FRAME_BITS and len(high) == FRAME_BITS - 1 and delay > DATA_SETUP and
                all(MIN_HALF <= interval <= MAX_HALF for interval in (*low, *high)),
                'PS/2 peer has invalid clock intervals or lacks first-bit setup')
        self.low, self.high = low, high
        self.falls, self.rises, self.drives = [], [], {}
        self.busy_start = None
        self.enabled = 0
        fall = delay
        for bit, low_ticks, high_ticks in zip(self.bits, low, (*high, 0)):
            rise = fall + low_ticks
            self.falls.append(fall)
            self.rises.append(rise)
            data = 0 if bit else DATA
            self.drives[fall - DATA_SETUP] = data
            self.drives[fall] = data | CLOCK
            self.drives[rise] = data
            fall = rise + high_ticks
        self.drives[self.rises[-1] + 1] = 0

    @property
    def terminal(self):
        return self.busy_start + self.falls[-1] + FINAL_FALL_TO_TERMINAL

    def drive(self, cycle, pads, _ui=0):
        require(pads.logical.enabled == 0, 'PS/2 receive enabled a protocol output')
        if self.busy_start is None and pads.status:
            self.busy_start = cycle
        if self.busy_start is not None:
            edge = cycle + 1 - self.busy_start
            self.enabled = self.drives.get(edge, self.enabled)
        return PadDrive(enabled=self.enabled)

    def check(self, records, captured):
        require(captured == self.bits, 'Host did not drain exactly the 11 external PS/2 frame bits')
        by_cycle = {record['cycle']: record for record in records if record['cycle'] >= self.busy_start}
        require(len(by_cycle) == self.terminal - self.busy_start + 1 and
                min(by_cycle) == self.busy_start and max(by_cycle) == self.terminal,
                'Missing PS/2 wire observation')
        falls, rises = [], []
        previous_clock = CLOCK
        for cycle, record in by_cycle.items():
            observed, drive = record['observation'], record['drive']
            require(observed['busy'] == (cycle < self.terminal), 'PS/2 BUSY interval changed')
            require(observed['enabled'] == drive['levels'] == drive['links'] == 0 and
                    drive['enabled'] & ~BUS == 0 and drive['pullups'] & BUS == BUS,
                    'PS/2 fixture violated released-output or open-drain wiring')
            raw = observed['edge_inputs']
            require(raw == observed['wires'] & BUS == BUS ^ drive['enabled'],
                    'PS/2 raw pins differ from resolved peer drive')
            clock = raw & CLOCK
            if clock != previous_clock:
                (rises if clock else falls).append(cycle)
            previous_clock = clock
        require(falls == [self.busy_start + offset for offset in self.falls] and
                rises == [self.busy_start + offset for offset in self.rises],
                'PS/2 observed clock transitions differ from the independently scheduled frame')
        apertures = []
        for fall, rise, bit in zip(falls, rises, self.bits):
            require(all(bool(by_cycle[cycle]['observation']['edge_inputs'] & DATA) == bit
                        for cycle in range(fall - DATA_SETUP, rise)),
                    'PS/2 data was unstable across a falling-edge aperture')
            apertures.append(dict(raw_fall=fall, expected_capture_edge=fall + SAMPLER_DELAY, data=bit))
        return dict(busy_start=self.busy_start, busy_end=self.terminal, low_ticks=self.low,
                    high_ticks=self.high, apertures=apertures)


def exchange(rtl, transport, loaded, name, byte, bad_field, delay, low, high, *, bit_count=FRAME_BITS):
    peer = KeyboardPeer(byte, bad_field, delay, low, high)
    rtl.device = peer
    exchanges = (Opcode.EXCHANGE32, Opcode.EXCHANGE64)
    before = tuple(transport.opcode_counts[op] for op in exchanges)
    pending = loaded.submit(bit_count=bit_count)
    require(peer.busy_start is not None and rtl.snapshot.busy, 'PS/2 START did not admit the receiver')
    transport.idle(peer.terminal - rtl.cycle)
    require(not rtl.snapshot.busy and before == tuple(transport.opcode_counts[op] for op in exchanges),
            'PS/2 did not reach its expected terminal edge without host service')
    wire_records = tuple(rtl.records)
    terminal = pending.wait(max_exchanges=6)
    require(terminal.retained and not terminal.fault and pending.tx_accepted == 0,
            'PS/2 did not retain the receive-only owner')
    wire = peer.check(wire_records, pending.rx_bits)
    decoded = decode_ps2_frame(pending.rx_bits)
    require(decoded == (byte if bad_field is None else None), 'PS/2 framing or parity verdict differs')
    released = pending.release()
    require(released.tag == pending.tag and not released.busy and not released.retained and
            pending.last.rx_start == FRAME_BITS and pending.last.rx_valid == 0,
            'PS/2 did not release after the exact acknowledged capture interval')
    rtl.device = None
    return dict(name=name, byte=byte, bad_field=bad_field, decoded=decoded, captured=list(pending.rx_bits),
                owner_tag=pending.tag, rx_acknowledged=pending.last.rx_start, wire=wire)


def replay(vvp, executable, trace_path):
    trace = EdgeTrace(trace_path)
    record_limit = max(delay + sum(low[:-1]) + sum(high) for _, _, _, delay, low, high in CASES)
    record_limit += FINAL_FALL_TO_TERMINAL + 1
    try:
        with QuadRTL(vvp, executable, record_limit=record_limit, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=DEPTH)
            host.initialize()
            loaded = host.load(ps2_receive_image())
            cases = [exchange(rtl, transport, loaded, *case) for case in CASES]
            require(transport.opcode_counts[Opcode.COMMIT] == 1 and
                    all(transport.opcode_counts[opcode] == len(CASES)
                        for opcode in (Opcode.START, Opcode.RELEASE)) and
                    transport.opcode_counts[Opcode.WARM_RESET] == 0 and
                    len({case['owner_tag'] for case in cases}) == len(CASES),
                    'PS/2 cases did not reuse one image under distinct owners')
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
             *(scripts / name for name in ('streaming_ready_ps2.py', 'streaming_ready_compile.py',
                'streaming_compile.py', 'streaming_8x4_jane_street_behavior.py',
                'streaming_ready_wrapper.py', 'streaming_ready_transport.py', 'streaming_transport.py',
                'streaming_rtl.py', 'streaming_wire_cases.py', 'pad_io.py', 'pinwheel_host.py'))]
    result = dict(schema='pinwheel.streaming-8x4-ps2.v1', passed=False, core_hz=CORE_HZ,
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
            print(f'{name}: {len(CASES)} PS/2 frame cases passed', flush=True)
        require(result['backends']['rtl'] == result['backends']['gate'] and
                (out / 'rtl-wire.bin').read_bytes() == (out / 'gate-wire.bin').read_bytes(),
                'Frozen RTL and gate results or public-edge traces differ')
        require(result['inputs'] == {str(path): artifact(path) for path in files},
                'A PS/2 replay input changed while running')
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
