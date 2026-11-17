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
CASES = (('valid-width-1', 1, False), ('valid-width-2', 2, False), ('bad-fcs', 2, True))


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


def push_burst(rtl, transport, tag, offset, bits):
    start = rtl.cycle
    reply = require_accepted(transport.exchange(tag, offset, 0, bits[offset:offset + BURST_BITS]))
    ready = next(record['cycle'] for record in rtl.records
                 if record['cycle'] > start and record['observation']['ready'])
    require((ready, rtl.cycle) == (start + READY, start + RESPONSE_CLOSE),
            'SNI host refill response timing changed')
    require(reply.tag == tag and reply.busy and not reply.fault and not reply.retained and
            reply.tx_accepted == offset + BURST_BITS and reply.rx_start == reply.rx_valid == 0,
            'SNI host did not accept the exact requested 64-bit burst')
    return dict(offset=offset, start=start, request_close=start + REQUEST_CLOSE, grant=start + GRANT,
                tx_push=[start + GRANT + 1, start + GRANT + 2], ready=ready, response_close=rtl.cycle)


def exchange(rtl, transport, loaded, name, high_ticks, corrupt):
    peer = SerialPHY(high_ticks)
    rtl.device = peer
    start = rtl.cycle
    frame = fixture_frame()
    if corrupt:
        frame = frame[:-1] + bytes([frame[-1] ^ 1])
    bits = serial_bits(frame)
    started = require_accepted(transport.request(Opcode.START, expected_generation=loaded.generation,
                                                 bit_count=WIRE_BITS))
    require(started.busy and started.tx_free == DEPTH and started.tx_accepted == 0,
            'SNI START did not create an empty armed owner')
    bursts = [push_burst(rtl, transport, started.tag, 0, bits)]
    first = peer.arm(rtl.cycle)
    for offset in range(BURST_BITS, WIRE_BITS, BURST_BITS):
        launch = first + FIRST_REFILL + (offset - BURST_BITS) * BIT_CYCLES
        require(rtl.cycle < launch, 'A previous refill exceeded the next host launch deadline')
        transport.idle(launch - rtl.cycle)
        bursts.append(push_burst(rtl, transport, started.tag, offset, bits))
    done = first + BIT_CYCLES * (WIRE_BITS - 1) + 4
    transport.idle(done - rtl.cycle)
    require(not rtl.snapshot.busy, 'SNI program did not finish at the exact final deadline')
    released = require_accepted(transport.request(Opcode.RELEASE, tag=started.tag))
    require(released.tag == started.tag and not released.busy and not released.retained,
            'SNI owner did not release after consuming the frame')
    trace = peer.check([record for record in rtl.records if record['cycle'] > start], first, bits, corrupt)
    rtl.device = None
    return dict(name=name, owner_tag=started.tag, tx_bits=bursts[-1]['offset'] + BURST_BITS,
                bursts=bursts, phy=trace)


def replay(vvp, executable, trace_path):
    trace = EdgeTrace(trace_path)
    try:
        with QuadRTL(vvp, executable, record_limit=6000, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=DEPTH)
            host.initialize()
            loaded = host.load(ethernet_sni_image())
            cases = [exchange(rtl, transport, loaded, *case) for case in CASES]
            require(transport.opcode_counts[Opcode.COMMIT] == 1 and
                    transport.opcode_counts[Opcode.EXCHANGE64] == len(CASES) * (WIRE_BITS // BURST_BITS) and
                    all(transport.opcode_counts[op] == len(CASES) for op in (Opcode.START, Opcode.RELEASE)) and
                    transport.opcode_counts[Opcode.WARM_RESET] == 0 and
                    len({case['owner_tag'] for case in cases}) == len(CASES),
                    'SNI cases changed image or reused an owner')
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
