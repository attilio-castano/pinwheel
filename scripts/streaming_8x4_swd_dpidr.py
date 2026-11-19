"""Replay a DPIDR read and its bad-parity control on frozen 8×4 RTL and gates."""
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import time

from pad_io import PadDrive
from streaming_8x4_bringup import DEPTH, TOP
from streaming_8x4_e982_native import require, sha, write
from streaming_8x4_jane_street_behavior import GDS, NETLIST, PDK_MODELS, RTL, artifact, compile_model
from streaming_ready_swd import REPLY_BITS, decode_dpidr, dpidr_image
from streaming_ready_transport import ReadyHost
from streaming_ready_wrapper import bridge_source
from streaming_rtl import QuadRTL
from streaming_transport import Opcode, QuadTransport
from streaming_wire_cases import EdgeTrace


SWCLK = 2
SWDIO = 3
SENSE = 1
DATA_OE = 1 << SWDIO
HALF_CYCLES = 4
RUN_CLOCKS = 506
CASES = (('valid', 0x2BA01477, False), ('bad-parity', 0x6BA02477, True))


class DpidrPeer:
    """An SWD target whose output changes follow observed SWCLK rising edges."""

    def __init__(self, word, *, bad_parity):
        # An independent ACK and payload serializer for the peer fixture.
        parity = word.bit_count() % 2 ^ int(bad_parity)
        reply = 1 | (word << 3) | (parity << 35)
        self.reply = tuple(bool(reply & (1 << index)) for index in range(36))
        self.target = None
        self.clock = False
        self.host = False
        self.host_level = False
        self.busy_start = None
        self.busy_end = None
        self.slots = []
        self.pulse_widths = []
        self.request = 0

    def drive(self, cycle, pads, _ui=0):
        pads.logical
        clock, data = bool(pads.bit(SWCLK)), bool(pads.bit(SWDIO))
        host, level = bool(pads.enabled & DATA_OE), bool(pads.levels & DATA_OE)
        require(data == bool(pads.bit(SENSE)), 'SWDIO drive and sense pads differ')
        if not pads.status and self.busy_start is None:
            return PadDrive()
        require(pads.enabled & (1 << SWCLK) and not pads.enabled & (1 << 4),
            'SWD needs a driven clock and an unused third output')
        require(not (host and self.target is not None), 'SWDIO ownership overlaps')
        if pads.status and self.busy_start is None:
            require(not clock and not host, 'SWD START did not establish idle pins before clocking')
            self.busy_start = cycle
        if not pads.status and self.busy_start is not None and self.busy_end is None:
            self.busy_end = cycle
            require(len(self.slots) == 54 and not clock and not host,
                'SWD stopped before all clocks or failed to release SWDIO')
        if clock and self.clock:
            require(host == self.host and (not host or level == self.host_level),
                'Controller changed SWDIO while SWCLK remained high')
        if self.clock and not clock:
            self.pulse_widths.append(cycle - self.slots[-1]['cycle'])
        if clock and not self.clock:
            self.rising(cycle, data, host)
        self.clock, self.host, self.host_level = clock, host, level
        return PadDrive(DATA_OE if self.target else 0, DATA_OE if self.target is not None else 0)

    def rising(self, cycle, data, host):
        index = len(self.slots)
        require(self.busy_start is not None and self.busy_end is None and index < 54,
            'SWD emitted an out-of-frame clock')
        self.slots.append(dict(cycle=cycle, host_enabled=host, target_enabled=self.target is not None, data=data))
        if index < 8:
            require(host and self.target is None, 'SWD request lacks host drive')
            self.request |= int(data) << index
            if index == 7:
                require(self.request == 0xA5, 'SWD request differs from a DPIDR read')
        elif index == 8:
            require(not host and self.target is None, 'SWD first turnaround was not released')
            self.target = self.reply[0]
        elif index < 45:
            bit = index - 9
            require(not host and self.target == data == self.reply[bit],
                'SWD target response differs at the rising edge')
            self.target = self.reply[bit + 1] if bit < 35 else None
        elif index == 45:
            require(not host and self.target is None, 'SWD second turnaround was not released')
        else:
            require(host and self.target is None and not data, 'SWD idle lacks controller-driven LOW')

    def check(self, records, captured):
        require(self.busy_end is not None and self.busy_end - self.busy_start == RUN_CLOCKS and
                self.pulse_widths == [HALF_CYCLES] * 54,
            'SWD changed the no-service run length or a SWCLK high duration')
        require(captured == self.reply, 'Host did not drain the exact 36 capture bits')
        by_cycle = {record['cycle']: record for record in records}
        apertures = []
        for index, expected in enumerate(self.reply, 9):
            rise = self.slots[index]['cycle']
            previous = self.slots[index - 1]['cycle']
            sample_edge = rise - 2
            require(sample_edge > previous and sample_edge in by_cycle, 'No earlier SWD sampler aperture')
            record = by_cycle[sample_edge]
            sampled = bool(record['observation']['edge_inputs'] & (1 << SENSE))
            drive = record['drive']
            require(drive['enabled'] == DATA_OE and sampled == expected ==
                    bool(drive['levels'] & DATA_OE), 'SWD response was unstable at the sampler aperture')
            apertures.append(dict(rise=rise, raw_sample=sample_edge, data=sampled))
        return dict(request=self.request, busy_start=self.busy_start, busy_end=self.busy_end,
            clock_pairs=54, swclk_high_cycles=HALF_CYCLES, slots=self.slots, apertures=apertures)


def exchange(rtl, transport, loaded, name, word, bad_parity):
    peer = DpidrPeer(word, bad_parity=bad_parity)
    rtl.device = peer
    exchanges = (Opcode.EXCHANGE32, Opcode.EXCHANGE64)
    before = tuple(transport.opcode_counts[op] for op in exchanges)
    pending = loaded.submit(bit_count=REPLY_BITS)
    transport.idle(RUN_CLOCKS)
    require(not rtl.snapshot.busy and before == tuple(transport.opcode_counts[op] for op in exchanges),
        'SWD needed queue service before the wire transaction completed')
    terminal = pending.wait(max_exchanges=6)
    require(terminal.retained and not terminal.fault and pending.tx_accepted == 0,
        'SWD receive did not retain the complete owner')
    wire = peer.check(rtl.records, pending.rx_bits)
    decoded = decode_dpidr(pending.rx_bits)
    require(decoded == (None if bad_parity else word), 'SWD ACK/parity validation returned the wrong result')
    released = pending.release()
    require(released.tag == pending.tag and not released.busy and not released.retained and
            pending.last.rx_start == REPLY_BITS and pending.last.rx_valid == 0,
        'SWD did not release the exact acknowledged capture interval')
    rtl.device = None
    return dict(name=name, word=word, decoded=decoded, captured=list(pending.rx_bits),
        bad_parity=bad_parity, owner_tag=pending.tag, rx_acknowledged=pending.last.rx_start, wire=wire)


def replay(vvp, executable, trace_path):
    trace = EdgeTrace(trace_path)
    try:
        with QuadRTL(vvp, executable, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=DEPTH)
            host.initialize()
            loaded = host.load(dpidr_image(HALF_CYCLES))
            cases = [exchange(rtl, transport, loaded, *case) for case in CASES]
            require(transport.opcode_counts[Opcode.COMMIT] == 1 and
                    all(transport.opcode_counts[opcode] == len(CASES)
                        for opcode in (Opcode.START, Opcode.RELEASE)) and
                    transport.opcode_counts[Opcode.WARM_RESET] == 0 and
                    len({case['owner_tag'] for case in cases}) == len(CASES),
                'SWD cases did not reuse one installed image under distinct owners')
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
             *(scripts / name for name in ('streaming_ready_swd.py', 'streaming_ready_compile.py',
                'streaming_compile.py', 'streaming_8x4_jane_street_behavior.py',
                'streaming_ready_wrapper.py', 'streaming_ready_transport.py', 'streaming_transport.py',
                'streaming_rtl.py', 'streaming_wire_cases.py', 'pad_io.py', 'pinwheel_host.py'))]
    result = dict(schema='pinwheel.streaming-8x4-swd-dpidr.v1', passed=False,
                  inputs={str(path): artifact(path) for path in files}, stages={}, backends={})
    started = time.monotonic()
    try:
        bridge = out / 'bridge.sv'
        bridge.write_text(bridge_source(DEPTH, swdio_link=True))
        result['bridge'] = artifact(bridge)
        sources = {'rtl': [release / 'src' / name for name in RTL],
                   'gate': [*(models / name for name in PDK_MODELS), netlist]}
        for name, paths in sources.items():
            exe, result['stages'][name] = compile_model(iverilog, out, name, [*paths, bridge])
            result['backends'][name] = replay(vvp, exe, out / (name + '-wire.bin'))
            print(f'{name}: valid and bad-parity SWD cases passed', flush=True)
        require(result['backends']['rtl'] == result['backends']['gate'] and
                (out / 'rtl-wire.bin').read_bytes() == (out / 'gate-wire.bin').read_bytes(),
                'Frozen RTL and gate results or public-edge traces differ')
        require(result['inputs'] == {str(path): artifact(path) for path in files},
                'An SWD replay input changed while running')
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
