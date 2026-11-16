"""Independent USB peer and public-pin witness for the opt-in depth-two core."""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from pad_io import PadDrive
from streaming_ready_wrapper import bridge_source, package_source, tt_source
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport, require_accepted
from usb_low_speed import descriptor_read


ROOT = Path(__file__).resolve().parents[1]
TOP = 'tt_um_pinwheel_usb_low_speed_d2'
SE0, K, J, SE1 = range(4)
CAPTURE_MASK = 0b1100
DEVICE_PREFIX = bytes.fromhex('1201000200000008')
FAILURES = ('bad_pid', 'bad_crc', 'bad_stuff', 'short_eop', 'long_eop',
            'bad_eop_exit', 'truncated', 'no_reply', 'nak', 'stall')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def lsb(value, width):
    return [(value >> i) & 1 for i in range(width)]


def value(bits):
    return sum(bit << place for place, bit in enumerate(bits))


def remainder(bits, width, polynomial):
    high = width - 1
    register = (1 << width) - 1
    for bit in bits:
        carry = bit ^ (register >> high)
        register = ((register << 1) & ((1 << width) - 1)) ^ (polynomial * carry)
    return register


def parse_packet(symbols):
    prior, ones, bits = J, 0, []
    for line in symbols:
        require(line in (J, K), 'Non-data line state in USB packet body')
        bit = int(line == prior)
        prior = line
        if ones == 6:
            require(bit == 0, 'Host omitted a stuffed transition')
            ones = 0
        else:
            bits.append(bit)
            ones = ones + 1 if bit else 0
    require(ones != 6 and len(bits) >= 16 and value(bits[:8]) == 0x80, 'Invalid host SYNC')
    pid, body = value(bits[8:16]), bits[16:]
    require((pid >> 4) ^ (pid & 15) == 15, 'Invalid host PID')
    if pid in (0x2d, 0x69, 0xe1):
        require(len(body) == 16 and remainder(body, 5, 0x05) == 0x0c, 'Invalid token CRC5')
        return pid, value(body[:7]), value(body[7:11])
    if pid in (0xc3, 0x4b):
        require(len(body) >= 16 and len(body) % 8 == 0, 'Invalid host packet length')
        require(remainder(body, 16, 0x8005) == 0x800d, 'Invalid host CRC16')
        return pid, bytes(value(body[i:i + 8]) for i in range(0, len(body) - 16, 8))
    require(pid == 0xd2 and not body, 'Invalid host handshake')
    return (pid,)


def parse_flight(clocks):
    require(len(clocks) % 16 == 0, 'Partial host symbol')
    cells = []
    for i in range(0, len(clocks), 16):
        cell = clocks[i:i + 16]
        require(len(set(cell)) == 1, 'Unstable host symbol')
        cells.append(cell[0])
    packets = []
    while cells:
        require(cells[0] == K and SE0 in cells, 'Missing host start or end marker')
        end = cells.index(SE0)
        require(cells[end:end + 3] == [SE0, SE0, J], 'Invalid host end marker')
        packets.append(parse_packet(cells[:end]))
        following = end + 2
        while following < len(cells) and cells[following] == J:
            following += 1
        gap = 1 if following == len(cells) else 3
        require(following == end + 2 + gap, 'Incorrect host interpacket gap')
        cells = cells[following:]
    return packets


def reply(pid, payload=b'', fault=None):
    bits = lsb(0x80, 8) + lsb(pid, 8)
    if pid in (0x4b, 0xcb):
        body = [bit for byte in payload for bit in lsb(byte, 8)]
        crc = remainder(body, 16, 0x8005) ^ 0xffff
        footer = [crc >> place & 1 for place in range(15, -1, -1)]
        if fault == 'bad_crc':
            footer[-1] ^= 1
        bits.extend(body + footer)
    if fault == 'truncated':
        del bits[-12:]
    line, ones, injected, symbols = J, 0, False, []
    for bit in bits:
        if bit == 0:
            line = 3 - line
        symbols.append(line)
        ones = ones + 1 if bit else 0
        if ones == 6:
            corrupt = fault == 'bad_stuff' and not injected
            if not corrupt:
                line = 3 - line
            symbols.append(line)
            ones, injected = 0, injected or corrupt
    require(fault != 'bad_stuff' or injected, 'The test payload had no stuffed bit')
    width = {'short_eop': 1, 'long_eop': 3}.get(fault, 2)
    return symbols + [SE0] * width


class Peer:
    flights = (
        [(0x2d, 0, 0), (0xc3, bytes.fromhex('8006000100000800'))],
        [(0x69, 0, 0)],
        [(0xd2,)],
        [(0xe1, 0, 0), (0x4b, b'')],
    )

    def __init__(self, data, period, phase, fault=None):
        self.data, self.period, self.phase, self.fault = data, period, phase, fault
        self.stage, self.clocks, self.first = 0, [], None
        self.tx, self.responses = [], []
        self.reply_at, self.reply_symbols, self.reply_exit = 0, [], J
        self.ack_delay = None

    def flight_ended(self, cycle):
        require(self.stage < len(self.flights), 'Host emitted an extra packet')
        require(self.fault is None or self.stage != 2, 'Host acknowledged a rejected reply')
        packets = parse_flight(self.clocks)
        require(packets == self.flights[self.stage], f'Unexpected USB packets at stage {self.stage}: {packets!r}')
        marker = cycle - 16
        self.tx.append(dict(first=self.first, marker=marker, release=cycle, pids=[p[0] for p in packets]))
        slots = 4 if self.stage in (0, 3) else 2
        self.reply_at = marker * 1000 + slots * self.period + self.phase
        self.reply_exit = J
        if self.stage in (0, 3):
            self.reply_symbols = reply(0xd2)
        elif self.stage == 1:
            pid = {'bad_pid': 0xcb, 'nak': 0x5a, 'stall': 0x1e}.get(self.fault, 0x4b)
            self.reply_symbols = [] if self.fault == 'no_reply' else reply(pid, self.data, self.fault)
            if self.fault == 'bad_eop_exit':
                self.reply_exit = K
        else:
            end = self.responses[-1]['marker']
            self.ack_delay = self.first - end
            require(32 <= self.ack_delay <= 120, f'Host ACK turnaround was {self.ack_delay} clocks')
            self.reply_symbols = []
        if self.reply_symbols:
            end = self.reply_at + len(self.reply_symbols) * self.period
            self.responses.append(dict(first=(self.reply_at + 999) // 1000,
                marker=(end + 999) // 1000, release=(end + self.period + 999) // 1000))
        self.stage += 1
        self.clocks.clear()

    def drive(self, cycle, pads, _ui):
        require(pads.enabled in (0, CAPTURE_MASK), 'Host partially drove the USB differential pair')
        if pads.enabled:
            if not self.clocks:
                self.first = cycle
            self.clocks.append((pads.levels >> 2) & 3)
        elif self.clocks:
            self.flight_ended(cycle)
        at = (cycle + 1) * 1000
        if self.reply_symbols and at >= self.reply_at:
            slot = (at - self.reply_at) // self.period
            if slot <= len(self.reply_symbols):
                line = self.reply_symbols[slot] if slot < len(self.reply_symbols) else self.reply_exit
                return PadDrive(levels=line << 2, enabled=CAPTURE_MASK)
        return PadDrive()


class QuietStartTransport(QuadTransport):
    def _read(self, sequence):
        if self.inflight.opcode is Opcode.START:
            seen_busy = False
            for _ in range(3300):
                state = self.idle(1)
                seen_busy |= bool(state['busy'])
                if seen_busy and not state['busy']:
                    break
            else:
                raise RuntimeError('USB engine did not finish with the quad host idle')
            self.idle(20)
        return super()._read(sequence)


def transact(transport, stage, *, reject=False, check_ownership=False):
    for address, word in enumerate(stage.words):
        require_accepted(transport.request(Opcode.WRITE, address=address, word=word))
    loaded = require_accepted(transport.request(Opcode.COMMIT, count=len(stage.words)))
    require(loaded.valid, 'USB image did not commit')
    started = require_accepted(transport.request(Opcode.START,
        expected_generation=loaded.generation, bit_count=stage.receive_bits))
    tag = started.tag
    require(started.generation == loaded.generation and started.transfer != 0, 'Wrong START owner')
    if check_ownership and not reject:
        stale = transport.request(Opcode.EXCHANGE0, tag=tag ^ 0x10000)
        require(stale.code is Code.REJECTED and stale.rx_valid == 0, 'A stale owner read the payload')
        early = transport.request(Opcode.RELEASE, tag=tag)
        require(early.code is Code.REJECTED and early.retained, 'RELEASE discarded queued data')
    partial = []
    for _ in range(4):
        receipt = require_accepted(transport.exchange(tag, 0, len(partial)))
        require(receipt.tag == tag and receipt.retained and receipt.fault == reject,
            'Unexpected terminal USB receipt')
        require(receipt.rx_start == len(partial), 'USB RX returned a duplicate or skipped interval')
        partial.extend(receipt.rx_bits)
        if not receipt.rx_valid:
            require(receipt.rx_queued == 0, 'USB RX did not drain')
            break
    require(len(partial) == (0 if reject else stage.receive_bits), 'Unexpected USB payload length')
    released = require_accepted(transport.request(Opcode.RELEASE, tag=tag))
    require(released.tag == tag and not (released.busy or released.retained), 'RELEASE lost owner identity')
    return partial


def case(executable, *, name, period, phase, data=DEVICE_PREFIX, fault=None):
    setup, read, status = descriptor_read()
    peer = Peer(data, period, phase, fault)
    with QuadRTL('vvp', executable) as rtl:
        transport = QuietStartTransport(rtl)
        transport.cold_reset()
        rtl.device = peer
        expected_ack = [line == K for line in reply(0xd2)[:16]]
        require(transact(transport, setup) == expected_ack, 'SETUP did not capture the peer ACK')
        drained = transact(transport, read, reject=fault is not None, check_ownership=True)
        if fault is None:
            recovered = bytes(value(drained[i:i + 8]) for i in range(0, 64, 8))
            require(recovered == data, f'Wrong descriptor bytes {recovered.hex()}')
            require(transact(transport, status) == expected_ack, 'Status did not capture the peer ACK')
            require(peer.stage == 4 and peer.ack_delay == 48, f'Incomplete USB read: {peer.tx!r}')
        else:
            recovered = b''
            require(peer.stage == 2 and peer.ack_delay is None, 'Rejected USB read advanced the peer')
        return dict(name=name, period=period, phase=phase, fault=fault,
            payload=recovered.hex(), ack_delay=peer.ack_delay, host_flights=peer.tx,
            peer_flights=peer.responses, edges=rtl.cycle, starts=transport.opcode_counts[Opcode.START])


def prepare(directory):
    core, frontend = json.loads((directory / 'interface.json').read_text())
    package = package_source(core, frontend).replace(core['module'], 'pinwheel_usb_low_speed_core_d2')
    tiny = tt_source(2)
    bridge = bridge_source(2).replace('    assign (weak1,weak0) pads[k]=pullups[k] ? 1\'b1 : 1\'bz;',
        "    assign (weak1,weak0) pads[k]=(k == 0) ? 1'b0 : (k == 1) ? 1'b1 : 1'bz;")
    anchor = '  tranif1 scl_link'
    require(bridge.count(anchor) == 1, 'Unexpected quad bridge pin wiring')
    bridge = bridge.replace(anchor, '  tran sense0(pads[0],pads[2]);\n'
        '  tran sense1(pads[1],pads[3]);\n' + anchor)
    for name, source in [('package', package), ('tt', tiny), ('bridge', bridge)]:
        text = source.replace('pinwheel_streaming_ready_quad_d2', 'pinwheel_usb_low_speed_quad_d2')
        (directory / f'{name}.sv').write_text(text.replace('tt_um_pinwheel_streaming_ready_d2', TOP))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--backend', choices=('rtl', 'gate'))
    parser.add_argument('--only', help='Run a single named case for diagnosis')
    args = parser.parse_args()
    image = json.loads((args.directory / 'in-image.json').read_text())
    require(list(descriptor_read()[1].words) == image, 'Replay IN words differ from the kernel-checked image')
    if args.prepare:
        prepare(args.directory)
        return
    require(args.backend, 'Choose an RTL or gate backend')
    cases = [
        ('fast', 15760, 123, bytes.fromhex('ff00ffa500c3ffff'), None),
        ('nominal', 16000, 0, DEVICE_PREFIX, None),
        ('slow', 16240, 999, bytes.fromhex('ffffffffff008055'), None),
    ] + [(fault, 16000, 123, b'\xff' * 8, fault) for fault in FAILURES]
    executable = args.directory / f'{args.backend}.vvp'
    results = []
    for name, period, phase, data, fault in cases:
        if args.only is None or name == args.only:
            results.append(case(executable, name=name, period=period, phase=phase, data=data, fault=fault))
            print(f'{args.backend}: {name} passed', flush=True)
    require(results, 'No USB cases ran')
    if args.only is None:
        design_files = [args.directory / f'{n}.sv' for n in ('core', 'frontend', 'package', 'tt', 'bridge')]
        if args.backend == 'gate':
            design_files.append(args.directory / 'gate.v')
        report = dict(backend=args.backend, cases=results,
            images=[list(stage.words) for stage in descriptor_read()],
            sha256={path.name: sha256(path.read_bytes()).hexdigest()
                for path in [*design_files, args.directory / 'in-image.json']})
        (args.directory / f'{args.backend}.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
