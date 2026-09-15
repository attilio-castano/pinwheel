#!/usr/bin/env python3
"""Independent E64 execution oracle and pin-driven protocol targets.

No Lean expected states are consumed. Compilers supply program images only.
All vectors run on one instance per store layout, including stopped reloads.
"""
import json
import random
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/reactive-core'
codec = runpy.run_path(str(ROOT / 'scripts/execution-vectors.py'))
pack, valid = codec['pack'], codec['decode']


def fields(word):
    result, shift = {}, 0
    for name, width in codec['FIELDS']:
        result[name] = (word >> shift) & ((1 << width)-1)
        shift += width
    return result


class Machine:
    def __init__(self, indexed):
        self.indexed = indexed
        self.words, self.dictionary, self.addresses = [0]*256, [0]*64, [0]*256
        self.idle, self.last = [0, 0], 0
        self.s = [0]*7  # mode, pc, remaining, wait budget, levels, enables, samples
        self.rows, self.cases = [], []
        self.initialized = False

    def read(self, pc):
        return self.dictionary[self.addresses[pc]] if self.indexed else self.words[pc]

    @staticmethod
    def capture(samples, descriptor, incoming):
        if descriptor & 1:
            destination, pin = descriptor >> 2, (descriptor >> 1) & 1
            samples = (samples & ~(1 << destination)) | (((incoming >> pin) & 1) << destination)
        return samples

    def stop(self, mode, samples):
        self.s = [mode, 0, 0, 0, *self.idle, samples]

    def enter(self, pc, samples, incoming):
        word = self.read(pc)
        if not valid(word):
            self.stop(7, samples)
            return
        d = fields(word)
        if d['kind'] == 4:
            self.stop(5, samples)
            return
        self.s = [d['kind']+1, pc, d['duration'], d['budget'] if d['kind'] == 3 else 0,
                  d['levels'], d['enabled'], self.capture(samples, d['entry'], incoming)]

    def dispatch(self, d, incoming):
        mode, pc, _, _, _, _, samples = self.s
        finish = d['finish'] if mode == 3 else 0
        if mode == 3:
            samples = self.capture(samples, d['terminal'], incoming)
        if finish == 0:
            target = pc+1
        elif finish == 1:
            target = d['yes']
        else:
            target = d['yes'] if (samples >> d['sample']) & 1 else d['no']
        if target > self.last or target > 255:
            self.stop(7, samples)
        else:
            self.enter(target, samples, incoming)

    def advance(self, incoming):
        mode, pc, remaining, budget, _, _, samples = self.s
        word = self.read(pc)
        d = fields(word)
        guarded = (incoming & (d['check'] & 3)) == ((d['check'] >> 2) & (d['check'] & 3))
        if mode != 1 and (not valid(word) or d['kind'] != mode-1):
            self.stop(7, samples)
        elif mode == 1:
            if remaining:
                self.s[2] -= 1
            else:
                self.dispatch(d, incoming)
        elif mode == 2:
            ready = ((incoming >> (d['check'] & 1)) & 1) == ((d['check'] >> 1) & 1)
            if ready:
                self.dispatch(d, incoming)
            elif remaining:
                self.s[2] -= 1
            else:
                self.stop(6, samples)
        elif mode == 3:
            if not guarded:
                self.stop(7, samples)
            elif remaining:
                self.s[2] -= 1
            else:
                self.dispatch(d, incoming)
        elif guarded:
            if remaining:
                self.s[2] -= 1
                self.s[3] = d['budget']
            else:
                self.dispatch(d, incoming)
        elif budget:
            self.s[2], self.s[3] = d['duration'], budget-1
        else:
            self.stop(6, samples)

    def edge(self, reset=0, start=0, incoming=0, write=0, bank=0, address=0, data=0, check=1):
        busy = 1 <= self.s[0] <= 4
        if reset:
            self.stop(0, 0)
        elif busy:
            self.advance(incoming)
        elif start:
            self.enter(0, 0, incoming)
        if write and not (busy or reset or start):
            if bank == 2:
                if address == 0:
                    self.idle = [data & 7, (data >> 3) & 7]
                elif address == 1:
                    self.last = data & 255
            elif self.indexed:
                if bank == 0 and address < 64:
                    self.dictionary[address] = data
                elif bank == 1:
                    self.addresses[address] = data & 63
            elif bank == 0:
                self.words[address] = data
        self.rows.append([reset, start, incoming, write, bank, address, data, int(check and self.initialized), *self.s])

    def load(self, name, words, last, idle=(0, 0)):
        self.cases.append(dict(name=name, edge=len(self.rows)))
        self.edge(reset=1)
        words = words + [4]*(256-len(words))
        if self.indexed:
            unique = list(dict.fromkeys(words))
            assert len(unique) <= 64
            addresses = [unique.index(w) for w in words]
            dictionary = unique + [4]*(64-len(unique))
            for bank, values in [(0, dictionary), (1, addresses)]:
                for addr, data in enumerate(values):
                    # Always write every location: setup has no assumed initial contents.
                    self.edge(write=1, bank=bank, address=addr, data=data)
        else:
            for addr, data in enumerate(words):
                self.edge(write=1, address=addr, data=data)
        self.edge(write=1, bank=2, address=0, data=idle[0] | idle[1] << 3)
        self.edge(write=1, bank=2, address=1, data=last)
        self.initialized = True
        self.edge(reset=1)


def i2c(m, read, byte=0x96, acks=(1, 1, 1), stretched=False):
    m.edge(start=1, incoming=3)
    expected_clocks = (9 if not acks[0] else 18 if not acks[1] else 27 if not acks[2] else 36) if read else 18
    previous, previous_command = [1, 1], [0, 0]
    target_sda, stretch_left, releases, starts, stopped = 0, 0, 0, 0, False
    clocks, pending, rise_at, fall_at = [], None, 0, 0
    for t in range(2000):
        assert m.s[4] == 0 and m.s[5] < 4, 'unsafe I2C drive'
        command = [m.s[5] & 1, (m.s[5] >> 1) & 1]
        if previous_command[0] and not command[0]:
            stretch_left = releases % 4 if stretched else 0
            releases += 1
        bus = [int(not (command[0] or stretch_left)), int(not (command[1] or target_sda))]
        if previous[0] and bus[0] and previous[1] != bus[1]:
            assert t-rise_at >= 4
            if previous[1]:
                starts += 1
                assert starts == 1 or (read and starts == 2 and len(clocks) == 18)
            else:
                assert starts > 0
                stopped = True
            pending = None
        if not previous[0] and bus[0] and starts and not stopped:
            assert t-fall_at >= 4
            rise_at, pending = t, bus[1]
        if previous[0] and not bus[0]:
            fall_at = t
            if pending is not None:
                assert t-rise_at >= 4
                clocks.append(pending)
                pending = None
        if not bus[0]:
            k = len(clocks)
            target_sda = acks[k//9] if k in ((8, 17, 26) if read else (8, 17)) else 0
            if read and acks[2] and 27 <= k < 35:
                target_sda = 1-((byte >> (34-k)) & 1)
        bus = [bus[0], int(not (command[1] or target_sda))]
        if bus[0] and pending is not None and len(clocks) < expected_clocks and (len(clocks) % 9 == 8 or (read and len(clocks) >= 27)):
            assert not command[1], 'controller drove ACK/data/NACK'
        # Attempt writes to all banks, including metadata, throughout execution.
        m.edge(incoming=bus[0] | bus[1] << 1, write=1, bank=t % 4,
               address=(t//4) % 2, data=(1 << 64)-1, start=int(t % 13 == 0))
        previous, previous_command = bus, command
        stretch_left = max(0, stretch_left-1)
        if m.s[0] >= 5:
            break
    assert m.s[0] == 5 and stopped
    n = (9 if not acks[0] else 18 if not acks[1] else 27 if not acks[2] else 36) if read else 18
    assert len(clocks) == n, (len(clocks), n)
    assert starts == (2 if read and acks[0] and acks[1] else 1)
    outgoing = [0xa6, 0xa6, 0xa7, byte]
    for k, bit in enumerate(clocks):
        expected = (1-acks[k//9] if k < 27 else 1) if k % 9 == 8 else ((outgoing[k//9] >> (7-k % 9)) & 1)
        assert bit == expected, (k, bit, expected)
    if read:
        for k in range(min(3, len(clocks)//9)):
            assert (m.s[6] >> (8+k)) & 1 == 1-acks[k], 'incorrect ACK status slot'
    if read and all(acks):
        assert m.s[6] & 255 == int(f'{byte:08b}'[::-1], 2)
    return t+1


def generate():
    images = {}
    for line in (OUT/'images.txt').read_text().splitlines():
        name, *numbers = line.split()
        last, levels, enabled, *words = map(int, numbers)
        assert len(words) == 256
        images[name] = (words, last, (levels, enabled))
    coverage = {}
    for indexed in [False, True]:
        m = Machine(indexed)
        # First reset establishes mode; metadata/pins become known only after setup.
        m.edge(reset=1, check=0)
        m.load('uart', *images['uart'])
        m.edge(start=1)
        expected = [0] + [(0x53 >> k) & 1 for k in range(8)] + [1]
        for t in range(40):
            assert m.s[4] & 1 == expected[t//4] and m.s[5] == 7
            m.edge(incoming=t % 4)
        assert m.s[0] == 5
        m.load('spi', *images['spi'])
        m.edge(start=1)
        received = 0x96
        for t in range(68):
            phase = t//4
            assert m.s[4] & 4 == 0
            assert (m.s[4] >> 1) & 1 == phase % 2
            if phase < 16:
                assert m.s[4] & 1 == (0xa6 >> (7-phase//2)) & 1
            # Input is set for the upcoming rising edge; slot order is wire order.
            input_bit = (received >> (7-min(7, (t+1)//8))) & 1
            m.edge(incoming=input_bit)
        assert m.s[0] == 5
        assert m.s[6] & 255 == int(f'{received:08b}'[::-1], 2)
        m.load('i2c-write', *images['i2c-write'])
        i2c(m, False, stretched=True)
        reads = []
        m.load('i2c-read', *images['i2c-read'])
        for byte in [0, 1, 0x55, 0x80, 0x96, 0xaa, 0xfe, 0xff]:
            for stretch in [False, True]:
                reads.append(i2c(m, True, byte, stretched=stretch))
        for ack_bits in range(7):
            acks = tuple((ack_bits >> k) & 1 for k in range(3))
            reads.append(i2c(m, True, acks=acks, stretched=True))
        # Terminal capture feeds branch, then successor entry may overwrite that slot.
        p = [pack(dict(kind=2, terminal=63, finish=2, sample=15, yes=1, no=2)),
             pack(dict(kind=0, levels=5, enabled=7, entry=61)), 4]
        m.load('capture-forward-and-overwrite', p, 2)
        m.edge(start=1)
        m.edge(incoming=2)
        assert m.s[1] == 1 and m.s[6] == 0 and m.s[4] == 5
        m.edge(); assert m.s[0] == 5
        # Guard failure cannot commit terminal capture.
        p[0] = pack(dict(kind=2, check=5, terminal=63))
        m.load('guard-priority', p, 2)
        m.edge(start=1); m.edge(incoming=2)
        assert m.s[0] == 7 and m.s[6] == 0
        # Ready on the final budget edge wins, including maximum countdown.
        for duration in [0, 1, 255]:
            m.load('wait-final-ready', [pack(dict(kind=1, duration=duration, check=2)), 4], 1)
            m.edge(start=1)
            for _ in range(duration): m.edge()
            m.edge(incoming=1); assert m.s[0] == 5
            m.edge(start=1)
            for _ in range(duration+1): m.edge()
            assert m.s[0] == 6
        m.load('qualification-interrupt-rebudget', [pack(dict(kind=3, duration=2, budget=2, check=5)), 4], 1)
        m.edge(start=1)
        for v in [0, 1, 0, 1, 0, 1, 1, 1]: m.edge(incoming=v)
        assert m.s[0] == 5
        m.edge(start=1)
        for _ in range(3): m.edge()
        assert m.s[0] == 6
        m.edge(start=1)
        m.edge(reset=1, start=1, write=1, bank=2, address=0, data=63)
        assert m.s[0] == 0 and m.s[6] == 0 and m.idle == [0, 0]
        # Unsigned target comparisons around the sign bit and end of memory.
        for target in [0, 1, 127, 128, 254, 255]:
            for last in [0, 1, 127, 128, 254, 255]:
                m.load('unsigned-jump-boundary', [pack(dict(kind=2, finish=1, yes=target))], last)
                m.edge(start=1); m.edge()
                assert m.s[0] == (7 if target > last else 3 if target == 0 else 5)
        m.load('sequential-no-wrap', [pack(dict(kind=0))]*256, 255)
        m.edge(start=1)
        for _ in range(256): m.edge()
        assert m.s[0] == 7
        rng = random.Random(64015)
        malformed = [1 << 63, 7, pack(dict(kind=2, finish=3)), pack(dict(kind=0, entry=2))]
        malformed += [rng.getrandbits(64) for _ in range(12)]
        for word in malformed:
            assert not valid(word)
            m.load('invalid-start-record', [word], 0)
            m.edge(start=1); assert m.s[0] == 7
        name = 'indexed' if indexed else 'direct'
        (OUT/f'{name}-vectors.txt').write_text(''.join(' '.join(map(str, row))+'\n' for row in m.rows))
        coverage[name] = dict(edges=len(m.rows), cases=m.cases, i2c_reads=len(reads),
                              quiet_read_cycles=reads[0], stretched_read_cycles=reads[1])
    (OUT/'coverage.json').write_text(json.dumps(coverage, indent=2)+'\n')
    return coverage

if __name__ == '__main__':
    print(json.dumps(generate(), indent=2))
