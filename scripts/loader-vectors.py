#!/usr/bin/env python3
"""Independent atomic-host oracle; reuse the independently written E64/pin models."""
import collections
import json
import random
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/loader'
core = runpy.run_path(str(ROOT/'scripts/reactive-core-vectors.py'))
valid, pack = core['valid'], core['pack']


def stream(words, last, idle=(0, 0)):
    words = words + [4]*(256-len(words))
    assert len(words) == 256 and all(valid(w) for w in words)
    dictionary = list(dict.fromkeys(words))
    assert len(dictionary) <= 64
    return dictionary + [4]*(64-len(dictionary)) + [dictionary.index(w) for w in words] + [idle[0] | idle[1] << 3, last]


class Atomic(core['Machine']):
    def __init__(self):
        super().__init__(True)
        self.images = [[0]*322, [0]*322]
        self.active = self.committed = self.pending = self.cursor = 0
        self.gates = [0]*4
        self.counters = collections.Counter()
        self.read_bank = 0

    def read(self, pc):
        image = self.images[self.read_bank]
        return image[image[64+pc]]

    def edge(self, init=0, reset=0, command=0, data=0, incoming=0):
        busy = 1 <= self.s[0] <= 4
        enabled = not (init or reset or busy)
        good = valid(data) if self.cursor < 64 else data < (64 if self.cursor < 321 else 256)
        push = int(enabled and command == 2 and self.pending and self.cursor < 322 and good)
        commit = int(enabled and command == 3 and self.pending and self.cursor == 322)
        start = int(enabled and command == 5 and self.committed)
        accepted = enabled and (command in [0, 1, 4] or push or commit or start)
        rejected = int(not (init or reset) and command != 0 and not accepted)
        self.gates = [push, commit, start, rejected]
        old_active = self.active
        self.read_bank = 1-self.active if commit else self.active
        image = self.images[self.read_bank]
        self.idle = [image[320] & 7, image[320] >> 3] if not init and (self.committed or commit) else [0, 0]
        self.last = image[321]
        if init or reset or not self.committed or commit:
            self.stop(0, 0)
        elif busy:
            self.advance(incoming)
        elif start:
            self.enter(0, 0, incoming)
        if push:
            self.images[1-self.active][self.cursor] = data
        if init:
            self.active = self.committed = self.pending = self.cursor = 0
        elif reset:
            self.pending = self.cursor = 0
        elif not busy:
            if command == 1:
                self.pending, self.cursor = 1, 0
            elif command == 4:
                self.pending = self.cursor = 0
            elif commit:
                self.active, self.committed, self.pending, self.cursor = 1-self.active, 1, 0, 0
            elif push:
                self.cursor += 1
        assert 0 <= self.cursor <= 322
        self.counters.update(dict(push=push, commit=commit, start=start, rejected=rejected))
        self.rows.append([init, reset, command, data, incoming, *self.gates,
                          self.active, self.committed, self.pending, self.cursor, *self.s])
        if not init and not commit:
            assert self.active == old_active

    def load(self, name, words, last, idle=(0, 0)):
        self.cases.append(dict(name=name, edge=len(self.rows)))
        self.edge(reset=1)
        self.edge(command=1)
        payload = stream(words, last, idle)
        for data in payload:
            self.edge(command=2, data=data)
            assert self.gates[0] == 1
        self.edge(command=3)
        assert self.gates[1] and self.images[self.active] == payload


class ProtocolAdapter:
    """Exercise all busy commands while the existing pin-driven target runs."""
    def __init__(self, machine): self.m, self.count = machine, 0
    @property
    def s(self): return self.m.s
    def load(self, *args): self.m.load(*args)
    def edge(self, incoming=0, start=0, write=0, **ignored):
        command = (self.count % 7)+1 if write else 5 if start else 0
        self.count += 1
        self.m.edge(command=command, data=(1 << 64)-1, incoming=incoming)
        if write:
            assert self.m.gates == [0, 0, 0, 1]


def generate():
    images = {}
    for line in (OUT/'images.txt').read_text().splitlines():
        name, *numbers = line.split()
        last, levels, enables, *words = map(int, numbers)
        images[name] = (words, last, (levels, enables))
    m = Atomic()
    m.edge(init=1, reset=1, command=5, incoming=3)
    for cmd in range(8):
        m.edge(command=cmd, data=(1 << 64)-1)
        assert not m.committed and m.s == [0]*7
    m.edge(reset=1)
    m.load('uart-first-commit', *images['uart'])

    def uart():
        m.edge(command=5)
        expected = [0] + [(0x53 >> k) & 1 for k in range(8)] + [1]
        for t in range(40):
            assert m.s[4] & 1 == expected[t//4] and m.s[5] == 7
            m.edge(incoming=t % 4, command=(t % 7)+1, data=4)
            assert m.gates == [0, 0, 0, 1]
        assert m.s[0] == 5
    uart()
    # Staging interruption across the dictionary/map/metadata boundaries.
    replacement = stream(*images['spi'])
    interruptions = []
    for cut in [0, 1, 63, 64, 65, 255, 319, 320, 321, 322]:
        for ending in ['abort', 'reset', 'restart']:
            old = m.images[m.active].copy()
            m.edge(command=1)
            for word in replacement[:cut]: m.edge(command=2, data=word)
            if cut < 322:
                m.edge(command=3)
                assert m.gates[3] and m.pending and m.cursor == cut
            if ending == 'reset': m.edge(reset=1, command=3)
            else: m.edge(command=4 if ending == 'abort' else 1)
            assert m.cursor == 0 and m.images[m.active] == old
            m.edge(command=3); assert m.gates[3]
            uart()
            interruptions.append(dict(cut=cut, ending=ending))
    # Start the old program with an in-progress upload; completion permits resuming.
    m.edge(command=1)
    for word in replacement[:17]: m.edge(command=2, data=word)
    uart()
    assert m.cursor == 17 and m.pending
    for word in replacement[17:]: m.edge(command=2, data=word)
    m.edge(command=2, data=4); assert m.gates[3] and m.cursor == 322
    uart()  # Commit is otherwise eligible throughout this run; busy must block it.
    assert m.cursor == 322 and m.pending
    m.edge(command=3); assert m.gates[1]
    m.edge(command=3); assert m.gates[3]
    m.edge(command=5)
    received = 0x96
    for t in range(68):
        phase = t//4
        assert m.s[4] & 4 == 0 and (m.s[4] >> 1) & 1 == phase % 2
        if phase < 16: assert m.s[4] & 1 == (0xa6 >> (7-phase//2)) & 1
        m.edge(incoming=(received >> (7-min(7, (t+1)//8))) & 1, command=3)
        assert m.gates[3]
    assert m.s[0] == 5 and m.s[6] & 255 == int(f'{received:08b}'[::-1], 2)
    # Retry malformed records and over-wide map/metadata values, without cursor advance.
    m.edge(command=1)
    malformed = [1 << 63, 7, pack(dict(kind=2, finish=3)), pack(dict(kind=0, entry=2))]
    rng = random.Random(32264)
    malformed += [rng.getrandbits(64) for _ in range(64)]
    for word in malformed:
        assert not valid(word)
        m.edge(command=2, data=word); assert m.gates[3] and m.cursor == 0
    payload = stream(*images['i2c-write'])
    invalid_widths = 0
    for cursor, word in enumerate(payload):
        if cursor >= 64:
            for bad in [64 if cursor < 321 else 256, (1 << 64)-1]:
                m.edge(command=2, data=bad)
                assert m.gates[3] and m.cursor == cursor
                invalid_widths += 1
        m.edge(command=2, data=word); assert m.gates[0]
    m.edge(command=3); assert m.gates[1]
    core['i2c'](ProtocolAdapter(m), False, stretched=True)
    m.load('i2c-read', *images['i2c-read'])
    reads = []
    for byte in [0, 1, 0x55, 0x80, 0x96, 0xaa, 0xfe, 0xff]:
        for stretch in [False, True]:
            reads.append(core['i2c'](ProtocolAdapter(m), True, byte, stretched=stretch))
    for bits in range(7):
        reads.append(core['i2c'](ProtocolAdapter(m), True, acks=tuple((bits >> k) & 1 for k in range(3)), stretched=True))
    delayed = core['i2c_latency'](ProtocolAdapter(m), images)
    rx_frames = core['uart_rx']['exercise'](ProtocolAdapter(m), images)
    # A live replacement must clear captured status, without a preceding reset.
    assert m.s[6] != 0
    m.edge(command=1)
    for word in stream([4], 0, (5, 6)): m.edge(command=2, data=word)
    m.edge(command=3)
    assert m.gates[1] and m.s == [0, 0, 0, 0, 5, 6, 0]
    # Reset has priority over an otherwise eligible commit/start; initialization forgets validity.
    m.edge(command=1)
    for word in replacement: m.edge(command=2, data=word)
    old = m.active
    m.edge(reset=1, command=3); assert m.active == old and not m.pending
    m.edge(command=5, incoming=3)
    m.edge(reset=1, command=5); assert m.s[0] == 0
    m.edge(init=1, command=3); assert not m.committed and m.s == [0]*7
    m.edge(command=5); assert m.gates[3] and m.s == [0]*7
    m.load('uart-after-reinitialization', *images['uart'])
    uart()
    # Commit applies new idle metadata immediately and clears previously captured samples.
    m.load('metadata-replacement', [4], 0, (5, 6))
    assert m.s == [0, 0, 0, 0, 5, 6, 0]
    m.edge(command=5); assert m.s == [5, 0, 0, 0, 5, 6, 0]
    coverage = dict(edges=len(m.rows), interruptions=interruptions, counters=dict(m.counters),
                    malformed_records=len(malformed), overwide_values=invalid_widths,
                    i2c_reads=len(reads), i2c_behind_two_registers=len(delayed), uart_rx_frames=rx_frames,
                    quiet_read_cycles=reads[0], stretched_read_cycles=reads[1], cases=m.cases)
    (OUT/'vectors.txt').write_text(''.join(' '.join(map(str, row))+'\n' for row in m.rows))
    (OUT/'coverage.json').write_text(json.dumps(coverage, indent=2)+'\n')
    # Observe physical storage only; no writes/backdoor initialization in the testbench.
    names = [f'word{k}' for k in range(64)] + [f'index{k}' for k in range(256)] + ['idle', 'last']
    (OUT/'memory-observe.svh').write_text('\n'.join(
        f'assign observed[{bank*322+k}] = dut.r_bank{bank}_{name};' for bank in range(2) for k, name in enumerate(names))+'\n')
    return coverage


if __name__ == '__main__':
    print(json.dumps(generate(), indent=2))
