#!/usr/bin/env python3
"""Independent E64 grammar oracle and reproducible raw-port stimuli.

The oracle reconstructs allowed fields for each operation, without the circuit's
validity masks. Store observations occur after each rising write edge.
"""
import json
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/execution'
FIELDS = [('kind', 3), ('levels', 3), ('enabled', 3), ('duration', 8),
          ('budget', 8), ('check', 4), ('entry', 6), ('terminal', 6),
          ('finish', 2), ('sample', 4), ('yes', 8), ('no', 8)]


def pack(fields):
    word, shift = 0, 0
    for name, width in FIELDS:
        word |= fields.get(name, 0) << shift
        shift += width
    return word


def decode(word):
    fields, shift = {}, 0
    for name, width in FIELDS:
        fields[name] = (word >> shift) & ((1 << width) - 1)
        shift += width
    kind = fields['kind']
    if kind > 4:
        return False
    allowed = {'kind': kind}
    if kind != 4:
        for key in ['levels', 'enabled', 'duration']:
            allowed[key] = fields[key]
    if kind in (0, 2):
        allowed['entry'] = fields['entry'] if fields['entry'] & 1 else 0
    if kind == 1:
        allowed['check'] = fields['check'] & 3
    if kind in (2, 3):
        allowed['check'] = fields['check']
    if kind == 3:
        allowed['budget'] = fields['budget']
    if kind == 2:
        allowed['terminal'] = fields['terminal'] if fields['terminal'] & 1 else 0
        finish = fields['finish']
        if finish == 3:
            return False
        allowed['finish'] = finish
        if finish in (1, 2):
            allowed['yes'] = fields['yes']
        if finish == 2:
            allowed['sample'] = fields['sample']
            allowed['no'] = fields['no']
    return pack(allowed) == word


def observation(word):
    # Raw field outputs remain visible even for rejected records; bit 63 is reserved.
    return [int(decode(word)), word & ((1 << 63) - 1)]


def generate():
    rng = random.Random(0xE64)
    images = []
    for line in (OUT / 'images.txt').read_text().splitlines():
        name, *raw = line.split()
        data = list(map(int, raw))
        assert len(data) == 576
        words, dictionary, addresses = data[:256], data[256:320], data[320:]
        assert all(decode(w) for w in words)
        assert [dictionary[k] for k in addresses] == words
        images.append((name, words, dictionary, addresses))
    vectors = set(range(65536))
    for _, words, _, _ in images:
        for word in set(words):
            vectors.add(word)
            vectors.update(word ^ (1 << bit) for bit in range(64))
    # Exercise legal field extrema, both input pins, every capture/branch destination,
    # and every branch address before adding unrestricted malformed words.
    for address in range(256):
        for slot in range(16):
            for finish in range(3):
                f = dict(kind=2, levels=address % 8, enabled=(255-address) % 8,
                         duration=address, check=slot, entry=(slot << 2) | 1,
                         terminal=(slot << 2) | 3, finish=finish)
                if finish:
                    f['yes'] = address
                if finish == 2:
                    f.update(sample=slot, no=255-address)
                word = pack(f)
                assert decode(word)
                vectors.add(word)
                vectors.add(word | (1 << 63))
    vectors.update(rng.getrandbits(64) for _ in range(8192))
    with (OUT / 'decoder-vectors.txt').open('w') as f:
        for word in sorted(vectors):
            f.write(' '.join(map(str, [word, *observation(word)])) + '\n')
    coverage = dict(images=len(images), decoder_vectors=len(vectors), stores={})

    for indexed in [False, True]:
        name = 'indexed' if indexed else 'direct'
        words, dictionary, addresses = [0]*256, [0]*64, [0]*256
        rows, checked = [], 0

        def edge(write=0, busy=0, bank=0, addr=0, data=0, a=0, b=255, check=True):
            nonlocal checked
            if write and not busy:
                if indexed:
                    if bank:
                        addresses[addr] = data & 63
                    elif addr < 64:
                        dictionary[addr] = data
                elif not bank:
                    words[addr] = data
            wa = dictionary[addresses[a]] if indexed else words[a]
            wb = dictionary[addresses[b]] if indexed else words[b]
            rows.append([write, busy, bank, addr, data, a, b, int(check),
                         *observation(wa), *observation(wb)])
            checked += int(check)

        # No RTL power-up value is assumed. Initialize every physical register first.
        for k in range(64 if indexed else 256):
            edge(write=1, addr=k, data=4, check=False)
        if indexed:
            for k in range(256):
                edge(write=1, bank=1, addr=k, data=0, check=False)
        edge()
        for _, image_words, image_dict, image_map in images:
            for k, word in enumerate(image_dict if indexed else image_words):
                edge(write=1, addr=k, data=word, a=k, b=255-k)
            if indexed:
                for k, value in enumerate(image_map):
                    edge(write=1, bank=1, addr=k, data=value, a=k, b=255-k)
            # Both candidates execute precisely the same address-pair workload.
            for k in range(256):
                edge(a=k, b=255-k, busy=1)
        # Set every logical address to a known, nonconstant record, then attempt
        # writes while busy and while write is disabled; inspect every address pair.
        if indexed:
            for k in range(256):
                edge(write=1, bank=1, addr=k, data=k % 64, a=k)
        for k in range(64 if indexed else 256):
            word = pack(dict(kind=0, levels=k % 8, enabled=7, duration=k))
            edge(write=1, addr=k, data=word, a=k, b=k)
            edge(write=1, busy=1, addr=k, data=4, a=k, b=k)
            edge(write=0, addr=k, data=(1 << 64)-1, a=k, b=k)
        for k in range(256):
            edge(write=1, busy=1, bank=1, addr=k, data=63-(k % 64), a=k)
            edge(write=0, bank=1, addr=k, data=4, a=k)
        # Bank/address bounds and low-six-bit map semantics.
        for k in range(256):
            edge(write=1, bank=1, addr=k, data=(1 << 63) | k, a=k)
            edge(write=1, addr=k, data=rng.getrandbits(64), a=k, b=k % 64)
        for _ in range(1024):
            edge(write=rng.randrange(2), busy=rng.randrange(2), bank=rng.randrange(2),
                 addr=rng.randrange(256), data=rng.getrandbits(64),
                 a=rng.randrange(256), b=rng.randrange(256))
        for k in range(256):
            edge(a=k, b=255-k)
        (OUT / f'{name}-vectors.txt').write_text(''.join(' '.join(map(str, row))+'\n' for row in rows))
        coverage['stores'][name] = dict(edges=len(rows), checked_pairs=checked,
                                      initialization_edges=len(rows)-checked)
    (OUT / 'coverage.json').write_text(json.dumps(coverage, indent=2)+'\n')
    return coverage


if __name__ == '__main__':
    print(json.dumps(generate(), indent=2))
