#!/usr/bin/env python3
"""Independent absolute-deadline oracle and protocol checks for Lean-emitted images."""
import json
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/core'


def generate():
    images = []
    for line in (OUT / 'images.txt').read_text().splitlines():
        name, *values = line.split()
        if name == 'random':
            continue
        duration, byte, idle, *words = map(int, values)
        assert len(words) == 32 and all(0 <= w < 65536 for w in words)
        images.append(dict(name=name, duration=duration, byte=byte, idle=idle, words=words))
    # Additional raw memory images exercise every address and all stored bits, including malformed entries.
    rng = random.Random(0x50494E)
    for k in range(32):
        words = [rng.randrange(65536) for _ in range(32)]
        # A valid prefix reaches address k, whose arbitrary word is then decoded.
        words[:k] = [((j % 8) << 12) | 8 | (j % 8) for j in range(k)]
        images.append(dict(name='random', duration=0, byte=0, idle=k % 8, words=words))
    (OUT / 'images.txt').write_text(''.join(
        ' '.join(map(str, [p['name'], p['duration'], p['byte'], p['idle'], *p['words']])) + '\n'
        for p in images))
    (OUT / 'images.hex').write_text(''.join(f"{sum(w << (16*k) for k, w in enumerate(p['words'])) | (p['idle'] << 512):0129x}\n" for p in images))
    names = {p['name']: k for k, p in enumerate(images)}
    rows = []
    edge = -1
    valid = status = pc = levels = rx = idle = 0
    deadline = None
    program = 0
    known = False

    def stop(reason, clear=False):
        nonlocal status, pc, deadline, levels, rx
        status, pc, deadline, levels = reason, 0, None, idle
        if clear:
            rx = 0

    def enter(address, sample):
        nonlocal status, pc, deadline, levels, rx
        if address == 32:
            stop(3)
            return
        w = images[program]['words'][address]
        if w == 0x8000:
            stop(2)
        elif w >= 0x8000 or (w % 16 in range(1, 8)):
            stop(3)
        else:
            status, pc, levels = 1, address, w // 4096
            deadline = edge + ((w // 16) % 256) + 1
            if w & 8:
                mask = 1 << (7 - w % 8)
                rx = (rx & ~mask) | (mask if sample else 0)

    def drive(*, init=0, reset=0, start=0, commit=0, sample=0, image=0):
        nonlocal edge, valid, program, known, idle
        edge += 1
        if init:
            idle, valid = 0, 0
            stop(0, True)
        elif reset:
            stop(0, True)
        elif status == 1:
            if valid and edge == deadline:
                enter(pc + 1, sample)
        elif commit:
            program, known, valid, idle = image, True, 1, images[image]['idle']
            stop(0, True)
        elif valid and start:
            stop(0, True)
            enter(0, sample)
        remaining = deadline - edge - 1 if status == 1 else 0
        assert 0 <= remaining <= 255
        flags = init | reset << 1 | start << 2 | commit << 3 | int(sample) << 4
        rows.append([flags, image, valid, status, pc, remaining, int(status == 1), levels, rx,
                     int(known), program, idle, int(status == 1), int(status == 2)])

    # First milestone: start at t=0, second action/capture at t=1, halt at t=2.
    drive(init=1, reset=1, start=1, commit=1, sample=1)
    drive(start=1, sample=1)
    drive(reset=1, start=1, sample=1)
    drive(commit=1, start=1, sample=1, image=names['two'])
    assert status == 0 and rx == 0
    drive(start=1, sample=0)
    assert (status, levels, rx) == (1, 1, 0)
    drive(start=1, commit=1, image=names['halt0'], sample=1)
    assert (status, levels, rx) == (1, 6, 1)
    drive(start=1, commit=1, image=names['halt0'], sample=0)
    assert (status, levels, rx) == (2, 7, 1)
    drive(start=1, sample=1)  # Restart clears old receive data, then captures slot zero.
    assert (status, rx) == (1, 128)
    drive(reset=1, commit=1, start=1, sample=1)

    transfers = 0
    protocol_edges = 0
    for index, p in enumerate(images):
        drive(reset=1)
        drive(commit=1, start=1, image=index)
        if p['name'] in ('uart', 'spi'):
            duration, byte = p['duration'], p['byte']
            spi = p['name'] == 'spi'
            length = (17 if spi else 10) * duration
            reply = 255 ^ byte
            expected_rx = 0
            for t in range(length + 2):
                sample = (t % 2 == 0)  # Noise away from SPI sample edges.
                for bit in range(8):
                    if spi and t == (2*bit + 1)*duration:
                        sample = bool(reply & (1 << (7-bit)))
                        expected_rx |= int(sample) << (7-bit)
                drive(start=int(t == 0 or t < length), commit=int(0 < t <= length),
                      sample=sample, image=(index + 1) % len(images))
                if spi:
                    half = t // duration
                    expected = 4 if half >= 17 else ((half % 2) << 1 | ((byte >> (7-half//2)) & 1)) if half < 16 else byte & 1
                else:
                    symbol = t // duration
                    expected = 0 if symbol == 0 else ((byte >> (symbol - 1)) & 1) if symbol < 9 else 1
                    expected |= 4  # Shared engine keeps SPI chip select inactive during UART.
                assert levels == expected, (p, t, levels, expected)
                assert status == (1 if t < length else 2)
                assert rx == (expected_rx if spi else 0), (p, t, rx, expected_rx)
                protocol_edges += 1
            transfers += 1
        else:
            drive(start=1, sample=1)
            if p['name'] == 'mixed':
                assert (levels, rx) == (1, 128)
            for t in range(1, 8200):
                drive(sample=int(t % 3 != 2), start=int(status == 1), commit=int(status == 1), image=names['halt0'])
                if p['name'] == 'mixed':
                    expected = 6 if t < 5 else 3 if t < 261 else 0 if t < 262 else 7
                    assert (levels, rx, status) == (expected, 129 if t < 5 else 1, 1 if t < 262 else 2)
                if status != 1:
                    break
            assert status != 1
            drive(sample=0)  # Stopped retention.

    # Abort and restart on every phase of a four-cycle SPI transaction, including completion.
    spi_index = next(k for k,p in enumerate(images) if p['name']=='spi' and p['duration']==4 and p['byte']==83)
    for phase in range(69):
        drive(reset=1)
        drive(commit=1, image=spi_index)
        drive(start=1, sample=1)
        for _ in range(phase):
            drive(sample=1)
        drive(reset=1, start=1, commit=1, sample=1, image=names['halt0'])
        assert status == 0 and rx == 0 and program == spi_index
        drive(start=1)
        drive(init=1, reset=1, commit=1, start=1, sample=1)
        assert not valid and status == 0 and levels == 0
        drive(start=1, sample=1)
        assert not valid and status == 0
    (OUT / 'stimuli.txt').write_text(''.join(' '.join(map(str, row))+'\n' for row in rows))
    coverage = dict(images=len(images), edges=len(rows), protocol_transfers=transfers,
                    protocol_edges=protocol_edges, decoder_words=65536, reset_phases=69,
                    protocol_matrix='All 256 bytes at durations 1 and 4; bytes 00,53,a6,ff at duration 256, UART and SPI.')
    (OUT / 'coverage.json').write_text(json.dumps(coverage, indent=2)+'\n')
    return coverage


if __name__ == '__main__':
    print(json.dumps(generate(), indent=2))
