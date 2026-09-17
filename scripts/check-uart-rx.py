#!/usr/bin/env python3
"""Portable independent waveform/E64 check; test/UARTRx.lean emits the input images."""
import json
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/uart-rx'


def main():
    oracle = runpy.run_path(str(ROOT / 'scripts/reactive-core-vectors.py'))
    images = {}
    for line in (OUT / 'images.txt').read_text().splitlines():
        name, *numbers = line.split()
        last, levels, enabled, *words = map(int, numbers)
        assert len(words) == 256
        images[name] = (words, last, (levels, enabled))
    frames = edges = 0
    for indexed in [False, True]:
        machine = oracle['Machine'](indexed)
        for name, period, pin in [('uart-rx', 16, 0), ('uart-rx-split', 257, 1),
                                  ('uart-rx-long', 5208, 0), ('uart-rx-max', 6656, 1)]:
            machine.load(name, *images[name])
            for byte in [0, 0x53, 0xa6, 255]:
                for stop in [0, 1]:
                    oracle['uart_rx']['receive'](machine, period=period, pin=pin, byte=byte, stop=stop)
                    frames += 1
                    edges += len(machine.rows)
                    machine.rows.clear()
    report = dict(frames=frames, edges=edges, backends=['direct', 'indexed'],
                  boundary='Independent sender, sampling oracle and E64 interpreter; no Lean expected states or RTL.')
    (OUT / 'independent-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Independent UART RX: {frames} frames, {edges} edges, both E64 stores; good and bad stops.')


if __name__ == '__main__':
    main()
