#!/usr/bin/env python3
"""Compare loader-data and protocol-input reachability to mapped cache registers.

This is structural connectivity, not a sensitizable-path or timing proof.
Sequential elements terminate a combinational cone.
"""
import argparse
from collections import defaultdict, deque
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOP = 'pinwheel_atomic_small_dense_cached'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sequential_cells(lib):
    text = lib.read_text()
    sequential, latches = set(), set()
    for match in re.finditer(r'\bcell\s*\(\s*(\w+)\s*\)\s*\{', text):
        start, depth, n = match.end(), 1, match.end()
        while depth:
            depth += (text[n] == '{') - (text[n] == '}')
            n += 1
        body = text[start:n]
        if re.search(r'\blatch\s*\(', body):
            latches.add(match[1])
        if re.search(r'\bff\s*\(', body):
            sequential.add(match[1])
    if not sequential:
        raise RuntimeError('No sequential cells identified in the pinned library')
    return sequential, latches


def inspect(path, sequential, latches):
    module = json.loads(path.read_text())['modules'][TOP]
    bits = module['netnames']['r_cached_word']['bits']
    if len(bits) != 64:
        raise RuntimeError('Unexpected cache width')
    cache = {b for b in bits if isinstance(b, int)}
    arcs = defaultdict(list)
    targets, cache_outputs = {}, set()
    connected = {b for port in module["ports"].values() for b in port["bits"]}
    for name, cell in module['cells'].items():
        if cell['type'] in latches:
            raise RuntimeError('Mapped latch requires a separate transparency analysis')
        if not cell['type'].startswith('sg13cmos5l_'):
            raise RuntimeError(f'Unexpected mapped cell: {cell["type"]}')
        outputs = [b for port, direction in cell['port_directions'].items() if direction == 'output'
                   for b in cell['connections'][port] if isinstance(b, int)]
        inputs = [b for port, direction in cell['port_directions'].items() if direction == 'input'
                  for b in cell['connections'][port] if isinstance(b, int)]
        connected.update(inputs + outputs)
        if cell['type'] in sequential:
            touched = cache.intersection(outputs)
            if touched:
                cache_outputs.update(touched)
                # Include reset/set controls as well as D, excluding only the clock.
                for port, direction in cell['port_directions'].items():
                    if direction == 'input' and port != 'CLK':
                        for b in cell['connections'][port]:
                            if isinstance(b, int):
                                targets[f'{name}/{port}'] = b
            continue
        for b in inputs:
            arcs[b].extend(outputs)
    removed = cache - connected
    if cache_outputs != cache - removed:
        raise RuntimeError('A connected cache bit is not a sequential output')
    result = {}
    for family, port in [('loader_data', 'data'), ('protocol', 'incoming')]:
        starts = module['ports'][port]['bits']
        seen = set(starts)
        queue = deque(starts)
        while queue:
            for bit in arcs[queue.popleft()]:
                if bit not in seen:
                    seen.add(bit)
                    queue.append(bit)
        reached = [pin for pin, bit in targets.items() if bit in seen]
        result[family] = dict(reached_cache_pins=len(reached), example_pins=reached[:3])
    return dict(cache_register_bits=len(cache_outputs), eliminated_unused_bits=len(removed),
                cache_input_pins=len(targets), families=result)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--candidate', type=Path, required=True)
    args = parser.parse_args()
    directory = args.candidate.resolve()
    out = directory / 'cones.json'
    if out.exists():
        raise RuntimeError('Preserve the existing cone receipt')
    screen = json.loads((directory / 'report.json').read_text())
    if screen['variant'] != 'command-split':
        raise RuntimeError('Expected a completed command-split screen')
    reports, sources = {}, [Path(__file__).resolve(), directory / 'report.json']
    for corner, filename in [('typical', 'sg13cmos5l_stdcell_typ_1p20V_25C.lib'),
                             ('slow', 'sg13cmos5l_stdcell_slow_1p08V_125C.lib')]:
        lib = ROOT / 'build/tools/ihp-cmos5l' / filename
        sequential, latches = sequential_cells(lib)
        paths = dict(baseline=ROOT / f'build/storage/small-dense-cached/{corner}.json',
                     candidate=directory / f'{corner}.json')
        reports[corner] = {name: inspect(path, sequential, latches) for name, path in paths.items()}
        sources.extend([lib, *paths.values()])
        if not reports[corner]['baseline']['families']['loader_data']['reached_cache_pins']:
            raise RuntimeError('Baseline positive control lacks the expected loader cone')
        if reports[corner]['candidate']['families']['loader_data']['reached_cache_pins']:
            raise RuntimeError('Candidate retains a loader-data path to cache inputs')
        if not reports[corner]['candidate']['families']['protocol']['reached_cache_pins']:
            raise RuntimeError('Candidate unexpectedly lacks protocol-input dependence')
    receipt = dict(results=reports, source_sha256={str(p.relative_to(ROOT)): sha(p) for p in sources},
                   boundary='Mapped combinational connectivity, cutting every Liberty-declared flip-flop. '
                            'No loader-data connectivity to cache data/control inputs; protocol connectivity remains. '
                            'Does not prove critical-path delay, physical closure, or absence of glitches.')
    out.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(reports, indent=2))


if __name__ == '__main__':
    main()
