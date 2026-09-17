#!/usr/bin/env python3
"""Inspect cache-control dependencies in the exact checked source graphs."""
import argparse
import hashlib
import json
from pathlib import Path

import backend_readback as rb
import bank_select_readback as banks

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ancestors(graph, node, stops=()):
    visited, pending = set(), [node]
    while pending:
        name = pending.pop()
        if name in visited: continue
        visited.add(name)
        if name not in stops: pending.extend(graph.nodes[name].args)
    return visited


def inspect(directory):
    receipt = json.loads((directory / 'report.json').read_text())
    for name in ('composed.mlir', 'composed.sv'):
        if sha(directory / name) != receipt['artifact_sha256'][name]:
            raise RuntimeError('Changed checked artifact')
    graph = rb.read_hints(directory / 'composed.mlir')
    cuts = banks.read_cuts(directory / 'cuts.tsv', graph, receipt['variant'])
    roles = {role: name for name, role in cuts.items()}
    if roles['pcValue'] != graph.next['r_pc']:
        raise RuntimeError('Next-PC hint differs from the actual register update')
    cache = graph.nodes[graph.next['r_cached_word']]
    if cache.op != 'mux' or cache.args[1:] != (roles['successorValue'], 'r_cached_word'):
        raise RuntimeError('Unexpected cache data/hold boundary')
    results = {}
    for label, stops in (('complete', ()), ('successor_abstracted', (roles['successorValue'],))):
        reached = ancestors(graph, cache.args[0], stops)
        leaves = sorted(n for n in reached if graph.nodes[n].op in ('input', 'reg'))
        depth = {'r_loader_cursor': 0}
        for name, node in graph.nodes.items():
            if name in stops: continue
            d = [depth[k] for k in node.args if k in depth]
            if d: depth[name] = max(d) + 1
        results[label] = {'cursor': 'r_loader_cursor' in leaves, 'command': 'command' in leaves,
            'loader_data': 'data' in leaves, 'next_pc_wire': roles['pcValue'] in reached,
            'dictionary_or_index_registers': sum(n.startswith('r_bank') and ('_word' in n or '_index' in n) for n in leaves),
            'expression_depth_from_cursor': depth.get(cache.args[0]), 'leaves': leaves}
    return {'variant': receipt['variant'], 'enable_node': cache.args[0], 'dependencies': results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--control', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise RuntimeError('Preserve earlier dependency evidence')
    results = {name: inspect(path) for name, path in (('control', args.control), ('candidate', args.candidate))}
    if results['control']['variant'] != 'command-split' or results['candidate']['variant'] != 'enable-split':
        raise RuntimeError('Expected the command-split control and enable-split candidate')
    sources = [Path(__file__).resolve(), ROOT / 'scripts/backend_readback.py', ROOT / 'scripts/bank_select_readback.py']
    for directory in (args.control, args.candidate):
        sources += [directory / name for name in ('report.json', 'composed.mlir', 'composed.sv', 'cuts.tsv')]
    report = {'results': results, 'source_sha256': {str(p.absolute().relative_to(ROOT)): sha(p) for p in sources},
        'boundary': 'Source expression reachability, with the full graph and a separately identified abstract successor input. '
                    'The abstracted view is not a physical path cut or timing exception. The shared lookup can retain an indirect loader dependency.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    for label, result in results.items():
        print(label, json.dumps({k: {n:v for n,v in row.items() if n != 'leaves'} for k,row in result['dependencies'].items()}))


if __name__ == '__main__': main()
