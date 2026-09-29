"""Opt-in balancing of mapped positive-buffer trees with placement guidance.

Only pre-CTS flat mappings are supported. Clock buffering, sequential changes,
gate substitution and inferred timing exceptions are outside this operation.
The old mapping is never mutated. Physical loads still need fresh measurement.
"""
from collections import defaultdict
from copy import deepcopy

from map_distribution import distribute, boundary_loads
from physical_buffer_repair import BUFFERS, _bufferless


def inventory(module):
    """Census each maximal positive-buffer forest by its actual source pin."""
    _bufferless(module)  # Reject floating inputs, shorts and buffer cycles first.
    buffers = {n: c for n, c in module['cells'].items() if c['type'] in BUFFERS}
    loads, drivers = defaultdict(list), {}
    for n, p in module['ports'].items():
        for i, b in enumerate(p['bits']):
            if type(b) is int:
                if p['direction'] == 'input':
                    drivers[b] = ('port', n, i)
                else:
                    loads[b].append(('port', n, i))
    for n, c in module['cells'].items():
        for p, bs in c['connections'].items():
            for i, b in enumerate(bs):
                if type(b) is int:
                    if c['port_directions'][p] == 'input':
                        loads[b].append(('cell', n, p, i))
                    else:
                        drivers[b] = ('cell', n, p, i)

    def walk(bit, level=0):
        tree, sinks = [], []
        for endpoint in loads[bit]:
            if endpoint[0] == 'cell' and endpoint[1] in buffers:
                name = endpoint[1]
                cell = buffers[name]
                if set(cell['connections']) != {'A', 'X'}:
                    raise ValueError('Require a fully connected mapped buffer')
                tree.append((name, level+1))
                child, leaf = walk(cell['connections']['X'][0], level+1)
                tree += child
                sinks += leaf
            else:
                sinks.append((endpoint, level))
        return tree, sinks

    rows = []
    for bit, source in drivers.items():
        if source[0] == 'cell' and source[1] in buffers:
            continue
        tree, sinks = walk(bit)
        if tree:
            if not sinks:
                raise ValueError('Unconsumed mapped buffer tree')
            rows.append(dict(source=list(source), buffers=len(tree), sink_pins=len(sinks),
                maximum_levels=max(v for _, v in tree),
                mean_sink_levels=sum(v for _, v in sinks)/len(sinks)))
    if sum(r['buffers'] for r in rows) != len(buffers):
        raise ValueError('Buffer forest does not cover each cell exactly once')
    return sorted(rows, key=lambda r: tuple(map(str, r['source'])))


def contract(module):
    """Remove only known positive buffers, retaining every other cell and alias."""
    _bufferless(module)
    if module['ports'].get('clk', {}).get('direction') != 'input' or len(module['ports']['clk']['bits']) != 1:
        raise ValueError('Expected one pre-CTS package clock')
    clock = module['ports']['clk']['bits'][0]
    aliases = {}
    removed = []
    for name, cell in module['cells'].items():
        if cell['type'] in BUFFERS:
            if set(cell['connections']) != {'A', 'X'}:
                raise ValueError('Require a fully connected mapped buffer')
            aliases[cell['connections']['X'][0]] = cell['connections']['A'][0]
            removed.append(name)

    def root(bit):
        while bit in aliases:
            bit = aliases[bit]
        return bit

    if any(root(b) == clock for b in aliases):
        raise ValueError('Clock trees are outside mapped signal balancing')
    result = deepcopy(module)
    result['cells'] = {n: c for n, c in result['cells'].items() if n not in removed}
    for p in result['ports'].values():
        p['bits'] = list(map(root, p['bits']))
    for c in result['cells'].values():
        c['connections'] = {p: list(map(root, bs)) for p, bs in c['connections'].items()}
    # Preserve typed state/interface aliases, including unused reserved x bits.
    for net in result['netnames'].values():
        net['bits'] = list(map(root, net['bits']))
    if _bufferless(module) != _bufferless(result):
        raise ValueError('Buffer contraction changed a logical connection')
    return result, sorted(removed)


def morton(x, y):
    """Deterministic spatial order in integer database coordinates."""
    if type(x) is not int or type(y) is not int or min(x, y) < 0:
        raise ValueError('Require nonnegative integer guidance coordinates')
    return sum(((x >> k) & 1) << (2*k) | ((y >> k) & 1) << (2*k+1)
               for k in range(max(x.bit_length(), y.bit_length())))


def rebalance(data, top, context, *, fixed_cells=(), limit=8):
    original = data['modules'][top]
    before = inventory(original)
    stripped, removed = contract(original)
    guidance = {}
    for name, cell in stripped['cells'].items():
        placed = context['instances'].get(name)
        if not placed or placed['cell'] != cell['type']:
            raise ValueError('Missing or mismatched placement guidance: ' + name)
        box = placed['bbox_dbu']
        if (len(box) != 4 or any(type(v) is not int for v in box) or
                not (0 <= box[0] < box[2] and 0 <= box[1] < box[3])):
            raise ValueError('Invalid placement guidance box')
        # One group permits shallow global trees; spatial order clusters their
        # leaves. Guidance is not a placement constraint or electrical model.
        guidance[name] = (0, morton((box[0]+box[2])//2, (box[1]+box[3])//2))
    candidate = deepcopy(data)
    candidate['modules'][top] = stripped
    candidate, distribution = distribute(candidate, top, guidance, limit=limit,
        fixed_cells=fixed_cells, prefix='paired_balanced_')
    actual = candidate['modules'][top]
    if _bufferless(original) != _bufferless(actual):
        raise ValueError('Balanced trees changed a logical connection')
    if any(n['loads'] > limit for n in boundary_loads(candidate['modules'], top, fixed_cells)):
        raise ValueError('Balanced tree exceeds sink-pin budget')
    after = inventory(actual)
    return candidate, dict(removed_buffers=removed, original_forests=before,
        balanced_forests=after, distribution=distribution,
        guidance_database_sha256=context['database_sha256'],
        positive_buffer_contracted_identity=True,
        scope='Same nonbuffer logic and buffer master; spatially ordered shallow trees. No physical timing or routing claim.')
