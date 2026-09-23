"""Distribute mapped boundary loads without changing child implementations.

The budget counts actual sink pins, including loads behind module inputs and
pass-through port aliases. It is a structural screen, not an electrical limit.
Only a two-level hierarchy of mapped children and library cells is supported.
"""
from collections import Counter, defaultdict
from copy import deepcopy
import math

BUFFER = 'sg13cmos5l_buf_1'


def boundary_loads(modules, top_name, fixed_cells=()):
    top = modules[top_name]
    fixed_cells = set(fixed_cells)
    if not fixed_cells <= set(top['cells']):
        raise ValueError('Unknown fixed boundary cell')
    parents = {}

    def find(bit):
        if type(bit) is not int:
            raise ValueError('Constant or unknown on a distribution boundary')
        parents.setdefault(bit, bit)
        if parents[bit] != bit:
            parents[bit] = find(parents[bit])
        return parents[bit]

    def join(a, b):
        parents[find(b)] = find(a)

    children = []
    for name, cell in sorted(top['cells'].items()):
        if cell['type'] == '$scopeinfo':
            continue
        module = modules[cell['type']]
        ports = module['ports']
        if set(ports) != set(cell['connections']) or set(ports) != set(cell['port_directions']):
            raise ValueError('Incomplete child interface')
        aliases = defaultdict(list)
        for port, desc in ports.items():
            if desc['direction'] not in ('input', 'output') or cell['port_directions'][port] != desc['direction']:
                raise ValueError('Unsupported child direction')
            bits = cell['connections'][port]
            if len(bits) != len(desc['bits']):
                raise ValueError('Child width mismatch')
            for index, (inner, outer) in enumerate(zip(desc['bits'], bits)):
                if outer not in ('0', '1'):
                    find(outer)
                if type(inner) is not int:
                    raise ValueError('Constant child port')
                aliases[inner].append((port, index, desc['direction'], outer))
        loads, drivers = Counter(), Counter()
        if module.get('cells'):
            for leaf in module['cells'].values():
                kind = leaf['type']
                if kind == '$scopeinfo':
                    continue
                library = modules[kind]
                if library.get('cells') or not int(library.get('attributes', {}).get('blackbox', '0'), 2):
                    raise ValueError('Expected mapped leaf cells')
                if set(leaf['connections']) != set(library['ports']) or set(leaf['port_directions']) != set(library['ports']):
                    raise ValueError('Incomplete leaf interface')
                for port, bits in leaf['connections'].items():
                    direction = library['ports'][port]['direction']
                    if direction not in ('input', 'output') or leaf['port_directions'][port] != direction or len(bits) != len(library['ports'][port]['bits']):
                        raise ValueError('Invalid leaf port')
                    if kind == 'sg13cmos5l_dfrbpq_1' and port == 'CLK':
                        continue
                    (loads if direction == 'input' else drivers).update(bits)
        elif int(module.get('attributes', {}).get('blackbox', '0'), 2):
            for desc in ports.values():
                (loads if desc['direction'] == 'input' else drivers).update(desc['bits'])
        else:
            raise ValueError('Empty or unmapped child')
        for inner, refs in aliases.items():
            constants = {r[3] for r in refs if r[3] in ('0', '1')}
            if constants:
                if len(constants) != 1 or any(r[3] not in constants for r in refs):
                    raise ValueError('Inconsistent constant boundary aliases')
                if drivers[inner]:
                    raise ValueError('Driven child output tied to a constant')
                continue
            for ref in refs[1:]:
                join(refs[0][3], ref[3])
        children.append((name, aliases, loads, drivers))

    nets = defaultdict(lambda: {'sources': [], 'fixed_loads': 0, 'endpoints': [], 'aliases': []})
    for name, port in top['ports'].items():
        if port['direction'] not in ('input', 'output'):
            raise ValueError('Unsupported top direction')
        for index, bit in enumerate(port['bits']):
            if bit in ('0', '1'):
                if port['direction'] != 'output':
                    raise ValueError('Constant top input')
                continue
            net = nets[find(bit)]
            label = f'{name}[{index}]'
            net['aliases'].append(label)
            if port['direction'] == 'input':
                net['sources'].append((label, bit))
            else:
                net['fixed_loads'] += 1
    for name, aliases, loads, drivers in children:
        for inner, refs in aliases.items():
            if refs[0][3] in ('0', '1'):
                continue
            net = nets[find(refs[0][3])]
            inputs = [(p, i) for p, i, d, _ in refs if d == 'input']
            outputs = [(p, i, b) for p, i, d, b in refs if d == 'output']
            net['aliases'].extend(f'{name}.{p}[{i}]' for p, i, _, _ in refs)
            if inputs:
                if drivers[inner]:
                    raise ValueError('Child drives an input')
                if outputs or name in fixed_cells:
                    # Keep a pass-through input on the source net. Rewiring it
                    # would also move its output aliases and downstream loads.
                    net['fixed_loads'] += loads[inner]
                elif loads[inner]:
                    net['endpoints'].append({'cell': name, 'ports': inputs, 'weight': loads[inner]})
            else:
                if drivers[inner] != 1:
                    raise ValueError('Missing or multiple boundary drivers')
                port, index, bit = outputs[0]
                net['sources'].append((f'{name}.{port}[{index}]', bit))
                net['fixed_loads'] += loads[inner]
    clock = top['ports'].get('clk', {})
    if clock.get('direction') != 'input' or len(clock.get('bits', [])) != 1:
        raise ValueError('Expected one top clock')
    clock_net = find(clock['bits'][0])
    result = []
    for key, net in nets.items():
        if len(net['sources']) != 1:
            raise ValueError('Missing or multiple distribution sources')
        if key != clock_net:
            net['source'], net['bit'] = net.pop('sources')[0]
            net['loads'] = net['fixed_loads'] + sum(e['weight'] for e in net['endpoints'])
            net['aliases'].sort()
            result.append(net)
    return sorted(result, key=lambda net: net['source'])


def distribute(data, top_name, banks, limit=10, fixed_cells=(), prefix='map_distribution_'):
    """Buffer signal loads, keeping bank groups and named fixed terminals intact.

    Binary tie-offs are excluded from the signal budget and never rewired.
    Fixed cell inputs still consume the producer's budget, as do internal loads
    and output aliases. This permits a complete-chip budget with exact SRAM
    terminals while preserving each mapped child implementation.
    """
    if type(limit) is not int or limit < 2:
        raise ValueError('Fanout budget must be an integer of at least two')
    if not prefix or not prefix.replace('_', '').isalnum() or not prefix[0].isalpha():
        raise ValueError('Invalid distribution instance prefix')
    library = data['modules'][BUFFER]
    if {p: (v['direction'], len(v['bits'])) for p, v in library['ports'].items()} != {
            'A': ('input', 1), 'X': ('output', 1)} or library.get('cells'):
        raise ValueError('Unexpected distribution buffer')
    area = float(library['attributes']['area'])
    if not math.isfinite(area) or area <= 0:
        raise ValueError('Invalid buffer area')
    nets = boundary_loads(data['modules'], top_name, fixed_cells)
    result = deepcopy(data)
    top = result['modules'][top_name]
    bit_lists = [p['bits'] for p in top['ports'].values()] + [n['bits'] for n in top['netnames'].values()]
    bit_lists += [bs for c in top['cells'].values() for bs in c['connections'].values()]
    next_bit = max(b for bs in bit_lists for b in bs if type(b) is int) + 1
    if any(n.startswith(prefix) for n in list(top['cells']) + list(top['netnames'])):
        raise ValueError('Distribution already present or reserved name collision')
    trees = []
    for net in nets:
        if net['loads'] <= limit:
            continue
        budget = limit - net['fixed_loads']
        if budget < 1 or not net['endpoints'] or any(e['weight'] > limit for e in net['endpoints']):
            raise ValueError('Cannot meet budget without changing child internals: ' + net['source'])
        added = []

        def buffer(endpoints):
            nonlocal next_bit
            name = f'{prefix}{len(trees)}_{len(added)}'
            output = next_bit
            next_bit += 1
            top['cells'][name] = {
                'hide_name': 0, 'type': BUFFER, 'parameters': {}, 'attributes': {'keep': '1'},
                'port_directions': {'A': 'input', 'X': 'output'},
                'connections': {'A': [net['bit']], 'X': [output]}}
            top['netnames'][name + '_out'] = {'hide_name': 0, 'bits': [output], 'attributes': {}}
            for endpoint in endpoints:
                for port, index in endpoint['ports']:
                    top['cells'][endpoint['cell']]['connections'][port][index] = output
            added.append({'cell': name, 'sink_pins': sum(e['weight'] for e in endpoints),
                          'downstream_buffer_levels': max((e.get('levels', 0) for e in endpoints), default=0)})
            return {'cell': name, 'ports': [('A', 0)], 'weight': 1,
                    'levels': 1 + max((e.get('levels', 0) for e in endpoints), default=0)}

        def pack(endpoints):
            buckets, bucket, weight = [], [], 0
            for endpoint in endpoints:
                if weight + endpoint['weight'] > limit:
                    buckets.append(bucket)
                    bucket, weight = [], 0
                bucket.append(endpoint)
                weight += endpoint['weight']
            if bucket:
                buckets.append(bucket)
            return buckets

        groups = defaultdict(list)
        order = lambda e: (banks.get(e['cell'], (2, 0)), e['cell'], e['ports'])
        for endpoint in sorted(net['endpoints'], key=order):
            groups[banks.get(endpoint['cell'], (2, 0))[0]].append(endpoint)
        frontiers = [[buffer(bucket) for bucket in pack(group)] for group in groups.values()]
        while sum(map(len, frontiers)) > budget:
            if all(len(group) == 1 for group in frontiers):
                frontiers = [[e for group in frontiers for e in group]]
            frontiers = [[buffer(bucket) for bucket in pack(group)] if len(group) > 1 else group
                         for group in frontiers]
        roots = [e for group in frontiers for e in group]
        trees.append({'source': net['source'], 'aliases': net['aliases'],
                      'original_sink_pins': net['loads'], 'fixed_sink_pins': net['fixed_loads'],
                      'root_sink_pins': net['fixed_loads'] + len(roots),
                      'maximum_added_levels': max(e['levels'] for e in roots), 'buffers': added})
    count = sum(len(tree['buffers']) for tree in trees)
    return result, {'fanout_limit': limit, 'buffer_cell': BUFFER, 'buffer_area_um2': area,
                    'added_buffers': count, 'added_area_um2': round(count * area, 4), 'trees': trees,
                    'scope': 'Signal sink-pin budget; bank-local leaf groups. No placement, electrical, wire or timing model.'}
