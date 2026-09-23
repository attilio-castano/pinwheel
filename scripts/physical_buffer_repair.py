"""Check a physical buffer-only edit by contracting known noninverting buffers.

This checks signal connectivity in independently read-back netlists. It does
not establish timing, power connectivity, or that inserted cells can be routed.
"""
from collections import Counter
from copy import deepcopy

from mapped_physical import connection_signature

BUFFERS = frozenset('sg13cmos5l_buf_' + size for size in ('1', '2', '4', '8'))


def _bufferless(module):
    aliases, drivers, unused_inputs = {}, {}, []

    def add_driver(bit, identity):
        if type(bit) is not int or bit in drivers:
            raise ValueError('Constant or multiply driven physical net')
        drivers[bit] = identity

    for name, port in module['ports'].items():
        if port['direction'] == 'input':
            for index, bit in enumerate(port['bits']):
                add_driver(bit, ('port', name, index))
    for name, cell in module['cells'].items():
        if set(cell['connections']) != set(cell['port_directions']):
            raise ValueError('Unclassified physical terminal')
        for pin, bits in cell['connections'].items():
            if cell['port_directions'][pin] == 'output':
                for index, bit in enumerate(bits):
                    add_driver(bit, ('cell', name, pin, index))
        if cell['type'] in BUFFERS:
            directions = cell['port_directions']
            if (cell.get('parameters') or
                    directions not in ({'A': 'input'}, {'A': 'input', 'X': 'output'}) or
                    len(cell['connections']['A']) != 1 or
                    ('X' in directions and len(cell['connections']['X']) != 1)):
                raise ValueError('Malformed pinned buffer')
            if 'X' in directions:
                aliases[cell['connections']['X'][0]] = cell['connections']['A'][0]
            else:
                # CTS balancing loads can omit their unconnected output from
                # Verilog. Validate their input without inventing a driven net.
                unused_inputs.append(cell['connections']['A'][0])

    memo = {}

    def root(bit, visiting=None):
        if bit in ('0', '1'):
            return bit
        if type(bit) is not int or bit not in drivers:
            raise ValueError('Unknown or undriven physical net')
        if bit in memo:
            return memo[bit]
        visiting = set() if visiting is None else visiting
        if bit in visiting:
            raise ValueError('Buffer cycle')
        visiting.add(bit)
        result = root(aliases[bit], visiting) if bit in aliases else bit
        visiting.remove(bit)
        memo[bit] = result
        return result

    # Check every buffer, including one with an unused output. An unused cycle
    # or floating input must not disappear silently during contraction.
    for bit in [*aliases, *unused_inputs]:
        root(bit)
    reduced = deepcopy(module)
    reduced['cells'] = {n: c for n, c in reduced['cells'].items() if c['type'] not in BUFFERS}
    for port in reduced['ports'].values():
        port['bits'] = [root(bit) for bit in port['bits']]
    for cell in reduced['cells'].values():
        for pin, bits in cell['connections'].items():
            cell['connections'][pin] = [root(bit) for bit in bits]
    return connection_signature(reduced)


def compare_buffer_repair(reference, repaired, *, allow_resizing=False, allow_rewiring=False):
    """Retain every original cell; optionally resize only known noninverting buffers."""
    if reference['ports'] != repaired['ports']:
        # Bit numbering is serialization-local; connection_signature compares
        # package order and directions after resolving buffer aliases below.
        def shape(module):
            return {n: {k: v for k, v in p.items() if k != 'bits'} | {'width': len(p['bits'])}
                    for n, p in module['ports'].items()}
        if shape(reference) != shape(repaired):
            raise ValueError('Changed package interface')
    original, current = reference['cells'], repaired['cells']
    if original.keys() - current.keys():
        raise ValueError('Removed original cells')
    resized = {}
    for name, cell in original.items():
        after = current[name]
        resize = allow_resizing and cell['type'] in BUFFERS and after['type'] in BUFFERS
        if (cell['type'] != after['type'] and not resize or cell.get('parameters', {}) != after.get('parameters', {}) or
                cell['port_directions'] != after['port_directions'] or
                {p: len(b) for p, b in cell['connections'].items()} !=
                {p: len(b) for p, b in after['connections'].items()}):
            raise ValueError('Changed original cell: ' + name)
        if cell['type'] != after['type']:
            resized[name] = dict(before=cell['type'], after=after['type'])
    added = {n: current[n] for n in current.keys() - original.keys()}
    rewired = allow_rewiring and connection_signature(reference) != connection_signature(repaired)
    if not (added or resized or rewired) or any(c['type'] not in BUFFERS for c in added.values()):
        raise ValueError('Require an actual edit containing only pinned buffer changes')
    if _bufferless(reference) != _bufferless(repaired):
        raise ValueError('Changed connectivity after buffer contraction')
    result = dict(original_cells=len(original), added_buffers=dict(sorted(Counter(
        c['type'] for c in added.values()).items())), added_instances=sorted(added),
        buffer_contracted_connectivity=True)
    if allow_resizing:
        result['resized_buffers'] = resized
    return result
