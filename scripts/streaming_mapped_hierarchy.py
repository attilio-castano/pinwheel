"""Untrusted hierarchy producer for locally certifiable mapped word operators.

Every source combinational cell retains an explicit word interface. Arithmetic
is a real ripple of separately mapped full-adder instances. The producer is not
an equivalence authority; later certificates check ports, leaves and linkage.
"""
from copy import deepcopy
import json

from streaming_mapped_liberty import require

FA = 'pinwheel_mapped_fa'
WORD_PREFIX = 'pinwheel_mapped_word_'
ARITHMETIC = frozenset(('$add', '$sub', '$lt', '$le', '$gt', '$ge'))
SUPPORTED = ARITHMETIC | frozenset(('$and', '$or', '$xor', '$xnor', '$not', '$mux',
    '$eq', '$ne', '$logic_not', '$reduce_and', '$reduce_or', '$reduce_xor', '$reduce_xnor'))


def parameter(value):
    require(type(value) is str and value and set(value) <= {'0', '1'}, 'Unsupported word parameter')
    return int(value, 2)


def binary(value): return format(value, '032b')


def gate(kind, inputs, output):
    require(kind in ('$xor', '$and', '$or', '$not'), 'Unsupported internal ripple gate')
    con = {**{name: [value] for name, value in inputs.items()}, 'Y': [output]}
    params = {'A_SIGNED': binary(0), 'A_WIDTH': binary(1), 'Y_WIDTH': binary(1)}
    if 'B' in inputs: params.update(B_SIGNED=binary(0), B_WIDTH=binary(1))
    return dict(type=kind, parameters=params, attributes={},
        port_directions={name: 'output' if name == 'Y' else 'input' for name in con}, connections=con)


def full_adder():
    ports = {name: dict(direction='output' if name in ('S', 'CO') else 'input', bits=[n])
        for n, name in enumerate(('A', 'B', 'CI', 'S', 'CO'), 2)}
    a, b, ci, s, co = [ports[name]['bits'][0] for name in ('A', 'B', 'CI', 'S', 'CO')]
    return dict(attributes={'keep_hierarchy': binary(1)}, ports=ports,
        cells={'xor_ab': gate('$xor', {'A': a, 'B': b}, 7),
            'xor_sum': gate('$xor', {'A': 7, 'B': ci}, s),
            'and_ab': gate('$and', {'A': a, 'B': b}, 8),
            'and_ci': gate('$and', {'A': 7, 'B': ci}, 9),
            'or_carry': gate('$or', {'A': 8, 'B': 9}, co)},
        netnames={name: dict(hide_name=0,bits=value['bits'],attributes={}) for name, value in ports.items()})


def make_word(cell):
    kind, params = cell['type'], cell['parameters']
    require(kind in SUPPORTED, 'Unsupported source word cell: ' + kind)
    require(all(parameter(value) == 0 for name, value in params.items() if name.endswith('_SIGNED')),
        'Signed source word cell needs a separate proof')
    ports, at = {}, 2
    for name, values in sorted(cell['connections'].items()):
        require(name in cell['port_directions'] and len(values) > 0, 'Missing word interface')
        ports[name] = dict(direction=cell['port_directions'][name], bits=list(range(at, at + len(values))))
        at += len(values)
    inputs = {'A'} if kind in ('$not', '$logic_not', '$reduce_and', '$reduce_or', '$reduce_xor', '$reduce_xnor') else ({'A', 'B', 'S'} if kind == '$mux' else {'A', 'B'})
    require(set(ports) == inputs | {'Y'} and
        all(ports[name]['direction'] == ('output' if name == 'Y' else 'input') for name in ports),
        'Unexpected source word directions')
    yw = len(ports['Y']['bits'])
    expected = {'WIDTH': yw} if kind == '$mux' else dict(A_SIGNED=0, A_WIDTH=len(ports['A']['bits']), Y_WIDTH=yw,
        **(dict(B_SIGNED=0, B_WIDTH=len(ports['B']['bits'])) if 'B' in inputs else {}))
    require({name: parameter(value) for name, value in params.items()} == expected,
        'Word parameters do not exactly match interface widths')
    if kind in ARITHMETIC - {'$add', '$sub'} or kind in ('$eq', '$ne'):
        require(yw == 1 and len(ports['A']['bits']) == len(ports['B']['bits']), 'Unsupported compare width')
    elif kind in ('$logic_not', '$reduce_and', '$reduce_or', '$reduce_xor', '$reduce_xnor'):
        require(yw == 1, 'Unsupported reduction width')
    else:
        require(all(len(ports[name]['bits']) == yw for name in inputs - {'S'}), 'Implicit extension needs a separate bridge')
    if kind == '$mux': require(len(ports['S']['bits']) == 1, 'Unsupported mux select width')
    module = dict(attributes={'keep_hierarchy': binary(1)}, ports=ports, cells={},
        netnames={name: dict(hide_name=0, bits=value['bits'], attributes={}) for name, value in ports.items()})
    if kind not in ARITHMETIC:
        module['cells']['operator'] = dict(type=kind, parameters=deepcopy(params), attributes={},
            port_directions=deepcopy(cell['port_directions']),
            connections={name: value['bits'] for name, value in ports.items()})
        return module
    require(set(ports) == {'A', 'B', 'Y'} and all(ports[name]['direction'] == 'input' for name in ('A', 'B')) and
        ports['Y']['direction'] == 'output', 'Unexpected arithmetic interface')
    aw, bw, yw = [len(ports[name]['bits']) for name in ('A', 'B', 'Y')]
    width = yw if kind in ('$add', '$sub') else max(aw, bw)
    require(width > 0 and (kind in ('$add', '$sub') or yw == 1), 'Unsupported arithmetic result width')
    def extended(name): return (ports[name]['bits'] + ['0'] * width)[:width]
    x, y = extended('A'), extended('B')
    if kind in ('$gt', '$le'): x, y = y, x
    subtract = kind != '$add'
    if subtract:
        inverted = list(range(at, at + width)); at += width
        for n, (old, new) in enumerate(zip(y, inverted)):
            module['cells']['invert_b_' + str(n)] = gate('$not', {'A': old}, new)
        y = inverted
    carries = ['1' if subtract else '0'] + list(range(at, at + width)); at += width
    sums = ports['Y']['bits'] if kind in ('$add', '$sub') else list(range(at, at + width))
    if kind not in ('$add', '$sub'): at += width
    for n in range(width):
        module['cells']['bit_' + str(n)] = dict(type=FA, parameters={}, attributes={'keep_hierarchy': binary(1)},
            port_directions=dict(A='input', B='input', CI='input', S='output', CO='output'),
            connections=dict(A=[x[n]], B=[y[n]], CI=[carries[n]], S=[sums[n]], CO=[carries[n + 1]]))
    if kind in ('$lt', '$gt'):
        module['cells']['borrow_result'] = gate('$not', {'A': carries[-1]}, ports['Y']['bits'][0])
    elif kind in ('$ge', '$le'):
        # JSON aliases encode a direct wire, with no fabricated buffer semantics.
        old = ports['Y']['bits'][0]
        module['ports']['Y']['bits'][0] = carries[-1]
        module['netnames']['Y']['bits'][0] = carries[-1]
        require(old not in carries, 'Internal result allocation collision')
    module['netnames'].update(carry=dict(hide_name=0,bits=carries,attributes={}),
        operand_a=dict(hide_name=0,bits=x,attributes={}), operand_b=dict(hide_name=0,bits=y,attributes={}),
        sum_bits=dict(hide_name=0,bits=sums,attributes={}))
    return module


def hierarchical_source(data, top, *, external_modules=()):
    require(type(data) is dict and set(data.get('modules', {})) == {top}, 'One exact source top is required')
    require(type(external_modules) in (tuple, list, set, frozenset) and all(type(name) is str and name for name in external_modules),
        'Expected explicit external module names')
    external_modules = frozenset(external_modules)
    require(FA not in external_modules and not (external_modules & SUPPORTED), 'External name collides with a word primitive')
    result = deepcopy(data)
    require(FA not in result['modules'], 'Full-adder name collision')
    result['modules'][FA] = full_adder()
    main = result['modules'][top]
    require(not main.get('processes') and not main.get('memories'), 'Unlowered source behavior')
    signatures, descriptions = {}, {}
    for name, cell in sorted(main['cells'].items()):
        if cell['type'] in external_modules:
            require(cell.get('parameters') == {} and set(cell['port_directions']) == set(cell['connections']) and
                all(direction in ('input', 'output') for direction in cell['port_directions'].values()) and
                all(type(values) is list and values for values in cell['connections'].values()),
                'Parameterized or malformed external boundary')
            cell.setdefault('attributes', {})['keep_hierarchy'] = binary(1)
            continue
        if cell['type'] == '$dff':
            cell.setdefault('attributes', {})['keep'] = binary(1)
            continue
        require(cell['type'] in SUPPORTED, 'Unsupported top word cell: ' + cell['type'])
        key = json.dumps([cell['type'], cell['parameters'], cell['port_directions'],
            {pin: len(values) for pin, values in cell['connections'].items()}], sort_keys=True)
        if key not in signatures:
            module_name = WORD_PREFIX + str(len(signatures))
            require(module_name not in result['modules'], 'Word module name collision')
            signatures[key] = module_name
            result['modules'][module_name] = make_word(cell)
            descriptions[module_name] = dict(kind=cell['type'], parameters=deepcopy(cell['parameters']),
                ports={pin: len(values) for pin, values in cell['connections'].items()})
        cell['type'] = signatures[key]
        cell['parameters'] = {}
        cell.setdefault('attributes', {})['keep_hierarchy'] = binary(1)
    return result, descriptions
