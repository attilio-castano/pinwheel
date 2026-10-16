"""Exact copied-reference LVS faults. Never edit the routed design or original NL."""
from __future__ import annotations
import re


def stripped(text):
    return re.sub(r'/\*.*?\*/|//[^\n]*',
        lambda m: ''.join('\n' if c == '\n' else ' ' for c in m[0]), text, flags=re.S)


def close_paren(text, opening):
    assert text[opening] == '('
    depth = 1
    for n in range(opening+1, len(text)):
        if text[n] == '(':
            depth += 1
        elif text[n] == ')':
            depth -= 1
            if depth == 0:
                return n
    raise ValueError('Unclosed flattened-netlist expression')


def standard_connections(text):
    clean = stripped(text)
    cells, pins = {}, {}
    pattern = r'(?m)^\s*(sg13cmos5l_[A-Za-z0-9_]+)\s+(\\\S+|[A-Za-z_$][\w$]*)\s*\('
    for match in re.finditer(pattern, clean):
        master, instance = match[1], match[2].removeprefix('\\')
        assert instance not in cells, 'Repeated standard-cell instance'
        cells[instance] = master
        opening = match.end()-1
        end = close_paren(clean, opening)
        cursor = opening+1
        while cursor < end:
            while cursor < end and (clean[cursor].isspace() or clean[cursor] == ','):
                cursor += 1
            if cursor == end:
                break
            pin = re.match(r'\.\s*(\\\S+|[A-Za-z_$][\w$]*)\s*\(', clean[cursor:end])
            if pin is None:
                raise ValueError('Unsupported positional/malformed standard-cell connection')
            name = pin[1].removeprefix('\\')
            start = cursor + pin.end()-1
            finish = close_paren(clean, start)
            assert finish < end
            key = (instance, name)
            assert key not in pins, 'Duplicate standard-cell terminal'
            pins[key] = {'expression': clean[start+1:finish].strip(), 'span': [start+1, finish]}
            cursor = finish+1
    if not cells:
        raise ValueError('No supported standard-cell instances')
    return clean, cells, pins


def apply(text, patches):
    result = text
    previous = len(text)+1
    for start, end, replacement in sorted(patches, reverse=True):
        assert 0 <= start <= end <= len(text) and end <= previous, 'Overlapping mutation patches'
        result = result[:start] + replacement + result[end:]
        previous = start
    return result


def reference_faults(text, inventory, *, terminal=('_30759_', 'D'), bridge_nets=('net8042', 'net8046')):
    clean, cells, pins = standard_connections(text)
    expected_cells = {name: item['master'] for name, item in inventory['instances'].items()
                      if item['master'].startswith('sg13cmos5l_')}
    assert cells == expected_cells, 'Reference standard-cell identities differ from native inventory'
    instance, pin = terminal
    assert instance in cells and cells[instance].startswith('sg13cmos5l_dfrbpq_')
    native_terms = inventory['instances'][instance]['terminals']
    rows = [row for row in native_terms if row[0] == pin]
    assert len(rows) == 1 and rows[0][2] == 'INPUT'
    original_net = rows[0][1]
    assert original_net and inventory['nets'][original_net]['sig_type'] == 'SIGNAL'
    assert len(inventory['nets'][original_net]['terminals']) + len(inventory['nets'][original_net]['ports']) >= 2
    assert pins[terminal]['expression'] == original_net
    a, b = bridge_nets
    assert a != b
    for net in (a, b):
        assert re.fullmatch(r'[A-Za-z_$][\w$]*', net)
        native = inventory['nets'][net]
        assert native['sig_type'] == 'SIGNAL' and not native['ports']
        assert len(native['terminals']) >= 2 and any(row[2] == 'INPUT' for row in native['terminals'])
        assert all(row[0] in cells for row in native['terminals']), 'Bridge requires only known standard-cell contacts'
        contacts = {(row[0], row[1]) for row in native['terminals']}
        observed = {key for key, value in pins.items() if value['expression'] == net}
        assert observed == contacts, 'Reference bridge-net contact coverage differs from native inventory'
        for assignment in re.findall(r'\bassign\b[^;]*;', clean):
            assert not re.search(r'(?<![\w$])' + re.escape(net) + r'(?![\w$])', assignment), 'Bridge-net aliases are unsupported'
    orphan = 'PW_LVS_NEG_OPEN_30759_D'
    assert orphan not in clean
    modules = list(re.finditer(r'\bmodule\s+(\S+)\s*\(', clean))
    assert len(modules) == 1 and modules[0][1] == 'tt_um_pinwheel_buffered'
    header_end = close_paren(clean, modules[0].end()-1)+1
    while clean[header_end].isspace():
        header_end += 1
    assert clean[header_end] == ';'
    opened = apply(text, [(header_end+1, header_end+1, '\n  wire ' + orphan + ';\n'),
                          (*pins[terminal]['span'], orphan)])
    bridge_contacts = {(row[0], row[1]) for row in inventory['nets'][b]['terminals']}
    bridged = apply(text, [(*pins[key]['span'], a) for key in bridge_contacts])
    original_values = {key: value['expression'] for key, value in pins.items()}
    descriptions = {}
    for name, mutant, changes in [('removed-terminal', opened, {terminal}),
                                  ('bridged-nets', bridged, bridge_contacts)]:
        _, mutant_cells, mutant_pins = standard_connections(mutant)
        assert mutant_cells == cells and set(mutant_pins) == set(pins)
        changed = {key for key, value in mutant_pins.items() if value['expression'] != original_values[key]}
        assert changed == changes, 'Mutation affected an unexpected terminal'
        descriptions[name] = {'changed_terminal_count': len(changed),
            'changed_terminals': [{'instance': key[0], 'pin': key[1], 'before': original_values[key],
                                   'after': mutant_pins[key]['expression']} for key in sorted(changed)],
            'all_other_standard_cell_connections_exact': True, 'all_standard_cell_instances_and_masters_exact': True,
            'mutates_original_layout_or_reference': False}
    descriptions['removed-terminal'].update(removed_consumed_contact=list(terminal), old_net=original_net,
        fresh_isolated_reference_wire=orphan, meaning='Detach exactly one FF D contact from its consumed net; cell and pin remain, connected only to a fresh isolated reference node.')
    descriptions['bridged-nets'].update(distinct_consumed_nets=[a, b],
        meaning='Merge every contact of the second consumed net into the first in a copied reference; retain original declarations and all other terminal connections.')
    return {'positive': text, 'removed-terminal': opened, 'bridged-nets': bridged}, descriptions


def native_verdict(report):
    finals = re.findall(r'^Final result:\s*(.*?)\s*$', report, re.M)
    if len(finals) != 1:
        raise ValueError('Missing/ambiguous native Netgen final comparison verdict')
    verdict = finals[0]
    if verdict == 'Circuits match uniquely.':
        return {'completed': True, 'match_uniquely': True, 'native_final_result': verdict}
    known_mismatch = {'Netlists do not match.', 'Netlists failed to match.', 'Circuits match with errors.'}
    if verdict not in known_mismatch:
        raise ValueError('Unqualified Netgen verdict: ' + verdict)
    return {'completed': True, 'match_uniquely': False, 'native_final_result': verdict}
