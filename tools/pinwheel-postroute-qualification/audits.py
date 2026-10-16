"""Host-readable source/SPEF audits; no CAD imports or execution."""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import re


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def spice_headers(text):
    text = re.sub(r'\n\+', ' ', text)
    result = {}
    for match in re.finditer(r'^\.subckt\s+(\S+)\s+(.*)$', text, re.M | re.I):
        name, ports = match[1], match[2].split()
        if name in result or len(ports) != len(set(ports)):
            raise ValueError('Duplicate circuit or terminal: ' + name)
        result[name] = ports
    return result


def port_map(cdl_ports, lef_ports):
    """Require a bijection: no aliases, omitted ports, implicit rail joining."""
    normalize = lambda x: x.replace('<', '[').replace('>', ']')
    if len(cdl_ports) != len(set(cdl_ports)) or len(lef_ports) != len(set(lef_ports)):
        raise ValueError('Repeated macro terminal')
    pairs = [(name, normalize(name)) for name in cdl_ports]
    if len({b for a, b in pairs}) != len(pairs):
        raise ValueError('Macro terminal normalization aliases two ports')
    if {b for a, b in pairs} != set(lef_ports):
        raise ValueError('Macro source terminal sets differ')
    return pairs


def def_routing_layers(text):
    result = {}
    for section in ('NETS', 'SPECIALNETS'):
        matches = re.findall(r'^' + section + r'\s+\d+\s*;(.*?)^END\s+' + section + r'\s*$', text, re.M | re.S)
        if len(matches) != 1:
            raise ValueError('Missing/ambiguous DEF ' + section)
        result[section] = sorted(set(re.findall(r'(?:\+\s+(?:ROUTED|FIXED|COVER)|\bNEW)\s+(\S+)', matches[0])))
    return result


def consumed_nets(inventory):
    """Logical coverage contract only; does not inspect physical routes."""
    result = {}
    for name, net in inventory['nets'].items():
        if net['sig_type'] not in ('SIGNAL', 'CLOCK'):
            continue
        terminals = net['terminals']
        ports = net['ports']
        # Input/inout receiver or a top-level port plus at least two contacts.
        loads = any(t[2] in ('INPUT', 'INOUT') for t in terminals) or bool(ports)
        if len(terminals) + len(ports) < 2 or not loads:
            continue
        result[name] = {('I', t[0] + '/' + t[1]) for t in terminals} | {('P', p) for p in ports}
    if not result:
        raise ValueError('Empty consumed-net coverage contract')
    return result


def _unescape(name):
    # Frozen names contain no whitespace. SPEF quotes and backslash-escaped
    # divider/bus characters are spelling, never permission to alias labels.
    return re.sub(r'\\(.)', r'\1', name.strip('"'))


def audit_spef(text, inventory):
    expected = consumed_nets(inventory)
    excluded = []
    for name, net in inventory['nets'].items():
        if net['sig_type'] not in ('SIGNAL', 'CLOCK') or name in expected:
            continue
        contacts = [('I', t[0] + '/' + t[1]) for t in net['terminals']] + [('P', p) for p in net['ports']]
        excluded.append({'net': name, 'kind': net['sig_type'], 'contacts': contacts,
            'reason': 'single-contact network: no interterminal RC coverage claim' if len(contacts) == 1 else
                      'no connected native contacts' if not contacts else 'no declared receiver in logical coverage contract'})
    expected_contacts = {kind: {name for contacts in expected.values() for k, name in contacts if k == kind}
                         for kind in ('I', 'P')}
    aliases = {}
    for candidates in [expected, *expected_contacts.values()]:
        index = {}
        for name in candidates:
            index.setdefault(_unescape(name), []).append(name)
        aliases[id(candidates)] = index
    name_map = {}
    divider = delimiter = None
    units = {}
    blocks = {}
    mode = None
    block = None

    def number(value):
        value = float(value)
        if not math.isfinite(value) or value < 0:
            raise ValueError('Invalid negative/nonfinite SPEF parasitic')
        return value

    def expand(value):
        value = value.strip('"')
        # A mapping may represent the whole pin or only its instance prefix.
        match = re.match(r'^(\*\d+)(.*)$', value)
        if match:
            if match[1] not in name_map:
                raise ValueError('Unknown SPEF name-map entry: ' + match[1])
            value = name_map[match[1]] + match[2]
        return value

    def native_name(value, candidates):
        if value in candidates:
            return value
        matches = aliases[id(candidates)].get(_unescape(value), [])
        if len(matches) > 1:
            raise ValueError('Ambiguous SPEF/native escape spelling: ' + value)
        return matches[0] if matches else value

    def pin(value):
        value = expand(value)
        if delimiter not in value:
            raise ValueError('Instance connection lacks a SPEF delimiter')
        instance, terminal = value.rsplit(delimiter, 1)
        if divider != '/':
            instance = instance.replace(divider, '/')
        return instance + '/' + terminal

    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith('//'):
            continue
        parts = line.split()
        key = parts[0]
        if key == '*DIVIDER':
            divider = parts[1]
        elif key == '*DELIMITER':
            delimiter = parts[1]
        elif key in ('*C_UNIT', '*R_UNIT'):
            if len(parts) != 3 or number(parts[1]) == 0:
                raise ValueError('Malformed SPEF units')
            units[key[1:]] = [float(parts[1]), parts[2]]
        elif key == '*NAME_MAP':
            mode = 'names'
        elif key == '*PORTS':
            mode = 'ports'
        elif mode == 'names' and re.fullmatch(r'\*\d+', key):
            if len(parts) != 2 or key in name_map:
                raise ValueError('Malformed/duplicate SPEF name map')
            name_map[key] = parts[1].strip('"')
        elif key == '*D_NET':
            if divider is None or delimiter is None or block is not None or len(parts) != 3:
                raise ValueError('Malformed SPEF net boundary')
            name = native_name(expand(parts[1]), expected)
            if name in blocks:
                raise ValueError('Repeated SPEF network: ' + name)
            block = {'name': name, 'total_capacitance': number(parts[2]),
                     'connections': set(), 'cap_count': 0, 'res_count': 0,
                     'edges': [], 'connection_nodes': {}}
            blocks[name] = block
            mode = None
        elif key in ('*CONN', '*CAP', '*RES'):
            if block is None:
                raise ValueError('Parasitic section outside SPEF net')
            mode = key[1:]
        elif key == '*END':
            if block is None:
                raise ValueError('Unexpected SPEF END')
            block = None
            mode = None
        elif block is not None and mode == 'CONN' and key in ('*P', '*I'):
            if len(parts) < 3:
                raise ValueError('Malformed SPEF connection')
            identity = (key[1:], native_name(pin(parts[1]) if key == '*I' else expand(parts[1]), expected_contacts[key[1:]]))
            if identity in block['connections']:
                raise ValueError('Duplicate SPEF connection')
            block['connections'].add(identity)
            block['connection_nodes'][identity] = expand(parts[1])
        elif block is not None and mode in ('CAP', 'RES') and key.isdigit():
            if mode == 'CAP':
                if len(parts) not in (3, 4):
                    raise ValueError('Malformed SPEF capacitor')
                for node in parts[1:-1]:
                    expand(node)
                number(parts[-1])
                block['cap_count'] += 1
            else:
                if len(parts) != 4:
                    raise ValueError('Malformed SPEF resistor')
                block['edges'].append((expand(parts[1]), expand(parts[2])))
                number(parts[-1])
                block['res_count'] += 1
        elif block is not None and mode == 'CONN' and key in ('*N',):
            # Internal-node coordinates carry no terminal coverage claim.
            continue
        elif block is not None:
            raise ValueError('Unsupported SPEF content in net: ' + line)
    if block is not None or not units.get('C_UNIT') or not units.get('R_UNIT'):
        raise ValueError('Incomplete SPEF file or units')
    missing = sorted(set(expected) - set(blocks))
    bad_connections = []
    bad_graph = []
    empty = []
    for name in sorted(set(expected) & set(blocks)):
        b = blocks[name]
        if b['connections'] != expected[name]:
            bad_connections.append({'net': name, 'missing': sorted(expected[name] - b['connections']),
                                    'unexpected': sorted(b['connections'] - expected[name])})
        if not b['cap_count'] or not b['res_count']:
            empty.append(name)
        adjacency = {}
        for a, c in b['edges']:
            adjacency.setdefault(a, set()).add(c)
            adjacency.setdefault(c, set()).add(a)
        nodes = set(b['connection_nodes'].values())
        seen = set()
        if nodes:
            todo = [min(nodes)]
            while todo:
                node = todo.pop()
                if node in seen:
                    continue
                seen.add(node)
                todo.extend(adjacency.get(node, set()) - seen)
        if nodes - seen:
            bad_graph.append({'net': name, 'unreachable_connection_nodes': sorted(nodes - seen)})
    result = {'schema': 'pinwheel-extracted-SPEF-coverage-v1',
        'status': 'passed' if not (missing or bad_connections or empty or bad_graph) else 'failed',
        'SPEF_network_count': len(blocks), 'expected_consumed_network_count': len(expected),
        'expected_consumed_terminal_count': sum(map(len, expected.values())),
        'all_connected_native_SIGNAL_CLOCK_contacts': sum(map(len, expected.values())) + sum(len(n['contacts']) for n in excluded),
        'excluded_native_contact_count': sum(len(n['contacts']) for n in excluded),
        'excluded_native_networks': sorted(excluded, key=lambda n: n['net']),
        'units': units, 'missing_networks': missing, 'connection_mismatches': bad_connections,
        'consumed_networks_without_RC_records': empty, 'resistance_graph_disconnections': bad_graph,
        'physical_connectivity_proven': False,
        'boundary': 'Logical pin coverage and extracted resistor-network reachability, not independent geometric connectivity or LVS.'}
    return result


def annotation_audit(text, inventory):
    matches = re.findall(r'Found (\d+) unannotated drivers\.\n(.*?)Found (\d+) partially unannotated drivers\.', text, re.S)
    if len(matches) != 1:
        raise ValueError('Missing/ambiguous native parasitic annotation report')
    count, names, partial = matches[0]
    names = names.split()
    if len(names) != int(count) or len(set(names)) != len(names):
        raise ValueError('Native annotation count/list mismatch')
    index = {}
    for name, net in inventory['nets'].items():
        for t in net['terminals']:
            index[t[0] + '/' + t[1]] = name
        for port in net['ports']:
            index[port] = name
    required = consumed_nets(inventory)
    unresolved, consumed, unused = [], [], []
    all_pins = {n + '/' + t[0] for n, v in inventory['instances'].items() for t in v['terminals']}
    for driver in names:
        if driver not in index:
            if driver in all_pins:
                unused.append(driver)
            else:
                unresolved.append(driver)
        elif index[driver] in required:
            consumed.append({'driver': driver, 'net': index[driver]})
        else:
            unused.append(driver)
    return {'status': 'passed' if not consumed and not unresolved and int(partial) == 0 else 'failed',
            'unannotated': int(count), 'partially_unannotated': int(partial),
            'consumed_unannotated': consumed, 'unresolved_drivers': unresolved,
            'unused_unannotated': unused}
