"""Strict supported OpenRCX SPEF capacitance subset and Maxwell reconstruction.

The pinned writer repeats each coupling in both endpoint-net CAP blocks and
includes its full value in each D_NET total. Printed %g rounding is accounted
for separately from physical accuracy. No field solve or native execution.
"""
from decimal import Decimal as D
import re

NUM = r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'


def need(value, message):
    if not value:
        raise ValueError(message)


def number(token):
    need(re.fullmatch(NUM, token) is not None, 'Unsupported nonnumeric capacitance')
    value = D(token)
    need(value.is_finite() and value >= 0, 'Negative/nonfinite capacitance')
    return value


def rounding(value):
    # C fprintf %g has six significant digits; omitted trailing zeroes do not
    # reduce its precision. Exact printed zero contributes no positive mass.
    return D(0) if value == 0 else D('.5') * D(10) ** (value.adjusted() - 5)


def parse(text, names, partners):
    need(len(names) == len(set(names)) and set(partners) == set(names), 'Invalid declared SPEF membership')
    units = re.findall(r'^\*C_UNIT\s+(' + NUM + r')\s+(FF|PF)\s*$', text, re.M)
    need(len(units) == 1 and text.count('*C_UNIT') == 1, 'Missing/duplicate/unsupported C_UNIT')
    unit = number(units[0][0]) * (D('1e-15') if units[0][1] == 'FF' else D('1e-12'))
    need(unit > 0, 'Nonpositive C_UNIT')
    need(len(re.findall(r'^\*DESIGN_FLOW\s+"NAME_SCOPE LOCAL"\s+"PIN_CAP NONE"\s*$', text, re.M)) == 1,
         'Unsupported pin-cap writer policy')
    mapping = {}
    maps = re.findall(r'^\*NAME_MAP\s*\n(.*?)(?=^\*(?:PORTS|D_NET)\b)', text, re.M | re.S)
    need(len(maps) <= 1, 'Duplicate NAME_MAP')
    for line in maps[0].splitlines() if maps else []:
        if not line.strip():
            continue
        row = re.fullmatch(r'\s*(\*\d+)\s+([A-Za-z0-9_]+)\s*', line)
        need(row is not None and row[1] not in mapping, 'Unsupported/duplicate SPEF name-map row')
        mapping[row[1]] = row[2]
    def resolve(token):
        head, sep, tail = token.partition(':')
        need(not head.startswith('*') or head in mapping, 'Unknown SPEF name-map reference')
        return mapping.get(head, head) + (sep + tail if sep else '')
    ports = {n + '_' + end: n for n in names for end in ('A', 'B')}
    def owner(node):
        if node in ports:
            return ports[node]
        head, sep, tail = node.partition(':')
        need(sep and head in partners and tail.isdigit() and int(tail) > 0, 'Unknown/foreign capacitance node')
        return head
    blocks = re.findall(r'^\*D_NET\s+(\S+)\s+(' + NUM + r')\s*\n(.*?)^\*END\s*$', text, re.M | re.S)
    need(len(blocks) == len(names) == text.count('*D_NET') == len(re.findall(r'^\*END\s*$', text, re.M)),
         'Missing/truncated/extra D_NET')
    nets = {}; mirrored = {}
    for token, total_token, body in blocks:
        net = resolve(token)
        need(net in partners and net not in nets, 'Unexpected/duplicate D_NET')
        total = number(total_token) * unit
        sections = re.fullmatch(r'\*CONN\s*\n(.*?)^\*CAP\s*\n(.*?)^\*RES\s*\n(.*)', body.strip(), re.M | re.S)
        need(sections is not None, 'Missing/duplicate/reordered CONN/CAP/RES')
        terminals = []
        for line in sections[1].splitlines():
            if not line.strip():
                continue
            row = re.fullmatch(r'\s*\*P\s+(\S+)\s+[IOB](?:\s+.*)?', line)
            need(row is not None, 'Unsupported ITerm/nonport connection')
            terminals.append(resolve(row[1]))
        need(set(terminals) == {net + '_A', net + '_B'} and len(terminals) == 2,
             'Exact two-port connection membership differs')
        ground = D(0); incident = D(0); error = rounding(number(total_token)) * unit
        ids = set(); ground_nodes = set(); local_cap_nodes = set(); coupling_keys = set()
        for line in sections[2].splitlines():
            if not line.strip():
                continue
            row = line.split()
            need(len(row) in (3, 4) and row[0].isdigit() and row[0] not in ids, 'Malformed/duplicate CAP row')
            ids.add(row[0]); value = number(row[-1]) * unit
            error += rounding(number(row[-1])) * unit
            a = resolve(row[1]); oa = owner(a)
            if len(row) == 3:
                need(oa == net and a not in ground_nodes, 'Duplicate/foreign grounded CAP node')
                ground_nodes.add(a); local_cap_nodes.add(a); ground += value
            else:
                b = resolve(row[2]); ob = owner(b)
                need(oa != ob and net in (oa, ob) and partners[net] in (oa, ob)
                     and partners[net] is not None, 'Unintended/same-net/nonpartner coupling')
                key = tuple(sorted((a, b)))
                need(key not in coupling_keys, 'Duplicate coupling within a net block')
                coupling_keys.add(key); mirrored.setdefault(key, []).append((net, value))
                local_cap_nodes.add(a if oa == net else b); incident += value
        need(ground_nodes and abs(total - ground - incident) <= error,
             'D_NET does not reconcile ground plus full incident coupling within writer rounding')
        adjacency = {}; resistor_ids = set()
        for line in sections[3].splitlines():
            if not line.strip():
                continue
            row = line.split()
            need(len(row) == 4 and row[0].isdigit() and row[0] not in resistor_ids, 'Malformed/duplicate RES row')
            resistor_ids.add(row[0]); a, b = resolve(row[1]), resolve(row[2]); number(row[3])
            need(a != b and owner(a) == owner(b) == net, 'Foreign/shorted resistor endpoints')
            adjacency.setdefault(a, set()).add(b); adjacency.setdefault(b, set()).add(a)
        need(set(terminals) <= set(adjacency) and local_cap_nodes <= set(adjacency),
             'Capacitance/port node missing from the physical resistor graph')
        seen = set(); todo = [terminals[0]]
        while todo:
            node = todo.pop()
            if node not in seen:
                seen.add(node); todo.extend(adjacency[node])
        need(seen == set(adjacency), 'Disconnected resistor/capacitance graph')
        nets[net] = {'ground_F': str(ground), 'incident_coupling_F': str(incident),
                     'D_NET_F': str(total), 'writer_rounding_bound_F': str(error),
                     'CAP_rows': len(ids), 'RES_rows': len(resistor_ids)}
    pair_totals = {}
    for key, copies in mirrored.items():
        owners = {owner(x) for x in key}
        need(len(copies) == 2 and {n for n, _ in copies} == owners
             and copies[0][1] == copies[1][1], 'Missing/unequal/duplicated mirrored coupling')
        pair = tuple(sorted(owners)); pair_totals[pair] = pair_totals.get(pair, D(0)) + copies[0][1]
    for net in names:
        target = partners[net]
        expected = D(0) if target is None else pair_totals.get(tuple(sorted((net, target))), D(0))
        need(D(nets[net]['incident_coupling_F']) == expected and (target is None or expected > 0),
             'Missing intended coupling or incident total differs')
    matrices = {}
    for net in names:
        target = partners[net]
        group = (net,) if target is None else tuple(sorted((net, target)))
        if group in matrices:
            continue
        k = D(0) if len(group) == 1 else pair_totals[group]
        matrix = [[D(nets[a]['ground_F']) + k if a == b else -k for b in group] for a in group]
        need(all(matrix[i][i] > 0 and sum(matrix[i]) > 0 for i in range(len(group))), 'Nonpositive Maxwell diagonal/ground')
        matrices[group] = {'names': list(group), 'matrix_F': [[str(x) for x in row] for row in matrix],
                           'ground_F': [nets[n]['ground_F'] for n in group], 'coupling_F': str(k)}
    return {'C_unit_F': str(unit), 'nets': nets, 'groups': list(matrices.values()),
            'unique_coupling_segments': len(mirrored), 'mirrored_coupling_semantics_checked': True,
            'all_D_NET_totals_reconciled': True, 'model_qualified': False}
