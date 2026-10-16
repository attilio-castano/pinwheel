"""Audited comparison spelling adapters for two fixed 345-port SRAM boundaries.

No geometry, model interior, source RTL, or instance/pin-to-net contract is changed.
"""
import hashlib
import json
import re

MASTER = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
RAILS = {'VDD!': 'VDD', 'VDDARRAY!': 'VDDARRAY', 'VSS!': 'VSS'}


def canonical_pin(pin):
    pin = pin.replace('<', '[').replace('>', ']')
    return RAILS.get(pin, pin)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def tokens(text):
    pattern = r'\s+|//[^\n]*|/\*.*?\*/|\\[^\s]+|[A-Za-z_$][\w$]*|\d+\x27[sS]?[bBoOdDhH][0-9a-fA-F_xXzZ]+|\d+|[^\s]'
    return [(m[0], m.start(), m.end()) for m in re.finditer(pattern, text, re.S)
            if not m[0].isspace() and not m[0].startswith(('//', '/*'))]


def identifier(token):
    if token.startswith('\\'):
        return token[1:]
    if re.fullmatch(r'[A-Za-z_$][\w$]*', token):
        return token
    raise ValueError('Unsupported non-identifier connection expression: ' + token)


def scalar(expression):
    if len(expression) != 1:
        raise ValueError('Only explicitly expanded scalar connections are supported')
    return identifier(expression[0])


def expand_expression(expression):
    if expression[0] != '{':
        return [scalar(expression)]
    assert expression[-1] == '}'
    pieces, current = [], []
    for token in expression[1:-1]:
        if token == ',':
            pieces.append(scalar(current))
            current = []
        else:
            assert token not in ('{', '}', '(', ')'), 'Nested or functional vector expression is unsupported'
            current.append(token)
    pieces.append(scalar(current))
    return pieces


def native_macro_contract(inventory):
    result = {}
    for name, instance in inventory['instances'].items():
        if instance['master'] != MASTER:
            continue
        terms = {pin: net for pin, net, direction in instance['terminals']}
        assert len(terms) == 345 and len(instance['terminals']) == 345
        assert all(net is not None for net in terms.values()), 'Unconnected source macro terminal'
        assert set(RAILS) <= set(terms)
        assert terms['VDD!'] == terms['VDDARRAY!'] == 'VPWR' and terms['VSS!'] == 'VGND'
        result[name] = terms
    assert len(result) == 2, 'Require the fixed two-SRAM design'
    return result


def positional_reference(text, inventory, model_order):
    original_contract = native_macro_contract(inventory)
    # OpenDB native net names escape bus brackets; write_verilog emits the
    # corresponding escaped Verilog identifier. Require a global one-to-one
    # spelling map before using it for any pin correspondence.
    net_spelling = {name: re.sub(r'\\([\[\]])', r'\1', name) for name in inventory['nets']}
    assert len(set(net_spelling.values())) == len(net_spelling), 'Native net spelling normalization aliases identities'
    contract = {instance: {pin: net_spelling[net] for pin, net in terms.items()} for instance, terms in original_contract.items()}
    assert len(model_order) == len(set(model_order)) == 345
    native_ports = set(next(iter(contract.values())))
    assert {canonical_pin(port) for port in native_ports} == set(model_order)
    inverse = {canonical_pin(port): port for port in native_ports}
    assert len(inverse) == 345
    pattern = re.compile(r'\b' + re.escape(MASTER) + r'\s+(\\[^\s]+|[A-Za-z_$][\w$]*)\s*\(')
    edits, facts = [], {}
    for match in pattern.finditer(text):
        name = identifier(match[1])
        assert name in contract and name not in facts
        rest = tokens(text[match.end():])
        depth, stop = 1, None
        for i, (token, start, end) in enumerate(rest):
            if token == '(':
                depth += 1
            elif token == ')':
                depth -= 1
                if depth == 0:
                    stop = i
                    break
        assert stop is not None
        assert rest[stop + 1][0] == ';'
        body = [t[0] for t in rest[:stop]]
        pin_to_net, cursor = {}, 0
        while cursor < len(body):
            assert body[cursor] == '.'
            pin = identifier(body[cursor + 1])
            assert body[cursor + 2] == '('
            closing = cursor + 3
            while body[closing] != ')':
                assert body[closing] != '(', 'Functional connection unsupported'
                closing += 1
            connections = expand_expression(body[cursor + 3:closing])
            if pin in native_ports:
                assert len(connections) == 1
                pairs = [(pin, connections[0])]
            else:
                indices = sorted((int(m[1]) for port in native_ports
                    if (m := re.fullmatch(re.escape(pin) + r'\[(\d+)\]', port))), reverse=True)
                assert indices and indices == list(range(max(indices), -1, -1))
                assert len(indices) == len(connections)
                pairs = [(pin + '[' + str(index) + ']', net) for index, net in zip(indices, connections)]
            for port, net in pairs:
                assert port not in pin_to_net
                pin_to_net[port] = net
            cursor = closing + 1
            if cursor < len(body):
                assert body[cursor] == ','
                cursor += 1
        assert pin_to_net == contract[name], 'Original reference/native macro pin-to-net mismatch: ' + name + ' ' + repr([(p, pin_to_net.get(p), n) for p, n in contract[name].items() if pin_to_net.get(p) != n][:8])
        # Preserve native escaped scalar net spellings. Every net is from the
        # exact original association; escaping below changes syntax, not identity.
        def spelling(net):
            return net if re.fullmatch(r'[A-Za-z_$][\w$]*', net) else '\\' + net + ' '
        ordered = [spelling(pin_to_net[inverse[port]]) for port in model_order]
        end = match.end() + rest[stop + 1][2]
        replacement = MASTER + ' ' + match[1] + ' (' + ', '.join(ordered) + ');'
        edits.append((match.start(), end, replacement))
        facts[name] = {'native_terminals_exact': True, 'pin_to_net': pin_to_net,
            'canonical_model_order': model_order, 'positional_node_count': len(ordered),
            'pin_to_net_sha256': digest(pin_to_net), 'exact_native_pin_to_net': original_contract[name]}
    assert set(facts) == set(contract)
    result = text
    for start, end, replacement in reversed(edits):
        result = result[:start] + replacement + result[end:]
    # Exact untouched text regions are guaranteed by splicing only the two
    # macro statements. This does not replace/normalize any other cell or net.
    return result, {'schema': 'pinwheel-positional-boundary-reference-v5',
        'status': 'source_spelling_adapter_verified_only', 'macro_count': 2,
        'native_macro_contacts_checked': 690, 'masters_and_all_pin_to_net_contracts_unchanged': True,
        'standard_cell_and_all_other_text_outside_two_macro_statements_exact': True,
        'macro_instances': facts, 'native_net_spelling_map_bijective_over_all_nets': True,
        'native_net_spelling_nonidentity_map': [[a, b] for a, b in net_spelling.items() if a != b],
        'explicit_name_map': [[p, canonical_pin(p)] for p in sorted(native_ports)],
        'physical_connectivity_proven': False, 'internal_SRAM_LVS_proven': False}


def normalized_extracted_header(text, native_ports):
    """Rename only an empty extracted macro header, preserving its pin order."""
    pattern = re.compile(r'^\.subckt\s+' + re.escape(MASTER) + r'\s+[^\n]*(?:\n\+[^\n]*)*', re.M | re.I)
    matches = list(pattern.finditer(text))
    assert len(matches) == 1
    match = matches[0]
    ports = re.sub(r'\n\+', ' ', match[0]).split()[2:]
    canonical = [canonical_pin(port) for port in ports]
    expected = {canonical_pin(pin) for pin in native_ports}
    assert len(ports) == len(set(ports)) == len(canonical) == len(set(canonical)) == 345
    assert set(canonical) == expected
    end = re.search(r'^\.ends(?:\s|$)', text[match.end():], re.M | re.I)
    assert end is not None
    body = text[match.end():match.end() + end.start()]
    assert all(not line.strip() or line.lstrip().startswith('*') for line in body.splitlines()), 'Extracted macro interior is not empty: no boundary suppression claim'
    replacement = '.subckt ' + MASTER + ' ' + ' '.join(canonical)
    result = text[:match.start()] + replacement + text[match.end():]
    return result, {'schema': 'pinwheel-extracted-empty-boundary-header-normalization-v5',
        'status': 'bijective_spelling_map_only', 'port_count': 345,
        'ordered_original_to_canonical': list(zip(ports, canonical)),
        'all_positional_instance_nodes_and_nonmacro_header_text_unchanged': True,
        'macro_interior_empty_verified': True, 'rails_are_not_merged': True,
        'internal_SRAM_LVS_proven': False}
