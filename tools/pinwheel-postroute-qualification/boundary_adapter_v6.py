"""Reversible safe named scalar pin spellings for native Netgen1.5.320.

Its Verilog parser requires dot-name associations; positional instances are dropped.
"""
import re
from boundary_adapter_v5 import MASTER, canonical_pin, positional_reference, normalized_extracted_header, tokens


def pin_aliases(model_order):
    assert len(model_order) == len(set(model_order)) == 345
    return {pin: 'PW_SRAM_PIN_' + str(i).zfill(3) for i, pin in enumerate(model_order)}


def named_reference(text, inventory, model_order):
    converted, audit = positional_reference(text, inventory, model_order)
    aliases = pin_aliases(model_order)
    pattern = re.compile(r'\b' + re.escape(MASTER) + r'\s+(\\[^\s]+|[A-Za-z_$][\w$]*)\s*\(')
    edits = []
    for match in pattern.finditer(converted):
        stream = tokens(converted[match.end():])
        assert [token[0] for token in stream[1:688:2]] == [','] * 344
        nodes = [token[0] for token in stream[:689:2]]
        assert len(nodes) == 345 and stream[689][0] == ')' and stream[690][0] == ';'
        def spelling(node):
            return node + ' ' if node.startswith('\\') else node
        named = ', '.join('.' + aliases[pin] + '(' + spelling(node) + ')' for pin, node in zip(model_order, nodes))
        end = match.end() + stream[690][2]
        edits.append((match.start(), end, MASTER + ' ' + match[1] + ' (' + named + ');'))
    assert len(edits) == 2
    result = converted
    for start, end, replacement in reversed(edits):
        result = result[:start] + replacement + result[end:]
    audit.update(schema='pinwheel-safe-named-boundary-reference-v6',
        comparison_connection_style='345 explicit dot-name scalar aliases required by native Verilog parser',
        canonical_to_safe_pin_aliases=aliases,
        native_parser_revision='b3af7b98b4a3bfbb149134e17eb3004a086b686a',
        native_parser_source='base/verilog.c:2246-2256')
    return result, audit


def aliased_extracted_header(text, native_ports, model_order):
    converted, audit = normalized_extracted_header(text, native_ports)
    aliases = pin_aliases(model_order)
    pattern = re.compile(r'^\.subckt\s+' + re.escape(MASTER) + r'\s+[^\n]*', re.M | re.I)
    matches = list(pattern.finditer(converted))
    assert len(matches) == 1
    match = matches[0]
    canonical = match[0].split()[2:]
    assert len(canonical) == 345 and set(canonical) == set(aliases)
    alias_order = [aliases[pin] for pin in canonical]
    result = converted[:match.start()] + '.subckt ' + MASTER + ' ' + ' '.join(alias_order) + converted[match.end():]
    audit.update(schema='pinwheel-extracted-empty-boundary-aliases-v6',
        ordered_original_canonical_safe_aliases=[[a, b, aliases[b]] for a, b in audit['ordered_original_to_canonical']],
        canonical_to_safe_pin_aliases=aliases,
        all_positional_instance_nodes_and_nonmacro_header_text_unchanged=True,
        no_interior_conductive_model_added=True)
    return result, audit
