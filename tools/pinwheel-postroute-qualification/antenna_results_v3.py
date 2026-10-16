"""Finite parser for actual pinned native antenna reports; no CAD or repairs."""
from collections import Counter
import hashlib
import json
import math
import re

# Pinned AntennaChecker.cc checkGates:796-824 increments once per ITerm
# after all layers; checkAntennas:1144-1162 sums those distinct pin counts.
# https://github.com/The-OpenROAD-Project/OpenROAD/blob/dcf36133a369abc8f3c5e5738cd4d82e4903c0e0/src/ant/src/AntennaChecker.cc
COUNTER_SOURCE = 'OpenROAD dcf36133a369abc8f3c5e5738cd4d82e4903c0e0 src/ant/src/AntennaChecker.cc:796-824,1144-1162'


def require(condition, message):
    if not condition: raise ValueError(message)


def parse_native(text, metrics, coverage, inventory):
    counts = {}
    for noun, code in [('net', '0002'), ('pin', '0001')]:
        found = re.findall(r'^\[INFO ANT-' + code + r'\] Found (\d+) ' + noun + r' violations\.$', text, re.M)
        require(len(found) == 1, 'Missing/ambiguous native antenna ' + noun + ' count')
        counts[noun] = int(found[0])
    require(not re.search(r'(?mi)^\s*(?:\[ERROR\b|Error:|Traceback)', text), 'Native antenna error')
    require(coverage['all_have_actual_ROUTED_detailed_wires'] is True and coverage['relevant_consumed_net_count'] > 0,
            'Missing/empty actual detailed-route denominator')
    require(coverage['all_input_gate_area_and_used_layer_rule_coverage_complete'] is True
            and coverage['relevant_connected_INPUT_ITerm_count'] > 0
            and coverage['native_positive_gate_area_contact_count'] == coverage['relevant_connected_INPUT_ITerm_count']
            and not coverage['uncovered_INPUT_contacts'] and not coverage['used_layers_without_positive_native_scalar_rule'],
            'Incomplete/empty native model coverage')
    layers = coverage['used_metal_and_via_cut_layers']
    require(isinstance(layers, list) and bool(layers) and len(layers) == len(set(layers)),
            'Missing/ambiguous used-layer denominator')
    rules = coverage['native_technology_rules']
    for layer in layers:
        require(layer in rules and rules[layer]['has_native_rule'] is True
                and rules[layer]['positive_scalar_rule'] is True and not rules[layer]['query_errors']
                and any(math.isfinite(value) and value > 0 for value in rules[layer]['scalar_ratios'].values()),
                'Missing positive native used-layer rule: ' + layer)
    models = coverage['master_gate_models']
    require(isinstance(models, dict) and bool(models), 'Empty native gate-area model map')
    consumed = {name for name, net in inventory['nets'].items()
        if net['sig_type'] in ('SIGNAL', 'CLOCK') and len(net['ports']) + len(net['terminals']) >= 2
        and (net['ports'] or any(t[2] in ('INPUT', 'INOUT') for t in net['terminals']))}
    contacts = [(inst['master'], pin) for inst in inventory['instances'].values()
        for pin, net, direction in inst['terminals'] if net in consumed and direction == 'INPUT']
    require(len(consumed) == coverage['relevant_consumed_net_count']
            and len(contacts) == coverage['relevant_connected_INPUT_ITerm_count']
            and {master + '/' + pin for master, pin in contacts} == set(models),
            'Native model coverage does not match actual source INPUT contacts')
    for record in models.values():
        require(record['has_native_model'] is True and record['positive_gate_area'] is True and record['query_error'] is None,
                'Unqualified imported pin gate-area model')
        require(any(math.isfinite(row[0]) and row[0] > 0 for row in record['gate_areas']), 'Missing positive native gate area')
    require(metrics.get('flow__errors__count') == 0, 'Missing/nonzero native error metric')
    key_net, key_pin = 'antenna__violating__nets', 'antenna__violating__pins'
    require((key_net in metrics) == (key_pin in metrics), 'Partial optional antenna metric telemetry')
    if key_net in metrics:
        require(type(metrics[key_net]) is int and type(metrics[key_pin]) is int
                and metrics[key_net] == counts['net'] and metrics[key_pin] == counts['pin'], 'Native text/metric antenna counts disagree')
        telemetry = 'present_and_equal_to_native_text'
    else:
        telemetry = 'absent_in_actual_native_metrics_file; not inferred_zero'
    net = pin = master = layer = previous = None
    net_sections, pin_sections, events = set(), set(), []
    for lineno, line in enumerate(text.splitlines(), 1):
        found = re.match(r'^\s*Net:\s+(\S+)\s*$', line)
        if found:
            net, pin, layer = found[1], None, None
            require(net not in net_sections and net in inventory['nets'], 'Duplicate/unknown native report network')
            net_sections.add(net)
        found = re.match(r'^\s*Pin:\s+(\S+)\s+\(([^)]+)\)\s*$', line)
        if found:
            pin, master, layer = found[1], found[2], None
            require(net is not None and (net, pin) not in pin_sections, 'Duplicate/unscoped native report input pin')
            pin_sections.add((net, pin))
            instance, terminal = pin.rsplit('/', 1)
            require(instance in inventory['instances'] and inventory['instances'][instance]['master'] == master
                    and [terminal, net, 'INPUT'] in inventory['instances'][instance]['terminals'], 'Native report pin not a consumed source INPUT contact')
        found = re.match(r'^\s*Layer:\s+(\S+)\s*$', line)
        if found: layer = found[1]
        if '(VIOLATED)' in line:
            require(net is not None and pin is not None and layer in coverage['used_metal_and_via_cut_layers'], 'Unscoped native violation')
            value = re.match(r'^\s*(Partial area ratio|Cumulative area ratio):\s+([0-9.+-]+)\s*$', previous or '')
            limit = re.match(r'^\s*Required ratio:\s+([0-9.+-]+)\s+\((Gate area|Cumulative area|Side area|Cumulative side area)\)\s+\(VIOLATED\)\s*$', line)
            require(value is not None and limit is not None, 'Unknown native violation ratio format')
            measured, required = float(value[2]), float(limit[1])
            # Native checks unrounded doubles but prints both to two decimal
            # places (e.g. checkCAR:667-686). Equality after printing is valid.
            require(math.isfinite(measured) and math.isfinite(required) and required > 0 and measured >= required,
                    'Nonfinite/nonviolating antenna ratio')
            events.append({'net': net, 'pin': pin, 'master': master, 'layer': layer, 'kind': limit[2],
                'reported_ratio': measured, 'required_ratio': required, 'line': lineno,
                'source_role': inventory['nets'][net]['sig_type'],
                'pin_class': 'SRAM_input' if inventory['instances'][instance]['macro'] else 'standard_cell_input'})
        previous = line
    bad_nets, bad_pins = {e['net'] for e in events}, {(e['net'], e['pin']) for e in events}
    require(len(bad_nets) == counts['net'] and len(bad_pins) == counts['pin'], 'Native summary disagrees with complete detailed violated-net/pin sections')
    require(net_sections == bad_nets, 'Unexpected partial/nonviolated report net section')
    # Pinned verbose output includes nonviolating INPUT loads of a violated
    # network as well. They must not be counted as antenna violations.
    expected_pin_sections = {(net, name + '/' + pin) for name, instance in inventory['instances'].items()
        for pin, net, direction in instance['terminals'] if net in net_sections and direction == 'INPUT'}
    require(pin_sections == expected_pin_sections, 'Partial/extra reported INPUT-pin sections')
    semantic = sorted([[e['net'], e['pin'], e['master'], e['layer'], e['kind'], e['reported_ratio'], e['required_ratio']] for e in events])
    warnings = re.findall(r'^\[(?:WARNING|ERROR)\s+[^\]]+\].*$', text, re.M)
    return {'native_net_violation_count': counts['net'], 'native_pin_violation_count': counts['pin'],
        'distinct_detailed_violated_nets': len(bad_nets), 'distinct_detailed_violated_net_pin_pairs': len(bad_pins),
        'all_reported_INPUT_pin_sections': len(pin_sections),
        'reported_nonviolating_INPUT_pin_sections': len(pin_sections - bad_pins),
        'detailed_ratio_violation_events': len(events), 'optional_metric_telemetry': telemetry,
        'native_pin_counter_semantics': 'Distinct INPUT ITerms with any violating layer/ratio; ratio-event count may exceed pin count.',
        'native_counter_source': COUNTER_SOURCE,
        'native_violations_with_equal_rounded_ratio_and_limit': sum(e['reported_ratio'] == e['required_ratio'] for e in events),
        'summary_and_detailed_sections_reconciled': True,
        'semantic_violation_signature_sha256': hashlib.sha256(json.dumps(semantic, separators=(',', ':')).encode()).hexdigest(),
        'events_by_layer': dict(Counter(e['layer'] for e in events)),
        'violated_nets_by_signal_type': dict(Counter(inventory['nets'][net]['sig_type'] for net in bad_nets)),
        'violated_input_contacts_by_class': dict(Counter(next(e['pin_class'] for e in events if (e['net'], e['pin']) == pair) for pair in bad_pins)),
        'native_warnings_errors': warnings, 'events': events,
        'interpretation': 'Actual native logical-dbNet detailed-wire antenna diagnostic; no proof of silicon physical-net connectivity, SRAM interior or diode requirement.'}


def validate_reference(parsed, expected):
    """A previous result is optional; when supplied, require its complete set."""
    keys = ('native_net_violation_count', 'native_pin_violation_count', 'semantic_violation_signature_sha256')
    present = [key in expected for key in keys]
    require(not any(present) or all(present), 'Partial same-source reference result')
    if all(present):
        for key in keys:
            require(parsed[key] == expected[key], 'Fresh same-source antenna result differs from reference: ' + key)
        return True
    return False
