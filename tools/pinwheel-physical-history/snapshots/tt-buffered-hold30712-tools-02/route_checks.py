"""Host/native whole-inventory guard; only CLOCK NDR association response allowed."""
import hashlib
import json


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def audit_route(before, after):
    assert set(before) == set(after), 'Snapshot schema changed'
    for key in before:
        if key != 'nets':
            assert before[key] == after[key], (key, 'Frozen native data changed')
    assert set(before['nets']) == set(after['nets']), 'Net names changed'
    changes = []
    initial = {}
    final = {}
    clocks = []
    rule_widths = {rule[0]: {layer[0]: {'width_dbu': layer[2], 'spacing_dbu': layer[3]} for layer in rule[3]} for rule in before['nondefault_rules']}
    defaults = before['routing_layer_defaults']
    for rule, layers in rule_widths.items():
        assert set(layers) == set(defaults), (rule, 'Incomplete NDR layer-width coverage')
        assert all(value['width_dbu'] == defaults[layer]['width_dbu'] for layer, value in layers.items()), (rule, 'NDR/default width mismatch affects imported-route resistance model')
    before_widths = {}
    after_widths = {}
    for name, old in before['nets'].items():
        actual = after['nets'][name]
        assert all(rule is None or rule in rule_widths for rule in (old['nondefault_rule'], actual['nondefault_rule'])), (name, 'NDR association references an unknown rule')
        assert set(old) == set(actual)
        assert {k: v for k, v in old.items() if k != 'nondefault_rule'} == {k: v for k, v in actual.items() if k != 'nondefault_rule'}, (name, 'Net topology/type/ports changed')
        initial[name] = old['nondefault_rule']
        final[name] = actual['nondefault_rule']
        if old['sig_type'] == 'CLOCK':
            clocks.append(name)
            before_widths[name] = {'db_nondefault_rule': old['nondefault_rule'], 'NDR_layer_width_spacing': rule_widths.get(old['nondefault_rule'], {}), 'resolved_layer_width_spacing': rule_widths.get(old['nondefault_rule'], defaults)}
            after_widths[name] = {'db_nondefault_rule': actual['nondefault_rule'], 'NDR_layer_width_spacing': rule_widths.get(actual['nondefault_rule'], {}), 'resolved_layer_width_spacing': rule_widths.get(actual['nondefault_rule'], defaults)}
            if old['nondefault_rule'] != actual['nondefault_rule']:
                changes.append({'net': name, 'initial': old['nondefault_rule'], 'post_route': actual['nondefault_rule']})
        else:
            assert old['nondefault_rule'] == actual['nondefault_rule'], (name, 'Nonclock NDR association changed')
    return {
        'schema': 'pinwheel-buffered-tt-route-effort-inventory-v1', 'status': 'measured',
        'all_frozen_native_invariants_passed': True, 'all_instances_unchanged': True,
        'placement_statuses_unchanged': True, 'masters_and_logical_connectivity_unchanged': True,
        'clock_instance_geometry_and_topology_unchanged': True,
        'PG_pins_macros_rows_groups_regions_blockages_unchanged': True,
        'NDR_rule_definitions_and_TechLEF_unchanged': True, 'nonclock_NDR_associations_unchanged': True,
        'whole_instance_count': len(before['instances']), 'whole_net_count': len(before['nets']),
        'CLOCK_net_count': len(clocks), 'CLOCK_NDR_association_changes': sorted(changes, key=lambda c: c['net']),
        'initial_CLOCK_db_NDR_width_map': before_widths, 'post_route_CLOCK_db_NDR_width_map': after_widths,
        'default_routing_layer_width_spacing': defaults, 'NDR_widths_equal_default_on_all_routing_layers': True,
        'db_NDR_map_not_claimed_to_encode_FastRoute_in_memory_fallback': True,
        'initial_NDR_association_sha256': digest(initial), 'post_route_NDR_association_sha256': digest(final),
        'initial_NDR_rule_definitions_sha256': digest(before['nondefault_rules']),
        'post_route_NDR_rule_definitions_sha256': digest(after['nondefault_rules']),
        'source_inventory_sha256': digest(before), 'post_route_inventory_sha256': digest(after),
        'initial_and_post_route_NDR_state_asserted_identical': not changes,
        'boundary': 'Only native CLOCK NDR association changes are admitted as routing response. No placement, logical, PG, pin, row, technology or rule-definition changes. Global guides/grid/segments are separate route outputs.'}
