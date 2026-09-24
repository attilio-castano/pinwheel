"""Keep declared physical path roles and cumulative budgets through buffer edits.

The original checkpoint resolves each role. Rebuilding the candidate never
guesses a role from its immediate sink, which may now be an inserted buffer.
This contract supplements the complete distribution families and global checks.
"""
import json
import math

from physical_connections import Connectivity, parse_measurements
from physical_distribution import inventory
from physical_distribution_acceptance import qualify_candidate
from physical_distribution_route import validate_exact_edit
from physical_repair_plan import validate_plan
from tiled_chip import FF
from validation_run import sha


BOUNDARY = ('Complete declared distribution families plus explicit status, dynamic SRAM-control '
    'and input-hold connections and every added branch. Static ties and clocks remain classified '
    'separately and whole-chip checks remain required.')


def declared_roles(source, ownership, roles, scope, watch):
    """Resolve the saved declarations and independently census non-data macro inputs."""
    if (set(scope) != {'distribution', 'explicit_connections'} or
            watch['source_database']['sha256'] != source['database_sha256']):
        raise ValueError('Unlinked path scope or source checkpoint')
    graph = Connectivity(source, ownership)
    status = graph.record(watch['status_net'], roles)
    if 'rejection_status' not in status['semantic_roles']:
        raise ValueError('Declared status link does not reach the status role')
    families = {watch['status_net']: {'status_path'}}
    endpoints = watch['hold_endpoints']
    if not endpoints or len(set(endpoints)) != len(endpoints):
        raise ValueError('Require distinct declared hold endpoints')
    for pin in endpoints:
        cell, terminal = pin.rsplit('/', 1)
        if source['instances'][cell]['cell'] != FF or terminal != 'D':
            raise ValueError('Hold role must target a state data input')
        net = graph.pin_net[pin]
        graph.terminals(net)
        families.setdefault(net, set()).add('input_hold')
    macro_inputs = []
    for net, value in source['nets'].items():
        for term in value['terminals']:
            pin = term['instance'] + '/' + term['pin']
            if (not source['instances'][term['instance']]['macro'] or
                    term['direction'] != 'INPUT' or pin in scope['distribution']['macro_inputs']):
                continue
            drivers = [t for t in value['terminals'] if t['direction'] == 'OUTPUT']
            if value['type'] == 'CLOCK':
                kind = 'clock'
            elif (len(drivers) == 1 and source['instances'][drivers[0]['instance']]['cell']
                    in {'sg13cmos5l_tielo', 'sg13cmos5l_tiehi'}):
                kind = 'static_tie'
            else:
                graph.terminals(net)
                kind = 'timed_control'
                families.setdefault(net, set()).add('sram_control')
            macro_inputs.append(dict(pin=pin, net=net, kind=kind))
    if sorted(macro_inputs, key=lambda r:r['pin']) != sorted(watch['macro_inputs'], key=lambda r:r['pin']):
        raise ValueError('Incomplete or changed non-data macro input census')
    if sorted(families) != scope['explicit_connections']:
        raise ValueError('Missing or unexpected declared path connection')
    saved = {r['net']:r for r in watch['additional_connections']}
    if (len(saved) != len(watch['additional_connections']) or set(saved) != set(families) or
            any(saved[n] != graph.record(n, roles) for n in families)):
        raise ValueError('Changed source path ownership or connectivity')
    return {n:sorted(v) for n,v in families.items()}


def path_inventory(source, context, ownership, roles, scope, watch, plan=None):
    """Rebuild all family members and propagate fixed path roles through new stages."""
    extra = declared_roles(source, ownership, roles, scope, watch)
    family = inventory(context, ownership, roles, scope['distribution'])
    graph = Connectivity(context, ownership)
    rows = {r['net']:r for r in family['connections']}
    for net, names in extra.items():
        if net not in rows:
            rows[net] = dict(graph.record(net, roles), families=names)
        else:
            rows[net]['families'] = sorted(set(rows[net]['families']) | set(names))
    if plan is not None:
        if plan['source_database']['sha256'] != source['database_sha256']:
            raise ValueError('Path plan belongs to another source')
        hold = {op['receiver'] for op in plan['operations'] if op['purpose'] == 'hold'}
        if hold != set(watch['hold_endpoints']):
            raise ValueError('Plan does not retain declared hold endpoints')
        for op in plan['operations']:
            for stage in op['stages']:
                net = stage['new_net']
                if net not in rows:
                    rows[net] = dict(graph.record(net, roles), families=rows[op['net']]['families'])
                else:
                    rows[net]['families'] = sorted(set(rows[net]['families']) | set(rows[op['net']]['families']))
    return dict(source_database_sha256=context['database_sha256'], scope=scope,
        connections=[rows[n] for n in sorted(rows)], family_connections=len(family['connections']),
        distribution_trees=len(family['components']), boundary=BOUNDARY)


def validate_preserved_budgets(contract, original, area_reference):
    """The parent measurement is not a new origin for the cumulative area allowance."""
    expected = dict(all_connections_including_added_branches=True, all_chip_electrical_zero=True,
        unchanged_timing_floors=True, unchanged_cumulative_area_cap=True,
        original_cells_clocks_and_hold_retained=True, independent_identity_placement_power=True,
        whole_chip_routing_revalidation_required=True)
    if (contract.get('schema') != 1 or contract.get('status') != 'checked-plan-only' or
            contract.get('acceptance') != expected or
            contract['scope']['distribution'] != original['scope'] or
            any(contract[k] != original[k] for k in
                ['reserve_fraction', 'max_added_area_fraction', 'timing_floors_ns']) or
            area_reference['source_database_sha256'] != original['source_database_sha256'] or
            contract['area_reference']['area_um2'] != area_reference['placed_instance_area_um2']):
        raise ValueError('Path contract reset or weakened the preserved budgets')
    return area_reference['placed_instance_area_um2']


def validate_path_evidence(report, contexts, measure, reference, design, root, receipt, immediate):
    """Recompute scope, raw numerical evidence, exact edit and original area cost."""
    if not report.get('local_path_contract_pass') or not report.get('local_electrical_pass'):
        raise ValueError('Path candidate lacks a local contract pass')
    before, after = contexts
    _, contract = receipt('path_contract', report['contract'])
    _, plan = receipt('path_plan', report['plan'])
    _, watch = receipt('path_declarations', report['evidence']['watchlist.json'])
    _, original = receipt('path_preserved_budget', contract['preserved_budget_contract'])
    _, area_reference = receipt('path_area_reference', contract['area_reference']['measurement'], artifacts=True, settled=True)
    _, parent_manifest = receipt('path_source_route', report['source_full_route'])
    if (report['preserved_budget_contract'] != contract['preserved_budget_contract'] or
            parent_manifest['contract'] != contract['preserved_budget_contract'] or
            parent_manifest['selected_database']['sha256'] != before['database_sha256'] or
            contract['source_database_sha256'] != before['database_sha256'] or
            measure['source_database_sha256'] != after['database_sha256']):
        raise ValueError('Unlinked path source, candidate or original budget')
    area = validate_preserved_budgets(contract, original, area_reference)
    validate_plan(plan, before, before['database_sha256'])
    validate_exact_edit(plan, before, after, immediate)
    ownership = json.loads((design/'state-ownership.json').read_text())
    roles = json.loads((design/'path-roles.json').read_text())
    source = path_inventory(before, before, ownership, roles, contract['scope'], watch)
    candidate = path_inventory(before, after, ownership, roles, contract['scope'], watch, plan)
    _, saved_source = receipt('path_source_inventory', report['evidence']['before-coverage.json'])
    _, saved_candidate = receipt('path_candidate_inventory', report['evidence']['qualified-coverage.json'])
    _, measurements = receipt('path_measurements', report['evidence']['measurements.json'])
    _, saved_acceptance = receipt('path_acceptance', report['evidence']['acceptance.json'])
    collection_path, collection = receipt('path_raw_collection', report['evidence']['connections/collection.json'], artifacts=True, settled=True)
    if (source != saved_source or candidate != saved_candidate or not collection.get('source_unchanged') or
            collection['inputs_sha256'].get(str(root/measure['source_database'])) != measure['source_database_sha256']):
        raise ValueError('Unlinked or incomplete declared path coverage')
    names = {r['net'] for r in candidate['connections']}
    for corner in measure['fresh_timing']:
        raw = collection_path.parent/'after'/corner/'connections.rpt'
        if (sha(raw) != collection['artifacts_sha256'].get(str(raw.relative_to(collection_path.parent))) or
                parse_measurements(raw.read_text(), names) != measurements[corner]):
            raise ValueError('Path records differ from raw candidate measurements')
    raw_timing = collection_path.parent/'after/fresh-timing.json'
    if (sha(raw_timing) != collection['artifacts_sha256'].get('after/fresh-timing.json') or
            json.loads(raw_timing.read_text()) != measure['fresh_timing']):
        raise ValueError('Path collection does not reproduce whole-chip timing')
    for context, measured in [(before, reference), (after, measure)]:
        physical_area = sum((i['bbox'][2]-i['bbox'][0])*(i['bbox'][3]-i['bbox'][1])
                            for i in context['instances'].values())
        if not math.isclose(physical_area, measured['placed_instance_area_um2'], rel_tol=0, abs_tol=1e-4):
            raise ValueError('Path area differs from the independently measured footprints')
    qualified = qualify_candidate(contract, source, candidate, plan, measurements, measure['fresh_timing'],
                                  area, measure['placed_instance_area_um2'])
    if qualified != saved_acceptance or not qualified['quantitative_gates_passed']:
        raise ValueError('Path candidate fails the original quantitative gates')
    return dict(contract_sha256=report['contract']['sha256'], covered_connections=len(names),
        reserve_fraction=contract['reserve_fraction'], timing_floors_ns=contract['timing_floors_ns'],
        cumulative_area_reference_um2=area, max_added_area_fraction=contract['max_added_area_fraction'],
        quantitative_gates_recomputed=True, exact_plan_recomputed=True, declared_roles_recomputed=True,
        helper_sha256=sha(__file__),
        boundary='Local qualification only; retain the same scope and original budgets after whole-chip routing.')
