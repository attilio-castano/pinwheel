"""Recompute declared edits, inherited scope and budgets before coarse routing."""
import json
import math

from physical_connections import parse_measurements
from physical_distribution_acceptance import qualify_candidate
from physical_organization_edits import import_local_plan, measurement_plan, verify_actual
from physical_path_contract import path_inventory, validate_preserved_budgets
from routing_evidence import pin_access_summary
from validation_run import sha


def validate_organization_evidence(selection, report, contexts, measure, reference,
                                   design, root, receipt, source_module, candidate_module):
    before, after = contexts
    if not all(report.get(k) is True for k in ('local_quantitative_contract_pass',
            'local_electrical_pass','local_identity_placement_power_pass','minimum_pin_access_pass')):
        raise ValueError('Organization candidate lacks complete local qualification')
    _, legacy = receipt('organization_local_plan', report['plan'])
    _, plan = receipt('organization_edits', selection['edits'])
    _, policy = receipt('organization_policy', selection['policy'])
    expected_plan, expected_policy = import_local_plan(legacy)
    if plan != expected_plan or policy != expected_policy:
        raise ValueError('Declared edits differ from the qualified local candidate')
    _, base = receipt('organization_base_policy', report['base_policy'])
    _, refinement = receipt('organization_refinement', report['refinement'])
    move = refinement['relocation']
    if (base['source_database_sha256'] != before['database_sha256'] or
            refinement['source_database_sha256'] != before['database_sha256'] or
            refinement['base_policy_sha256'] != report['base_policy']['sha256'] or
            policy['protected_instances'] != base['protected_instances'] or
            policy['relocations'] != {move['instance']:{k:v for k,v in move.items() if k != 'instance'}} or
            any(op['cell'] not in base['resize_cells'] for op in plan['operations']
                if op['kind'] in ('resize_buffer','move_resize_buffer'))):
        raise ValueError('Organization edit widened its original policy')
    edit_proof = verify_actual(plan, policy, before, after, source_module, candidate_module)
    _, identity = receipt('organization_local_readback', report['evidence']['identity.json'])
    if edit_proof != identity['proof']:
        raise ValueError('Organization readback differs from local qualification')

    _, contract = receipt('organization_contract', report['contract'])
    _, parent_contract = receipt('organization_parent_contract', report['parent_contract'])
    _, parent = receipt('organization_source_route', report['source_full_route'])
    _, prior_manifest = receipt('organization_prior_candidate', parent['source_candidate'])
    _, prior = receipt('organization_prior_validation', dict(path=prior_manifest['report'],sha256=prior_manifest['report_sha256']))
    _, watch = receipt('organization_original_roles', prior['evidence']['watchlist.json'])
    _, prior_plan = receipt('organization_prior_plan', prior['plan'])
    _, origin_manifest = receipt('organization_scope_origin', prior['source_full_route'])
    origin_path, origin = receipt('organization_scope_measurement', origin_manifest['measurement'], artifacts=True, settled=True)
    _, source = receipt('organization_scope_context', dict(path=str((origin_path.parent/'context.json').relative_to(root)),
        sha256=origin['artifacts_sha256']['context.json']))
    _, original = receipt('organization_original_budget', contract['preserved_budget_contract'])
    _, area_reference = receipt('organization_area_reference', contract['area_reference']['measurement'], artifacts=True, settled=True)
    if (parent['selected_database']['sha256'] != before['database_sha256'] or
            parent['contract'] != report['parent_contract'] or prior['contract'] != report['parent_contract'] or
            contract['parent_path_contract'] != report['parent_contract'] or
            contract['source_database_sha256'] != before['database_sha256'] or
            after['database_sha256'] != measure['source_database_sha256'] or
            source['database_sha256'] != parent_contract['source_database_sha256'] or
            any(contract[k] != parent_contract[k] for k in ('scope','preserved_budget_contract','area_reference'))):
        raise ValueError('Unlinked organization scope or original budget ancestry')
    area = validate_preserved_budgets(contract, original, area_reference)
    ownership = json.loads((design/'state-ownership.json').read_text())
    roles = json.loads((design/'path-roles.json').read_text())
    coverage = path_inventory(source, before, ownership, roles, contract['scope'], watch, prior_plan)
    candidate = path_inventory(source, after, ownership, roles, contract['scope'], watch, prior_plan)
    _, saved_before = receipt('organization_before_scope', report['evidence']['before-coverage.json'])
    _, saved_after = receipt('organization_after_scope', report['evidence']['after-coverage.json'])
    _, saved_descriptor = receipt('organization_measurement_plan', report['evidence']['measurement-plan.json'])
    descriptor = measurement_plan(plan, before)
    if coverage != saved_before or candidate != saved_after or descriptor != saved_descriptor:
        raise ValueError('Organization scope or incident connections changed')
    _, measurements = receipt('organization_measurements', report['evidence']['measurements.json'])
    _, saved_acceptance = receipt('organization_acceptance', report['evidence']['acceptance.json'])
    collection_path, collection = receipt('organization_collection', report['evidence']['connections/collection.json'], artifacts=True, settled=True)
    if (not collection.get('source_unchanged') or
            collection['inputs_sha256'].get(str(root/measure['source_database'])) != after['database_sha256']):
        raise ValueError('Unlinked organization raw collection')
    names = {r['net'] for r in candidate['connections']}
    for corner in measure['fresh_timing']:
        raw = collection_path.parent/'after'/corner/'connections.rpt'
        if (sha(raw) != collection['artifacts_sha256'].get(str(raw.relative_to(collection_path.parent))) or
                parse_measurements(raw.read_text(), names) != measurements[corner]):
            raise ValueError('Organization measurements differ from raw records')
    timing_path = collection_path.parent/'after/fresh-timing.json'
    if (sha(timing_path) != collection['artifacts_sha256'].get('after/fresh-timing.json') or
            json.loads(timing_path.read_text()) != measure['fresh_timing']):
        raise ValueError('Organization timing differs from complete collection')
    for context, measured in [(before,reference),(after,measure)]:
        actual = sum((i['bbox'][2]-i['bbox'][0])*(i['bbox'][3]-i['bbox'][1]) for i in context['instances'].values())
        if not math.isclose(actual, measured['placed_instance_area_um2'], rel_tol=0, abs_tol=1e-4):
            raise ValueError('Organization area differs from saved footprints')
    acceptance = qualify_candidate(contract, coverage, candidate, descriptor, measurements,
        measure['fresh_timing'], area, measure['placed_instance_area_um2'])
    if acceptance != saved_acceptance or not acceptance['quantitative_gates_passed']:
        raise ValueError('Organization candidate fails the original quantitative gates')
    access_path, access = receipt('organization_pin_access', report['evidence']['pin-access/report.json'], artifacts=True, settled=True)
    if (access['source_database_sha256'] != after['database_sha256'] or
            pin_access_summary((access_path.parent/'pin-access.log').read_text()) != access['pin_access'] or
            access['pin_access']['decision'] != 'pass'):
        raise ValueError('Unlinked or failed organization pin access')
    return dict(contract_sha256=report['contract']['sha256'], covered_connections=len(names),
        reserve_fraction=contract['reserve_fraction'], timing_floors_ns=contract['timing_floors_ns'],
        cumulative_area_reference_um2=area, max_added_area_fraction=contract['max_added_area_fraction'],
        quantitative_gates_recomputed=True, exact_plan_recomputed=True, declared_roles_recomputed=True,
        helpers_sha256={name:sha(root/'scripts'/name) for name in
            ('physical_organization_route.py','physical_organization_edits.py','physical_path_contract.py',
             'physical_distribution_acceptance.py','physical_organization.py')},
        boundary='Declared local organization admitted to one coarse route; all original budgets remain required afterwards.')
