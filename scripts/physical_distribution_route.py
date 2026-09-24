"""Recompute the distribution contract before admitting its exact local candidate."""
import json

from physical_connections import connection_terminals, parse_measurements
from physical_distribution import inventory, assess, validate_contract
from physical_distribution_acceptance import qualify_candidate
from physical_floorplan import overlaps
from validation_run import sha


def validate_distribution_evidence(report, contexts, measure, reference, design, root, receipt, immediate):
    before,after=contexts
    if not report.get('local_distribution_contract_pass') or not report.get('local_electrical_pass'):
        raise ValueError('Distribution candidate lacks a local contract pass')
    _,preparation=receipt('distribution_preparation',report['source_preparation'])
    _,contract=receipt('distribution_contract',report['contract'])
    _,plan=receipt('distribution_plan',report['plan'])
    if (report['contract']!=preparation['candidate']['contract'] or report['plan']!=preparation['candidate']['plan'] or
            preparation['source_database']['sha256']!=before['database_sha256'] or
            measure['source_database_sha256']!=after['database_sha256']):
        raise ValueError('Unlinked distribution preparation, contract or candidate')
    ownership=json.loads((design/'state-ownership.json').read_text())
    roles=json.loads((design/'path-roles.json').read_text())
    coverage=inventory(before,ownership,roles,contract['scope'])
    candidate=inventory(after,ownership,roles,contract['scope'])
    _,saved_coverage=receipt('distribution_source_inventory',preparation['evidence']['inventory'])
    _,saved_assessment=receipt('distribution_source_assessment',preparation['evidence']['assessment'])
    _,source_measurements=receipt('distribution_source_measurements',preparation['evidence']['parsed_measurements'])
    assessment=assess(coverage['connections'],source_measurements,sorted(reference['fresh_timing']),contract['reserve_fraction'])
    if coverage!=saved_coverage or assessment!=saved_assessment:
        raise ValueError('Changed source distribution coverage or measured selection')
    validate_contract(contract,coverage,assessment,plan,before,reference['fresh_timing'])
    _,saved_candidate=receipt('distribution_inventory',report['evidence']['inventory.json'])
    _,measurements=receipt('distribution_measurements',report['evidence']['measurements.json'])
    _,saved_acceptance=receipt('distribution_acceptance',report['evidence']['acceptance.json'])
    collection_path,collection=receipt('distribution_collection',report['evidence']['connections/collection.json'],artifacts=True,settled=True)
    if (candidate!=saved_candidate or not collection.get('source_unchanged') or
            collection['inputs_sha256'].get(str(root/measure['source_database']))!=measure['source_database_sha256']):
        raise ValueError('Unlinked candidate distribution inventory or raw collection')
    names={r['net'] for r in candidate['connections']}
    for corner in measure['fresh_timing']:
        raw=collection_path.parent/'after'/corner/'connections.rpt'
        if (sha(raw)!=collection['artifacts_sha256'].get(str(raw.relative_to(collection_path.parent))) or
                parse_measurements(raw.read_text(),names)!=measurements[corner]):
            raise ValueError('Distribution records differ from raw candidate measurements')
    measured=qualify_candidate(contract,coverage,candidate,plan,measurements,measure['fresh_timing'],
        reference['placed_instance_area_um2'],measure['placed_instance_area_um2'])
    if measured!=saved_acceptance or not measured['quantitative_gates_passed']:
        raise ValueError('Distribution candidate fails fixed quantitative gates')
    validate_exact_edit(plan,before,after,immediate)
    return dict(contract_sha256=report['contract']['sha256'],covered_connections=len(names),
        reserve_fraction=contract['reserve_fraction'],timing_floors_ns=contract['timing_floors_ns'],
        quantitative_gates_recomputed=True,exact_plan_recomputed=True,
        boundary='Local qualification only; the same contract must be remeasured after whole-chip routing.')


def validate_exact_edit(plan,before,after,immediate):
    """Require precisely the compiled signal edit and legal added footprints."""
    added={stage['instance'] for op in plan['operations'] for stage in op.get('stages', [op])}
    if set(immediate['added_instances'])!=added:
        raise ValueError('Distribution plan differs from the immediate buffer identity')
    changed=set();new=set()
    for op in plan['operations']:
        changed.add(op['net'])
        stages = op.get('stages', [op])
        new.update(stage['new_net'] for stage in stages)
        if op['mode']=='driver':
            old=dict(driver=stages[-1]['instance']+'/X',consumers=op['consumers'],ports=op['ports'])
            branches = [dict(driver=op['driver'] if i==0 else stages[i-1]['instance']+'/X',
                consumers=[stage['instance']+'/A'],ports=[]) for i,stage in enumerate(stages)]
        else:
            old=dict(driver=op['driver'],consumers=sorted([p for p in op['consumers'] if p!=op['receiver']]+[stages[0]['instance']+'/A']),ports=op['ports'])
            branches = [dict(driver=stage['instance']+'/X',
                consumers=[stages[i+1]['instance']+'/A' if i+1<len(stages) else op['receiver']],ports=[])
                for i,stage in enumerate(stages)]
        if (connection_terminals(after,op['net'])!=old or
                any(connection_terminals(after,stage['new_net'])!=branch for stage,branch in zip(stages,branches))):
            raise ValueError('Distribution consumers differ from the exact plan')
        for stage in stages:
            inst=stage['instance']
            if after['instances'][inst]['cell']!=stage['cell']:
                raise ValueError('Distribution buffer type differs from plan')
            box=after['instances'][inst]['bbox_dbu']
            if (not any(r['bbox_dbu'][0]<=box[0]<box[2]<=r['bbox_dbu'][2] and
                        r['bbox_dbu'][1]<=box[1]<box[3]<=r['bbox_dbu'][3] for r in after['rows']) or
                    any(overlaps(box,i['bbox_dbu']) for n,i in after['instances'].items() if n!=inst) or
                    any(overlaps(box,b['bbox_dbu']) for b in after['placement_blockages'])):
                raise ValueError('Illegal added distribution footprint')
    actual={n for n in before['nets'] if before['nets'][n]!=after['nets'].get(n)
            and before['nets'][n]['type'] not in ['POWER','GROUND']}
    if actual!=changed or after['nets'].keys()-before['nets'].keys()!=new or not before['nets'].keys()<=after['nets'].keys():
        raise ValueError('Distribution edit changed unrelated connections')
