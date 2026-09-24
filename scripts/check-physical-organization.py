#!/usr/bin/env python3
"""Reconstruct a saved distribution and cost policy choices without running CAD."""
import argparse
from datetime import datetime, timezone
from fnmatch import fnmatch
import json
from pathlib import Path
import sys
import time

from physical_connections import parse_measurements
from physical_distribution import inventory
from physical_organization import Library, Planner, BufferGeometry, portfolios, screen_exchange_identity, validate_refinement, mechanism_screen
from physical_path_contract import validate_preserved_budgets
from validation_run import fresh_directory, sha


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-manifest',type=Path,required=True)
    ap.add_argument('--policy',type=Path,required=True)
    ap.add_argument('--refinement',type=Path,help='Optional bounded relocation and weak-branch exchange policy')
    ap.add_argument('--check-tag',required=True)
    args=ap.parse_args();root=Path.cwd();started=time.monotonic()
    out=fresh_directory(root/'build/validation',args.check_tag);inputs={}
    def read(path,digest=None):
        path=root/path
        if digest is not None and sha(path)!=digest:raise ValueError('Changed input: '+str(path))
        inputs[str(path)]=sha(path)
        return json.loads(path.read_text())
    def reference(ref):return read(Path(ref['path']),ref['sha256'])
    def verify_artifacts(path,data):
        for name,digest in data.get('artifacts_sha256',{}).items():
            file=root/path.parent/name
            if sha(file)!=digest:raise ValueError('Changed saved artifact: '+str(file))
            inputs[str(file)]=digest
    def write(name,value):
        with (out/name).open('x') as output:output.write(json.dumps(value,indent=2)+'\n')
    manifest=read(args.source_manifest)
    source=read(Path(manifest['report']),manifest['report_sha256'])
    if source['status']!='passed' or not source['collection_pass']:raise ValueError('Require completed source collection')
    for key in ['selected_database','selected_netlist','contract','measurement','invocation','distribution','area']:
        if manifest[key]!=source[key]:raise ValueError('Source manifest differs from bound report')
    verify_artifacts(Path(manifest['report']),source)
    for key in ['selected_database','selected_netlist']:
        ref=source[key];path=root/ref['path']
        if sha(path)!=ref['sha256']:raise ValueError('Changed selected artifact')
        inputs[str(path)]=ref['sha256']
    diagnostic=reference(source['measurement']);verify_artifacts(Path(source['measurement']['path']),diagnostic)
    diag_dir=Path(source['measurement']['path']).parent
    context=read(diag_dir/'context.json');invocation=reference(source['invocation'])
    design=Path('build/physical')/invocation['design']
    ownership=read(design/'state-ownership.json');roles=read(design/'path-roles.json')
    resolved=read(design/'runs'/diagnostic['physical_tag']/'resolved.json')
    contract=reference(source['contract']);original=reference(contract['preserved_budget_contract'])
    area_reference=reference(contract['area_reference']['measurement'])
    validate_preserved_budgets(contract,original,area_reference)
    policy=read(args.policy)
    if policy['contract_sha256']!=source['contract']['sha256']:raise ValueError('Policy changed the source budget contract')
    refinement=read(args.refinement) if args.refinement else None
    if refinement:
        if refinement['base_policy_sha256']!=sha(args.policy):raise ValueError('Refinement changed the base policy')
        validate_refinement(refinement,policy,context)
    collection=reference(source['evidence']['connections/collection.json'])
    collection_dir=Path(source['evidence']['connections/collection.json']['path']).parent
    verify_artifacts(Path(source['evidence']['connections/collection.json']['path']),collection)
    if not collection['source_unchanged'] or set(collection['containers'].values())!={'absent'}:
        raise ValueError('Require a settled immutable collection')
    geometry=read(collection_dir/'geometry.json')['after']
    full=reference(source['evidence']['inventory.json'])
    saved=reference(source['evidence']['measurements.json'])
    acceptance=reference(source['evidence']['acceptance.json'])
    for corner in saved:
        text=(root/collection_dir/'after'/corner/'connections.rpt').read_text()
        if parse_measurements(text,{r['net'] for r in full['connections']})!=saved[corner]:
            raise ValueError('Saved measurement differs from its raw report')
    coverage=inventory(context,ownership,roles,contract['scope']['distribution'])
    targets=sorted(r['net'] for r in acceptance['connections'] if r['verdict']!='within_trial_reserve')
    records={r['net']:r for r in coverage['connections']}
    if not targets or not set(targets)<=set(records):raise ValueError('Residual target outside distribution policy scope')
    if set(context['nets'])==set():raise ValueError('Empty source checkpoint')
    pdk=Path(invocation['pdk_root']);installed=read(pdk/'installed.json',invocation['pdk_receipt_sha256'])
    def local_file(name):
        if name.startswith('/work/pdk/'):return pdk/name.removeprefix('/work/pdk/')
        if name.startswith('/work/core/'):return root/design/name.removeprefix('/work/core/')
        raise ValueError('Unsupported pinned library location')
    texts={}
    for corner in sorted(saved):
        paths=[local_file(p) for p in resolved['CELL_LIBS'][corner] if '/sg13cmos5l_stdcell/' in p]
        if len(paths)!=1:raise ValueError('Require one standard-cell library per corner')
        for macro in resolved['MACROS'].values():
            matches=[p for pattern,files in macro['lib'].items() if fnmatch(corner,pattern) for p in files]
            if len(matches)!=1:raise ValueError('Ambiguous macro library corner')
            paths.append(local_file(matches[0]))
        texts[corner]=[]
        for path in paths:
            digest=sha(path)
            if path.is_relative_to(pdk):
                expected=installed['files_sha256'][str(path.relative_to(pdk))]
            else:
                expected=invocation['snapshot_files_sha256'][str(path.relative_to(root/design/'experiments'/diagnostic['physical_tag']))]
            if digest!=expected:raise ValueError('Changed pinned library: '+str(path))
            inputs[str(path)]=digest;texts[corner].append(path.read_text())
    library=Library(texts)
    planner=Planner(context,coverage,geometry,saved,library,policy,contract)
    if abs(planner.current_area-source['area']['candidate_um2'])>1e-4:raise ValueError('Area reconstruction failed')
    by_root={}
    for net in targets:by_root.setdefault(records[net]['distribution_root'],[]).append(net)
    affected={n for t in planner.model['trees'] if t['root'] in by_root for n in t['nets']}
    pins_checked=planner.reconcile_pins(affected)
    candidates=[]
    for root_net,nets in sorted(by_root.items()):
        for cell in policy['resize_cells']:
            candidate=planner.resize(root_net,nets,cell)
            if candidate is not None:candidates.append(candidate)
        exchange=planner.exchange(root_net,nets);candidates.append(exchange)
        if refinement:
            rule=refinement['exchange']
            candidates.append(planner.exchange(root_net,nets,objective=rule['objective'],max_passes=rule['max_passes']))
        for net in nets:
            if any(context['instances'][p.rsplit('/',1)[0]]['macro'] for p in records[net]['consumers']):
                for cell in sorted(planner.sizes):candidates.append(planner.receiver(root_net,net,cell))
    if refinement:
        lef=pdk/'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_stdcell.lef'
        digest=sha(lef)
        if digest!=installed['files_sha256'][str(lef.relative_to(pdk))]:raise ValueError('Changed pinned buffer LEF')
        inputs[str(lef)]=digest;move=refinement['relocation']
        if planner.pin_net[move['instance']+'/X'] not in targets:raise ValueError('Relocation outside residual scope')
        masters=BufferGeometry(lef.read_text(),[context['instances'][move['instance']]['cell'],move['cell']],context['dbu_per_micron'])
        candidates.extend(planner.relocate(move,masters))
    readback_name='functional/after.json'
    readback=read(Path(manifest['report']).parent/readback_name,source['artifacts_sha256'][readback_name])
    module=readback['modules']['tt_um_pinwheel'];virtual_checks=0
    for index,candidate in enumerate(candidates):
        candidate['id']=f'candidate-{index:02d}'
        candidate['mechanism_screen']=mechanism_screen(candidate,saved,contract['reserve_fraction'])
        if candidate['kind']=='exchange_leaf_consumers' and candidate['edits']:
            candidate['virtual_identity']=screen_exchange_identity(module,candidate['edits']);virtual_checks+=1
    combinations=portfolios(candidates,targets,planner.current_area,planner.area_limit)
    eligible=[p for p in combinations if p['area_screen_pass'] and p['combined_footprints_disjoint']]
    by_id={c['id']:c for c in candidates}
    for portfolio in combinations:
        portfolio['pass_conditional_mechanism_screen']=all(by_id[i]['mechanism_screen']['pass_conditional_screen'] for i in portfolio['candidates'])
    screened=[p for p in eligible if p['pass_conditional_mechanism_screen']]
    write('organization.json',planner.model);write('coverage.json',coverage)
    write('candidates.json',candidates);write('portfolios.json',combinations)
    # Cost the complete stronger-driver arm even when footprints reject it.
    minimum_resize=sum(min(c['added_area_um2'] for c in candidates if c['root']==r and c['kind']=='resize_buffer') for r in by_root)
    sources=['physical_organization.py','check-physical-organization.py','physical_distribution.py',
        'physical_connections.py','physical_repair_plan.py','physical_path_contract.py','physical_buffer_repair.py',
        'physical_floorplan.py','mapped_physical.py','tiled_chip.py','validation_run.py']
    report=dict(schema=1,status='passed',recorded_at_utc=datetime.now(timezone.utc).isoformat(),
        source_manifest=dict(path=str(args.source_manifest),sha256=sha(args.source_manifest)),
        source_database=source['selected_database'],source_netlist=source['selected_netlist'],
        policy=dict(path=str(args.policy),sha256=sha(args.policy)),contract=source['contract'],
        refinement=dict(path=str(args.refinement),sha256=sha(args.refinement)) if refinement else None,
        reconstructed=dict(trees=len(planner.model['trees']),branches=planner.model['branch_count'],
            transport_cells=planner.model['transport_count'],buffers=planner.model['buffer_count'],
            delay_cells=planner.model['delay_count'],transport_area_um2=planner.model['transport_area_um2'],
            leaves=planner.model['leaf_count'],total_instance_area_um2=planner.current_area,
            complete_path_contract_connections=len(full['connections'])),
        scope=dict(targets=targets,affected_roots=sorted(by_root),affected_branches=len(affected),
            independent_library_pin_corner_checks=pins_checked),
        area=dict(original_um2=contract['area_reference']['area_um2'],current_um2=planner.current_area,
            cap_um2=planner.area_limit,remaining_um2=planner.area_limit-planner.current_area,
            minimum_complete_resize_um2=minimum_resize),
        comparison=dict(candidates=len(candidates),complete_portfolios=len(combinations),
            affordable_footprint_screened_portfolios=len(eligible),eligible=eligible,
            virtual_exchange_identity_checks=virtual_checks,
            conditional_mechanism_screened_portfolios=len(screened),conditionally_screened=screened,
            search_boundary='Bounded greedy exchanges, uniform per-tree residual resizes, one macro receiver, and optionally one bounded same-row move/resize; not an exhaustive search.'),
        unchanged_timing_floors=contract['timing_floors_ns'],reserve_fraction=contract['reserve_fraction'],
        execution_admitted=False,repair_executed=False,new_whole_chip_route=False,
        physical_qualification=False,congestion_diagnosed=False,
        boundary=['Candidate topology and geometric cost only; no source database or netlist is edited.',
            'Pin capacitance is reconciled with independent saved STA. New wire loads, slew and setup/hold remain unmeasured.',
            'Virtual branch exchanges preserve buffer-contracted connectivity in the saved independent netlist readback; actual edits still require new independent readback.',
            'The unchanged whole-chip contract and original cumulative budgets remain required.',
            'The unresolved 22/21 congestion discrepancy is not used to rank geometric candidates.'],
        inputs_sha256=inputs,source_sha256={str(Path('scripts')/n):sha(root/'scripts'/n) for n in sources},
        elapsed_seconds=round(time.monotonic()-started,3))
    report['artifacts_sha256']={p.name:sha(p) for p in out.iterdir() if p.is_file()}
    write('report.json',report)
    print(json.dumps({k:report[k] for k in ['status','reconstructed','scope','area','comparison','elapsed_seconds']},indent=2))


if __name__=='__main__':main()
