"""Source-bound fresh exact-arm global-route RC STA; root owns native launch."""
import argparse,math,re,shutil,sys,time
from pathlib import Path
from common import ROOT,IMAGE,execute,read,sha,write
from segments import parse_segments
SOURCE='95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
TOOLS=Path(__file__).resolve().parent

def hashes(values,base=ROOT):
    for name,digest in values.items():
        p=Path(name);assert sha(p if p.is_absolute() else base/p)==digest,('Changed input',name)

def route_guard(receipt,path,selection,arm):
    assert path.resolve()==(ROOT/'build/physical'/('tt-buffered-route-effort-'+arm+'-route-01')/'report.json').resolve()
    assert receipt['schema']=='pinwheel-buffered-tt-route-effort-route-v1'
    assert receipt['status']=='passed' and receipt['exit_code']==0 and receipt['inputs_unchanged']
    assert receipt['arm']==arm and receipt['source_database_sha256']==receipt['reference_database_sha256']==SOURCE
    assert receipt['selection_sha256']==sha(selection)
    assert receipt['native_extra_iterations']==({'control':5,'probe':10}[arm])
    assert receipt['container_termination']['status']=='absent' and not receipt['container_termination']['owned_container_ids']
    assert receipt['container_termination']['ownership_label']==receipt['ownership_label']
    assert receipt['image_id']==IMAGE and receipt['bounds']['network']=='none'
    hashes(receipt['input_sha256']);hashes(receipt['artifact_sha256'],path.parent)
    m=receipt['measurement'];assert m['status']=='measured' and m['native_frozen_inventory']['all_frozen_native_invariants_passed']
    assert m['native_iterations_per_segment']==receipt['native_extra_iterations']
    assert m['route_segments']['sha256']==receipt['artifact_sha256']['after_grt.segments']
    assert m['exported_netlist_unchanged'] and m['inventory_unchanged']
    ni=m['native_frozen_inventory'];assert ni['canonical_block_NDR_DEF_unchanged'] and ni['block_NDR_via_lists_empty'] and ni['NDR_widths_equal_default_on_all_routing_layers']
    assert sha(path.parent/'before.v')==sha(path.parent/'after.v')
    return m

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--selection',type=Path,required=True);p.add_argument('--arm',choices=('control','probe'),required=True);p.add_argument('--route-report',type=Path,required=True);p.add_argument('--tag',required=True)
    a=p.parse_args();started=time.monotonic();assert a.tag=='tt-buffered-route-effort-'+a.arm+'-timing-01'
    prepared=read(TOOLS/'prepared.json');hashes(prepared['tool_sha256'],TOOLS);hashes(prepared['derivation_sha256'])
    selection=read(a.selection);assert selection['schema']=='pinwheel-buffered-tt-route-effort-selection-v1'
    assert selection['routing_effort']=={'control_iterations':5,'probe_iterations':10}
    for key,path in [('intake',ROOT/prepared['intake']['path']),('timing_tools',TOOLS/'prepared.json')]:
        r=selection['references'][key];assert (ROOT/r['path']).resolve()==path.resolve() and r['sha256']==sha(path)
    for r in selection['references'].values():assert sha(ROOT/r['path'])==r['sha256']
    intake_path=ROOT/prepared['intake']['path'];intake=read(intake_path)
    assert sha(intake_path)==prepared['intake']['sha256'] and intake['schema']=='pinwheel-buffered-tt-route-effort-intake-v1' and intake['status']=='passed'
    hashes(intake['custody_sha256'])
    for key in ('protected_sources_sha256','prior_current_source_sha256','references_sha256','original_checkpoint_views_sha256','original_recipe_sha256'):hashes(intake[key])
    for name,r in intake['prior_manifests'].items():assert sha(ROOT/name)==r['sha256'];hashes(r['evidence_sha256'])
    ref=intake['source_checkpoint'];recipe=ROOT/ref['design'];source=ROOT/ref['database'];state=ROOT/ref['state'];env=ROOT/ref['environment']
    assert sha(source)==ref['database_sha256']==SOURCE and sha(state)==ref['state_sha256'] and sha(env)==ref['environment_sha256']
    route_path=a.route_report.resolve();route=read(route_path);route_measure=route_guard(route,route_path,a.selection,a.arm);arm_root=route_path.parent
    database=arm_root/'routed.odb';segments=arm_root/'after_grt.segments';segment_data=parse_segments(segments)
    assert sha(database)==route['artifact_sha256']['routed.odb']
    snapshot=read(arm_root/'after-inventory.json');post_ndr={n:r['nondefault_rule'] for n,r in snapshot['nets'].items()}
    assert len(post_ndr)==route_measure['native_frozen_inventory']['whole_net_count']
    assert {r[0] for r in snapshot['nondefault_rules']}=={'CTS_NDR_0','CTS_NDR_1'}
    prior=ROOT/'build/physical/tt-buffered-postcts-timing-01';pi=read(prior/'inputs.json');pr=read(prior/'report.json')
    assert sha(recipe/'core.sdc')==pi['files']['core.sdc']['sha256']
    out=ROOT/'build/physical'/a.tag;out.mkdir()
    paths=[source,state,env,database,segments,route_path,a.selection,intake_path,TOOLS/'prepared.json',prior/'inputs.json',prior/'report.json',recipe/'core.sdc',recipe/'core.json',*[TOOLS/name for name in prepared['tool_sha256']],*[Path(n) for n in route['input_sha256']],*[arm_root/n for n in route['artifact_sha256']],*[Path(n) for n in intake['protected_sources_sha256']]]
    expected={str(database):sha(database),str(segments):sha(segments)}
    def copy(path,name):
        target=out/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,target);assert sha(path)==sha(target);paths.extend((path,target));expected[str(target.resolve())]=sha(path);return target
    copy(database,'checkpoint.odb');copy(segments,'after_grt.segments');copy(recipe/'core.sdc','core.sdc');copy(arm_root/'baseline-env.tcl','baseline-env.tcl')
    retained_route_env=ROOT/'build/physical/tt-buffered-access-incremental-control-route-01/baseline-env.tcl'
    assert sha(arm_root/'baseline-env.tcl')==sha(retained_route_env);paths.append(retained_route_env)
    for name in ('timing-worker.py','segments.py','route-corner.tcl'):copy(TOOLS/name,name)
    for entry in pi['corners']:
        for relative in entry['libs']:
            retained=pi['files'][relative];name=Path(relative).name;path=recipe/'macro'/name if name.startswith('RM_') else ROOT/retained['source_path'];assert sha(path)==retained['sha256'];copy(path,relative)
    assert len(list((out/'lib').glob('*.lib')))==9
    native_scripts=dict(pr['native_script_sha256'])
    retained_native=ROOT/'build/physical/tt-buffered-access-incremental-control-route-01/native-scripts'
    for name in ('openroad/common/set_routing_layers.tcl','openroad/common/set_layer_adjustments.tcl'):
        path=retained_native/name;native_scripts[name]=sha(path);paths.append(path)
    scope='Fresh3corner RC estimates from exact completed arm global-route segments and routedODB; same9libs/SDC/env and originalfixedplacements/NL/PG. No placement RC fallback, inherited SPEF/SDF, optimization, extracted timing or signoff. Conditional fast uses -40C logic/I/O and -55C SRAM. NativeNDR fallback may remain internal; all route/pin-layer widths equal defaults, so this estimator width term is neutral; NDRspacing/coupling/detailedvia choices are outside this estimator.'
    inputs=dict(corners=pi['corners'],native_script_sha256=native_scripts,route_source_report_sha256=sha(route_path),routed_database_sha256=sha(database),route_segments_sha256=sha(segments),netlist_sha256=sha(arm_root/'after.v'),post_route_ndr_map=post_ndr,canonical_block_NDR_DEF_sha256=route_measure['native_frozen_inventory']['canonical_block_NDR_DEF_sha256'],scope=scope,original_source_database_sha256=SOURCE,segment_summary={k:v for k,v in segment_data.items() if k!='nets'},runtime_NDR_fallback_net_order=route_measure['native_clock_ndr_fallback_net_order'])
    write(out/'inputs.json',inputs);paths.append(out/'inputs.json')
    stage=time.monotonic()-started;assert stage<=5,('Staging exceeded5s reserve',stage);work=min(115,math.floor(170-stage-50));assert work>0
    report=execute(out,paths,['python3','-B','/work/diagnostic/timing-worker.py'],seconds=work,cpus=3,memory='3g',schema='pinwheel-buffered-tt-route-effort-timing-v1',scope=scope,expected_hashes=expected,
        extra=dict(arm=a.arm,route_based_only=True,parasitic_model='estimate_parasitics -global_routing',source_database=str(database.relative_to(ROOT)),source_database_sha256=sha(database),routed_database_sha256=sha(database),route_segments_sha256=sha(segments),route_source_report=str(route_path.relative_to(ROOT)),route_source_report_sha256=sha(route_path),reference_database_sha256=SOURCE,selection_sha256=sha(a.selection),exact_library_count=9,clock_period_ns=20,io_max_ns=4,io_min_ns=.2,source_reference_native_flow_status='failed',source_reference_native_flow_exit_code=2,source_reference_inherited_power_count=30396,fresh_native_checks_waived=False,placement_estimate_reproduction_asserted=False))
    if report['status']=='passed':
        m=report['measurement'];assert m['route_based_only'] and m['route_segments_sha256']==sha(segments) and m['routed_database_sha256']==sha(database)
        assert set(m['corners'])=={e['name'] for e in pi['corners']}
    report['all_in_elapsed_seconds']=round(time.monotonic()-started,3);report['host_staging_seconds']=round(stage,3);report['overall_bound_seconds']=170
    report['all_in_scope']='Source staging<=5s, Dockerwork<=115s, ownedcleanup<=50s, source/artifact recustody; finalreceiptwrite/print excluded.'
    if report['all_in_elapsed_seconds']>170:report['status']='bound_exceeded'
    write(out/'report.json',report);print(out/'report.json',flush=True);return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
