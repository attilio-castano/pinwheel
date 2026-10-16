"""Single-use exact timing ECO, <=120 seconds all-in, root headroom required."""
import argparse,datetime,math,shutil,time
from pathlib import Path
from common import ROOT,execute,sha,read,write
HERE=Path(__file__).resolve().parent

def rehash(mapping):
    for name,digest in mapping.items():
        p=Path(name) if Path(name).is_absolute() else ROOT/name
        assert p.is_file() and sha(p)==digest,name

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--selection',type=Path,required=True);parser.add_argument('--headroom',type=Path,required=True);parser.add_argument('--tag',default='tt-buffered-timing-eco-edit-01');args=parser.parse_args();started=time.monotonic()
    assert args.tag=='tt-buffered-timing-eco-edit-01','Exactly one authorized physical candidate'
    prepared=read(HERE/'prepared.json');rehash(prepared['source_sha256']);rehash(prepared['tool_sha256'])
    selection=read(args.selection);plan=read(HERE/'plan.json');headroom=read(args.headroom)
    assert selection['schema']=='pinwheel-buffered-tt-timing-eco-selection-v1'
    assert selection['one_candidate_only'] and selection['routing_iterations']==10
    assert selection['source_database_sha256']==plan['source_database_sha256']
    assert headroom['schema']=='pinwheel-buffered-tt-timing-eco-headroom-gate-v1' and headroom['status']=='passed'
    assert headroom['all_24_endpoint_setup_at_least_1ns'] and headroom['owned_absence_confirmed']
    assert set(headroom['endpoints'])==set(plan['allowed_original_sink_rewires'])
    rehash(headroom['source_sha256']);native=read(ROOT/headroom['native_report']['path']);assert native['status']=='passed' and native['exit_code']==0 and native['inputs_unchanged'] and native['container_termination']['status']=='absent'
    assert sha(ROOT/headroom['native_report']['path'])==headroom['native_report']['sha256']
    assert len(headroom['corners'])==3 and all(v['setup_slack_ns']>=1 for c in headroom['corners'].values() for v in c.values())
    # The root selection is sealed after prepared tools; its hashes are independent.
    for key in ('tool_sha256','source_custody_sha256'):
        if key in selection:rehash(selection[key])
    out=ROOT/'build/physical'/args.tag;assert not out.exists(),'Immutable single-use native ECO'
    deadline=datetime.datetime.fromisoformat(selection.get('deadline_utc','2026-10-13T16:29:27Z').replace('Z','+00:00'));remaining=(deadline-datetime.datetime.now(datetime.timezone.utc)).total_seconds();assert remaining>=180,'Insufficient deadline allowance for cap+60s'
    out.mkdir()
    for p in HERE.iterdir():
        if p.is_file():shutil.copyfile(p,out/p.name)
        elif p.name in ('identity','lib'):shutil.copytree(p,out/p.name)
    shutil.copyfile(ROOT/plan['source_database'],out/'input.odb');assert sha(out/'input.odb')==plan['source_database_sha256']
    shutil.copyfile(ROOT/plan['source_native_inventory'],out/'source-inventory.json')
    paths=[Path(n) if Path(n).is_absolute() else ROOT/n for n in prepared['source_sha256']]+[Path(n) if Path(n).is_absolute() else ROOT/n for n in prepared['tool_sha256']]+[HERE/'prepared.json',args.selection.resolve(),args.headroom.resolve(),out/'input.odb',out/'source-inventory.json']
    paths += list(out.rglob('*.py'))+list(out.rglob('*.lib'))+[out/'plan.json',out/'edit.tcl']
    work=min(65,math.floor(120-(time.monotonic()-started)-55));assert work>0
    report=execute(out,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=work,cpus=1,memory='1g',schema='pinwheel-buffered-tt-timing-eco-producer-v1',scope='Exactly2function-preservingresizes+8terminalidentitydelaystages; no optimizer/DPL/GPL/CTS/routing; source95f0 originalR0. Native legal/PG/fullsnapshot/allcornerfunctionidentity gates.',extra={'network':'none','overall_bound_seconds':120,'cleanup_reserve_seconds':50,'host_hash_reserve_seconds':5,'selection_sha256':sha(args.selection),'headroom_gate_sha256':sha(args.headroom),'prepared_sha256':sha(HERE/'prepared.json'),'plan_sha256':sha(HERE/'plan.json'),'source_database':plan['source_database'],'source_database_sha256':plan['source_database_sha256'],'source_original_state':plan['source_original_state'],'source_original_state_sha256':plan['source_original_state_sha256'],'original_LibreLane_reference_status':'failed','original_reference_power_counter':30396,'original_reference_failure_not_relabelled':True,'container_design_root':'/work/recovery'},expected_hashes={out/'input.odb':plan['source_database_sha256']})
    if report['status']=='passed':
        proof=read(out/'change-proof.json');assert proof['exact_edit_gate_passed']
        descriptor={'schema':'pinwheel-buffered-tt-timing-eco-checkpoint-v1','odb':'/work/recovery/candidate.odb','nl':'/work/recovery/after.v','container_design_root':'/work/recovery','source_original_state':plan['source_original_state'],'source_original_state_sha256':plan['source_original_state_sha256'],'source_database':plan['source_database'],'source_database_sha256':plan['source_database_sha256'],'plan_sha256':sha(HERE/'plan.json'),'change_proof_sha256':sha(out/'change-proof.json'),'output_database_sha256':sha(out/'candidate.odb'),'output_netlist_sha256':sha(out/'after.v'),'boundary':'Scratch checkpoint without inherited metrics. Exact8noninvertingDdelays+2samefunctionresizes; originalfailed30396 remains separate; no timing/routing/signoff claim.'}
        write(out/'checkpoint.json',descriptor);report['completed_descriptor']=str((out/'checkpoint.json').relative_to(ROOT));report['completed_descriptor_sha256']=sha(out/'checkpoint.json');report['artifact_sha256']['checkpoint.json']=sha(out/'checkpoint.json')
    rehash(prepared['source_sha256']);rehash(prepared['tool_sha256'])
    report['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
    if report['all_in_elapsed_seconds']>120:report['status']='bound_exceeded'
    report['all_in_scope']='Source+headroom admission/staging,oneexactnativeedit+legal/PGchecks+serializedfullinventory/functionproof,ownedcleanup,sourcecustody,descriptor; finalreceiptwrite excluded.'
    write(out/'report.json',report);print(out/'report.json');return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
