"""Root-only launch of single LIVE bounded incremental ECO container."""
import argparse,datetime,json,math,shutil,time
from pathlib import Path
from common import ROOT,execute,sha,read,write
H=Path(__file__).resolve().parent
STOP=datetime.datetime.fromisoformat('2026-10-13T17:42:14+00:00').timestamp()
DEADLINE=datetime.datetime.fromisoformat('2026-10-13T17:44:14+00:00').timestamp()
def verify(items):
    for n,h in items.items():
        p=Path(n) if Path(n).is_absolute() else ROOT/n;assert p.is_file() and sha(p)==h,n

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--selection',type=Path,required=True);p.add_argument('--tag',default='tt-buffered-incremental-eco-route-02');a=p.parse_args();started=time.monotonic()
    assert a.tag=='tt-buffered-incremental-eco-route-02';selection=read(a.selection);prepared=read(H/'prepared.json')
    assert selection['schema']=='pinwheel-buffered-tt-incremental-eco-selection-v1' and selection['routing_iterations']==10
    assert sha(ROOT/prepared['source_database'])==prepared['source_database_sha256']=='95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
    verify(prepared['source_sha256']);verify(prepared['tool_sha256'])
    verification=read(ROOT/prepared['executable_verification']['path']);assert sha(ROOT/prepared['executable_verification']['path'])==prepared['executable_verification']['sha256']
    assert verification['status']=='passed' and verification['exit_code']==0 and verification['inputs_unchanged'] and verification['container_termination']['status']=='absent'
    out=ROOT/'build/physical'/a.tag;assert not out.exists(),'Single-use immutable LIVE experiment';assert STOP-time.time()>350,'Insufficient native stop allowance'
    out.mkdir()
    for f in H.iterdir():
        if f.is_file():shutil.copyfile(f,out/f.name)
        elif f.name in ('identity','lib'):shutil.copytree(f,out/f.name)
    prior=ROOT/'build/physical/tt-buffered-timing-eco-control-route-01'
    source=ROOT/prepared['source_database'];shutil.copyfile(source,out/'postcts.odb');shutil.copyfile(prior/'before.v',out/'reference.v')
    for n in ('baseline-env.tcl','corner-env.tcl','core.sdc'):shutil.copyfile(prior/n,out/n)
    for f in (prior/'lib').glob('*.lib'):shutil.copyfile(f,out/'lib'/f.name)
    phase_inputs={str(Path('/work/diagnostic')/f.relative_to(out)):sha(f) for f in out.rglob('*') if f.is_file()}
    write(out/'phase-inputs.json',phase_inputs)
    paths=[a.selection.resolve(),H/'prepared.json',*[ROOT/n if not Path(n).is_absolute() else Path(n) for n in prepared['source_sha256']],*[ROOT/n if not Path(n).is_absolute() else Path(n) for n in prepared['tool_sha256']],*list(out.rglob('*'))]
    paths=[f for f in paths if f.is_file()]
    work=min(300,math.floor(350-(time.monotonic()-started)-50),math.floor(STOP-time.time()));assert work>0
    report=execute(out,paths,['python3','-B','/work/diagnostic/coordinator.py'],seconds=work,cpus=4,memory='3g',schema='pinwheel-buffered-tt-incremental-eco-route-v1',scope='ONE live originalR0 10iteration GRT baseline→no-opincrementalguard→same2resizes8delayECO→incremental22signalnetmax. All332CLOCK/allunrelatedroutes frozen; no coldimport/GPL/DPL/CTS/repair. Separate3cornerrouteRC andfinitefunctional gates.',extra={'network':'none','selection_sha256':sha(a.selection),'prepared_sha256':sha(H/'prepared.json'),'executable_verification_sha256':prepared['executable_verification']['sha256'],'source_database':prepared['source_database'],'source_database_sha256':prepared['source_database_sha256'],'exact_plan_sha256':sha(H/'plan.json'),'overall_bound_seconds':350,'native_stop_utc':'2026-10-13T17:42:14Z','deadline_utc':'2026-10-13T17:44:14Z','reference_native_flow_status':'failed','reference_native_flow_exit_code':2,'reference_inherited_power_count':30396},expected_hashes={out/'postcts.odb':prepared['source_database_sha256']})
    # common.execute captures root files; bind every nested phase artifact too.
    report['artifact_sha256'].update({str(f.relative_to(out)):sha(f) for f in sorted(out.rglob('*')) if f.is_file() and str(f.resolve()) not in report['input_sha256'] and f.name!='report.json'})
    verify(prepared['source_sha256']);verify(prepared['tool_sha256']);report['all_in_elapsed_seconds']=round(time.monotonic()-started,3)
    if report['all_in_elapsed_seconds']>350 or time.time()>DEADLINE:report['status']='bound_exceeded'
    write(out/'report.json',report);print(out/'report.json');return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
