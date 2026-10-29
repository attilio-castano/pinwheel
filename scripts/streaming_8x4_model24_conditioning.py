"""One bounded eight-call residual×interaction experiment; Root alone Native."""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import sys
import subprocess
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_smoke as S
import streaming_8x4_model24_smoke_readback as R
import streaming_8x4_model24_conditioning_parser as Q

P,E,I,K=S.P,S.E,S.I,S.K
ROOT=S.ROOT
NEW=('streaming_8x4_model24_conditioning.py','streaming_8x4_model24_conditioning_parser.py','streaming_8x4_model24_conditioning_readback.py')
SMOKE_LAUNCHER='f11bb3e6df36e4c1de8bbe2edff6ae070c5e4ece4c75581346aa4d97e14082a4'
SOLVER_SOURCE_MANIFEST='bc77f662bc2bf61c255194110255944c71667413f849d597a3dcb8f880577417'
SMOKE_PLAN='dbbea83d261877367eca371b24ef6bae14034528c78d7b1f48df199dafe9b887'
OUTPUT='model24-fullstack-conditioning-01';CONTAINER='pinwheel-'+OUTPUT
write=S.write


def policy():
    return dict(schema='pinwheel.model24-fullstack-conditioning-policy.v1',branches=Q.branches(),maximum_calls=8,
        cpu=1,memory_bytes=6442450944,extra_swap_bytes=0,tmpfs_bytes=536870912,maximum_output_bytes=268435456,
        leaf_seconds=60,work_seconds=540,outer_seconds=600,manual_mesh=K.MESH,unit_m=K.UNIT,
        preconditioner='Jacobi',out_of_core_ratio='0',all_warnings_fatal=True,complete_full_matrix_reciprocity='0.01',
        exact_smoke_geometries_unchanged=True,fresh_baseline_repeated=True,
        if_no_profile_passes_both_geometries='stop conditioning/numerical tuning this campaign',
        passing_profile_is_not_mesh_length_boundary_reference_or_full_universe_qualification=True,
        full_generic_27900_solve_deck_not_admitted=True,postroute_census_before_reduced_envelope_calibration=True,
        model_qualified=False,qualified_timing=False)


def sources():
    pending=list(NEW)+['streaming_8x4_closure24_resources.py'];done={}
    while pending:
        name=pending.pop()
        if name in done:continue
        p=Path(__file__).with_name(name);done[name]=E.sha(p)
        for node in ast.walk(ast.parse(p.read_text())):
            imports=[n.name for n in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            pending += [n+'.py' for n in imports if n.startswith('streaming_') and '.' not in n]
    return dict(sorted(done.items()))


def parent_smoke(launcher):
    P.need(E.sha(launcher)==SMOKE_LAUNCHER,'Exact failed smoke launcher differs')
    row=json.loads(launcher.read_text());a=row['HOST_closeout_argv'];P.need(len(a[3:])%2==0,'Malformed smoke reader argv')
    args=dict(zip(a[3::2],a[4::2]));P.need(set(args)=={'--inputs','--plan-sha256','--runtime','--directory','--resource-report','--command-proposal','--root-go','--output'},'Exact smoke reader argument membership differs')
    closed=R.readback(Path(args['--inputs']),args['--plan-sha256'],Path(args['--runtime']),Path(args['--directory']),Path(args['--resource-report']),Path(args['--command-proposal']),Path(args['--root-go']))
    P.need(closed==json.loads(Path(args['--output']).read_text()) and closed['measurement_packet_completed'] is True
        and closed['smoke_passed'] is False and closed['resource_feasible'] is True,'Actual failed two-geometry complete smoke required')
    return args,closed


def prepare(launcher,output):
    args,closed=parent_smoke(launcher);P.need(not output.exists() and output.parent.is_dir(),'Fresh conditioning preparation required');output.mkdir()
    shutil.copytree(Path(args['--inputs']),output/'smoke-inputs');shutil.copyfile(launcher,output/'smoke-launcher.json');shutil.copyfile(Path(args['--output']),output/'smoke-authority.json')
    source=ROOT/'build/campaigns/8x4-20261022-01/rc-fastercap-iterative-source-intake-01';owned=output/'solver-source';owned.mkdir()
    for n in ('SolveCapacitance.cpp','FasterCapConsole.cpp','SolveCapacitance.h','manifest.json'):shutil.copyfile(source/n,owned/n)
    jobs=[dict(index=c*4+b,case=c,branch=r) for c in range(2) for b,r in enumerate(Q.branches())]
    row=dict(schema='pinwheel.model24-fullstack-conditioning-plan.v1',policy=policy(),smoke_launcher_sha256=SMOKE_LAUNCHER,
        smoke_plan_sha256=SMOKE_PLAN,smoke_authority_sha256=E.sha(output/'smoke-authority.json'),runtime=S.verify(output/'smoke-inputs',SMOKE_PLAN)['runtime'],
        jobs=jobs,producer_sha256=sources(),files=I.W.input_files(output),root_go_required=True,native_executed=False,model_qualified=False,qualified_timing=False)
    write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'Conditioning plan differs');r=json.loads((inputs/'plan.json').read_text());old=S.verify(inputs/'smoke-inputs',SMOKE_PLAN)
    P.need(E.sha(inputs/'smoke-launcher.json')==SMOKE_LAUNCHER and E.sha(inputs/'smoke-authority.json')==r['smoke_authority_sha256'],'Actual failed smoke identity differs')
    closed=json.loads((inputs/'smoke-authority.json').read_text());P.need(closed['measurement_packet_completed'] is True and closed['smoke_passed'] is False and closed['resource_feasible'] is True,'Failed smoke must remain failed')
    P.need(E.sha(inputs/'solver-source/manifest.json')==SOLVER_SOURCE_MANIFEST,'Pinned FasterCap source provenance differs')
    manifest=json.loads((inputs/'solver-source/manifest.json').read_text())
    for row in manifest['files']:
        n=Path(row['path']).name
        if n in ('SolveCapacitance.cpp','FasterCapConsole.cpp','SolveCapacitance.h'):P.need(E.sha(inputs/'solver-source'/n)==row['sha256'],'Pinned source causal input differs')
    expected=[dict(index=c*4+b,case=c,branch=branch) for c in range(2) for b,branch in enumerate(Q.branches())]
    P.need(r['schema']=='pinwheel.model24-fullstack-conditioning-plan.v1' and r['policy']==policy() and r['jobs']==expected
        and r['smoke_launcher_sha256']==SMOKE_LAUNCHER and r['smoke_plan_sha256']==SMOKE_PLAN and r['runtime']==old['runtime']
        and r['producer_sha256']==sources() and r['files']==I.W.input_files(inputs) and r['root_go_required'] is True
        and all(r[k] is False for k in ('native_executed','model_qualified','qualified_timing')),'Conditioning geometry/complete universe/source/claim differs')
    return r


def proposal(inputs,digest,runtime,parent,require_fresh=True):
    plan=verify(inputs,digest);P.need(E.tree(runtime)==plan['runtime'] and parent.is_dir() and (not require_fresh or not(parent/OUTPUT).exists()),'Conditioning exact runtime/fresh output differs')
    old=S.proposal(inputs/'smoke-inputs',SMOKE_PLAN,runtime,parent,False);argv=list(old['argv']);argv[argv.index('--name')+1]=CONTAINER
    argv=[a.replace('src='+str((inputs/'smoke-inputs').resolve()),'src='+str(inputs.resolve())).replace('/model24-source/streaming_8x4_model24_smoke.py','/model24-source/'+NEW[0]).replace(SMOKE_PLAN,digest).replace('/model24-output-parent/'+S.OUTPUT,'/model24-output-parent/'+OUTPUT) for a in argv]
    return dict(schema='pinwheel.model24-fullstack-conditioning-command-proposal.v1',root_go_required=True,admitted=False,native_executed=False,model_qualified=False,
        qualified_timing=False,plan_path=str((inputs/'plan.json').resolve()),plan_sha256=digest,runtime_path=str(runtime.resolve()),producer_sha256=plan['producer_sha256'],
        timeout_seconds=600,policy=policy(),container_name=CONTAINER,argv=argv)


def leaf(inputs,digest,plan,job,runtime,output):
    P.need(not output.exists(),'Fresh conditioning leaf required');output.mkdir();work=output/'work';work.mkdir();case=S.verify(inputs/'smoke-inputs',SMOKE_PLAN)['cases'][job['case']]
    source=inputs/'smoke-inputs'/('case-'+str(job['case']).zfill(3))/'geometry'
    for name in case['files_sha256']:shutil.copyfile(source/name,work/name);(work/name).chmod(0o444)
    started=time.monotonic();row=dict(schema='pinwheel.model24-fullstack-conditioning-leaf.v1',plan_sha256=digest,job=job,
        argv=Q.argv(job['branch']),environment=I.W.C.ENVIRONMENT,cgroups=E.verify_cgroups(),cgroup_before=I.cgroup_snapshot(),
        numeric_passed=False,resource_feasible=False,passed=False,native_executed=False,model_qualified=False,qualified_timing=False,
        timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,process_tree_reaped=False,exit_code=None,numeric=None)
    peak=row['cgroup_before']['memory_current'];child=None;raw=''
    try:
        with (output/'native.log').open('xb') as stream:
            child=subprocess.Popen(row['argv'],cwd=work,env=dict(row['environment']),stdout=stream,stderr=subprocess.STDOUT,start_new_session=True);row['native_executed']=True
            while child.poll() is None:
                current=I.cgroup_snapshot()['memory_current'];peak=max(peak,current);size=sum(p.stat().st_size for p in output.rglob('*') if p.is_file() and not p.is_symlink())
                if time.monotonic()-started>=60 or current>=6442450944*95//100 or size>policy()['maximum_output_bytes']:
                    row['timed_out']=time.monotonic()-started>=60;row['memory_guard_triggered']=current>=6442450944*95//100;row['output_guard_triggered']=size>policy()['maximum_output_bytes'];os.killpg(child.pid,signal.SIGKILL);break
                try:child.wait(timeout=.25)
                except subprocess.TimeoutExpired:pass
            row['exit_code']=child.wait(timeout=2)
        try:os.killpg(child.pid,0)
        except ProcessLookupError:row['process_tree_reaped']=True
        else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('Conditioning process group remained live')
        raw=(output/'native.log').read_text();row['numeric']=Q.parse(raw,case['ordered_conductor_roles'],job['branch'],row['exit_code'],row['timed_out'],row['memory_guard_triggered']);row['numeric_passed']=True
    except BaseException as error:row['error']=type(error).__name__+': '+str(error)
    finally:
        if child is not None and child.poll() is None:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=2)
        row['cgroup_after']=I.cgroup_snapshot();row['cgroup_counter_deltas']=I.counters(row['cgroup_before'],row['cgroup_after'])
        row['maximum_polled_memory_current']=peak;row['copied_inputs_unchanged']=E.tree(work)==E.tree(source);row['inputs_sources_unchanged']=verify(inputs,digest)==plan;row['runtime_unchanged']=E.tree(runtime)==plan['runtime']
        raw=(output/'native.log').read_text() if (output/'native.log').exists() else raw;row['actual_f0_observed']=I.mode_observed(raw)
        row['actual_output_bytes']=sum(p.stat().st_size for p in output.rglob('*') if p.is_file() and not p.is_symlink())
        row['resource_feasible']=I.resource_feasible(row) and row['process_tree_reaped'] and row['output_guard_triggered'] is False and row['actual_output_bytes']<=policy()['maximum_output_bytes'];row['wall_seconds']=time.monotonic()-started
        row['passed']=row['numeric_passed'] and row['resource_feasible'] and row['copied_inputs_unchanged'] and row['inputs_sources_unchanged'] and row['runtime_unchanged'];row['native_log_sha256']=E.sha(output/'native.log') if (output/'native.log').exists() else None;write(output/'report.json',row)
    return row


def run(inputs,digest,runtime,output):
    started=time.monotonic();plan=verify(inputs,digest);P.need(str(runtime)=='/solver/runtime' and E.tree(runtime)==plan['runtime'],'Exact conditioning runtime mount differs');P.need(not output.exists() and output.name==OUTPUT and output.parent.is_dir(),'Fresh conditioning output required');output.mkdir();jobs=[]
    row=dict(schema='pinwheel.model24-fullstack-conditioning-execution.v1',plan_sha256=digest,policy=policy(),jobs=jobs,measurement_packet_completed=False,all_numeric_passed=False,resource_feasible=False,passed=False,model_qualified=False,qualified_timing=False,profile_results=None)
    try:
        for job in plan['jobs']:
            P.need(time.monotonic()-started<470,'Insufficient full next-leaf budget');owner=output/('job-'+str(job['index']).zfill(3));result=leaf(inputs,digest,plan,job,runtime,owner)
            jobs.append(dict(**job,numeric_passed=result['numeric_passed'],resource_feasible=result['resource_feasible'],report_sha256=E.sha(owner/'report.json')))
            P.need(result['process_tree_reaped'] and result['copied_inputs_unchanged'] and result['inputs_sources_unchanged'] and result['runtime_unchanged'] and result['resource_feasible'],'Conditioning resource/custody failure stops suffix')
    except BaseException as error:row['error']=type(error).__name__+': '+str(error)
    row['inputs_sources_runtime_unchanged']=verify(inputs,digest)==plan and E.tree(runtime)==plan['runtime'];row['actual_work_seconds']=time.monotonic()-started;row['work_budget_passed']=row['actual_work_seconds']<=540;row['measurement_packet_completed']=len(jobs)==8;row['all_numeric_passed']=len(jobs)==8 and all(r['numeric_passed'] for r in jobs);row['resource_feasible']=len(jobs)==8 and all(r['resource_feasible'] for r in jobs) and row['work_budget_passed']
    if len(jobs)==8:row['profile_results']=Q.aggregate(jobs)
    row['passed']=row['resource_feasible'] and row['inputs_sources_runtime_unchanged'] and row['profile_results'] is not None and any(p['both_geometries_passed'] for p in row['profile_results']);write(output/'report.json',row);return row


def main():
    q=argparse.ArgumentParser(description=__doc__);sub=q.add_subparsers(dest='action',required=True)
    p=sub.add_parser('prepare');p.add_argument('--smoke-launcher',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    for n in ('verify','proposal','run'):
        p=sub.add_parser(n);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--plan-sha256',required=True)
        if n!='verify':p.add_argument('--runtime',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
        if n=='proposal':p.add_argument('--output-parent',type=Path,required=True)
    a=q.parse_args()
    if a.action=='prepare':prepare(a.smoke_launcher,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':write(a.output,proposal(a.inputs,a.plan_sha256,a.runtime,a.output_parent));return 0
    r=run(a.inputs,a.plan_sha256,a.runtime,a.output);return 0 if r['passed'] else 2
if __name__=='__main__':raise SystemExit(main())
