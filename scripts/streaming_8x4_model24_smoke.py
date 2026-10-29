"""Two fixed observed six-conductor full-stack cost/terminal representatives.

Root alone executes Native. This cannot qualify a mesh/length/boundary/reference
universe, generated table, heldout, complete model or extracted timing.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_contract as K
import streaming_8x4_model24_native_geometry as G
import streaming_8x4_model24_patterns as N
import streaming_8x4_model24_patterns_readback as R
import streaming_8x4_rc_ooc as O

P,E,I=O.P,O.E,K.I
ROOT=N.ROOT
OUTPUT='model24-fullstack-cost-smoke-01';CONTAINER='pinwheel-'+OUTPUT
NEW=('streaming_8x4_model24_smoke.py','streaming_8x4_model24_smoke_readback.py',
    'streaming_8x4_model24_custody.py','streaming_8x4_model24_native_geometry.py')
RUNTIME_AUTHORITY='c31469a9a8bfcdf3bad0fced51d74eb8cd4d1bd39fdaf725244febedf29cd314'
PATTERN_LAUNCHER='9b7abdc68aba1a16ac11f6aec83d14ce15d07f2347a289187710728746a1f283'


def write(path,value):
    P.need(not path.exists(),'Preserve model24 smoke evidence');path.write_bytes(K.canonical(value)+b'\n')


def policy():
    row=K.policy();row.update(maximum_calls=2,work_seconds=270,outer_seconds=330,
        purpose='two observed near/far six-conductor fullstack numerical/cost representatives',
        selection='actual310-case TYP inventory maximum6conductors/65initialfaces/29dielectricfaces; near/far top-context bracket is not a proven universal runtime upper bound',
        lengths_um=['20'],ground_extension_um='20',native_case_paths=G.REPRESENTATIVES,maximum_output_bytes=268435456)
    return row


def sources():
    pending=list(NEW)+list(N.NEW)+['streaming_8x4_closure24_resources.py'];done={}
    while pending:
        name=pending.pop()
        if name in done:continue
        path=Path(__file__).with_name(name);done[name]=E.sha(path)
        for node in ast.walk(ast.parse(path.read_text())):
            imports=[n.name for n in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            pending += [n+'.py' for n in imports if n.startswith('streaming_') and '.' not in n]
    return dict(sorted(done.items()))


def parent_pattern(launcher):
    P.need(E.sha(launcher)==PATTERN_LAUNCHER,'Exact closed Native pattern launcher differs')
    row=json.loads(launcher.read_text());argv=row['HOST_closeout_argv']
    P.need(len(argv[3:])%2==0,'Malformed exact HOST pattern reopener')
    args=dict(zip(argv[3::2],argv[4::2]))
    P.need(set(args)=={'--inputs','--plan-sha256','--directory','--resource-report','--command-proposal','--root-go','--output'},
        'Exact actual pattern readback argument membership differs')
    actual=R.readback(Path(args['--inputs']),args['--plan-sha256'],Path(args['--directory']),
        Path(args['--resource-report']),Path(args['--command-proposal']),Path(args['--root-go']))
    receipt=Path(args['--output']);P.need(actual==json.loads(receipt.read_text()) and actual['pattern_intake_completed'] is True,
        'Complete actual Native pattern/custody observation required')
    return args,actual,E.sha(receipt)


def geometry_case(inputs,index):
    path=G.REPRESENTATIVES[index];text=(inputs/('case-'+str(index).zfill(3))/'wires.source.txt').read_text()
    itf=(inputs/'itf-typ.txt').read_text();P.need(hashlib.sha256(itf.encode()).hexdigest()==N.ITF_SHA,'Exact fullstack ITF differs')
    value=G.build(text,path,itf);files=dict(value['files'])
    files['geometry-certificate.json']=K.canonical(value['certificate']).decode()+'\n'
    metadata=dict(index=index,native_path=path,raw_pattern_sha256=hashlib.sha256(text.encode()).hexdigest(),
        ordered_conductor_roles=value['ordered_conductor_roles'],normalization=value['normalization'],
        geometry_certificate=value['certificate'],files_sha256={n:hashlib.sha256(t.encode()).hexdigest() for n,t in files.items()})
    return metadata,files


def prepare(pattern_launcher,runtime_authority,runtime,output):
    args,closed,receipt_hash=parent_pattern(pattern_launcher)
    P.need(E.sha(runtime_authority/'plan.json')==RUNTIME_AUTHORITY,'Pinned215-entry runtime authority differs')
    old=O.verify(runtime_authority,RUNTIME_AUTHORITY)
    P.need(len(old['runtime'])==215 and E.tree(runtime)==old['runtime'] and E.sha(runtime/'bin/FasterCap')==P.SOLVER_SHA256,
        'Exact restored FasterCap runtime differs')
    P.need(not output.exists() and output.parent.is_dir(),'Fresh six-conductor smoke inputs required')
    output.mkdir();shutil.copyfile(Path(args['--inputs'])/'itf-typ.txt',output/'itf-typ.txt')
    shutil.copyfile(pattern_launcher,output/'pattern-launcher.json');shutil.copyfile(Path(args['--output']),output/'pattern-authority.json')
    shutil.copyfile(runtime_authority/'plan.json',output/'runtime-authority.json');cases=[]
    native_root=Path(args['--directory']);observed={r['path']:r for r in closed['inventory']['observed_cases']}
    for index,path in enumerate(G.REPRESENTATIVES):
        source=native_root/path;P.need(path in observed and E.sha(source)==observed[path]['sha256'],'Actual representative pattern hash differs')
        owner=output/('case-'+str(index).zfill(3));owner.mkdir();shutil.copyfile(source,owner/'wires.source.txt')
        metadata,files=geometry_case(output,index);geometry=owner/'geometry';geometry.mkdir()
        for n,text in files.items():(geometry/n).write_text(text)
        P.need(len(metadata['ordered_conductor_roles'])==6 and metadata['geometry_certificate']['all_faces']==65
            and metadata['geometry_certificate']['dielectric_faces']==29,'Representative measured HOST complexity differs')
        cases.append(metadata)
    row=dict(schema='pinwheel.model24-fullstack-smoke-plan.v1',policy=policy(),root_go_required=True,
        native_executed=False,model_qualified=False,qualified_timing=False,
        mesh_boundary_length_reference_heldout_qualification_passed=False,
        pattern_launcher_sha256=PATTERN_LAUNCHER,pattern_authority_sha256=receipt_hash,
        runtime_authority_sha256=RUNTIME_AUTHORITY,runtime=old['runtime'],solver_sha256=P.SOLVER_SHA256,
        fastercap_source_commit='b42179a8fdd25ab42fe45527282b4a738d7e7f87',cases=cases,
        producer_sha256=sources(),files=I.W.input_files(output),qualification_requirements=K.qualification_requirements())
    write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'Six-conductor smoke plan identity differs');row=json.loads((inputs/'plan.json').read_text())
    P.need(E.sha(inputs/'pattern-launcher.json')==PATTERN_LAUNCHER and E.sha(inputs/'runtime-authority.json')==RUNTIME_AUTHORITY
        and E.sha(inputs/'pattern-authority.json')==row['pattern_authority_sha256'],'Smoke exact source/runtime/pattern authority differs')
    old=json.loads((inputs/'runtime-authority.json').read_text());closed=json.loads((inputs/'pattern-authority.json').read_text())
    P.need(closed['schema']=='pinwheel.model24-pattern-independent-readback.v1' and closed['pattern_intake_completed'] is True
        and closed['model_qualified'] is False,'Observed pattern data cannot be promoted to physics')
    cases=[];observed={r['path']:r for r in closed['inventory']['observed_cases']}
    for index,path in enumerate(G.REPRESENTATIVES):
        metadata,files=geometry_case(inputs,index);owner=inputs/('case-'+str(index).zfill(3))
        P.need(metadata['raw_pattern_sha256']==observed[path]['sha256'],'Smoke actual native pattern binding differs')
        P.need(E.tree(owner/'geometry')=={n:dict(kind='file',bytes=len(t.encode()),sha256=hashlib.sha256(t.encode()).hexdigest()) for n,t in files.items()},
            'Actual representative geometry differs');cases.append(metadata)
    P.need(row['schema']=='pinwheel.model24-fullstack-smoke-plan.v1' and row['policy']==policy() and row['root_go_required'] is True
        and all(row[k] is False for k in ('native_executed','model_qualified','qualified_timing','mesh_boundary_length_reference_heldout_qualification_passed'))
        and row['pattern_launcher_sha256']==PATTERN_LAUNCHER and row['runtime_authority_sha256']==RUNTIME_AUTHORITY
        and row['runtime']==old['runtime'] and len(row['runtime'])==215 and row['solver_sha256']==P.SOLVER_SHA256
        and row['fastercap_source_commit']=='b42179a8fdd25ab42fe45527282b4a738d7e7f87'
        and row['cases']==cases and row['producer_sha256']==sources()
        and row['qualification_requirements']==K.qualification_requirements() and row['files']==I.W.input_files(inputs),
        'Smoke exact source/geometry/role/unit/complete membership/claim differs')
    return row


def proposal(inputs,digest,runtime,parent,require_fresh=True):
    plan=verify(inputs,digest);P.need(E.tree(runtime)==plan['runtime'] and parent.is_dir()
        and (not require_fresh or not(parent/OUTPUT).exists()),'Smoke runtime/fresh output differs')
    argv=['docker','run','--name',CONTAINER,'--rm','--pull','never','--network','none','--read-only',
        '--cpus','1','--memory','6g','--memory-swap','6g','--pids-limit','128','--tmpfs','/tmp:rw,nosuid,noexec,size=536870912',
        '--mount',f'type=bind,src={Path(__file__).resolve().parent},dst=/model24-source,readonly',
        '--mount',f'type=bind,src={inputs.resolve()},dst=/model24-inputs,readonly',
        '--mount',f'type=bind,src={runtime.resolve()},dst=/solver/runtime,readonly',
        '--mount',f'type=bind,src={parent.resolve()},dst=/model24-output-parent','--entrypoint',N.C.PYTHON,N.C.IMAGE,
        '-I','-B','/model24-source/'+NEW[0],'run','--inputs','/model24-inputs','--plan-sha256',digest,
        '--runtime','/solver/runtime','--output','/model24-output-parent/'+OUTPUT]
    return dict(schema='pinwheel.model24-fullstack-smoke-command-proposal.v1',root_go_required=True,admitted=False,
        native_executed=False,model_qualified=False,qualified_timing=False,plan_path=str((inputs/'plan.json').resolve()),
        plan_sha256=digest,runtime_path=str(runtime.resolve()),producer_sha256=plan['producer_sha256'],
        timeout_seconds=330,policy=policy(),container_name=CONTAINER,argv=argv)


def leaf(inputs,digest,plan,index,runtime,output):
    P.need(not output.exists(),'Fresh representative leaf required');output.mkdir();work=output/'work';work.mkdir();case=plan['cases'][index]
    source=inputs/('case-'+str(index).zfill(3))/'geometry'
    for name in case['files_sha256']:shutil.copyfile(source/name,work/name);(work/name).chmod(0o444)
    started=time.monotonic();row=dict(schema='pinwheel.model24-fullstack-smoke-leaf.v1',plan_sha256=digest,index=index,
        native_path=case['native_path'],argv=K.solver_argv(),environment=I.W.C.ENVIRONMENT,cgroups=E.verify_cgroups(),cgroup_before=I.cgroup_snapshot(),
        numeric_passed=False,resource_feasible=False,passed=False,native_executed=False,model_qualified=False,qualified_timing=False,
        timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,process_tree_reaped=False,exit_code=None,numeric=None)
    peak=row['cgroup_before']['memory_current'];child=None;raw=''
    try:
        with (output/'native.log').open('xb') as stream:
            child=subprocess.Popen(row['argv'],cwd=work,env=dict(row['environment']),stdout=stream,stderr=subprocess.STDOUT,start_new_session=True);row['native_executed']=True
            while child.poll() is None:
                current=I.cgroup_snapshot()['memory_current'];peak=max(peak,current)
                size=sum(p.stat().st_size for p in output.rglob('*') if p.is_file() and not p.is_symlink())
                if time.monotonic()-started>=120 or current>=6442450944*95//100 or size>policy()['maximum_output_bytes']:
                    row['output_guard_triggered']=size>policy()['maximum_output_bytes']
                    row['timed_out']=time.monotonic()-started>=120;row['memory_guard_triggered']=current>=6442450944*95//100
                    os.killpg(child.pid,signal.SIGKILL);break
                try:child.wait(timeout=.25)
                except subprocess.TimeoutExpired:pass
            row['exit_code']=child.wait(timeout=2)
        try:os.killpg(child.pid,0)
        except ProcessLookupError:row['process_tree_reaped']=True
        else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('Smoke process group remained live')
        raw=(output/'native.log').read_text();row['numeric']=K.parse_terminal(raw,case['ordered_conductor_roles'],row['exit_code'],row['timed_out'],row['memory_guard_triggered']);row['numeric_passed']=True
    except BaseException as error:row['error']=type(error).__name__+': '+str(error)
    finally:
        if child is not None and child.poll() is None:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=2)
        row['cgroup_after']=I.cgroup_snapshot();row['cgroup_counter_deltas']=I.counters(row['cgroup_before'],row['cgroup_after'])
        row['maximum_polled_memory_current']=peak;row['copied_inputs_unchanged']=E.tree(work)==E.tree(source)
        row['inputs_sources_unchanged']=verify(inputs,digest)==plan;row['runtime_unchanged']=E.tree(runtime)==plan['runtime']
        raw=(output/'native.log').read_text() if (output/'native.log').exists() else raw
        row['actual_f0_observed']=I.mode_observed(raw);row['actual_output_bytes']=sum(p.stat().st_size for p in output.rglob('*') if p.is_file() and not p.is_symlink())
        row['resource_feasible']=I.resource_feasible(row) and row['process_tree_reaped'] and row['output_guard_triggered'] is False and row['actual_output_bytes']<=policy()['maximum_output_bytes']
        row['wall_seconds']=time.monotonic()-started
        row['passed']=row['numeric_passed'] and row['resource_feasible'] and row['copied_inputs_unchanged'] and row['inputs_sources_unchanged'] and row['runtime_unchanged']
        row['native_log_sha256']=E.sha(output/'native.log') if (output/'native.log').exists() else None;write(output/'report.json',row)
    return row


def run(inputs,digest,runtime,output):
    started=time.monotonic();plan=verify(inputs,digest)
    P.need(str(runtime)=='/solver/runtime' and E.tree(runtime)==plan['runtime'],'Exact representative runtime mount differs')
    P.need(not output.exists() and output.name==OUTPUT and output.parent.is_dir(),'Fresh exact representative packet required')
    output.mkdir();jobs=[];row=dict(schema='pinwheel.model24-fullstack-smoke-execution.v1',plan_sha256=digest,policy=policy(),jobs=jobs,
        measurement_packet_completed=False,all_numeric_passed=False,resource_feasible=False,passed=False,model_qualified=False,qualified_timing=False)
    try:
        for index in range(2):
            P.need(time.monotonic()-started<140,'Insufficient complete next-representative budget')
            owner=output/('job-'+str(index).zfill(3));result=leaf(inputs,digest,plan,index,runtime,owner)
            jobs.append(dict(index=index,native_path=plan['cases'][index]['native_path'],numeric_passed=result['numeric_passed'],
                resource_feasible=result['resource_feasible'],report_sha256=E.sha(owner/'report.json')))
            P.need(result['process_tree_reaped'] and result['copied_inputs_unchanged'] and result['inputs_sources_unchanged'] and result['runtime_unchanged'],
                'Representative custody failure stops suffix')
            P.need(result['resource_feasible'],'Representative resource failure stops suffix')
    except BaseException as error:row['error']=type(error).__name__+': '+str(error)
    row['inputs_sources_runtime_unchanged']=verify(inputs,digest)==plan and E.tree(runtime)==plan['runtime']
    row['actual_work_seconds']=time.monotonic()-started;row['work_budget_passed']=row['actual_work_seconds']<=270
    row['measurement_packet_completed']=len(jobs)==2;row['all_numeric_passed']=len(jobs)==2 and all(r['numeric_passed'] for r in jobs)
    row['resource_feasible']=len(jobs)==2 and all(r['resource_feasible'] for r in jobs) and row['work_budget_passed']
    row['passed']=row['all_numeric_passed'] and row['resource_feasible'] and row['inputs_sources_runtime_unchanged']
    write(output/'report.json',row);return row


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    q=sub.add_parser('prepare')
    for n in ('pattern-launcher','runtime-authority','runtime','output'):q.add_argument('--'+n,type=Path,required=True)
    for name in ('verify','proposal','run'):
        q=sub.add_parser(name);q.add_argument('--inputs',type=Path,required=True);q.add_argument('--plan-sha256',required=True)
        if name!='verify':q.add_argument('--runtime',type=Path,required=True);q.add_argument('--output',type=Path,required=True)
        if name=='proposal':q.add_argument('--output-parent',type=Path,required=True)
    a=p.parse_args()
    if a.action=='prepare':prepare(a.pattern_launcher,a.runtime_authority,a.runtime,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':write(a.output,proposal(a.inputs,a.plan_sha256,a.runtime,a.output_parent));return 0
    row=run(a.inputs,a.plan_sha256,a.runtime,a.output);return 0 if row['passed'] else 2


if __name__=='__main__':raise SystemExit(main())
