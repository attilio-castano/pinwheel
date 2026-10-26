"""Owned three-corner grammar/case observation only; Root alone Native."""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_smoke as S
import streaming_8x4_model24_process as U
P,E,I=S.P,S.E,S.I
ROOT=S.ROOT
OUTPUT='model24-owned-itf-pattern-census-01';CONTAINER='pinwheel-'+OUTPUT
NEW=('streaming_8x4_model24_process_patterns.py','streaming_8x4_model24_process_patterns_readback.py')
PROCESS_MANIFEST='bde97789d062746d40372f146b535ac6f14b88238ff30754c6f6f1eedf3b70f4'
OPENROAD_SHA='b2159d4a99a9b236a6e95bbf6efc88bcfd2b843df273e97f169b456bc3b0453b'
write=S.write


def policy():
    return dict(schema='pinwheel.model24-owned-itf-pattern-policy.v1',corners=list(U.CORNERS),wire_sets=['1v2','3v2'],
        native_calls=1,generator_calls=6,expected_case_counts_per_corner=dict(one_wire=45,three_wire=265,total=310),
        grammar_and_source_material_observation_only=True,no_FasterCap=True,no_calibration=True,no_coefficients=True,
        leaf_seconds=60,work_seconds=90,outer_seconds=120,cpu=1,memory_bytes=2147483648,extra_swap_bytes=0,
        tmpfs_bytes=134217728,maximum_output_bytes=268435456,model_qualified=False,qualified_timing=False)


def sources():
    pending=list(NEW)+list(S.N.sources())+['streaming_8x4_closure24_resources.py'];done={}
    while pending:
        n=pending.pop()
        if n in done:continue
        p=Path(__file__).with_name(n);done[n]=E.sha(p)
        for node in ast.walk(ast.parse(p.read_text())):
            names=[n.name for n in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            pending += [n+'.py' for n in names if n.startswith('streaming_') and '.' not in n]
    return dict(sorted(done.items()))


def tcl():
    lines=['puts "MODEL24_ITF_VERSION_BEGIN"','set v [ord::openroad_version]','puts $v','puts "MODEL24_ITF_VERSION_END"',
        'puts "MODEL24_ITF_API_BEGIN"','help gen_solver_patterns','puts "MODEL24_ITF_API_END"','set base [pwd]']
    for corner in U.CORNERS:
        for wires in (1,3):
            owner=corner+'/'+str(wires)+'v2';lines+=['file mkdir '+owner,'cd '+owner,
                'gen_solver_patterns -process_file /model24-inputs/owned-itf/'+corner+'.process -process_name '+corner+' -version 2 -wire_cnt '+str(wires),
                'puts "MODEL24_ITF_SET '+corner+' '+str(wires)+'v2 DONE"','cd $base']
    return '\n'.join(lines+['puts "MODEL24_ITF_TERMINAL"','exit',''])


def expected_cases(inputs):
    old=json.loads((inputs/'pattern-authority.json').read_text());P.need(old['pattern_intake_completed'] is True and old['model_qualified'] is False,'Original pattern scope differs')
    original=old['inventory']['observed_cases'];P.need(len(original)==310 and len({r['path'] for r in original})==310,'Original complete case census differs')
    return [(corner,corner+'/'+r['path'].replace('MODEL24_TYP',corner),r['path']) for corner in U.CORNERS for r in original]


def prepare(owned_itf,pattern_launcher,output):
    P.need(E.sha(owned_itf/'manifest.json')==PROCESS_MANIFEST,'Exact frozen owned-ITF policy manifest differs');U.verify(owned_itf)
    args,closed,h=S.parent_pattern(pattern_launcher);P.need(not output.exists() and output.parent.is_dir(),'Fresh owned-ITF pattern preparation required');output.mkdir()
    shutil.copytree(owned_itf,output/'owned-itf');shutil.copyfile(pattern_launcher,output/'pattern-launcher.json');shutil.copyfile(Path(args['--output']),output/'pattern-authority.json');(output/'run.tcl').write_text(tcl())
    row=dict(schema='pinwheel.model24-owned-itf-pattern-plan.v1',policy=policy(),process_manifest_sha256=PROCESS_MANIFEST,
        pattern_launcher_sha256=S.PATTERN_LAUNCHER,pattern_authority_sha256=h,expected_cases=expected_cases(output),
        openroad_sha256=OPENROAD_SHA,producer_sha256=sources(),files=I.W.input_files(output),root_go_required=True,
        native_executed=False,model_qualified=False,qualified_timing=False)
    write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'Owned-ITF grammar plan differs');row=json.loads((inputs/'plan.json').read_text());U.verify(inputs/'owned-itf')
    P.need(E.sha(inputs/'owned-itf/manifest.json')==PROCESS_MANIFEST and E.sha(inputs/'pattern-launcher.json')==S.PATTERN_LAUNCHER
        and E.sha(inputs/'pattern-authority.json')==row['pattern_authority_sha256'] and (inputs/'run.tcl').read_text()==tcl(),'Owned-ITF/source/census/command identities differ')
    P.need(row['schema']=='pinwheel.model24-owned-itf-pattern-plan.v1' and row['policy']==policy() and row['process_manifest_sha256']==PROCESS_MANIFEST
        and row['pattern_launcher_sha256']==S.PATTERN_LAUNCHER and row['expected_cases']==[list(r) for r in expected_cases(inputs)]
        and row['openroad_sha256']==OPENROAD_SHA and row['producer_sha256']==sources() and row['files']==I.W.input_files(inputs)
        and row['root_go_required'] is True and all(row[k] is False for k in ('native_executed','model_qualified','qualified_timing')),
        'Owned-ITF grammar source/case/complete membership/scope differs');return row


def parse_terminal(raw,code,timeout):
    P.need(type(code) is int and code==0 and timeout is False and not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout',raw),'Owned-ITF Native exit/warning/timeout failed')
    v=re.findall(r'^MODEL24_ITF_VERSION_BEGIN\n(.*?)^MODEL24_ITF_VERSION_END$',raw,re.M|re.S)
    P.need(len(v)==1 and raw.count('MODEL24_ITF_VERSION_BEGIN')==raw.count('MODEL24_ITF_VERSION_END')==1,'Owned-ITF actual version missing/duplicated')
    tokens=[t for t in re.findall(r'[0-9a-f]+',v[0]) if len(t)>=40];P.need(tokens and set(tokens)=={S.N.OPENROAD_COMMIT},'Owned-ITF actual OpenROAD commit differs')
    expected=[(c,s) for c in U.CORNERS for s in ('1v2','3v2')]
    P.need(re.findall(r'^MODEL24_ITF_SET (\w+) (\w+) DONE$',raw,re.M)==expected and all(raw.count(m)==1 for m in ('MODEL24_ITF_API_BEGIN','MODEL24_ITF_API_END','MODEL24_ITF_TERMINAL')),
        'Owned-ITF complete ordered six-set terminal differs')
    markers=['MODEL24_ITF_VERSION_END','MODEL24_ITF_API_BEGIN','MODEL24_ITF_API_END']+['MODEL24_ITF_SET '+c+' '+s+' DONE' for c,s in expected]+['MODEL24_ITF_TERMINAL']
    P.need([raw.index(m) for m in markers]==sorted(raw.index(m) for m in markers),'Owned-ITF observed version/API/generation order differs')
    return dict(native_process_grammar_accepted=True,observed_openroad_commit=S.N.OPENROAD_COMMIT,sets=[list(r) for r in expected],model_qualified=False)


def inventory(inputs,output):
    actual=sorted(str(p.relative_to(output)) for p in output.rglob('wires') if p.is_file());expected=expected_cases(inputs)
    P.need(actual==sorted(r[1] for r in expected),'Owned-ITF exact six-set/930-case membership differs');rows=[]
    for corner,path,oldpath in expected:
        raw=(output/path).read_text();prefix='PATTERN '+corner+'/';P.need(raw.startswith(prefix),'Exact generated native corner identity differs')
        normalized=raw.replace(prefix,'PATTERN MODEL24_TYP/',1)
        witness=S.G.normalize(normalized,oldpath,(inputs/'owned-itf'/(corner+'.itf')).read_text())
        rows.append(dict(corner=corner,path=path,raw_sha256=E.sha(output/path),normalization=witness,
            corner_relabel_for_frozen_grammar_only=True,no_physical_coordinates_or_materials_rewritten=True))
    files={}
    for p in sorted(output.rglob('*')):
        P.need(not p.is_symlink(),'Owned-ITF output aliases forbidden')
        if p.is_file() and p!=output/'report.json':files[str(p.relative_to(output))]=dict(bytes=p.stat().st_size,sha256=E.sha(p))
    P.need(sum(r['bytes'] for r in files.values())<=policy()['maximum_output_bytes'],'Owned-ITF output capacity exceeded')
    return dict(complete_expected_membership=True,cases=rows,files=files,material_and_global_coordinate_roles_checked=True,
        source_corner_policy=U.policy(),independent_physics_accuracy=False,model_qualified=False)


def run(inputs,digest,output):
    plan=verify(inputs,digest);P.need(not output.exists() and output.name==OUTPUT and output.parent.is_dir(),'Fresh owned-ITF pattern output required');output.mkdir();shutil.copyfile(inputs/'run.tcl',output/'run.tcl')
    exe=shutil.which('openroad');P.need(exe and E.sha(Path(exe).resolve())==OPENROAD_SHA,'Exact observed OpenROAD executable differs');start=time.monotonic();child=None
    env=dict(PATH=os.environ['PATH'],HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE')
    row=dict(schema='pinwheel.model24-owned-itf-pattern-execution.v1',plan_sha256=digest,policy=policy(),argv=[exe,'-no_init','-exit','run.tcl'],environment=env,openroad_sha256=OPENROAD_SHA,
        cgroups=S.N.C.cgroups(),cgroup_before=I.cgroup_snapshot(),exit_code=None,timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,process_tree_reaped=False,
        native_executed=False,passed=False,terminal=None,inventory=None,resource_feasible=False,model_qualified=False,qualified_timing=False,numeric_solver_executed=False)
    peak=row['cgroup_before']['memory_current']
    try:
        with (output/'native.log').open('xb') as stream:
            child=subprocess.Popen(row['argv'],cwd=output,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True);row['native_executed']=True
            while child.poll() is None:
                current=I.cgroup_snapshot()['memory_current'];peak=max(peak,current);size=sum(p.stat().st_size for p in output.rglob('*') if p.is_file() and not p.is_symlink())
                if time.monotonic()-start>=60 or current>=2147483648*95//100 or size>policy()['maximum_output_bytes']:
                    row['timed_out']=time.monotonic()-start>=60;row['memory_guard_triggered']=current>=2147483648*95//100;row['output_guard_triggered']=size>policy()['maximum_output_bytes'];os.killpg(child.pid,signal.SIGKILL);break
                try:child.wait(timeout=.25)
                except subprocess.TimeoutExpired:pass
            row['exit_code']=child.wait(timeout=2)
        try:os.killpg(child.pid,0)
        except ProcessLookupError:row['process_tree_reaped']=True
        else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('Owned-ITF generator process group remained live')
        row['terminal']=parse_terminal((output/'native.log').read_text(),row['exit_code'],row['timed_out']);row['inventory']=inventory(inputs,output);row['passed']=True
    except BaseException as e:row['error']=type(e).__name__+': '+str(e)
    finally:
        if child is not None and child.poll() is None:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=2)
        row['inputs_sources_unchanged']=verify(inputs,digest)==plan;row['copied_tcl_unchanged']=(output/'run.tcl').read_bytes()==(inputs/'run.tcl').read_bytes();row['openroad_unchanged']=E.sha(Path(exe).resolve())==OPENROAD_SHA
        row['actual_work_seconds']=time.monotonic()-start;row['work_budget_passed']=row['actual_work_seconds']<=90;row['cgroup_after']=I.cgroup_snapshot();row['cgroup_counter_deltas']=I.counters(row['cgroup_before'],row['cgroup_after']);row['maximum_polled_memory_current']=peak
        row['resource_feasible']=S.N.resource_observation(row);row['native_log_sha256']=E.sha(output/'native.log') if (output/'native.log').exists() else None
        row['passed']=row['passed'] and row['work_budget_passed'] and row['resource_feasible'] and row['inputs_sources_unchanged'] and row['copied_tcl_unchanged'] and row['openroad_unchanged'];write(output/'report.json',row)
    return row


def proposal(inputs,digest,parent,require_fresh=True):
    plan=verify(inputs,digest);P.need(parent.is_dir() and (not require_fresh or not(parent/OUTPUT).exists()),'Fresh owned-ITF output required')
    argv=['docker','run','--name',CONTAINER,'--rm','--pull','never','--network','none','--read-only','--cpus','1','--memory','2g','--memory-swap','2g','--pids-limit','128','--tmpfs','/tmp:rw,nosuid,noexec,size=134217728',
        '--mount',f'type=bind,src={Path(__file__).resolve().parent},dst=/model24-source,readonly','--mount',f'type=bind,src={inputs.resolve()},dst=/model24-inputs,readonly','--mount',f'type=bind,src={parent.resolve()},dst=/model24-output-parent','--entrypoint',S.N.C.PYTHON,S.N.C.IMAGE,'-I','-B','/model24-source/'+NEW[0],'run','--inputs','/model24-inputs','--plan-sha256',digest,'--output','/model24-output-parent/'+OUTPUT]
    return dict(schema='pinwheel.model24-owned-itf-pattern-command-proposal.v1',root_go_required=True,admitted=False,native_executed=False,model_qualified=False,qualified_timing=False,plan_path=str((inputs/'plan.json').resolve()),plan_sha256=digest,producer_sha256=plan['producer_sha256'],timeout_seconds=120,policy=policy(),container_name=CONTAINER,argv=argv)


def main():
    q=argparse.ArgumentParser(description=__doc__);sub=q.add_subparsers(dest='action',required=True);p=sub.add_parser('prepare')
    for n in ('owned-itf','pattern-launcher','output'):p.add_argument('--'+n,type=Path,required=True)
    for n in ('verify','proposal','run'):
        p=sub.add_parser(n);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--plan-sha256',required=True)
        if n!='verify':p.add_argument('--output',type=Path,required=True)
        if n=='proposal':p.add_argument('--output-parent',type=Path,required=True)
    a=q.parse_args()
    if a.action=='prepare':prepare(a.owned_itf,a.pattern_launcher,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':write(a.output,proposal(a.inputs,a.plan_sha256,a.output_parent));return 0
    row=run(a.inputs,a.plan_sha256,a.output);return 0 if row['passed'] else 2
if __name__=='__main__':raise SystemExit(main())
