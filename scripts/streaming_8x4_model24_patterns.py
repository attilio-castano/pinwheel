"""Fresh pinned OpenROAD API/pattern observation; Root alone executes Native.

Pattern files are data. No speculative parser, FasterCap, coefficient fitting,
table assembly, consumer extraction or qualification is included in this probe.
"""
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
import streaming_8x4_rc_process as P
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_consumer_cap as C
import streaming_8x4_model24_contract as K
import streaming_8x4_model24_geometry as G24
import streaming_8x4_rc_incore as I
import streaming_8x4_closure24_policy as R24

ROOT=Path(__file__).resolve().parents[1]
OUTPUT='model24-pattern-census-01'
CONTAINER='pinwheel-'+OUTPUT
NEW=('streaming_8x4_model24_patterns.py','streaming_8x4_model24_patterns_readback.py',
    'streaming_8x4_model24_contract.py','streaming_8x4_model24_geometry.py')
PROCESS_SHA='89d69b5213165c935e61628187521f457db1065db2fc4bc307798084c90a5325'
ITF_SHA='08d0de3413256b996b7b6c5a1816e02f8dae4151e0df12c7a8f081ccee415cea'
OPENROAD_COMMIT='dcf36133a369abc8f3c5e5738cd4d82e4903c0e0'


def write(path,value):
    P.need(not path.exists(),'Preserve model24 evidence');path.write_bytes(K.canonical(value)+b'\n')


def policy():
    return dict(schema='pinwheel.model24-pattern-policy.v1',calls=1,generator_calls=2,
        pattern_sets=[dict(name='1v2',wire_count=1,version=2),dict(name='3v2',wire_count=3,version=2)],
        corner='TYP',process_source_role='retained draft pattern grammar data; not accepted physical stack',
        leaf_seconds=60,work_seconds=90,outer_seconds=120,maximum_output_bytes=268435456,
        cpus=1,memory_bytes=2147483648,tmpfs_bytes=134217728,no_extra_swap=True,
        all_warnings_fatal=True,no_native_pattern_grammar_assumed=True,
        pattern_manifest_is_observation_not_generation_acceptance=True,
        model_qualified=False,qualified_timing=False)


def sources():
    pending=list(NEW)+['streaming_8x4_closure24_resources.py','streaming_8x4_closure24_policy.py',
        'streaming_8x4_acceptance_resources.py','streaming_tt_resources.py'];done={}
    while pending:
        name=pending.pop()
        if name in done:continue
        path=Path(__file__).with_name(name);done[name]=E.sha(path)
        for node in ast.walk(ast.parse(path.read_text())):
            imports=[x.name for x in node.names] if isinstance(node,ast.Import) else ([node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            pending += [n+'.py' for n in imports if n.startswith('streaming_') and '.' not in n]
    return dict(sorted(done.items()))


def tcl():
    lines=['puts "MODEL24_OPENROAD_VERSION_BEGIN"','set model24_version [ord::openroad_version]',
        'puts "MODEL24_OPENROAD_VERSION_RETURN <$model24_version>"','puts "MODEL24_OPENROAD_VERSION_END"',
        'puts "MODEL24_PATTERN_API_BEGIN"','help gen_solver_patterns','help read_rcx_tables','help write_rcx_model',
        'puts "MODEL24_PATTERN_API_END"','set owner [pwd]']
    for row in policy()['pattern_sets']:
        lines += ['file mkdir '+row['name'],'cd [file join $owner '+row['name']+']',
            'gen_solver_patterns -process_file /model24-inputs/process.txt -process_name MODEL24_TYP -wire_cnt '+str(row['wire_count'])+' -version 2',
            'cd $owner','puts "MODEL24_PATTERN_SET '+row['name']+' DONE"']
    lines.append('puts "MODEL24_PATTERN_TERMINAL"')
    return '\n'.join(lines)+'\n'


def expected_files(intake):
    texts,manifest=P.verify_intake(intake)
    process=(intake/'draft_TYP_process.txt').read_bytes();itf=(intake/'itf_typ.txt').read_bytes()
    P.need(hashlib.sha256(process).hexdigest()==PROCESS_SHA and hashlib.sha256(itf).hexdigest()==ITF_SHA,
        'Exact retained TYP process/ITF identity differs')
    return {'process.txt':process,'itf-typ.txt':itf,'run.tcl':tcl().encode()},manifest


def geometry_commitment(itf_text):
    cases=[]
    for recipe in G24.recipes():
        row=G24.build(itf_text,recipe)
        cases.append(dict(recipe=recipe,physical_case=row['case'],ordered_conductor_roles=row['ordered_conductor_roles'],
            files_sha256={n:hashlib.sha256(t.encode()).hexdigest() for n,t in row['files'].items()},
            geometry_certificate_sha256=K.digest(row['certificate']),
            physical_values_measured=False,independent_accuracy_passed=False))
    return dict(cases=cases,material_sha256=ITF_SHA,operator_sha256=P.sha(G24.G.__file__),
        native_training_manifest_disjointness_still_required=True,model_qualified=False)


def prepare(intake,output):
    files,manifest=expected_files(intake)
    P.need(not output.exists() and output.parent.is_dir(),'Fresh model24 pattern owner required')
    output.mkdir()
    for n,data in files.items():(output/n).write_bytes(data)
    row=dict(schema='pinwheel.model24-pattern-plan.v1',policy=policy(),native_executed=False,
        model_qualified=False,qualified_timing=False,root_go_required=True,
        openroad_commit=OPENROAD_COMMIT,cad_image=C.IMAGE,
        retained_process_intake_manifest_sha256=E.sha(intake/'manifest.json'),
        process_sha256=PROCESS_SHA,itf_sha256=ITF_SHA,
        geometry_commitment=geometry_commitment(files['itf-typ.txt'].decode()),
        files_sha256={n:hashlib.sha256(data).hexdigest() for n,data in files.items()},
        producer_sha256=sources(),full_stack_solver_executed=False,
        unsupported_review_allegations_not_treated_as_defects=True)
    write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'Pattern plan hash differs');row=json.loads((inputs/'plan.json').read_text())
    P.need(row['schema']=='pinwheel.model24-pattern-plan.v1' and row['policy']==policy()
        and row['native_executed'] is False and row['model_qualified'] is False and row['qualified_timing'] is False
        and row['root_go_required'] is True and row['openroad_commit']==OPENROAD_COMMIT and row['cad_image']==C.IMAGE
        and row['process_sha256']==PROCESS_SHA and row['itf_sha256']==ITF_SHA
        and row['geometry_commitment']==geometry_commitment((inputs/'itf-typ.txt').read_text())
        and row['producer_sha256']==sources() and row['full_stack_solver_executed'] is False
        and row['unsupported_review_allegations_not_treated_as_defects'] is True,
        'Pattern exact source/scope/policy identity differs')
    files={'process.txt':PROCESS_SHA,'itf-typ.txt':ITF_SHA,'run.tcl':hashlib.sha256(tcl().encode()).hexdigest()}
    P.need(row['files_sha256']==files and {p.name for p in inputs.iterdir()}==set(files)|{'plan.json'},
        'Pattern input membership differs')
    for n,h in files.items():P.need((inputs/n).is_file() and not (inputs/n).is_symlink() and E.sha(inputs/n)==h,'Pattern owned input changed')
    return row


def output_inventory(owner):
    files={}
    for p in sorted(owner.rglob('*')):
        P.need(not p.is_symlink(),'Pattern output symlink forbidden')
        if p.is_dir():continue
        P.need(p.is_file(),'Unsupported pattern output node')
        relative=str(p.relative_to(owner))
        if relative=='report.json':continue
        files[relative]=dict(bytes=p.stat().st_size,sha256=E.sha(p))
    total=sum(r['bytes'] for r in files.values());P.need(total<=policy()['maximum_output_bytes'],'Pattern output budget exceeded')
    cases=[]
    for group in policy()['pattern_sets']:
        selected=[n for n in files if n.startswith(group['name']+'/') and Path(n).name=='wires']
        P.need(selected and all(files[n]['bytes']>0 for n in selected),'Native pattern set empty/truncated')
        cases += [dict(pattern_set=group['name'],path=n,**files[n],unparsed_pattern_data=True) for n in selected]
    P.need(len({r['path'] for r in cases})==len(cases),'Duplicate native pattern identity')
    return dict(files=files,total_bytes=total,observed_cases=cases,
        complete_observed_file_inventory=True,expected_physical_case_universe_proven=False,
        actual_native_pattern_grammar_qualified=False,model_qualified=False)


def parse_terminal(raw,code,timed_out):
    P.need(type(code) is int and code==0 and timed_out is False,'Pattern Native exit/timeout failed')
    P.need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout',raw),
        'Pattern Native warning/error/failure')
    versions=re.findall(r'^MODEL24_OPENROAD_VERSION_BEGIN\n(.*?)^MODEL24_OPENROAD_VERSION_END$',raw,re.M|re.S)
    P.need(len(versions)==1 and raw.count('MODEL24_OPENROAD_VERSION_BEGIN')==raw.count('MODEL24_OPENROAD_VERSION_END')==1,
        'Exact OpenROAD version observation missing/duplicated')
    commits=[token for token in re.findall(r'[0-9a-f]+',versions[0]) if len(token)>=40]
    P.need(commits and set(commits)=={OPENROAD_COMMIT},'Actual OpenROAD full commit differs/absent')
    P.need(raw.count('MODEL24_PATTERN_API_BEGIN')==raw.count('MODEL24_PATTERN_API_END')==1
        and raw.count('MODEL24_PATTERN_TERMINAL')==1
        and re.findall(r'^MODEL24_PATTERN_SET (\w+) DONE$',raw,re.M)==['1v2','3v2'],
        'Exact pattern API/set/terminal membership differs')
    P.need(raw.find('MODEL24_PATTERN_API_END')<raw.find('MODEL24_PATTERN_SET 1v2 DONE')
        <raw.find('MODEL24_PATTERN_SET 3v2 DONE')<raw.find('MODEL24_PATTERN_TERMINAL'),
        'Pattern Native terminal order differs')
    P.need(raw.find('MODEL24_OPENROAD_VERSION_END')<raw.find('MODEL24_PATTERN_API_BEGIN'),
        'Version identity must precede API/pattern observation')
    return dict(terminal_passed=True,generation_sets_observed=['1v2','3v2'],
        observed_openroad_commit=OPENROAD_COMMIT,version_observation=versions[0],model_qualified=False)


def resource_observation(row):
    changes=I.counters(row['cgroup_before'],row['cgroup_after'])
    need=P.need
    need(row['cgroup_counter_deltas']==changes,'Pattern cgroup counters differ')
    for snapshot in (row['cgroup_before'],row['cgroup_after']):
        need(snapshot['memory_max']==2147483648 and snapshot['memory_swap_max']==0,'Pattern cgroup memory/swap differs')
    peak=row['maximum_polled_memory_current'];after=row['cgroup_after']
    need(type(peak) is int and peak>=row['cgroup_before']['memory_current']
        and peak<=after['memory_peak'],'Pattern polled/kernel peak differs')
    return (row['exit_code']==0 and row['timed_out'] is False and row['memory_guard_triggered'] is False
        and row['output_guard_triggered'] is False and row['process_tree_reaped'] is True
        and after['memory_peak']<2147483648*95//100
        and all(all(v==0 for k,v in values.items() if k=='max' or k.startswith('oom')) for values in changes.values()))


def proposal(inputs,digest,parent,require_fresh=True):
    plan=verify(inputs,digest);P.need(parent.is_dir() and (not require_fresh or not(parent/OUTPUT).exists()),'Fresh pattern output required')
    argv=['docker','run','--name',CONTAINER,'--rm','--pull','never','--network','none','--read-only',
        '--cpus','1','--memory','2g','--memory-swap','2g','--pids-limit','128',
        '--tmpfs','/tmp:rw,nosuid,noexec,size=134217728','--mount',f'type=bind,src={Path(__file__).resolve().parent},dst=/model24-source,readonly',
        '--mount',f'type=bind,src={inputs.resolve()},dst=/model24-inputs,readonly',
        '--mount',f'type=bind,src={parent.resolve()},dst=/model24-output-parent',
        '--entrypoint',C.PYTHON,C.IMAGE,'-I','-B','/model24-source/'+NEW[0],'run','--inputs','/model24-inputs',
        '--plan-sha256',digest,'--output','/model24-output-parent/'+OUTPUT]
    return dict(schema='pinwheel.model24-pattern-command-proposal.v1',root_go_required=True,admitted=False,
        native_executed=False,model_qualified=False,qualified_timing=False,plan_path=str((inputs/'plan.json').resolve()),
        plan_sha256=digest,producer_sha256=plan['producer_sha256'],timeout_seconds=120,
        policy=policy(),container_name=CONTAINER,argv=argv)


def run(inputs,digest,output):
    plan=verify(inputs,digest);cg=C.cgroups();P.need(not output.exists() and output.name==OUTPUT and output.parent.is_dir(),'Fresh exact pattern output required')
    output.mkdir();shutil.copyfile(inputs/'run.tcl',output/'run.tcl');start=time.monotonic();child=None
    exe=shutil.which('openroad');P.need(exe is not None,'Pinned image OpenROAD absent')
    environment=dict(PATH=os.environ['PATH'],HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE')
    row=dict(schema='pinwheel.model24-pattern-execution.v1',plan_sha256=digest,policy=policy(),
        argv=[exe,'-no_init','-exit','run.tcl'],environment=environment,openroad_sha256=E.sha(Path(exe).resolve()),
        cgroups=cg,cgroup_before=I.cgroup_snapshot(),passed=False,native_executed=False,model_qualified=False,qualified_timing=False,
        timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,
        exit_code=None,process_tree_reaped=False,numeric_solver_executed=False)
    peak=row['cgroup_before']['memory_current']
    try:
        with (output/'native.log').open('xb') as stream:
            child=subprocess.Popen(row['argv'],cwd=output,env=environment,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True);row['native_executed']=True
            while child.poll() is None:
                elapsed=time.monotonic()-start
                current=I.cgroup_snapshot()['memory_current'];peak=max(peak,current)
                size=sum(p.stat().st_size for p in output.rglob('*') if p.is_file() and not p.is_symlink())
                if elapsed>=60 or size>policy()['maximum_output_bytes'] or current>=2147483648*95//100:
                    row['timed_out']=elapsed>=60;row['output_guard_triggered']=size>policy()['maximum_output_bytes']
                    row['memory_guard_triggered']=current>=2147483648*95//100;os.killpg(child.pid,signal.SIGKILL);break
                time.sleep(.25)
            row['exit_code']=child.wait(timeout=2)
        try:os.killpg(child.pid,0)
        except ProcessLookupError:row['process_tree_reaped']=True
        else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('Pattern child left process group')
        row['terminal']=parse_terminal((output/'native.log').read_text(),row['exit_code'],row['timed_out'])
        row['inventory']=output_inventory(output);row['passed']=True
    except BaseException as error:row['error']=type(error).__name__+': '+str(error)
    finally:
        if child is not None and child.poll() is None:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=2)
        row['inputs_sources_unchanged']=verify(inputs,digest)==plan
        row['copied_tcl_unchanged']=E.sha(output/'run.tcl')==plan['files_sha256']['run.tcl']
        row['openroad_unchanged']=E.sha(Path(exe).resolve())==row['openroad_sha256']
        row['actual_work_seconds']=time.monotonic()-start;row['work_budget_passed']=row['actual_work_seconds']<=90
        row['cgroup_after']=I.cgroup_snapshot();row['cgroup_counter_deltas']=I.counters(row['cgroup_before'],row['cgroup_after'])
        row['maximum_polled_memory_current']=peak;row['resource_feasible']=resource_observation(row)
        row['passed']=row['passed'] and row['work_budget_passed'] and row['resource_feasible'] and row['inputs_sources_unchanged'] and row['copied_tcl_unchanged'] and row['openroad_unchanged']
        row['native_log_sha256']=E.sha(output/'native.log') if (output/'native.log').exists() else None
        write(output/'report.json',row)
    return row


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    s=sub.add_parser('prepare');s.add_argument('--intake',type=Path,required=True);s.add_argument('--output',type=Path,required=True)
    for name in ('verify','proposal','run'):
        s=sub.add_parser(name);s.add_argument('--inputs',type=Path,required=True);s.add_argument('--plan-sha256',required=True)
        if name!='verify':s.add_argument('--output',type=Path,required=True)
        if name=='proposal':s.add_argument('--output-parent',type=Path,required=True)
    a=p.parse_args()
    if a.action=='prepare':prepare(a.intake,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':write(a.output,proposal(a.inputs,a.plan_sha256,a.output_parent));return 0
    r=run(a.inputs,a.plan_sha256,a.output);return 0 if r['passed'] else 2


if __name__=='__main__':raise SystemExit(main())
