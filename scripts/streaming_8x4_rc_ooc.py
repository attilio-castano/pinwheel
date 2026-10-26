"""New fixed count97 -> one finest M1 OOC diagnostic. Root alone runs Native."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_rc_incore as I
import streaming_8x4_rc_incore_readback as IR
P,E,W=I.P,I.E,I.W
ROOT=W.ROOT
NEW=('streaming_8x4_rc_ooc.py','streaming_8x4_rc_ooc_readback.py')
PRIOR='53393b5c1e68ee4ad3c619dc4622dbb27ca2f3bfbe298dd57565eb1222fb53b6'
SOURCE='95f4db1c89839cf73ce8167e8cf28a3cac4137f5e7a9f7a069f80afc0748d26a'
OUTPUT='rc-ooc-single-finest-01';CONTAINER='pinwheel-8x4-'+OUTPUT
MESH='0.0000431745';CASE='TYP-w.16-self-L10-E20';CHUNK=1048576;CHUNK_BYTES=CHUNK*16
EXPECTED_ERRORS=['Error: available free memory is not enough to allocate any chunk','Error: Cannot go Out-of-Core (possibly disk full)!']


def policy():
    return dict(schema='pinwheel.streaming-8x4-rc-ooc-policy.v1',maximum_calls=2,
        stages=['count97','solve'],count_ratio='1000000000000',count_expected_exit=97,solve_ratio='5',
        case=CASE,mesh=MESH,only_resource_deltas=['count-only f1e12 then restored default f5','TMPDIR/TMP/TEMP owned disk bind'],
        work_seconds=270,outer_seconds=330,seconds_per_leaf=120,cpus=1,memory_bytes=6442450944,
        no_extra_swap=True,pids=128,tmpfs_bytes=536870912,scratch_threshold_bytes=17179869184,
        scratch_threshold_is_hard_quota=False,poll_seconds='0.25',memory_preempt_fraction='0.95',
        host_disk_admission_reserve_bytes=12884901888,host_disk_running_reserve_bytes=12884901888,
        count_probe_expected97_is_numerical_success=False,no_retry_or_fallback=True,
        file_cache_charged_to_cgroup=True,unchanged_120s_may_limit_OOC_IO=True,
        model_qualified=False,full_pilot_passed=False,qualified_timing=False,root_go_required=True,
        scope='one exact finest M1 geometry only; count97, resource feasibility and point numerics are distinct')


def sources():return dict(I.sources(),**{n:E.sha(Path(__file__).with_name(n)) for n in NEW})


def evidence(inputs):
    base=inputs/'ooc-source';P.need(E.sha(base/'manifest.json')==SOURCE,'OOC source intake differs')
    manifest=json.loads((base/'manifest.json').read_text())
    for row in manifest['files']:
        raw=(base/row['name']).read_bytes()
        P.need(Path(row['name']).name==row['name'] and len(raw)==row['bytes']
            and hashlib.sha256(raw).hexdigest()==row['sha256']
            and hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==row['git_blob'],
            'Pinned OOC logging/wx source blob differs')
    return E.tree(base)


def previous(inputs):
    prior=inputs/'prior';plan=I.verify(prior/'preparation',PRIOR)
    fixed={'resource.json':'80ed9b0d475abd0f1420701e671bcc130bbe4dc2a2d8b2090c3729737109e2fb',
        'proposal.json':'ac8dbd09ae5450f9e285fd944a887bbf634862814993b3c7cf9d692c5e17c589'}
    for n,pin in fixed.items():P.need(E.sha(prior/n)==pin,'Exact original in-core resource/proposal differs')
    report=json.loads((prior/'results/report.json').read_text());proposal=json.loads((prior/'proposal.json').read_text())
    resource=json.loads((prior/'resource.json').read_text())
    P.need(report['plan_sha256']==PRIOR and report['passed'] is True and report['measurement_packet_completed'] is True
        and report['resource_feasible'] is True and report['numeric_passed'] is True
        and resource['argv']==proposal['argv'] and resource['status']=='completed' and resource['exit_code']==0
        and resource['cleanup_confirmed'] is True and resource['inputs_unchanged'] is True
        and resource['owned_processes_remaining']==resource['containers_remaining']==resource['cleanup_errors']==[],
        'Original two-leaf pass/closed cleanup differs')
    for index,job in enumerate(report['jobs']):
        owner=prior/'results'/('job-'+str(index).zfill(3));P.need(E.sha(owner/'report.json')==job['report_sha256'],'Original in-core leaf seal differs')
        row=IR.leaf(prior/'preparation',PRIOR,index,owner)
        P.need(row['numeric_passed'] and row['resource_feasible'],'Original in-core leaf not fully passed')
    P.need(len(report['jobs'])==2,'Original complete two-leaf membership differs')
    old,case=I.original(prior/'preparation',0)
    P.need(case['name']==CASE,'Exact selected M1 geometry differs')
    return old,case,plan['runtime']


def prepare(campaign,runtime,output):
    campaign,runtime,output=(p.resolve() for p in (campaign,runtime,output))
    P.need(campaign.resolve()==ROOT/'build/campaigns/8x4-20261022-01' and not output.exists() and output.parent.is_dir(),
        'Wrong campaign/fresh OOC owner')
    # Full independent original readback is performed on original HOST paths.
    pp=campaign/'rc-incore-command-proposal-02.json';proposal=json.loads(pp.read_text())
    closed=IR.readback(campaign/'rc-incore-preparation-02',PRIOR,campaign/'rc-native-outputs'/I.OUTPUT,runtime,
        ROOT/'build/streaming-tt-resources/8x4-rc-incore-two-leaf-01/report.json',pp)
    P.need(closed['numeric_passed'] and closed['resource_feasible'],'Original in-core authority not closed')
    output.mkdir();(output/'prior').mkdir()
    shutil.copytree(campaign/'rc-incore-preparation-02',output/'prior/preparation')
    shutil.copytree(campaign/'rc-native-outputs'/I.OUTPUT,output/'prior/results')
    shutil.copyfile(pp,output/'prior/proposal.json')
    shutil.copyfile(ROOT/'build/streaming-tt-resources/8x4-rc-incore-two-leaf-01/report.json',output/'prior/resource.json')
    shutil.copytree(campaign/'rc-ooc-source-intake-01',output/'ooc-source')
    old,case,inventory=previous(output);P.need(E.tree(runtime)==inventory,'OOC runtime differs')
    shutil.copytree(campaign/'rc-incore-preparation-02/original-0/failed/work',output/'geometry')
    scratch=campaign/('rc-ooc-scratch-'+output.name.rsplit('-',1)[-1]);P.need(not scratch.exists(),'Fresh OOC scratch owner required')
    row=dict(schema='pinwheel.streaming-8x4-rc-ooc-plan.v1',qualified=False,model_qualified=False,
        full_pilot_passed=False,qualified_timing=False,native_executed=False,policy=policy(),
        prior_incore_plan_sha256=PRIOR,case=case,original_solver_policy=old['policy'],runtime=inventory,
        scratch_host_path=str(scratch),source_evidence=evidence(output),producer_sha256=sources(),files=W.input_files(output))
    W.write(output/'plan.json',row);digest=E.sha(output/'plan.json');verify(output,digest)
    scratch.mkdir();W.write(scratch/'owner.json',ownership(row,digest));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'New OOC plan hash differs')
    row=json.loads((inputs/'plan.json').read_text());old,case,runtime=previous(inputs)
    scratch=Path(row['scratch_host_path'])
    P.need(row['schema']=='pinwheel.streaming-8x4-rc-ooc-plan.v1'
        and all(row[k] is False for k in ('qualified','model_qualified','full_pilot_passed','qualified_timing','native_executed'))
        and row['policy']==policy() and row['prior_incore_plan_sha256']==PRIOR and row['case']==case
        and row['original_solver_policy']==old['policy'] and row['runtime']==runtime
        and row['source_evidence']==evidence(inputs) and row['producer_sha256']==sources()
        and row['files']==W.input_files(inputs) and E.tree(inputs/'geometry')==case['files']
        and scratch.parent==ROOT/'build/campaigns/8x4-20261022-01'
        and re.fullmatch(r'rc-ooc-scratch-\d{2}',scratch.name), 'OOC exact authority/source/input/policy differs')
    return row


def ownership(plan,digest):
    return dict(schema='pinwheel.streaming-8x4-rc-ooc-scratch-owner.v1',plan_sha256=digest,
        scratch_host_path=plan['scratch_host_path'],stages=policy()['stages'],ephemeral_solver_scratch_only=True)


def verify_owner(root,plan,digest,fresh=False):
    P.need(root.is_dir() and not root.is_symlink() and (root/'owner.json').is_file() and not (root/'owner.json').is_symlink()
        and json.loads((root/'owner.json').read_text())==ownership(plan,digest),'OOC scratch ownership differs')
    allowed={'owner.json'} if fresh else {'owner.json','count97','solve'}
    P.need({x.name for x in root.iterdir()}<=allowed,'Unowned OOC scratch entry')
    P.need(all(x.is_dir() and not x.is_symlink() for x in root.iterdir() if x.name!='owner.json'),'Aliased/non-directory OOC stage scratch')


def proposal(inputs,digest,runtime,parent,require_fresh=True):
    inputs,runtime,parent=(p.resolve() for p in (inputs,runtime,parent));plan=verify(inputs,digest)
    scratch=Path(plan['scratch_host_path']);verify_owner(scratch,plan,digest,fresh=require_fresh)
    P.need(E.tree(runtime)==plan['runtime'] and parent.is_dir() and (not require_fresh or not (parent/OUTPUT).exists()),'OOC runtime/output differs')
    argv=['docker','run','--name',CONTAINER,'--rm','--pull','never','--network','none','--read-only',
        '--cpus','1','--memory','6g','--memory-swap','6g','--pids-limit','128','--tmpfs','/tmp:rw,nosuid,noexec,size=536870912',
        '--mount',f'type=bind,src={Path(__file__).resolve().parent},dst=/rc-source,readonly',
        '--mount',f'type=bind,src={inputs},dst=/rc-inputs,readonly',
        '--mount',f'type=bind,src={runtime},dst=/solver/runtime,readonly',
        '--mount',f'type=bind,src={scratch},dst=/ooc-scratch',
        '--mount',f'type=bind,src={parent},dst=/rc-output-parent','--entrypoint',
        '/nix/store/lqn6mbgzzdrqq2qkwddcmxj9z6amdd86-python3-3.13.13/bin/python3',W.C.D.IMAGE,
        '-I','-B','/rc-source/'+NEW[0],'run','--inputs','/rc-inputs','--plan-sha256',digest,
        '--runtime','/solver/runtime','--output','/rc-output-parent/'+OUTPUT]
    return dict(schema='pinwheel.streaming-8x4-rc-ooc-command-proposal.v1',root_go_required=True,admitted=False,
        native_executed=False,model_qualified=False,full_pilot_passed=False,qualified_timing=False,
        plan_path=str(inputs/'plan.json'),plan_sha256=digest,runtime_path=str(runtime),scratch_host_path=str(scratch),
        scratch_owner_sha256=E.sha(scratch/'owner.json'),timeout_seconds=330,container_name=CONTAINER,policy=policy(),
        producer_sha256=plan['producer_sha256'],argv=argv)


def memtotal(raw):
    found=re.findall(r'^MemTotal:\s+(\d+) kB$',raw,re.M)
    P.need(len(found)==1 and 0<int(found[0])*1024<16_000_000_000_000,'Unsupported whole-VM memory bound')
    return int(found[0])*1024


def counts(raw):
    values={}
    for key,pattern in [('panels',r'^Number of panels after refinement: (\d+)$'),('links',r'^Number of links to be computed: (\d+)$')]:
        found=re.findall(pattern,raw,re.M);P.need(len(found)>=1 and len(set(found))==1 and int(found[0])>0,'Missing/mixed exact '+key)
        values[key]=int(found[0])
    return values


def header(raw,ratio):
    P.need(type(raw)is str and len(raw)<=8*1024*1024,'OOC raw log unsupported')
    for pattern,value in [(r'^Out-of-core free memory to link memory condition \(-f\):\s*('+P.NUM+r')\s*$',ratio),
        (r'^Mesh refinement \(-m\):\s*('+P.NUM+r')\s*$',MESH),
        (r'^Solution scheme \(-g\): Galerkin, GMRES tolerance \(-t\):\s*('+P.NUM+r')\s*$','0.0005'),
        (r'^Potential interaction coefficient to mesh refinement ratio \(-d\):\s*('+P.NUM+r')\s*$','0.25')]:
        found=re.findall(pattern,raw,re.M);P.need(len(found)==1 and P.number(found[0])==P.number(value),'OOC actual fixed header differs')
    P.need(re.findall(r'^Precond Type\(s\) \(-p\):\s*([^\r\n]*?)\s*$',raw,re.M)==['Jacobi'],'OOC preconditioner differs')


def parse_count(raw):
    header(raw,'1000000000000');result=counts(raw)
    errors=[line.strip() for line in raw.splitlines() if re.search(r'(?i)warning|\b(?:warn|error|fatal)\b|segmentation fault|killed|timeout',line)]
    P.need(errors==EXPECTED_ERRORS and raw.count('Cannot go out-of-core, terminating process')==1
        and len(re.findall(r'^Number of panels after refinement: \d+$',raw,re.M))==1
        and len(re.findall(r'^Number of links to be computed: \d+$',raw,re.M))==1
        and re.findall(r"^Out-of-core temporary files folder: '([^']+)'$",raw,re.M)==['/ooc-scratch/count97']
        and 'Dimension' not in raw and 'GMRES Iteration:' not in raw
        and len(re.findall(r'^Total time: '+P.NUM+r's \(\d+ days, \d+ hours, \d+ mins, \d+ s\)$',raw,re.M))==1,
        'Count probe is not exact intentional zero-chunk97 branch')
    return result


def projection(count,vm_total,base_peak):
    P.need(type(vm_total)is int and 0<vm_total<16_000_000_000_000 and type(base_peak)is int and base_peak>=0,
        'OOC projection actual memory observations invalid')
    n,l=count['panels'],count['links'];P.need(type(n)is int and type(l)is int and n>0 and l>0,'OOC dry counts invalid')
    maximum=vm_total//(5*CHUNK_BYTES)
    P.need(0<maximum<=200000,'OOC possible chunk range unsupported')
    padded=max(((l+c*CHUNK-1)//(c*CHUNK))*c*CHUNK_BYTES for c in range(1,maximum+1))
    terms=dict(observed_count_probe_cumulative_peak_bytes=base_peak,maximum_link_buffer_bytes=maximum*CHUNK_BYTES,
        two_worst_1001_vector_arrays_bytes=2*1001*n*8,work_vectors_bytes=24*n*8,
        Hessenberg_reserve_bytes=8016000,additional_untracked_reserve_bytes=536870912)
    total=sum(terms.values());disk=policy()['scratch_threshold_bytes']
    return dict(actual_counts=count,whole_VM_MemTotal_bytes=vm_total,possible_nonzero_chunks=[1,maximum],
        maximum_padded_file_bytes=padded,maximum_temp_files=2*max(((l+c*CHUNK-1)//(c*CHUNK))*c for c in range(1,maximum+1)),
        RAM_terms=terms,planning_RAM_total_bytes=total,not_a_proven_malloc_RSS_bound=True,
        all_VM_free_values_force_OOC=l*16*5>=vm_total,
        admitted=padded<disk and total<6442450944*95//100 and l*16*5>=vm_total)


def census(directory):
    P.need(directory.is_dir() and not directory.is_symlink(),'OOC stage scratch must be owned directory')
    entries=list(directory.iterdir());P.need(len(entries)<=10000,'OOC scratch entry limit exceeded');rows=[]
    for path in sorted(entries):
        try:info=path.lstat()
        except FileNotFoundError:continue
        P.need(re.fullmatch(r'frc[lp][0-9A-F]+\.tmp',path.name) and stat.S_ISREG(info.st_mode)
            and info.st_nlink==1,'Unowned/aliased/nonregular OOC scratch file')
        rows.append(dict(name=path.name,device=info.st_dev,inode=info.st_ino,bytes=info.st_size,
            allocated_bytes=info.st_blocks*512,mode=stat.S_IMODE(info.st_mode),uid=info.st_uid,
            content_hashed=False,ephemeral_not_numerical_authority=True))
    return rows


def scratch_measure(rows):return dict(logical_bytes=sum(r['bytes'] for r in rows),allocated_bytes=sum(r['allocated_bytes'] for r in rows),files=len(rows))


def scratch_cleanup(directory):
    rows=census(directory)
    for row in rows:
        path=directory/row['name'];info=path.lstat()
        P.need((info.st_dev,info.st_ino,info.st_size,info.st_blocks*512)==(row['device'],row['inode'],row['bytes'],row['allocated_bytes']),
            'OOC scratch changed after child reaping')
        path.unlink()
    P.need(not list(directory.iterdir()),'OOC owned scratch cleanup incomplete')
    return dict(before=rows,after=[],only_exact_owned_regular_scratch_removed=True)


def solver_argv(plan,stage):
    P.need(stage in policy()['stages'],'Undeclared OOC stage')
    return W.solver_argv(plan['original_solver_policy'],MESH)+['-f'+('1000000000000' if stage=='count97' else '5')]


def environment(stage):return dict(W.C.ENVIRONMENT,TMPDIR='/ooc-scratch/'+stage,TMP='/ooc-scratch/'+stage,TEMP='/ooc-scratch/'+stage)


def resource_pass(row):
    delta=I.counters(row['cgroup_before'],row['cgroup_after'])
    P.need(row['cgroup_before']['memory_max']==row['cgroup_after']['memory_max']
        and row['cgroup_after']['memory_peak']>=row['cgroup_before']['memory_peak']
        and row['counter_deltas']==delta and row['cgroup_before']['memory_current']<=row['maximum_polled_memory_current']<=row['cgroup_after']['memory_peak'],
        'OOC actual counter/polled peak mismatch')
    return (row['stage'] in policy()['stages'] and type(row['exit_code'])is int
        and row['exit_code']==(97 if row['stage']=='count97' else 0) and row['process_tree_reaped'] is True and not row['timed_out'] and row['guard_reason'] is None
        and row['cgroup_after']['memory_peak']<row['cgroup_after']['memory_max']*95//100
        and all(v==0 for values in delta.values() for k,v in values.items() if k=='max' or k.startswith('oom'))
        and max(row['maximum_scratch_logical_bytes'],row['maximum_scratch_allocated_bytes'])<policy()['scratch_threshold_bytes']
        and row['minimum_bind_disk_free_bytes']>=policy()['host_disk_running_reserve_bytes']
        and row['scratch_cleanup']['after']==[] and row['inputs_runtime_unchanged'] is True)


def leaf(inputs,digest,plan,runtime,stage,output,admission=None):
    P.need(not output.exists() and str(runtime)=='/solver/runtime','Fresh OOC leaf/runtime mount required')
    output.mkdir();work=output/'work';shutil.copytree(inputs/'geometry',work)
    scratch=Path('/ooc-scratch')/stage;P.need(not scratch.exists(),'Fresh OOC stage scratch required');scratch.mkdir()
    before=I.cgroup_snapshot();started=time.monotonic();child=None
    meminfo=Path('/proc/meminfo').read_text();(output/'meminfo.txt').write_text(meminfo);total=memtotal(meminfo)
    if stage=='solve':P.need(admission and admission['admitted'] and total==admission['whole_VM_MemTotal_bytes'],'OOC pre-exec whole-VM projection changed')
    row=dict(schema='pinwheel.streaming-8x4-rc-ooc-leaf.v1',plan_sha256=digest,stage=stage,
        argv=solver_argv(plan,stage),environment=environment(stage),timeout_seconds=120,
        cgroups=E.verify_cgroups(),cgroup_before=before,maximum_polled_memory_current=before['memory_current'],
        minimum_bind_disk_free_bytes=shutil.disk_usage(scratch).free,maximum_scratch_logical_bytes=0,
        maximum_scratch_allocated_bytes=0,maximum_scratch_files=0,observed_temp_prefixes=[],timed_out=False,guard_reason=None,
        process_tree_reaped=False,exit_code=None,expected_count97_observed=False,counts=None,numeric=None,
        numerical_passed=False,resource_feasible=False,qualified=False,model_qualified=False,full_pilot_passed=False,qualified_timing=False)
    try:
        P.need(row['minimum_bind_disk_free_bytes']>=17179869184+12884901888,'OOC disk admission lacks threshold+12GiB reserve')
        with (output/'native.log').open('xb') as stream:
            child=subprocess.Popen(row['argv'],cwd=work,env=row['environment'],stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
            while child.poll() is None:
                current=I.cgroup_snapshot()['memory_current'];row['maximum_polled_memory_current']=max(current,row['maximum_polled_memory_current'])
                sample=census(scratch);measure=scratch_measure(sample);free=shutil.disk_usage(scratch).free
                row['observed_temp_prefixes']=sorted(set(row['observed_temp_prefixes'])|{r['name'][:4] for r in sample})
                row['minimum_bind_disk_free_bytes']=min(free,row['minimum_bind_disk_free_bytes'])
                for key,source in [('maximum_scratch_logical_bytes','logical_bytes'),('maximum_scratch_allocated_bytes','allocated_bytes'),('maximum_scratch_files','files')]:row[key]=max(row[key],measure[source])
                elapsed=time.monotonic()-started
                reason=('memory95' if current>=before['memory_max']*95//100 else 'scratch16GiB' if max(measure['logical_bytes'],measure['allocated_bytes'])>=17179869184 else 'disk12GiB' if free<12884901888 else 'timeout120' if elapsed>=120 else None)
                if reason:row['guard_reason']=reason;row['timed_out']=reason=='timeout120';break
                time.sleep(.25)
            if child.poll() is None:os.killpg(child.pid,signal.SIGKILL)
            row['exit_code']=child.wait(timeout=2)
        try:os.killpg(child.pid,0)
        except ProcessLookupError:row['process_tree_reaped']=True
        else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('OOC process group remained live')
        raw=(output/'native.log').read_text()
        if stage=='count97':
            P.need(row['exit_code']==97,'Count probe expected97 exit missing');row['counts']=parse_count(raw);row['expected_count97_observed']=True
        else:
            P.need(row['exit_code']==0,'OOC solve exit failure');header(raw,'5')
            P.need(re.findall(r"^Out-of-core temporary files folder: '([^']+)'$",raw,re.M)==['/ooc-scratch/solve'],'OOC actual temp path/fallback differs')
            row['counts']=counts(raw);row['numeric']=I.X.parse(raw,dict(policy=plan['original_solver_policy']),plan['case'],MESH);row['numerical_passed']=True
    except BaseException as error:row['error']=type(error).__name__+': '+str(error)
    finally:
        if child is not None and child.poll() is None:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=2)
        terminal=census(scratch);measure=scratch_measure(terminal)
        row['observed_temp_prefixes']=sorted(set(row['observed_temp_prefixes'])|{r['name'][:4] for r in terminal})
        for key,source in [('maximum_scratch_logical_bytes','logical_bytes'),('maximum_scratch_allocated_bytes','allocated_bytes'),('maximum_scratch_files','files')]:row[key]=max(row[key],measure[source])
        row['scratch_cleanup']=scratch_cleanup(scratch) if row['process_tree_reaped'] else dict(before=terminal,after=terminal,only_exact_owned_regular_scratch_removed=False)
        row['cgroup_after']=I.cgroup_snapshot();row['counter_deltas']=I.counters(before,row['cgroup_after'])
        row['inputs_runtime_unchanged']=verify(inputs,digest)==plan and E.tree(runtime)==plan['runtime'] and E.tree(work)==plan['case']['files']
        row['resource_feasible']=resource_pass(row)
        if stage=='solve':row['resource_feasible'] &= row['observed_temp_prefixes']==['frcl','frcp'] and row['maximum_scratch_logical_bytes']>0
        row['log_sha256']=E.sha(output/'native.log') if (output/'native.log').exists() else None
        row['meminfo_sha256']=E.sha(output/'meminfo.txt');row['wall_seconds']=time.monotonic()-started;W.write(output/'report.json',row)
    return row


def run(inputs,digest,runtime,output):
    plan=verify(inputs,digest);E.verify_cgroups();root=Path('/ooc-scratch');verify_owner(root,plan,digest,fresh=True)
    P.need(not output.exists() and output.parent.is_dir() and E.tree(runtime)==plan['runtime'],'OOC fresh output/runtime differs')
    output.mkdir();started=time.monotonic();row=dict(schema='pinwheel.streaming-8x4-rc-ooc-execution.v1',plan_sha256=digest,
        policy=policy(),qualified=False,model_qualified=False,full_pilot_passed=False,qualified_timing=False,
        passed=False,measurement_packet_completed=False,resource_feasible=False,numerical_passed=False,projection=None,jobs=[])
    try:
        first=leaf(inputs,digest,plan,runtime,'count97',output/'count97')
        row['jobs'].append(dict(stage='count97',report_sha256=E.sha(output/'count97/report.json')))
        P.need(first['resource_feasible'] and first['expected_count97_observed'],'Count97 resource/typed branch gate failed')
        P.need(first['scratch_cleanup']['before']==[],'Count97 unexpectedly created chunk files')
        raw=Path('/proc/meminfo').read_text();(output/'solve-admission-meminfo.txt').write_text(raw)
        total=memtotal(raw);P.need(total==memtotal((output/'count97/meminfo.txt').read_text()),'Whole VM memory total changed')
        row['projection']=projection(first['counts'],total,first['cgroup_after']['memory_peak'])
        P.need(row['projection']['admitted'],'Exact finest OOC count-derived resource projection rejected')
        P.need(time.monotonic()-started<140,'Insufficient full second-call budget')
        second=leaf(inputs,digest,plan,runtime,'solve',output/'solve',row['projection'])
        row['jobs'].append(dict(stage='solve',report_sha256=E.sha(output/'solve/report.json')))
        row['solve_counts_match_probe']=second['counts']==first['counts']
        row['measurement_packet_completed']=first['process_tree_reaped'] and second['process_tree_reaped']
        row['resource_feasible']=first['resource_feasible'] and second['resource_feasible']
        row['numerical_passed']=second['numerical_passed'] and row['solve_counts_match_probe'];row['passed']=row['resource_feasible'] and row['numerical_passed']
    except BaseException as error:row['error']=type(error).__name__+': '+str(error)
    finally:
        row['inputs_runtime_unchanged']=verify(inputs,digest)==plan and E.tree(runtime)==plan['runtime']
        verify_owner(root,plan,digest);row['scratch_terminal_entries']=sorted(p.name for p in root.iterdir())
        row['scratch_stage_directories_empty']=all(not list(p.iterdir()) for p in root.iterdir() if p.is_dir())
        row['passed'] &= row['inputs_runtime_unchanged'] and row['scratch_stage_directories_empty']
        row['work_wall_seconds']=time.monotonic()-started;row['work_budget_satisfied']=row['work_wall_seconds']<=270
        row['resource_feasible'] &= row['work_budget_satisfied'];row['passed'] &= row['work_budget_satisfied']
        row['wall_seconds']=row['work_wall_seconds'];W.write(output/'report.json',row)
    return row


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    q=sub.add_parser('prepare')
    for n in ('campaign','runtime','output'):q.add_argument('--'+n,type=Path,required=True)
    for action in ('verify','proposal','run'):
        q=sub.add_parser(action);q.add_argument('--inputs',type=Path,required=True);q.add_argument('--plan-sha256',required=True)
        if action!='verify':
            q.add_argument('--runtime',type=Path,required=True);q.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if a.action=='prepare':prepare(a.campaign,a.runtime,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':W.write(a.output,proposal(a.inputs,a.plan_sha256,a.runtime,a.output.parent/'rc-native-outputs'));return 0
    row=run(a.inputs,a.plan_sha256,a.runtime,a.output);return 0 if row['passed'] else 2


if __name__=='__main__':raise SystemExit(main())
