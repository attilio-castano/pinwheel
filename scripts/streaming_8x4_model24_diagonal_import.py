"""Two fresh synthetic import→consumer calls; Root alone admits Native."""
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
import streaming_8x4_model24_diagonal_projection as D
import streaming_8x4_rc_cap_marker as M
P,E,I=S.P,S.E,S.I
ROOT=S.ROOT
NEW=('streaming_8x4_model24_diagonal_import.py','streaming_8x4_model24_diagonal_projection.py','streaming_8x4_model24_diagonal_readback.py')
OUTPUT='model24-synthetic-diagonal-import-01';CONTAINER='pinwheel-'+OUTPUT
API_SOURCE='4c55aa722c16faae0192f026cea54d069c59e20f999eee9370ea289df4abee2e'
NATIVE_SOURCE='e344e7e6ff5315e9d5e993d50bf29db4cbdd2ae1b85486b61ebb2ee77ff467a9'
HISTORICAL_MARKER='633725e5669b788df4200af45db46c183f1b8c008136e7291308357f533bf59d'
OPENROAD_SHA='b2159d4a99a9b236a6e95bbf6efc88bcfd2b843df273e97f169b456bc3b0453b'
write=S.write


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


def native_source(inputs):
    owner=inputs/'native-source';P.need(E.sha(owner/'manifest.json')==NATIVE_SOURCE,'Exact native parser/import/writer intake differs');m=json.loads((owner/'manifest.json').read_text())
    P.need(m['imported_or_executed'] is False,'Source intake must remain data')
    for row in m['sources']:
        data=(owner/row['name']).read_bytes();P.need(len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['computed_git_blob'],'Native source content/blob differs')
    return m


def api_source(inputs):
    owner=inputs/'api-source';path=owner/'manifest.json';P.need(E.sha(path)==API_SOURCE,'Exact public model API/context source differs')
    m=json.loads(path.read_text());P.need(m['commit']==S.N.OPENROAD_COMMIT and m['source_as_data_only'] is True and m['imported_or_executed'] is False,
        'Model API source must remain pinned data')
    expected={'manifest.json'}|set(m['auxiliary_files'])|{r['name'] for r in m['files']}
    P.need({p.name for p in owner.iterdir()}==expected and len(m['files'])==4,'Complete public model API source membership differs')
    for row in m['files']:
        p=owner/row['name'];data=p.read_bytes();P.need(p.is_file() and not p.is_symlink() and Path(row['name']).name==row['name']
            and len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
            and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['observed_and_computed_git_blob'],
            'Public model API/context source bytes/blob differ')
    for n,row in m['auxiliary_files'].items():
        p=owner/n;P.need(p.is_file() and not p.is_symlink() and Path(n).name==n and p.stat().st_size==row['bytes'] and E.sha(p)==row['sha256'],
            'Public model API tree/provenance witness differs')
    return m


def tcl():
    begin='''puts "MODEL24_DIAG_VERSION_BEGIN"
set v [ord::openroad_version]
puts $v
puts "MODEL24_DIAG_VERSION_END"
puts "MODEL24_DIAG_API_BEGIN"
help init_rcx_model
help read_rcx_tables
help write_rcx_model
puts "MODEL24_DIAG_API_END"
init_rcx_model -corner_names {MODEL24_SYNTHETIC} -met_cnt 5
read_rcx_tables -corner_name MODEL24_SYNTHETIC -file synthetic.caps
write_rcx_model -file imported.rules
puts "MODEL24_DIAG_IMPORT_DONE"
'''
    widths='foreach l {Metal1 Metal2 Metal3 Metal4 TopMetal1} { puts "MODEL24_DIAG_WIDTH layer=$l width=[[$tech findLayer $l] getWidth]" }\n'
    body=D.G.C.tcl().replace('write_def before.def',widths+'write_def before.def')
    return begin+body.replace('rules.txt','imported.rules').replace('puts "PINWHEEL_CAP_TERMINAL"','puts "PINWHEEL_CAP_TERMINAL"\nputs "MODEL24_DIAG_TERMINAL"')


def pattern_data(inputs):
    closed=json.loads((inputs/'pattern-authority.json').read_text());P.need(closed['pattern_intake_completed'] is True and closed['model_qualified'] is False,'Exact closed native pattern scope differs');patterns=json.loads((inputs/'patterns.json').read_text());expected=closed['inventory']['observed_cases']
    P.need(len(patterns)==len(expected)==310 and [(r['path'],hashlib.sha256(r['text'].encode()).hexdigest()) for r in patterns]==[(r['path'],r['sha256']) for r in expected],
        'Full actual native pattern/data order/hash differs');return patterns


def files(inputs):
    patterns=pattern_data(inputs);return {'tech.lef':(inputs/'tech.lef').read_bytes(),'fixture.def':D.fixture().encode(),'run.tcl':tcl().encode(),
        **{mode+'.caps':D.caps(patterns,mode).encode() for mode in D.MODES}}


def prepare(pattern_launcher,native_intake,marker_intake,api_intake,output):
    args,closed,h=S.parent_pattern(pattern_launcher);P.need(not output.exists() and output.parent.is_dir(),'Fresh synthetic import preparation required');output.mkdir()
    shutil.copytree(native_intake,output/'native-source');shutil.copytree(api_intake,output/'api-source')
    for name in M.INTAKES:shutil.copytree(marker_intake/name,output/name)
    shutil.copyfile(marker_intake/'tech.lef',output/'tech.lef');P.need(E.sha(output/'tech.lef')==D.G.C.TECH_HASH,'Exact retained technology LEF differs')
    shutil.copyfile(ROOT/'build/campaigns/8x4-20261022-01/rc-cap-marker-independent-readback-01.json',output/'historical-factor-two-failure.json')
    shutil.copyfile(pattern_launcher,output/'pattern-launcher.json');shutil.copyfile(Path(args['--output']),output/'pattern-authority.json')
    patterns=[dict(path=r['path'],text=(Path(args['--directory'])/r['path']).read_text()) for r in closed['inventory']['observed_cases']];write(output/'patterns.json',patterns)
    for n,data in files(output).items():
        if n=='tech.lef':continue
        (output/n).write_bytes(data)
    row=dict(schema='pinwheel.model24-synthetic-diagonal-plan.v1',policy=D.policy(),synthetic_projection=D.synthetic_projection(),
        pattern_launcher_sha256=S.PATTERN_LAUNCHER,pattern_authority_sha256=h,openroad_sha256=OPENROAD_SHA,historical_factor_two_failure_sha256=HISTORICAL_MARKER,
        native_source=native_source(output),api_source=api_source(output),source_intakes={n:M.source_intake(output,n) for n in M.INTAKES},
        producer_sha256=sources(),files=I.W.input_files(output),root_go_required=True,native_executed=False,model_qualified=False,qualified_timing=False)
    write(output/'plan.json',row);verify(output,E.sha(output/'plan.json'));return row


def verify(inputs,digest):
    P.need(E.sha(inputs/'plan.json')==digest,'Synthetic import plan differs');row=json.loads((inputs/'plan.json').read_text());expected=files(inputs)
    for name,data in expected.items():P.need((inputs/name).read_bytes()==data and not(inputs/name).is_symlink(),'Exact synthetic owned input bytes differ')
    history=json.loads((inputs/'historical-factor-two-failure.json').read_text());P.need(E.sha(inputs/'historical-factor-two-failure.json')==HISTORICAL_MARKER and history['lookup_marker_diagnostic_passed'] is False and history['model_qualified'] is False,'Historical factor-two failure must remain failed')
    P.need(E.sha(inputs/'tech.lef')==D.G.C.TECH_HASH and E.sha(inputs/'pattern-launcher.json')==S.PATTERN_LAUNCHER
        and E.sha(inputs/'pattern-authority.json')==row['pattern_authority_sha256'],'Exact source/census/LEF identity differs')
    P.need(row['schema']=='pinwheel.model24-synthetic-diagonal-plan.v1' and row['policy']==D.policy() and row['synthetic_projection']==D.synthetic_projection()
        and row['historical_factor_two_failure_sha256']==HISTORICAL_MARKER and row['pattern_launcher_sha256']==S.PATTERN_LAUNCHER and row['openroad_sha256']==OPENROAD_SHA
        and row['native_source']==native_source(inputs) and row['api_source']==api_source(inputs) and row['source_intakes']=={n:M.source_intake(inputs,n) for n in M.INTAKES}
        and row['producer_sha256']==sources() and row['files']==I.W.input_files(inputs) and row['root_go_required'] is True
        and all(row[k] is False for k in ('native_executed','model_qualified','qualified_timing')),'Synthetic source/projection/complete membership/claim differs');return row


def parse_leaf(owner,mode):
    raw=(owner/'native.log').read_text();P.need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout',raw),'Synthetic Native warning/error')
    versions=re.findall(r'^MODEL24_DIAG_VERSION_BEGIN\n(.*?)^MODEL24_DIAG_VERSION_END$',raw,re.M|re.S);P.need(len(versions)==1 and raw.count('MODEL24_DIAG_VERSION_BEGIN')==raw.count('MODEL24_DIAG_VERSION_END')==1,'Synthetic actual version missing/duplicated')
    commits=[t for t in re.findall(r'[0-9a-f]+',versions[0]) if len(t)>=40];P.need(commits and set(commits)=={S.N.OPENROAD_COMMIT},'Synthetic actual full OpenROAD commit differs')
    markers=['MODEL24_DIAG_VERSION_END','MODEL24_DIAG_API_BEGIN','MODEL24_DIAG_API_END','MODEL24_DIAG_IMPORT_DONE','PINWHEEL_CAP_TERMINAL','MODEL24_DIAG_TERMINAL']
    P.need(all(raw.count(m)==1 for m in markers) and [raw.index(m) for m in markers]==sorted(raw.index(m) for m in markers),'Synthetic actual API/import/extraction terminal order differs')
    P.need(re.findall(r'PINWHEEL_CAP_INVENTORY insts=(\d+) iterms=(\d+) nets=(\d+) bterms=(\d+)',raw)==[('0','0','6','12')]
        and re.findall(r'PINWHEEL_CAP_TECH dbu=(\d+) m1_width=(\d+)',raw)==[('1000','160')],'Synthetic actual cell/port/unit/default-width inventory differs')
    P.need(re.findall(r'MODEL24_DIAG_WIDTH layer=(\w+) width=(\d+)',raw)==[(m,str(D.G.WIDTHS[m])) for m in D.G.METALS],'Synthetic actual all-default-width inventory differs')
    P.need((owner/'before.def').read_bytes()==(owner/'after.def').read_bytes(),'Synthetic geometry changed');D.G.validate((owner/'before.def').read_text(),D.G.definition('retained'))
    return dict(imported_grid=D.import_grid((owner/'imported.rules').read_text(),mode),consumer=D.read_cap((owner/'result.spef').read_text(),mode),
        actual_openroad_commit=S.N.OPENROAD_COMMIT,source_data_executed=False,model_qualified=False)


def owned_inventory(owner):
    result={}
    for p in sorted(owner.rglob('*')):
        P.need(not p.is_symlink(),'Synthetic owned output aliases forbidden')
        if p.is_file() and p!=owner/'report.json':result[str(p.relative_to(owner))]=dict(bytes=p.stat().st_size,sha256=E.sha(p))
    return result


def leaf(inputs,digest,plan,mode,owner):
    owner.mkdir()
    for n in ('tech.lef','fixture.def','run.tcl'):shutil.copyfile(inputs/n,owner/n)
    shutil.copyfile(inputs/(mode+'.caps'),owner/'synthetic.caps');exe=shutil.which('openroad');P.need(exe and E.sha(Path(exe).resolve())==OPENROAD_SHA,'Pinned observed OpenROAD executable differs')
    start=time.monotonic();cg=D.G.C.cgroups();env=dict(PATH=os.environ['PATH'],HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE');child=None
    row=dict(schema='pinwheel.model24-synthetic-diagonal-leaf.v1',plan_sha256=digest,mode=mode,argv=[exe,'-no_init','-exit','run.tcl'],environment=env,openroad_sha256=OPENROAD_SHA,
        cgroups=cg,cgroup_before=I.cgroup_snapshot(),exit_code=None,timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,process_tree_reaped=False,
        native_executed=False,control_passed=False,numeric=None,resource_feasible=False,passed=False,model_qualified=False,qualified_timing=False)
    peak=row['cgroup_before']['memory_current']
    try:
        with (owner/'native.log').open('xb') as stream:
            child=subprocess.Popen(row['argv'],cwd=owner,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True);row['native_executed']=True
            while child.poll() is None:
                current=I.cgroup_snapshot()['memory_current'];peak=max(peak,current);size=sum(p.stat().st_size for p in owner.rglob('*') if p.is_file() and not p.is_symlink())
                if time.monotonic()-start>=30 or current>=2147483648*95//100 or size>D.policy()['maximum_output_bytes']:
                    row['timed_out']=time.monotonic()-start>=30;row['memory_guard_triggered']=current>=2147483648*95//100;row['output_guard_triggered']=size>D.policy()['maximum_output_bytes'];os.killpg(child.pid,signal.SIGKILL);break
                try:child.wait(timeout=.25)
                except subprocess.TimeoutExpired:pass
            row['exit_code']=child.wait(timeout=2)
        try:os.killpg(child.pid,0)
        except ProcessLookupError:row['process_tree_reaped']=True
        else:os.killpg(child.pid,signal.SIGKILL);raise ValueError('Synthetic child process group remains live')
        P.need(row['exit_code']==0 and not row['timed_out'] and not row['memory_guard_triggered'] and not row['output_guard_triggered'],'Synthetic actual native resource/exit failed')
        row['numeric']=parse_leaf(owner,mode);row['control_passed']=True
    except BaseException as e:row['error']=type(e).__name__+': '+str(e)
    finally:
        if child is not None and child.poll() is None:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=2)
        row['inputs_sources_unchanged']=verify(inputs,digest)==plan;row['openroad_unchanged']=E.sha(Path(exe).resolve())==OPENROAD_SHA
        row['copied_inputs_unchanged']=all((owner/n).read_bytes()==(inputs/n).read_bytes() for n in ('tech.lef','fixture.def','run.tcl')) and (owner/'synthetic.caps').read_bytes()==(inputs/(mode+'.caps')).read_bytes()
        row['actual_work_seconds']=time.monotonic()-start;row['work_budget_passed']=row['actual_work_seconds']<=40
        row['cgroup_after']=I.cgroup_snapshot();row['cgroup_counter_deltas']=I.counters(row['cgroup_before'],row['cgroup_after']);row['maximum_polled_memory_current']=peak;row['resource_feasible']=S.N.resource_observation(row) and row['work_budget_passed']
        row['output_inventory']=owned_inventory(owner);row['resource_feasible']=row['resource_feasible'] and sum(r['bytes'] for r in row['output_inventory'].values())<=D.policy()['maximum_output_bytes'];row['native_log_sha256']=E.sha(owner/'native.log') if (owner/'native.log').exists() else None
        row['passed']=row['control_passed'] and row['resource_feasible'] and row['inputs_sources_unchanged'] and row['openroad_unchanged'] and row['copied_inputs_unchanged'];write(owner/'report.json',row)
    return row


def run(inputs,digest,output):
    start=time.monotonic();plan=verify(inputs,digest);P.need(not output.exists() and output.name==OUTPUT and output.parent.is_dir(),'Fresh synthetic output required');output.mkdir();jobs=[]
    row=dict(schema='pinwheel.model24-synthetic-diagonal-execution.v1',plan_sha256=digest,policy=D.policy(),jobs=jobs,passed=False,measurement_packet_completed=False,model_qualified=False,qualified_timing=False)
    try:
        for mode in D.MODES:
            P.need(time.monotonic()-start<50,'Insufficient complete next-call budget');owner=output/mode;r=leaf(inputs,digest,plan,mode,owner);jobs.append(dict(mode=mode,passed=r['passed'],resource_feasible=r['resource_feasible'],report_sha256=E.sha(owner/'report.json')))
            P.need(r['resource_feasible'] and r['inputs_sources_unchanged'] and r['openroad_unchanged'] and r['copied_inputs_unchanged'],'Synthetic resource/custody failure stops suffix')
    except BaseException as e:row['error']=type(e).__name__+': '+str(e)
    row['deck_delta']=None
    if len(jobs)==2 and all(j['passed'] for j in jobs):
        try:row['deck_delta']=D.compare_decks((output/D.MODES[0]/'imported.rules').read_text(),(output/D.MODES[1]/'imported.rules').read_text())
        except ValueError as e:row['error']=type(e).__name__+': '+str(e)
    row['actual_work_seconds']=time.monotonic()-start;row['work_budget_passed']=row['actual_work_seconds']<=90;row['measurement_packet_completed']=len(jobs)==2
    row['inputs_sources_unchanged']=verify(inputs,digest)==plan;row['passed']=len(jobs)==2 and all(j['passed'] for j in jobs) and row['work_budget_passed'] and row['inputs_sources_unchanged'] and row['deck_delta'] is not None;write(output/'report.json',row);return row


def proposal(inputs,digest,parent,require_fresh=True):
    plan=verify(inputs,digest);P.need(parent.is_dir() and (not require_fresh or not(parent/OUTPUT).exists()),'Fresh synthetic output required')
    argv=['docker','run','--name',CONTAINER,'--rm','--pull','never','--network','none','--read-only','--cpus','1','--memory','2g','--memory-swap','2g','--pids-limit','128','--tmpfs','/tmp:rw,nosuid,noexec,size=134217728',
        '--mount',f'type=bind,src={Path(__file__).resolve().parent},dst=/model24-source,readonly','--mount',f'type=bind,src={inputs.resolve()},dst=/model24-inputs,readonly','--mount',f'type=bind,src={parent.resolve()},dst=/model24-output-parent','--entrypoint',D.G.C.PYTHON,D.G.C.IMAGE,'-I','-B','/model24-source/'+NEW[0],'run','--inputs','/model24-inputs','--plan-sha256',digest,'--output','/model24-output-parent/'+OUTPUT]
    return dict(schema='pinwheel.model24-synthetic-diagonal-command-proposal.v1',root_go_required=True,admitted=False,native_executed=False,model_qualified=False,qualified_timing=False,
        plan_path=str((inputs/'plan.json').resolve()),plan_sha256=digest,producer_sha256=plan['producer_sha256'],timeout_seconds=120,policy=D.policy(),container_name=CONTAINER,argv=argv)


def main():
    q=argparse.ArgumentParser(description=__doc__);sub=q.add_subparsers(dest='action',required=True);p=sub.add_parser('prepare')
    for n in ('pattern-launcher','native-intake','marker-intake','api-intake','output'):p.add_argument('--'+n,type=Path,required=True)
    for n in ('verify','proposal','run'):
        p=sub.add_parser(n);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--plan-sha256',required=True)
        if n!='verify':p.add_argument('--output',type=Path,required=True)
        if n=='proposal':p.add_argument('--output-parent',type=Path,required=True)
    a=q.parse_args()
    if a.action=='prepare':prepare(a.pattern_launcher,a.native_intake,a.marker_intake,a.api_intake,a.output);print(E.sha(a.output/'plan.json'));return 0
    if a.action=='verify':verify(a.inputs,a.plan_sha256);print('verified');return 0
    if a.action=='proposal':write(a.output,proposal(a.inputs,a.plan_sha256,a.output_parent));return 0
    row=run(a.inputs,a.plan_sha256,a.output);return 0 if row['passed'] else 2
if __name__=='__main__':raise SystemExit(main())
