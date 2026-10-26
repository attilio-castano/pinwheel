"""One same-target layout resource replay; Root GO only, no work on import.

The original 65-file views authority is kept in its original module namespace.
Only run_layout is derived: Docker memory/swap 2g->6g, new entry and typed schema.
The canonical Native antenna/LVS body and strict readers remain unchanged.
"""
import argparse
import ast
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import xml.etree.ElementTree as ET

import streaming_8x4_closure24_signoff_execute as BASE
import streaming_8x4_closure24_policy as POLICY
from streaming_tt_intake import dependency_closure

ROOT = Path(__file__).resolve().parents[1]
OWN = 'scripts/streaming_8x4_closure24_layout_resource.py'
CONTROLLER = 'scripts/streaming_8x4_closure24_signoff_execute.py'
NATIVE = 'scripts/streaming_8x4_signoff_execute.py'
READER = 'scripts/streaming_tt_layout.py'
PINS = {CONTROLLER: '2ee9bb80e980aeebf8533ac14023f7fd095738650b9e6a3175fb7aa9cff7f1e6',
        NATIVE: '3b897232fb0b56d70a5b2936d75794a4c0064d850a099572023eb25a25f2d043',
        READER: '84f8a35f2e2ec9d3ae12ab0d9a27f2ebfee75d9e4310e7011c62dd3dfad4c9d6'}
OLD_REPORT = 'b1d93c5544481f96bce3ca099d51acbb3343f0c096392874ae6a18cc35c4b61f'
OLD_GUARD = '80b19cf2d287fc4dcd2e83fcf50f31e36a7213da8f99bf256f12718e41d351ea'
B = ROOT/'build/campaigns/8x4-20261024-01'
OUTPUT = B/'final24-layout-resource-01'
PREPARATION = 'pinwheel.closure24-layout-resource-preparation.v1'
RUN = 'pinwheel.closure24-layout-resource-run.v1'
need, sha, regular = BASE.require, BASE.sha, BASE.regular


def policy():
    return dict(schema='pinwheel.closure24-layout-resource-policy.v1',maximum_resource_replays=1,
        cpus=1,memory_bytes=6442450944,memory_plus_swap_bytes=6442450944,extra_swap_bytes=0,
        tmpfs_bytes=268435456,worker_seconds=1800,deck_seconds=750,reader_cleanup_reserve_seconds=300,
        supervisor_seconds=1920,host_rss_mib=2048,all_antenna_categories=23,
        deck_order=['antenna','lvs'],readers_or_flags_changed=False,old_partial_XML_is_not_a_verdict=True,
        OpenROAD_antenna_failure_remains_open=True,physical_variant_changed=False,
        physical_acceptance=False,qualified_timing=False,model_qualified=False)


def read(path):
    return BASE.P.read(path)


def bound(path):
    path=regular(path).resolve();return dict(path=str(path),sha256=sha(path))


def categories():
    return [['Ant.a'],['Ant.c'],*[[f'Ant.{rule}_{layer}'] for layer in
        ('Metal1','Metal2','Metal3','Metal4','TopMetal1') for rule in ('b','e')],
        *[[f'Ant.{rule}_{layer}'] for layer in ('Via1','Via2','Via3','TopVia1') for rule in ('d','f')],
        ['Ant.g'],['Ant.h'],['Ant.i']]


def artifacts(output):
    output=Path(output)
    need(not any(p.is_symlink() for p in output.rglob('*')),'Layout owner contains symlinks')
    return {str(p.relative_to(output)):sha(p) for p in sorted(output.rglob('*'))
            if p.is_file() and p!=output/'report.json'}


def validate_failed(report,guard,execution):
    need(report['schema']=='pinwheel.closure24-layout-run.v1' and report['completed'] is False and
         report['passed'] is False and report['physical_acceptance'] is False and
         report['error']=='ValueError: Final native layout execution failed' and report['execution']==execution,
         'Original layout failure was changed/promoted')
    need(execution['status']=='interrupted' and execution['exit_code']==130 and execution['error']=='signal 15'
         and execution['timeout_seconds']==1800 and execution['container_termination']['status']=='absent',
         'Original interrupted layout phase differs')
    need(guard['schema']=='pinwheel.streaming-tt-resource-job.v1' and guard['kind']=='cad-validation' and
         guard['status']=='stopped' and guard['exit_code']==124 and guard['timeout_seconds']==1920 and
         guard['stop_reason']=='ValueError: Container approaching memory limit' and guard['cleanup_confirmed'] is True
         and guard['inputs_unchanged'] is True and all(guard[k]==[] for k in
         ('owned_processes_remaining','containers_remaining','cleanup_errors')),'Original memory stop/cleanup differs')


def previous(report_path,guard_path):
    need(sha(report_path)==OLD_REPORT and sha(guard_path)==OLD_GUARD,'Exact original layout receipts changed')
    report,guard=read(report_path),read(guard_path);owner=Path(report_path).parent
    validate_failed(report,guard,read(owner/'execution.json'))
    need(artifacts(owner)==report['artifact_sha256'] and len(report['artifact_sha256'])==72,
         'Preserve every original partial layout artifact')
    need(len(guard['input_sha256'])==1657 and all(sha(regular(path))==pin for path,pin in
         guard['input_sha256'].items()),'Original layout resource input changed')
    boundary=guard['campaign_boundary']
    need(boundary['campaign_id']==POLICY.CAMPAIGN and boundary['campaign_kind']=='fixed_cad' and
         boundary['shared_lease']==POLICY.shared_lease_paths(ROOT),'Original layout campaign lease differs')
    views,prepared=BASE.closed_views(report['views_report']['path'])
    need(bound(report['views_report']['path'])==report['views_report'] and views['target']==report['target'] and
         views['physical_candidate']==report['physical_candidate'] and len(prepared['producer_sha256'])==65,
         'Original 65-file closed views authority changed')
    need(not any((owner/name).exists() for name in
         ('native-journal.json','native-result.json','antenna-result.json','lvs.log','lvs.lvsdb','lvs-result.json')),
         'Original stopped antenna prefix gained completed/foreign layout evidence')
    xml=ET.fromstring((owner/'antenna.xml').read_bytes())
    need([[x.findtext('name')] for x in xml.findall('./categories/category')]==categories() and
         len(xml.findall('./items/item'))==0 and read(owner/'antenna-categories.json')==categories(),
         'Original diagnostic-only partial XML differs')
    return report,guard,views,prepared


def pinned_source(name):
    need(sha(ROOT/name)==PINS[name],'Frozen layout source changed: '+name)
    return (ROOT/name).read_text()


def run_source():
    original=pinned_source(CONTROLLER);node=next(x for x in ast.parse(original).body
        if isinstance(x,ast.FunctionDef) and x.name=='run_layout')
    text=''.join(original.splitlines(keepends=True)[node.lineno-1:node.end_lineno])
    changes=[("'--memory','2g','--memory-swap','2g'","'--memory','6g','--memory-swap','6g'"),
             ('/worker/scripts/streaming_8x4_closure24_signoff_execute.py','/worker/'+OWN),
             ('pinwheel.closure24-layout-run.v1',RUN)]
    result=text
    for old,new in changes:
        need(result.count(old)==1,'Exact layout adaptation anchor differs: '+old)
        result=result.replace(old,new,1)
    return result,''.join(difflib.unified_diff(text.splitlines(True),result.splitlines(True),
        fromfile='immutable/run_layout',tofile='resource6g/run_layout'))


def sources():
    for name in PINS:pinned_source(name)
    closure=dependency_closure(ROOT,(*BASE.SOURCE_ENTRIES,OWN))
    return closure,{name:sha(ROOT/name) for name in closure['files']}


def stage_producer(inputs):
    closure,files=sources();head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip()
    for name,pin in files.items():
        data=subprocess.check_output(['git','show',head+':'+name],cwd=ROOT,timeout=30)
        need(hashlib.sha256(data).hexdigest()==pin,'Commit new layout resource producer before staging: '+name)
        target=Path(inputs)/'producer'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    return head,files,closure


def runner():
    text,_=run_source();namespace=dict(vars(BASE))
    # Original view functions retain BASE's untouched global SOURCE_ENTRIES.
    namespace.update(closed_views=BASE.closed_views,stage_producer=stage_producer)
    exec(compile(text,'<closure24-layout-resource-run>','exec'),namespace)
    return namespace['run_layout']


def command(inputs,gds,cdl,packet,output,runtime,owner,name):
    tree=ast.parse(run_source()[0]);node=next(n for n in tree.body[0].body
        if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='command' for t in n.targets))
    return eval(compile(ast.Expression(node.value),'<exact-layout-resource-command>','eval'),{},locals())


def prepare(report_path,guard_path,output):
    report_path,guard_path=regular(report_path).resolve(),regular(guard_path).resolve()
    old,guard,views,prepared=previous(report_path,guard_path)
    output=BASE.Q.owned(output,ROOT);need(not output.exists(),'Preserve earlier layout resource preparation')
    closure,files=sources();text,diff=run_source();output.mkdir()
    (output/'run-layout.diff').write_text(diff)
    row=dict(schema=PREPARATION,policy=policy(),prior_report=bound(report_path),prior_guard=bound(guard_path),
        views_report=old['views_report'],target=old['target'],physical_candidate=old['physical_candidate'],
        original_view_producer_sha256=prepared['producer_sha256'],output=str(OUTPUT),
        producer_dependency_closure=closure,producer_sha256=files,diff=bound(output/'run-layout.diff'),
        executed=False,Root_GO_required=True,physical_acceptance=False)
    BASE.P.write(output/'plan.json',row);return verify_plan(output/'plan.json')


def verify_plan(path):
    path=regular(path).resolve();row=read(path);old,guard,views,prepared=previous(row['prior_report']['path'],row['prior_guard']['path'])
    need(row['schema']==PREPARATION and row['policy']==policy() and row['executed'] is False and
         row['Root_GO_required'] is True and row['physical_acceptance'] is False and row['output']==str(OUTPUT),
         'Layout resource plan policy/scope differs')
    need(row['prior_report']==bound(row['prior_report']['path']) and row['prior_guard']==bound(row['prior_guard']['path'])
         and row['views_report']==old['views_report'] and row['target']==old['target'] and
         row['physical_candidate']==old['physical_candidate'] and
         row['original_view_producer_sha256']==prepared['producer_sha256'],'Same final views/source authority differs')
    closure,files=sources();need(row['producer_dependency_closure']==closure and row['producer_sha256']==files,
         'New layout resource producer closure changed')
    need({p.name for p in path.parent.iterdir()}=={'plan.json','run-layout.diff'} and
         row['diff']==bound(path.parent/'run-layout.diff') and (path.parent/'run-layout.diff').read_text()==run_source()[1],
         'Exact resource diff/membership changed')
    return row


def proposal(path):
    row=verify_plan(path)
    return dict(schema='pinwheel.closure24-layout-resource-command.v1',plan=bound(path),policy=policy(),
        argv=[sys.executable,'-B',str(ROOT/OWN),'run','--plan',str(Path(path).resolve())],
        output=row['output'],container_name='pinwheel-24-final-layout-resource-01',
        views_report=row['views_report'],producer_sha256=row['producer_sha256'],
        executed=False,Root_GO_required=True,physical_acceptance=False)


def run(path):
    plan=verify_plan(path);need(not Path(plan['output']).exists(),'Preserve prior resource replay attempt')
    result=runner()(Path(plan['views_report']['path']),Path(plan['output']),
        'pinwheel-24-final-layout-resource-01',policy()['worker_seconds'])
    result.update(resource_plan=bound(path),resource_policy=policy(),
        prior_memory_stop=dict(report=plan['prior_report'],resource=plan['prior_guard']),
        OpenROAD_antenna_failure_remains_open=True,physical_variant_changed=False)
    BASE.R.write(Path(plan['output'])/'report.json',result);return result


def known_inputs(path):
    plan=verify_plan(path);guard=read(plan['prior_guard']['path']);pins=dict(guard['input_sha256'])
    def add(p):
        p=regular(p).resolve();value=sha(p)
        need(str(p) not in pins or pins[str(p)]==value,'Conflicting layout input seal')
        pins[str(p)]=value
    for p in (Path(plan['prior_report']['path']).parent).rglob('*'):
        if p.is_file():add(p)
    for p in (Path(path),Path(path).parent/'run-layout.diff',Path(plan['prior_guard']['path'])):add(p)
    for name in plan['producer_sha256']:add(ROOT/name)
    for name in ('scripts/streaming_8x4_closure24_resources.py','scripts/streaming_8x4_closure24_policy.py',
        'test/test_streaming_8x4_closure24_layout_resource.py',
        'docs/research/streaming-8x4-closure24-layout-resource-replay-20261024.md'):add(ROOT/name)
    for name in POLICY.historical_sources(ROOT):add(name)
    need(all(sha(regular(p))==pin for p,pin in pins.items()),'Frozen layout resource input changed')
    return dict(sorted(pins.items()))


def launch_packet(path,output):
    row=proposal(path);output=BASE.Q.owned(output,ROOT)
    need(not output.exists(),'Preserve earlier layout launch owner');output.mkdir()
    row['input_sha256']=known_inputs(path)
    BASE.P.write(output/'proposal.json',row)
    go=output/'Root-GO.json';argv=[sys.executable,'-B',str(ROOT/'scripts/streaming_8x4_closure24_resources.py'),
        '--campaign-root',str(ROOT),'--kind','fixed-cad','--tag','8x4-24-final-layout-resource-01',
        '--timeout-seconds','1920','--rss-mib','2048','--container-name',row['container_name'],
        '--validation-parent',row['views_report']['path']]
    for p in [*row['input_sha256'],str(output/'proposal.json'),str(output/'launch.json'),str(go)]:argv+=['--input',p]
    argv+=['--',*row['argv']]
    result=dict(schema='pinwheel.closure24-layout-resource-launch.v1',proposal=bound(output/'proposal.json'),
        resource_supervisor_argv=argv,external_Root_GO=str(go),Root_GO_created=False,
        resource_report=str(ROOT/'build/streaming-tt-resources/8x4-24-final-layout-resource-01/report.json'),
        HOST_check_argv=[sys.executable,'-B',str(ROOT/OWN),'check','--launch',str(output/'launch.json')],
        HOST_readback_argv=[sys.executable,'-B',str(ROOT/OWN),'readback','--launch',str(output/'launch.json'),
            '--output',str(B/'final24-layout-resource-independent-readback-01.json')],
        executed=False,physical_acceptance=False)
    BASE.P.write(output/'launch.json',result);return check_launch(output/'launch.json',before_native=True)


def check_launch(path,*,before_native):
    path=regular(path).resolve();launch=read(path);row=read(launch['proposal']['path'])
    need(launch['schema']=='pinwheel.closure24-layout-resource-launch.v1' and
         launch['proposal']==bound(path.parent/'proposal.json') and launch['Root_GO_created'] is False and
         launch['executed'] is False and launch['physical_acceptance'] is False,'Layout launch scope differs')
    expected=proposal(row['plan']['path']);expected['input_sha256']=known_inputs(row['plan']['path'])
    need(row==expected,'Layout resource proposal does not rederive')
    argv=launch['resource_supervisor_argv'];divider=argv.index('--');args=argv[:divider];worker=argv[divider+1:]
    prefix=[sys.executable,'-B',str(ROOT/'scripts/streaming_8x4_closure24_resources.py'),'--campaign-root',str(ROOT),
        '--kind','fixed-cad','--tag','8x4-24-final-layout-resource-01','--timeout-seconds','1920','--rss-mib','2048',
        '--container-name',row['container_name'],'--validation-parent',row['views_report']['path']]
    need(args[:len(prefix)]==prefix and worker==row['argv'],'Layout guard/worker argv differs')
    inputs=[args[i+1] for i in range(len(prefix),len(args),2)]
    need(all(args[i]=='--input' for i in range(len(prefix),len(args),2)),'Unexpected layout guard options')
    go=path.parent/'Root-GO.json'
    need(launch['external_Root_GO']==str(go) and inputs==[*row['input_sha256'],str(path.parent/'proposal.json'),str(path),str(go)]
         and len(inputs)==len(set(inputs)),'Layout guard input/GO membership differs')
    if before_native:need(not go.exists() and not OUTPUT.exists(),'Root GO/output must remain absent at HOST preparation')
    return launch,row


def validate_resource(resource,launch,row):
    argv=launch['resource_supervisor_argv'];boundary=resource['campaign_boundary'];cut=argv.index('--')
    pins=dict(row['input_sha256'])
    for p in (Path(launch['proposal']['path']),Path(launch['proposal']['path']).parent/'launch.json',Path(launch['external_Root_GO'])):
        pins[str(p)]=sha(regular(p))
    need(resource['schema']=='pinwheel.streaming-tt-resource-job.v1' and resource['kind']=='cad-validation' and
         resource['timeout_seconds']==1920 and resource['rss_mib']==2048 and resource['argv']==argv[cut+1:] and
         resource['validation_parent']==row['views_report'] and resource['input_sha256']==pins and
         all(sha(regular(p))==pin for p,pin in pins.items()),'Exact layout resource command/inputs differ')
    need(resource['status'] in ('completed','failed','stopped') and resource['cleanup_confirmed'] is True and
         resource['inputs_unchanged'] is True and all(resource[k]==[] for k in
         ('owned_processes_remaining','containers_remaining','cleanup_errors')),'Layout resource did not close cleanly')
    need(boundary['campaign_id']==POLICY.CAMPAIGN and boundary['campaign_kind']=='fixed_cad' and
         boundary['campaign_root']==str(ROOT) and boundary['schedule']==POLICY.SCHEDULE and
         boundary['shared_lease']==POLICY.shared_lease_paths(ROOT) and
         boundary['frozen_parent']==row['views_report'],'Layout campaign/shared lease differs')
    need(boundary['actual_wrapper_argv']==[sys.orig_argv[0],*argv[1:]],'Actual layout wrapper argv differs')
    for key in ('wrapper','policy','inherited_supervisor'):
        need(sha(regular(boundary[key+'_path']))==boundary[key+'_sha256'],'Layout supervisor source differs')
    need(boundary['historical_producer_sha256']==POLICY.historical_sources(ROOT),'Historical layout guard closure differs')


def readback(launch_path):
    launch,row=check_launch(launch_path,before_native=False);plan=verify_plan(row['plan']['path'])
    guard=read(launch['resource_report']);validate_resource(guard,launch,row)
    output=Path(plan['output']);report=read(output/'report.json');execution=read(output/'execution.json')
    need(report['schema']==RUN and report['artifact_sha256']==artifacts(output) and
         report['resource_plan']==row['plan'] and report['resource_policy']==policy() and
         report['prior_memory_stop']==dict(report=plan['prior_report'],resource=plan['prior_guard']) and
         report['views_report']==plan['views_report'] and report['target']==plan['target'] and
         report['physical_candidate']==plan['physical_candidate'] and report['execution']==execution and
         report['OpenROAD_antenna_failure_remains_open'] is True and report['physical_variant_changed'] is False and
         report['qualified'] is False and report['physical_acceptance'] is False,'Layout report/custody/scope differs')
    need(report['producer_sha256']==plan['producer_sha256'] and
         report['producer_dependency_closure']==plan['producer_dependency_closure'],'Layout worker closure differs')
    for name,pin in report['producer_sha256'].items():
        need(sha(output/'inputs/producer'/name)==sha(ROOT/name)==pin,'Staged layout worker changed')
        data=subprocess.check_output(['git','show',report['source_commit']+':'+name],cwd=ROOT,timeout=30)
        need(hashlib.sha256(data).hexdigest()==pin,'Layout worker is not its recorded committed source')
    views,prepared=BASE.closed_views(plan['views_report']['path']);packet=BASE.P.verify(Path(prepared['prepared']))
    need(prepared['producer_sha256']==plan['original_view_producer_sha256'] and report['runtime']==views['runtime'],
         'Original view/runtime authority differs')
    request=dict(schema='pinwheel.streaming-8x4-layout-native-request.v1',timeout_each=750,
        source_odb_sha256=plan['target']['actual_odb']['sha256'],producer_sha256=plan['producer_sha256'],
        input_sha256={'/input/actual.gds':sha(Path(plan['views_report']['path']).parent/'design.gds'),
            '/input/actual.cdl':sha(Path(plan['views_report']['path']).parent/'complete-reference.cdl')},qualified=False)
    need(read(output/'inputs/request.json')==request,'Exact fixed layout request differs')
    need(execution['argv']==command(output/'inputs',Path(plan['views_report']['path']).parent/'design.gds',
        Path(plan['views_report']['path']).parent/'complete-reference.cdl',packet,output,report['runtime'],
        execution['owner'],row['container_name']) and execution['timeout_seconds']==1800 and
        execution['container_termination']['status']=='absent','Layout Native resource/mount/cleanup differs')
    completed=report['completed']
    if completed:
        native=read(output/'native-result.json');events=read(output/'native-journal.json')
        need(guard['status'] in ('completed','failed') and guard['exit_code']==(0 if report['passed'] else 2) and
             execution['status']=='completed' and execution['exit_code']==0 and native['completed'] is True and
             native['inputs_unchanged'] is True and native['source_odb_sha256']==request['source_odb_sha256'] and
             native['events']==events and [e['kind']for e in events]==['antenna','lvs'] and
             all(e['exit_code']==0 and 0<=e['seconds']<=750 for e in events),'Full fresh deck events incomplete')
        results={}
        for kind,extension in [('antenna','xml'),('lvs','lvsdb')]:
            parsed=read(output/(kind+'-result.json'))
            need(parsed['schema']=='pinwheel.streaming-tt-layout-result.v1' and
                 parsed['kind']==('geometry'if kind=='antenna'else'lvs') and parsed['result']['top']==BASE.Q.TOP and
                 parsed['reader_sha256']==PINS[READER] and parsed['report_sha256']==sha(output/(kind+'.'+extension)),
                 'Same-top strict layout reader/actual report binding differs')
            results[kind]=parsed['result']
        need(read(output/'antenna-categories.json')==categories() and report['results']==results and
             report['passed']==all(x['passed'] for x in results.values()),'Antenna/LVS result membership differs')
    else:
        need(report['passed'] is False,'Incomplete layout attempt promoted')
    return dict(schema='pinwheel.closure24-layout-resource-independent-readback.v1',
        report=bound(output/'report.json'),resource_report=bound(launch['resource_report']),plan=row['plan'],
        old_failure_preserved=True,original_view_producer_files=65,resource_custody_closed=True,
        native_layout_completed=completed,layout_decks_passed=report['passed'],
        results=report.get('results'),OpenROAD_antenna_failure_remains_open=True,
        physical_variant_changed=False,model_qualified=False,qualified_timing=False,physical_acceptance=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('prepare')
    for name in ('prior-report','prior-resource','output'):p.add_argument('--'+name,type=Path,required=True)
    for mode in ('verify-plan','proposal','run'):
        p=sub.add_parser(mode);p.add_argument('--plan',type=Path,required=True)
    p=sub.add_parser('launch-packet');p.add_argument('--plan',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('check');p.add_argument('--launch',type=Path,required=True)
    p=sub.add_parser('readback');p.add_argument('--launch',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('native-layout');p.add_argument('--request',type=Path,required=True)
    args=parser.parse_args()
    if args.mode=='prepare':prepare(args.prior_report,args.prior_resource,args.output)
    elif args.mode=='verify-plan':verify_plan(args.plan)
    elif args.mode=='proposal':print(json.dumps(proposal(args.plan),sort_keys=True))
    elif args.mode=='launch-packet':launch_packet(args.plan,args.output)
    elif args.mode=='check':check_launch(args.launch,before_native=True)
    elif args.mode=='readback':
        value=readback(args.launch)
        with args.output.open('x')as stream:json.dump(value,stream,indent=2,sort_keys=True,allow_nan=False);stream.write('\n')
    elif args.mode=='run':return 0 if run(args.plan)['passed'] else 2
    else:BASE.native_layout(args.request)
    return 0


if __name__=='__main__':raise SystemExit(main())
