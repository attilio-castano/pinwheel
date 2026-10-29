"""New fixed-target8x4 coordinators using unchanged canonical native bodies.

Prepare/run only after a separate Root GO and under the campaign supervisor.
The new coordinator binds8x4 metadata without changing historical6x4 owners.
No mode grants device, RC-model, timing or tapeout acceptance.
"""
import argparse
from datetime import datetime,timezone
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
import uuid

import process_group
import streaming_8x4_prepare as P
import streaming_8x4_export as E
import streaming_8x4_run as R
import streaming_8x4_closure24_signoff_plan as Q
import streaming_8x4_signoff_execute as ORIGINAL
import streaming_tt_signoff as S
from streaming_8x4_geometry import regular,require,sha
from streaming_tt_intake import dependency_closure
from streaming_tt_physical import inspect_runtime

SOURCE_ENTRIES=('scripts/streaming_8x4_closure24_signoff_execute.py','scripts/streaming_tt_export_signoff.py',
    'scripts/streaming_tt_export_odb.py','scripts/streaming_tt_cdl_context.py','scripts/streaming_tt_layout.py',
    'scripts/streaming_tt_lef_format.py','tools/physical-toolchain.json','tools/streaming-tt-signoff.json')


layout_budget = ORIGINAL.layout_budget


master_libraries = ORIGINAL.master_libraries


def checked_plan(path):
    path=regular(path).resolve();Q.owned(path.parent,P.ROOT);report=P.read(path)
    require(report.get('schema')=='pinwheel.closure24-signoff-plan.v1' and report.get('executed') is False and
        report.get('physical_acceptance') is False,'Not a fixed-target8x4 signoff plan')
    for name,value in report['file_sha256'].items():
        require(Path(name).name==name and sha(path.parent/name)==value,'Signoff plan component changed')
    for name,value in report['source_sha256'].items():require(sha(P.ROOT/name)==value,'Signoff plan source changed')
    target=report['target'];prepared=Q.T.base_preparation(target['physical_report']['path']);packet=P.verify(prepared)
    require(Q.T.select_report(target['physical_report']['path'],target['physical_report']['sha256'],prepared,packet)==target,
        'Final physical target changed after planning')
    require(report.get('physical_candidate')==Q.T.candidate_identity(target,prepared),'Signoff physical candidate identity differs')
    return report,prepared,packet


def stage_producer(inputs):
    closure=dependency_closure(P.ROOT,SOURCE_ENTRIES)
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip();sources={}
    for name in closure['files']:
        data=subprocess.check_output(['git','show',head+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(data).hexdigest()==sha(P.ROOT/name),'Commit8x4 signoff producer first: '+name)
        target=inputs/'producer'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        sources[name]=sha(target)
    return head,sources,closure


unchanged_producer = ORIGINAL.unchanged_producer


def views_request(target, flow, base, reference):
    actual=regular(target['actual_odb']['path']).resolve();flow=Path(flow).resolve()
    require(actual.is_relative_to(flow) and sha(actual)==target['actual_odb']['sha256'],
            'Final view request is not the actual selected fresh ODB')
    return dict(schema='pinwheel.streaming-8x4-final-views-native-request.v1',
        source_odb='/work/source/'+str(actual.relative_to(flow)),source_odb_sha256=sha(actual),
        resolved_config='/work/source/resolved.json',resolved_config_sha256=sha(flow/'resolved.json'),
        input_sha256=base['input_sha256'],reference_sha256=sha(reference),top=Q.TOP,
        qualified=False,physical_acceptance=False)


def prepare_views(plan_path,reference,output):
    plan_path=regular(plan_path).resolve();plan,prepared,packet=checked_plan(plan_path)
    target=plan['target'];reference=regular(reference).resolve()
    require(sha(reference)==Q.T.FLAT_REFERENCE_SHA256,'Not the exact historically certified flat reference')
    output=Q.owned(output,P.ROOT);require(not output.exists(),'Preserve prior final8x4 view preparation')
    inputs=output/'inputs';inputs.mkdir(parents=True)
    head,sources,closure=stage_producer(inputs);shutil.copyfile(reference,inputs/'reference.json')
    actual=Path(target['actual_odb']['path']);flow=Path(target['physical_report']['path']).parent/'flow'
    request=views_request(target,flow,packet,reference)
    P.write(inputs/'request.json',request)
    result=dict(schema='pinwheel.closure24-final-views-preparation.v1',plan=Q.bound(plan_path),target=target,
        physical_candidate=plan['physical_candidate'],
        producer_commit=head,producer_sha256=sources,producer_dependency_closure=closure,
        prepared=str(prepared),prepared_input_sha256=sha(prepared/'preparation.json'),
        source_flow=str(flow),pdk_root=packet['pdk_root'],input_sha256=P.inventory(inputs),
        executed=False,qualified=False,physical_acceptance=False)
    P.write(output/'preparation.json',result);return result


def verify_views_preparation(output):
    output=Q.owned(output,P.ROOT);packet=P.read(output/'preparation.json')
    require(packet.get('schema')=='pinwheel.closure24-final-views-preparation.v1' and
        P.inventory(output/'inputs')==packet.get('input_sha256'),'Final view preparation changed')
    require(sha(packet['plan']['path'])==packet['plan']['sha256'],'Final signoff plan changed')
    plan,prepared,base=checked_plan(packet['plan']['path'])
    require(packet.get('physical_candidate')==plan['physical_candidate']==Q.T.candidate_identity(packet['target'],prepared),
        'Final views physical candidate changed')
    flow=Path(packet['target']['physical_report']['path']).parent/'flow'
    require(packet['target']==plan['target'] and Path(packet['prepared']).resolve()==prepared and
        packet['prepared_input_sha256']==sha(prepared/'preparation.json') and
        Path(packet['source_flow']).resolve()==flow.resolve() and packet['pdk_root']==base['pdk_root'] and
        sha(output/'inputs/reference.json')==Q.T.FLAT_REFERENCE_SHA256 and
        P.read(output/'inputs/request.json')==views_request(packet['target'],flow,base,output/'inputs/reference.json'),
        'Final view source/config/PDK/reference request differs')
    require(dependency_closure(P.ROOT,SOURCE_ENTRIES)==packet['producer_dependency_closure'] and
        set(packet['producer_sha256'])==set(packet['producer_dependency_closure']['files']),
        'Final view producer dependency membership differs')
    for name,value in packet['producer_sha256'].items():
        require(sha(P.ROOT/name)==value==sha(output/'inputs/producer'/name),'Final view producer changed')
        data=subprocess.check_output(['git','show',packet['producer_commit']+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(data).hexdigest()==value,'Final view producer is not its committed source')
    return packet


native_views = ORIGINAL.native_views


owned_native = ORIGINAL.owned_native


def views_command(output, packet, runtime, owner, name):
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+', name) and str(uuid.UUID(owner)) == owner,
            'Unsafe final-view container identity')
    return ['docker','run','--rm','--pull','never','--name',name,'--label','org.pinwheel.streaming8_owner='+owner,
        '--network','none','--cpus','1','--memory','2g','--memory-swap','2g','--read-only','--tmpfs','/tmp:rw,size=256m',
        '--env','PYTHONDONTWRITEBYTECODE=1','--env','PYTHONPATH=/work/export/inputs/producer/scripts:/work/inputs',
        '--mount',f'type=bind,source={output},target=/work/export',
        '--mount',f'type=bind,source={output/"inputs"},target=/work/export/inputs,readonly',
        '--mount',f'type=bind,source={Path(packet["prepared"])/"inputs"},target=/work/inputs,readonly',
        '--mount',f'type=bind,source={packet["source_flow"]},target=/work/source,readonly',
        '--mount',f'type=bind,source={packet["pdk_root"]},target=/work/pdk,readonly',
        '--workdir','/work/export',runtime['image_id'],'python3','-B',
        '/work/export/inputs/producer/scripts/streaming_8x4_closure24_signoff_execute.py','native-views',
        '--request','/work/export/inputs/request.json']


def run_views(output,name,timeout):
    from streaming_tt_lef_format import canonicalize
    output=Q.owned(output,P.ROOT);packet=verify_views_preparation(output)
    require(set(path.name for path in output.iterdir())=={'inputs','preparation.json'},'Final view output is not fresh')
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name),'Unsafe final view container name')
    runtime=inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'));owner=str(uuid.uuid4())
    command=views_command(output,packet,runtime,owner,name)
    execution=owned_native(command,output,owner,timeout)
    report=dict(schema='pinwheel.closure24-final-views-run.v1',target=packet['target'],physical_candidate=packet['physical_candidate'],
        preparation_sha256=sha(output/'preparation.json'),runtime=runtime,execution=execution,
        completed=False,qualified=False,physical_acceptance=False)
    try:
        require(execution.get('status')=='completed' and execution.get('exit_code')==0 and
            execution['container_termination']['status']=='absent','Final native view execution failed')
        native=P.read(output/'final-views-native.json');require(native.get('completed') is True and
            native['source_odb_sha256']==packet['target']['actual_odb']['sha256'] and native.get('source_odb_unchanged') is True,
            'Final native view database binding differs')
        for key,path in [('canonical_signoff_report_sha256','signoff-views/report.json'),
            ('canonical_boolean_report_sha256','actual-signal/receipt.json'),('canonical_streamout_report_sha256','native-report.json'),
            ('complete_cdl_sha256','complete-reference.cdl'),('cdl_context_sha256','cdl-context.json')]:
            require(sha(output/path)==native[key],'Final native report/context changed')
        canonical=P.read(output/'signoff-views/report.json')
        require(canonical.get('completed') is True and canonical.get('exit_code')==0 and canonical.get('inputs_unchanged') is True and
            canonical['actual_database_sha256']==packet['target']['actual_odb']['sha256'] and canonical.get('inherited_netlist') is False,
            'Canonical final signoff views did not close')
        for name,value in canonical['artifacts_sha256'].items():require(sha(output/'signoff-views'/name)==value,'Canonical final view changed')
        boolean=P.read(output/'actual-signal/receipt.json')
        require(boolean.get('read_only_database') is True and boolean['database_sha256']==native['source_odb_sha256'] and
            boolean['reference_sha256']==sha(output/'inputs/reference.json') and boolean.get('top')==Q.TOP and
            boolean.get('source_sha256')==packet['producer_sha256']['scripts/streaming_tt_export_odb.py'],
            'Canonical Boolean target/reference differs')
        for name,value in boolean['artifacts_sha256'].items():require(sha(output/'actual-signal'/name)==value,'Canonical Boolean output changed')
        stream=P.read(output/'native-report.json')
        require(stream.get('source_odb_unchanged') is True and stream['source_odb_sha256']==native['source_odb_sha256'] and
            set(stream['generated_files_sha256'])=={'design.def','design.lef','design.gds','native-geometry.json'},
            'Canonical streamout target/membership differs')
        for name,value in stream['generated_files_sha256'].items():require(sha(output/name)==value,'Canonical streamout changed')
        context=P.read(output/'cdl-context.json')
        require(context.get('exact_top_bytes_preserved') is True and context.get('exact_master_bytes_preserved') is True and
            context.get('actual_odb_pin_order_and_net_binding_verified') is True and
            context['actual_instances']==native['actual_instances'] and context['actual_terminals']==native['actual_terminal_bindings'],
            'Complete actual CDL context binding differs')
        formatted,formatting=canonicalize((output/'signoff-views/implemented.lef').read_text())
        (output/'official-format.lef').write_text(formatted);P.write(output/'lef-format.json',formatting)
        require(verify_views_preparation(output)==packet and inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))==runtime,
            'Final views input/runtime changed')
        report.update(completed=True,inputs_pdk_runtime_unchanged=True,native_report=Q.bound(output/'final-views-native.json'))
    except BaseException as error:report.update(error=type(error).__name__+': '+str(error))
    report['artifact_sha256']={str(path.relative_to(output)):sha(path) for path in sorted(output.rglob('*')) if path.is_file() and path!=output/'report.json'}
    R.write(output/'report.json',report);return report


def checked_view_outputs(output, packet):
    from streaming_tt_lef_format import canonicalize
    native=P.read(output/'final-views-native.json');require(native.get('schema')=='pinwheel.streaming-8x4-final-views-native.v1' and
        native.get('completed') is True and
        native['source_odb_sha256']==packet['target']['actual_odb']['sha256'] and
        native['resolved_config_sha256']==sha(Path(packet['source_flow'])/'resolved.json') and
        native.get('source_odb_unchanged') is True,
        'Final native view database binding differs')
    for key,path in [('canonical_signoff_report_sha256','signoff-views/report.json'),
        ('canonical_boolean_report_sha256','actual-signal/receipt.json'),('canonical_streamout_report_sha256','native-report.json'),
        ('complete_cdl_sha256','complete-reference.cdl'),('cdl_context_sha256','cdl-context.json')]:
        require(sha(output/path)==native[key],'Final native report/context changed')
    canonical=P.read(output/'signoff-views/report.json')
    require(canonical.get('completed') is True and canonical.get('exit_code')==0 and canonical.get('inputs_unchanged') is True and
        canonical['actual_database_sha256']==packet['target']['actual_odb']['sha256'] and canonical.get('inherited_netlist') is False,
        'Canonical final signoff views did not close')
    for name,value in canonical['artifacts_sha256'].items():require(sha(output/'signoff-views'/name)==value,'Canonical final view changed')
    boolean=P.read(output/'actual-signal/receipt.json')
    require(boolean.get('read_only_database') is True and boolean['database_sha256']==native['source_odb_sha256'] and
        boolean['reference_sha256']==sha(output/'inputs/reference.json') and boolean.get('top')==Q.TOP and
        boolean.get('source_sha256')==packet['producer_sha256']['scripts/streaming_tt_export_odb.py'] and
        set(boolean['artifacts_sha256'])=={'connectivity.json','inventory.json'},
        'Canonical Boolean target/reference differs')
    for name,value in boolean['artifacts_sha256'].items():require(sha(output/'actual-signal'/name)==value,'Canonical Boolean output changed')
    stream=P.read(output/'native-report.json')
    require(stream.get('source_odb_unchanged') is True and stream['source_odb_sha256']==native['source_odb_sha256'] and
        set(stream['generated_files_sha256'])=={'design.def','design.lef','design.gds','native-geometry.json'},
        'Canonical streamout target/membership differs')
    for name,value in stream['generated_files_sha256'].items():require(sha(output/name)==value,'Canonical streamout changed')
    context=P.read(output/'cdl-context.json')
    require(context.get('exact_top_bytes_preserved') is True and context.get('exact_master_bytes_preserved') is True and
        context.get('actual_odb_pin_order_and_net_binding_verified') is True and
        context['actual_instances']==native['actual_instances'] and context['actual_terminals']==native['actual_terminal_bindings'],
        'Complete actual CDL context binding differs')
    formatted, formatting=canonicalize((output/'signoff-views/implemented.lef').read_text())
    require((output/'official-format.lef').read_text()==formatted and P.read(output/'lef-format.json')==formatting,
            'Final exact-coordinate LEF serialization differs')
    return native


def artifact_membership(output):
    return {name:pin for name,pin in P.inventory(output).items() if name != 'report.json'}


def closed_views(path):
    path=regular(path).resolve();Q.owned(path.parent,P.ROOT);report=P.read(path)
    require(report.get('schema')=='pinwheel.closure24-final-views-run.v1' and report.get('completed') is True and
        report.get('inputs_pdk_runtime_unchanged') is True and report.get('physical_acceptance') is False and
        report.get('execution',{}).get('container_termination',{}).get('status')=='absent','Final view run is not closed')
    preparation=verify_views_preparation(path.parent)
    require(report['target']==preparation['target'] and report.get('physical_candidate')==preparation['physical_candidate'] and
        sha(path.parent/'preparation.json')==report['preparation_sha256'],
        'Final view target/preparation differs')
    require(artifact_membership(path.parent)==report['artifact_sha256'],
            'Closed final view complete artifact membership changed')
    execution=P.read(path.parent/'execution.json');argv=execution.get('argv')
    require(type(argv) is list and len(argv)>6 and report['execution']==execution and
        execution.get('status')=='completed' and type(execution.get('exit_code')) is int and execution['exit_code']==0 and
        type(execution.get('timeout_seconds')) is int and 1<=execution['timeout_seconds']<=3600 and
        execution.get('container_termination',{}).get('status')=='absent' and
        argv==views_command(path.parent,preparation,report['runtime'],execution['owner'],argv[6]),
        'Closed final-view actual command/status/resources differ')
    physical=P.read(preparation['target']['physical_report']['path'])
    require(report['runtime']==physical['runtime'], 'Final views use another physical runtime')
    require(report['native_report']==Q.bound(path.parent/'final-views-native.json'), 'Final native-view receipt changed')
    checked_view_outputs(path.parent,preparation)
    return report,preparation


def run_official(views_report,support,python,output,timeout):
    views_report=regular(views_report).resolve();views,preparation=closed_views(views_report)
    output=Q.owned(output,P.ROOT);require(not output.exists(),'Preserve prior official8x4 precheck')
    require(1<=timeout<=1800,'Official precheck exceeds bounded30minute allowance')
    inputs=output/'inputs';inputs.mkdir(parents=True);head,sources,closure=stage_producer(inputs)
    packet=P.verify(Path(preparation['prepared']));support=Path(support).resolve(strict=True)
    lock,frozen,expected=Q.official_sources(support,Path(preparation['prepared'])/'inputs/tt_block_8x4_pgvdd.def')
    tt=output/'tt';tt.mkdir()
    relative_files=list(lock['support_files'])+[P.read(P.ROOT/'physical/streaming_8x4/allocation.json')['template_path']]
    for name in relative_files:
        target=tt/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(support/name,target)
    S.verify_support(tt,lock);frozen.update({str(tt/name):sha(tt/name) for name in relative_files})
    design=output/'design';design.mkdir()
    for source,suffix in [(views_report.parent/'design.gds','gds'),(views_report.parent/'official-format.lef','lef'),
        (views_report.parent/'signoff-views/implemented.power.v','v')]:
        target=design/(Q.TOP+'.'+suffix);shutil.copyfile(source,target);frozen[str(target)]=sha(target)
    P.write(design/'info.yaml',dict(project=dict(top_module=Q.TOP,tiles='8x4',analog_pins=0,uses_3v3=False),pinout={}))
    frozen[str(design/'info.yaml')]=sha(design/'info.yaml')
    python=Path(python).absolute();require(python.is_file(),'Official precheck Python unavailable')
    aliases={};link=python
    while link.is_symlink():
        aliases[str(link)]=dict(target=os.readlink(link),resolved=str(link.resolve()));link=(link.parent/os.readlink(link)).absolute()
    actual=python.resolve();frozen[str(actual)]=sha(actual)
    roots=[python.parent.parent/'lib',actual.parent.parent/'lib'];payload={}
    for root in roots:payload.update(S.inventory(root,aliases=aliases))
    frozen.update(payload)
    environment=S.python_environment(os.environ)
    probe='import sys,json,importlib.metadata as m;print(json.dumps(dict(version=sys.version,optimize=sys.flags.optimize,no_user_site=sys.flags.no_user_site,packages={n:m.version(n) for n in '+repr(list(lock['precheck_python_packages']))+'})))'
    observed=subprocess.run([str(python),'-B','-c',probe],env=environment,capture_output=True,text=True,timeout=30)
    require(observed.returncode==0,'Official Python identity probe failed');identity=json.loads(observed.stdout)
    require(identity['version'].startswith(lock['python_version_prefix']) and identity['packages']==lock['precheck_python_packages'] and
        identity['optimize']==0 and identity['no_user_site']==1,'Official Python version/packages/flags differ')
    runtime=inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'));owner=str(uuid.uuid4());pdk=Path(packet['pdk_root'])
    main_drc=pdk/'ihp-sg13cmos5l/libs.tech/klayout/tech/drc/ihp-sg13cmos5l.drc'
    drc_scope=dict(deck=Q.bound(main_drc),scope='Unchanged official main SG13CMOS5L DRC deck with default rule switches',
        disabled_rule_switches=[],boundary='Execution and exact native journal must close before any DRC pass claim')
    config=output/'native-config.json';S.write(config,dict(out=str(output),pdk=str(pdk),owner=owner,
        image_id=runtime['image_id'],container_name=S.container_name(output)))
    binary=output/'bin';binary.mkdir();wrapper=binary/'klayout';source=inputs/'producer/scripts/streaming_tt_signoff.py'
    wrapper.write_text('#!'+str(python)+'\nimport runpy,sys\nsys.path.insert(0,'+repr(str(source.parent))+')\nm=runpy.run_path('+repr(str(source))+')\nraise SystemExit(m["native_klayout"]('+repr(str(config))+',sys.argv[1:]))\n');wrapper.chmod(0o755)
    frozen.update({str(config):sha(config),str(wrapper):sha(wrapper),str(views_report):sha(views_report)})
    frozen.update({str(inputs/'producer'/name):value for name,value in sources.items()})
    input_membership=P.inventory(inputs);unchanged_producer(inputs,sources,input_membership)
    env=dict(environment,PDK_ROOT=str(pdk),PDK=lock['tech'],PATH=str(binary)+os.pathsep+os.environ['PATH'])
    removed=sorted(key for key in os.environ if key.startswith('PYTHON') or key=='__PYVENV_LAUNCHER__')
    overrides={key:env[key] for key in ('PDK_ROOT','PDK','PATH','PYTHONDONTWRITEBYTECODE','PYTHONNOUSERSITE','PYTHONPATH')}
    command=['env',*[value for key in removed for value in ('-u',key)],
        *[key+'='+value for key,value in overrides.items()],str(python),'-B','precheck.py',
        '--gds',str(design/(Q.TOP+'.gds')),'--tech',lock['tech']]
    report=dict(schema='pinwheel.closure24-official-precheck-run.v1',passed=False,executed=False,qualified=False,
        physical_acceptance=False,target=views['target'],source_commit=head,producer_sha256=sources,producer_dependency_closure=closure,
        physical_candidate=views['physical_candidate'],
        views_report=Q.bound(views_report),runtime=runtime,python=identity,official_support_commit=lock['support_commit'],
        selected_checks=expected,official_omissions=list(Q.OMITTED),drc_scope=drc_scope,
        argv=command,input_sha256=frozen,runtime_aliases=aliases)
    S.write(output/'report.json',report);start=time.monotonic();previous=signal.getsignal(signal.SIGTERM)
    def interrupted(signum,frame):raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    try:
        result=process_group.run_captured(command,cwd=tt/'precheck',timeout=timeout,log_path=output/'precheck.log')
        report['exit_code']=result.returncode
        report['result']=S.precheck_result(tt/'precheck/reports/results.xml',expected,result.returncode)
        report['native']=S.native_journal(output/'native-klayout.jsonl',out=output,pdk=pdk,owner=owner,
            image_id=runtime['image_id'],gds=design/(Q.TOP+'.gds'))
        report.update(executed=True,passed=report['result']['passed'] and report['native']['passed'])
    except BaseException as error:report['error']=type(error).__name__+': '+str(error)
    finally:
        signal.signal(signal.SIGTERM,previous)
        try:
            report['cleanup']=S.cleanup(owner);S.unchanged(frozen);S.unchanged_aliases(aliases)
            unchanged_producer(inputs,sources,input_membership)
            current={}
            for root in roots:current.update(S.inventory(root,aliases={}))
            require(current==payload and closed_views(views_report)[0]==views and
                inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))==runtime,'Official precheck input/runtime changed')
            report['inputs_pdk_runtime_unchanged']=True
        except BaseException as error:report.update(passed=False,closeout_error=type(error).__name__+': '+str(error))
        report['elapsed_seconds']=time.monotonic()-start;S.write(output/'report.json',report)
    return report


native_layout = ORIGINAL.native_layout


def run_layout(views_report,output,name,timeout):
    views_report=regular(views_report).resolve();views,preparation=closed_views(views_report)
    output=Q.owned(output,P.ROOT);require(not output.exists(),'Preserve prior final8x4 layout result')
    inputs=output/'inputs';inputs.mkdir(parents=True);head,sources,closure=stage_producer(inputs)
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name),'Unsafe layout container name')
    per_deck=layout_budget(timeout)
    packet=P.verify(Path(preparation['prepared']));runtime=inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))
    gds=views_report.parent/'design.gds';cdl=views_report.parent/'complete-reference.cdl';owner=str(uuid.uuid4())
    request=dict(schema='pinwheel.streaming-8x4-layout-native-request.v1',timeout_each=per_deck,
        source_odb_sha256=views['target']['actual_odb']['sha256'],producer_sha256=sources,
        input_sha256={'/input/actual.gds':sha(gds),'/input/actual.cdl':sha(cdl)},qualified=False)
    P.write(inputs/'request.json',request)
    input_membership=P.inventory(inputs);unchanged_producer(inputs,sources,input_membership)
    command=['docker','run','--rm','--pull','never','--name',name,'--label','org.pinwheel.streaming8_owner='+owner,
        '--network','none','--cpus','1','--memory','2g','--memory-swap','2g','--read-only','--tmpfs','/tmp:rw,size=256m',
        '--env','PYTHONDONTWRITEBYTECODE=1','--env','PYTHONPATH=/worker/scripts',
        '--mount',f'type=bind,source={inputs/"producer"},target=/worker,readonly',
        '--mount',f'type=bind,source={inputs},target=/input/requests,readonly',
        '--mount',f'type=bind,source={gds},target=/input/actual.gds,readonly',
        '--mount',f'type=bind,source={cdl},target=/input/actual.cdl,readonly',
        '--mount',f'type=bind,source={packet["pdk_root"]},target=/work/pdk,readonly',
        '--mount',f'type=bind,source={output},target=/work/export',
        '--mount',f'type=bind,source={inputs},target=/work/export/inputs,readonly',
        '--workdir','/work/export',runtime['image_id'],'python3','-B','/worker/scripts/streaming_8x4_closure24_signoff_execute.py',
        'native-layout','--request','/input/requests/request.json']
    execution=owned_native(command,output,owner,timeout)
    report=dict(schema='pinwheel.closure24-layout-run.v1',views_report=Q.bound(views_report),target=views['target'],
        physical_candidate=views['physical_candidate'],
        source_commit=head,producer_sha256=sources,producer_dependency_closure=closure,runtime=runtime,execution=execution,
        completed=False,passed=False,qualified=False,physical_acceptance=False)
    try:
        require(execution.get('status')=='completed' and execution.get('exit_code')==0 and
            execution.get('container_termination',{}).get('status')=='absent','Final native layout execution failed')
        native=P.read(output/'native-result.json');require(native.get('completed') is True and native.get('inputs_unchanged') is True and
            native['source_odb_sha256']==views['target']['actual_odb']['sha256'],'Final native layout target changed')
        require([event.get('kind') for event in native['events']]==['antenna','lvs'] and
            all(event.get('exit_code')==0 for event in native['events']),'Incomplete/failed layout deck execution')
        results={}
        for kind,extension in [('antenna','xml'),('lvs','lvsdb')]:
            value=P.read(output/(kind+'-result.json'))
            require(value.get('schema')=='pinwheel.streaming-tt-layout-result.v1' and value['report_sha256']==sha(output/(kind+'.'+extension)) and
                value['reader_sha256']==sources['scripts/streaming_tt_layout.py'] and
                value.get('kind')==('geometry' if kind=='antenna' else 'lvs') and value.get('result',{}).get('top')==Q.TOP,
                'Layout interpretation report/reader/top differs')
            results[kind]=value['result']
        unchanged_producer(inputs,sources,input_membership)
        require(P.read(inputs/'request.json')==request,'Fixed layout request changed')
        require(closed_views(views_report)[0]==views and inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))==runtime,'Final layout inputs/runtime changed')
        report.update(completed=True,passed=all(value['passed'] for value in results.values()),results=results,inputs_pdk_runtime_unchanged=True)
    except BaseException as error:report['error']=type(error).__name__+': '+str(error)
    report['artifact_sha256']={str(path.relative_to(output)):sha(path) for path in sorted(output.rglob('*')) if path.is_file() and path!=output/'report.json'}
    R.write(output/'report.json',report);return report


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    pre=sub.add_parser('prepare-views')
    for name in ('plan','reference','output'):pre.add_argument('--'+name,type=Path,required=True)
    views=sub.add_parser('views');layout=sub.add_parser('layout');official=sub.add_parser('official')
    for part in (views,layout,official):
        part.add_argument('--output',type=Path,required=True);part.add_argument('--timeout',type=int,default=900)
    for part in (views,layout):part.add_argument('--name',required=True)
    for part in (layout,official):part.add_argument('--views-report',type=Path,required=True)
    for name in ('support','python'):official.add_argument('--'+name,type=Path,required=True)
    for name in ('native-views','native-layout'):
        nat=sub.add_parser(name);nat.add_argument('--request',type=Path,required=True)
    args=parser.parse_args()
    if args.mode=='native-views':native_views(args.request);return 0
    if args.mode=='native-layout':native_layout(args.request);return 0
    if args.mode=='prepare-views':prepare_views(args.plan,args.reference,args.output);print(args.output/'preparation.json');return 0
    if args.mode=='views':report=run_views(args.output,args.name,args.timeout)
    elif args.mode=='official':report=run_official(args.views_report,args.support,args.python,args.output,args.timeout)
    else:report=run_layout(args.views_report,args.output,args.name,args.timeout)
    print(args.output/'report.json');return 0 if report.get('passed',report.get('completed',False)) else 2


if __name__=='__main__':raise SystemExit(main())
