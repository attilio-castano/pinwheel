"""One sealed native positive-buffer transformation followed by full rerouting.

The admitted source checkpoint and all prior evidence remain immutable. This
derivative requires fresh final-netlist correspondence and every physical gate.
"""
import argparse
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
import uuid

import streaming_tt_final as F
import streaming_tt_physical as P
from streaming_tt_intake import dependency_closure

START='OpenROAD.ResizerTimingPostCTS'
ENTRIES=('scripts/streaming_tt_fanout_final.py','scripts/run-streaming-tt-fanout-final.py',
    'scripts/streaming_tt_apply_fanout.py','test/test_streaming_tt_fanout_final.py')
TCL_COMMANDS=('write_db {/work/run/transformation/partitioned-before-legalization.odb}',
    'set_thread_count 1','detailed_placement -max_displacement {500 100}','check_placement -verbose',
    'write_db {/work/run/transformation/implemented.odb}','write_def {/work/run/transformation/implemented.def}',
    'write_verilog {/work/run/transformation/implemented.v}')
BOUNDARY=('One exact positive-buffer fanout partition and native legalization, followed by unchanged '
    'certified postCTS repair, fresh global/detailed routing and scheduled signoff. No inherited RC, SDF, '
    'guides or metrics enter the fresh seed. Native completion does not establish source correspondence, '
    'timing/electrical, geometric power, DRC/LVS/antenna or official TT acceptance.')


def bind(path):
    path=P.regular(Path(path).absolute()).resolve();return path,P.sha(path)


def derive_config(before,resolved):
    P.require(before.get('CLOCK_PERIOD')==20 and before.get('RUN_POST_GRT_RESIZER_TIMING') is False and
        resolved.get('GRT_ADJUSTMENT')==0.3 and before.get('GRT_ADJUSTMENT',0.3)==0.3 and
        resolved.get('PL_MAX_DISPLACEMENT_X')==500 and resolved.get('PL_MAX_DISPLACEMENT_Y')==100,
        'Expected unchanged admitted 20 ns recipe with original 30 percent routing adjustment')
    after=dict(before,GRT_ADJUSTMENT=0.19,RUN_POST_GRT_RESIZER_TIMING=True,
        PL_MAX_DISPLACEMENT_X=1500,PL_MAX_DISPLACEMENT_Y=800)
    validate_config_delta(before,after);return after


def validate_config_delta(before,after):
    expected=dict(before,GRT_ADJUSTMENT=0.19,RUN_POST_GRT_RESIZER_TIMING=True,
        PL_MAX_DISPLACEMENT_X=1500,PL_MAX_DISPLACEMENT_Y=800)
    P.require(json.dumps(after,sort_keys=True,allow_nan=False)==json.dumps(expected,sort_keys=True,allow_nan=False) and type(after['GRT_ADJUSTMENT']) is float and
        after['RUN_POST_GRT_RESIZER_TIMING'] is True and
        type(after['PL_MAX_DISPLACEMENT_X']) is int and type(after['PL_MAX_DISPLACEMENT_Y']) is int,
        'Unapproved fanout reroute recipe/configuration change')
    return {'GRT_ADJUSTMENT':{'before_effective':0.3,'after':0.19},
        'RUN_POST_GRT_RESIZER_TIMING':{'before':False,'after':True},
        'PL_MAX_DISPLACEMENT_X':{'before_effective':500,'after':1500},
        'PL_MAX_DISPLACEMENT_Y':{'before_effective':100,'after':800}}


def intake(export_path,proposal_path,plan_path,corners_path,*,source_odb_sha256):
    export_path,proposal_path,plan_path,corners_path=[bind(path)[0] for path in
        (export_path,proposal_path,plan_path,corners_path)]
    exported,proposal,plan,corners=map(P.read,(export_path,proposal_path,plan_path,corners_path))
    from streaming_tt_ties import CORNERS_SHA256
    P.require(exported.get('schema')=='pinwheel.streaming-tt-odb-export-run.v1' and exported.get('passed') is True and
        exported.get('exit_code')==0 and exported.get('native_export_binding') is True and
        all(exported.get(name) is True for name in ('inputs_unchanged','staged_inputs_unchanged','runtime_unchanged')) and
        exported.get('container_termination',{}).get('status')=='absent' and
        exported.get('actual_odb_sha256')==source_odb_sha256,'Fanout readback is not closed on the admitted actual ODB')
    database,reference=map(lambda path:bind(path)[0],(exported['actual_odb'],exported['reference']))
    P.require(P.sha(database)==source_odb_sha256,'Fanout source ODB changed')
    directory=export_path.parent/'native/export';receipt=P.read(directory/'receipt.json')
    P.require(receipt.get('schema')=='pinwheel.streaming-tt-odb-export.v1' and
        receipt.get('database_sha256')==source_odb_sha256 and receipt.get('reference_sha256')==P.sha(reference) and
        receipt.get('read_only_database') is True and receipt.get('top')=='tt_um_pinwheel_streaming_ready_d2' and
        receipt.get('source_sha256')==hashlib.sha256(P.committed(P.ROOT/'scripts/streaming_tt_export_odb.py')).hexdigest(),
        'Native fanout reference/exporter/database identity differs')
    actual={str(path.relative_to(export_path.parent)):P.sha(path) for path in
        sorted((export_path.parent/'native').rglob('*')) if path.is_file()}
    P.require(actual==exported.get('artifact_sha256'),'Fanout readback artifact bytes/membership changed')
    P.require(proposal.get('schema')=='pinwheel.streaming-tt-fanout-proposal.v1' and
        proposal.get('status')=='unexecuted_proposal' and proposal.get('qualified') is False and
        proposal.get('native_transformation_executed') is False and proposal.get('input_unchanged') is True and
        proposal.get('validation',{}).get('passed') is True and proposal.get('actual_odb_sha256')==source_odb_sha256 and
        proposal.get('plan_sha256')==P.sha(plan_path) and
        plan.get('schema')=='pinwheel.streaming-tt-fanout-clone-plan.v1' and plan.get('status')=='unexecuted' and
        plan.get('maximum_loads')==8 and type(plan.get('projected_added_cells')) is int and
        1<=plan['projected_added_cells']<=1024,
        'Native transformation proposal does not bind the admitted actual ODB/plan')
    inventory=directory/'inventory.json'
    P.require(receipt.get('artifacts_sha256',{}).get('inventory.json')==P.sha(inventory) and
        [value for name,value in proposal['input_sha256'].items() if name.endswith('/native/export/inventory.json')]==[P.sha(inventory)],
        'Fanout proposal names a different actual inventory')
    P.require(type(corners) is dict and len(corners)==3 and {item.get('sha256') for item in corners.values()}==CORNERS_SHA256 and
        all(type(item) is dict and set(item)=={'path','sha256'} and
        P.sha(P.regular(item['path']))==item['sha256'] for item in corners.values()),'Fanout three-corner input changed')
    files={name:bind(path)[0] for name,path in [('database',database),('reference',reference),('inventory',inventory),
        ('plan',plan_path),('proposal',proposal_path),('corners-original',corners_path),('export-host',export_path),
        ('export-receipt',directory/'receipt.json'),('connectivity',directory/'connectivity.json')]}
    frozen={str(path):P.sha(path) for path in files.values()}
    for mapping in (exported.get('input_sha256',{}),proposal.get('input_sha256',{})):
        for name,value in mapping.items():
            path=P.regular(name).resolve();P.require(P.sha(path)==value,'Closed fanout proposal/readback input changed: '+name)
            frozen[str(path)]=value
    return files,frozen,corners


def prepare(admission,expected,tag,timeout_seconds,export_host,proposal,plan,corners):
    path=F.prepare(admission,expected,tag,timeout_seconds);metadata=F.verify(path);out=path.parent;inputs=out/'inputs'
    source=P.regular(inputs/metadata['authoritative_odb'].removeprefix('/work/inputs/'))
    files,frozen,corner_inputs=intake(export_host,proposal,plan,corners,source_odb_sha256=P.sha(source))
    fanout=inputs/'fanout';fanout.mkdir()
    for name,original in files.items():shutil.copyfile(original,fanout/(name+original.suffix))
    before=P.read(inputs/'core.json');shutil.copyfile(inputs/'core.json',fanout/'source-core.json')
    admitted=P.read(metadata['admission']);coarse_path=F.bound(admitted['coarse_report'])
    resolved_path=coarse_path.parent/'flow/resolved.json';resolved=P.read(resolved_path)
    P.require(P.read(coarse_path)['artifact_sha256'].get('flow/resolved.json')==P.sha(resolved_path),
        'Original resolved recipe differs from the closed admitted producer')
    derived=derive_config(before,resolved);P.write(inputs/'core.json',derived)
    frozen[str(resolved_path)]=P.sha(resolved_path)
    pdk=Path(metadata['pdk']).resolve();native_corners={}
    for name,item in corner_inputs.items():
        original=P.regular(item['path']).resolve()
        # The same pinned Liberty may have been read from another immutable
        # staged PDK copy; locate its exact content under this admitted mount.
        parts=original.parts;index=parts.index('ihp-sg13cmos5l');relative=Path(*parts[index:])
        actual=P.regular(pdk/relative);P.require(P.sha(actual)==item['sha256'],'Admitted PDK corner differs')
        native_corners[name]={'path':'/work/pdk/'+str(relative),'sha256':item['sha256']}
    P.write(fanout/'corners.json',native_corners)
    arguments=['apply_fanout.py','--database','/work/inputs/fanout/database.odb',
        '--reference','/work/inputs/fanout/reference.json','--inventory','/work/inputs/fanout/inventory.json',
        '--plan','/work/inputs/fanout/plan.json','--proposal-report','/work/inputs/fanout/proposal.json',
        '--corners-json','/work/inputs/fanout/corners.json','--out','/work/run/transformation',
        '--top','tt_um_pinwheel_streaming_ready_d2']
    launch='import runpy,sys\nsys.argv='+repr(arguments)+'\nrunpy.run_path("/work/inputs/producer/scripts/streaming_tt_apply_fanout.py",run_name="__main__")\n'
    (fanout/'launch.py').write_text(launch)
    P.write(fanout/'request.json',dict(schema='pinwheel.streaming-tt-fanout-native-request.v1',
        source_odb_sha256=P.sha(source),plan_sha256=P.sha(files['plan']),tag=tag,top='tt_um_pinwheel_streaming_ready_d2',
        launch='/work/inputs/fanout/launch.py',out='/work/run',from_step=START,to_step=F.TAIL[-1],
        core_config_sha256=P.sha(inputs/'core.json'),expected_added_cells=P.read(files['plan'])['projected_added_cells'],
        expected_original_instances=len(P.read(files['inventory'])['instances'])))
    producer_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip()
    closure=dependency_closure(P.ROOT,[*metadata['producer_sha256'],*ENTRIES])
    sources={name:hashlib.sha256(P.committed(P.ROOT/name)).hexdigest() for name in closure['files']}
    for name in closure['files']:
        destination=inputs/'producer'/name;data=P.committed(P.ROOT/name)
        if destination.exists():P.require(destination.read_bytes()==data,'Existing frozen base producer changed')
        else:destination.parent.mkdir(parents=True,exist_ok=True);destination.write_bytes(data)
    P.require(subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip()==producer_commit,
        'Producer commit changed during fanout source snapshot')
    for item in inputs.rglob('*'):
        if item.is_file():item.chmod(0o444)
    metadata.update(producer_sha256=sources,producer_dependency_closure=closure,producer_commit=producer_commit,boundary=BOUNDARY,
        transformation=dict(schema='pinwheel.streaming-tt-fanout-derivative.v1',source_odb_sha256=P.sha(source),
            plan_sha256=P.sha(files['plan']),source_readback_host={'path':str(files['export-host']),'sha256':P.sha(files['export-host'])},
            fresh_seed_policy=['odb','def','nl','metrics'],inherited_metrics=False,inherited_parasitics=False,
            native_executor='scripts/streaming_tt_apply_fanout.py',request='/work/inputs/fanout/request.json'),
        config_derivative=dict(schema='pinwheel.streaming-tt-fanout-config.v1',source_core_sha256=P.sha(fanout/'source-core.json'),
            derived_core_sha256=P.sha(inputs/'core.json'),changes=validate_config_delta(before,derived)),
        input_sha256={str(item.relative_to(inputs)):P.sha(item) for item in sorted(inputs.rglob('*')) if item.is_file()})
    metadata['external_input_sha256'].update(frozen);P.write(path,metadata);verify(path);return path


def verify(path):
    metadata=F.verify(path);inputs=Path(path).parent/'inputs';request=P.read(inputs/'fanout/request.json')
    source=P.regular(inputs/metadata['authoritative_odb'].removeprefix('/work/inputs/'))
    original=P.read(inputs/'fanout/source-core.json');derived=P.read(inputs/'core.json')
    changes=validate_config_delta(original,derived);projection=metadata.get('config_derivative',{})
    P.require(projection.get('schema')=='pinwheel.streaming-tt-fanout-config.v1' and projection.get('changes')==changes and
        projection.get('source_core_sha256')==P.sha(inputs/'fanout/source-core.json')==P.sha(Path(metadata['design'])/'inputs/core.json') and
        projection.get('derived_core_sha256')==P.sha(inputs/'core.json')==request.get('core_config_sha256'),
        'Fanout derivative recipe projection no longer binds the admitted configuration')
    P.require(request.get('source_odb_sha256')==P.sha(source)==metadata.get('transformation',{}).get('source_odb_sha256') and
        request.get('plan_sha256')==P.sha(inputs/'fanout/plan.json')==metadata.get('transformation',{}).get('plan_sha256') and
        request.get('from_step')==START and request.get('to_step')==F.TAIL[-1] and
        metadata['transformation'].get('fresh_seed_policy')==['odb','def','nl','metrics'],
        'Fanout derivative no longer binds its admitted ODB/plan/fresh seed policy')
    return metadata


def validate_order(ids):
    F.validate_order(ids)
    prefix=[START,'OpenROAD.GlobalRouting','OpenROAD.RepairDesignPostGRT','OpenROAD.RepairAntennas',
        'OpenROAD.ResizerTimingPostGRT','OpenROAD.STAMidPNR-3']
    for first,second in zip(prefix,prefix[1:]):
        P.require(first in ids and second in ids and ids.index(first)<ids.index(second),'Required fresh repair/routing step missing')
    return ids[ids.index(START):]


def validate_transformation(directory,request):
    directory=Path(directory);report=P.read(P.regular(directory/'report.json'))
    P.require(report.get('schema')=='pinwheel.streaming-tt-native-fanout-partition.v1' and
        all(report.get(name) is True for name in ('passed','completed','inputs_unchanged','exact_source_inventory_re_read',
            'exact_topology_checked','placement_passed','native_detailed_placement_executed','native_check_placement_executed',
            'actual_odb_roundtrip_checked')) and report.get('qualified') is False and report.get('physical_acceptance_claim') is False and
        report.get('inherited_netlist') is False and report.get('original_ff_bits')==6039 and
        report.get('source_odb_sha256')==request['source_odb_sha256'] and report.get('plan_sha256')==request['plan_sha256'],
        'Native fanout topology/state/placement/roundtrip receipt is incomplete')
    commands=report.get('native_tcl_commands')
    P.require(report.get('native_tcl_all_success') is True and type(commands) is list and len(commands)==len(TCL_COMMANDS) and
        all(type(row) is dict and set(row)=={'command','tcl_catch_status','tcl_result'} and row['command']==command and
            type(row['tcl_catch_status']) is str and row['tcl_catch_status']=='0' and type(row['tcl_result']) is str
            for row,command in zip(commands,TCL_COMMANDS)),
        'Actual native Tcl placement/check/write status is failed, omitted or unrecognized')
    topology=report.get('topology',{})
    P.require(all(topology.get(name) is True for name in ('passed','exact_pin_partition_checked','all_signal_and_clock_loads_at_most_eight')) and
        topology.get('positive_clone_cells')==request['expected_added_cells'] and
        topology.get('original_instances_retained')==request['expected_original_instances'],
        'Native exact full topology/load/instance partition did not close')
    actual={str(path.relative_to(directory)):P.sha(path) for path in sorted(directory.rglob('*'))
        if path.is_file() and path!=directory/'report.json'}
    P.require(actual==report.get('artifacts_sha256') and all(name in actual and P.regular(directory/name).stat().st_size>0
        for name in ('implemented.odb','implemented.def','implemented.v','inventory.json','connectivity.json')),
        'Native transformed output bytes/membership changed or incomplete')
    inventory=P.read(directory/'inventory.json');document=P.read(directory/'connectivity.json')
    P.require(inventory.get('top')==request['top'] and set(document.get('modules',{}))=={request['top']},'Native derivative top differs')
    return report


def fresh_seed(directory):
    directory=Path(directory)
    for name in ('implemented.odb','implemented.def','implemented.v'):P.require(P.regular(directory/name).stat().st_size>0,'Empty derivative view')
    return {
        'odb':str(directory/'implemented.odb'),'def':str(directory/'implemented.def'),
        'nl':str(directory/'implemented.v'),'metrics':{}}


def native_command(argv,name,out,journal):
    out,journal=Path(out),Path(journal);located=shutil.which(argv[0])
    P.require(located is not None,'Native transformation/routing command unavailable: '+argv[0]);declared=Path(located).absolute()
    executable=P.regular(declared.resolve());argv=[str(declared),*argv[1:]]
    row=dict(name=name,argv=argv,resolved_executable=str(executable),executable_sha256_before=P.sha(executable));started=time.monotonic()
    def record(event):
        with journal.open('a') as stream:stream.write(json.dumps(event,sort_keys=True)+'\n');stream.flush();os.fsync(stream.fileno())
    record(dict(event='intent',**row))
    with (out/(name+'.log')).open('w') as log:result=subprocess.run(argv,stdout=log,stderr=subprocess.STDOUT)
    row.update(exit_code=result.returncode,executable_sha256_after=P.sha(executable),elapsed_seconds=round(time.monotonic()-started,3),
        log_sha256=P.sha(out/(name+'.log')));record(dict(event='result',**row))
    P.require(declared.resolve()==executable and row['executable_sha256_before']==row['executable_sha256_after'],
        'Native command executable/alias changed')
    return result.returncode


def route_arguments(python,tag):
    return [python,'-B','-m','librelane','--manual-pdk','--pdk-root','/work/pdk','--pdk','ihp-sg13cmos5l',
        '--jobs','4','--run-tag',tag,'--force-run-dir','/work/run/route','--with-initial-state','/work/run/fresh-seed.json',
        '--from',START,'--to',F.TAIL[-1],'/work/inputs/core.json']


def validate_native_closeout(output,request,*,request_sha256):
    output=Path(output);packet=P.read(P.regular(output/'native-report.json'))
    P.require(packet.get('schema')=='pinwheel.streaming-tt-fanout-native-run.v1' and packet.get('completed') is True and
        packet.get('exit_code')==0 and packet.get('status')=='completed' and
        packet.get('request_sha256')==request_sha256 and
        packet.get('executed_suffix')==validate_order(packet.get('native_step_ids')),
        'Native transformed repair/routing execution is not closed')
    transformation=validate_transformation(output/'transformation',request)
    P.require(packet.get('transformation')==transformation and
        packet.get('transformation_report_sha256')==P.sha(output/'transformation/report.json'),
        'Native derivative report changed after routed continuation')
    seed=P.read(output/'fresh-seed.json');expected={key:'/work/run/transformation/implemented.'+suffix for key,suffix in
        [('odb','odb'),('def','def'),('nl','v')]};expected['metrics']={}
    P.require(seed==expected and packet.get('fresh_seed_keys')==sorted(expected) and
        packet.get('fresh_seed_sha256')==P.sha(output/'fresh-seed.json'),'Native continuation inherited stale views or metrics')
    journal=P.regular(output/'native-journal.jsonl');events=[json.loads(line) for line in journal.read_text().splitlines()]
    P.require(len(events)==4 and packet.get('native_journal_sha256')==P.sha(journal),'Unclosed or changed native two-command journal')
    for index,name in enumerate(('transformation','route')):
        intent,result=events[index*2:index*2+2];argv=intent.get('argv',[])
        P.require(intent.get('event')=='intent' and result.get('event')=='result' and intent.get('name')==result.get('name')==name and
            argv==result.get('argv') and argv and Path(argv[0]).is_absolute() and result.get('exit_code')==0 and
            intent.get('executable_sha256_before')==result.get('executable_sha256_before')==result.get('executable_sha256_after') and
            intent.get('resolved_executable')==result.get('resolved_executable') and
            result.get('log_sha256')==P.sha(output/(name+'.log')),'Native actual executable/argv/result/log changed')
        wanted=['-exit','-python',request['launch']] if name=='transformation' else route_arguments(argv[0],request['tag'])[1:]
        P.require(argv[1:]==wanted,'Native transformation/continuation changed its declared inputs or repair range')
    P.require(packet.get('resolved_config_sha256')==P.sha(output/'resolved.json')==P.sha(output/'route/resolved.json'),
        'Authoritative routed resolved configuration copy changed')
    return dict(passed=True,qualified=False,native_journal_sha256=P.sha(journal),closed_native_commands=2,
        transformation_report_sha256=P.sha(output/'transformation/report.json'),fresh_seed_sha256=P.sha(output/'fresh-seed.json'),
        exact_topology_and_6039_state_checked=True,placement_and_roundtrip_checked=True)


def fresh_route_directory(out):
    route=Path(out)/'route'
    route.mkdir(exist_ok=False)
    return route


def native(request_path):
    request=P.read(P.regular(request_path));P.require(request.get('schema')=='pinwheel.streaming-tt-fanout-native-request.v1' and
        request.get('from_step')==START and request.get('to_step')==F.TAIL[-1] and request.get('out')=='/work/run',
        'Unknown native fanout/reroute request')
    P.require(P.sha('/work/inputs/core.json')==request['core_config_sha256'],'Derived native routing recipe changed')
    validate_config_delta(P.read('/work/inputs/fanout/source-core.json'),P.read('/work/inputs/core.json'))
    out=Path(request['out']);from librelane_plugin_streaming_tt import StreamingTTCertified
    ids=[step.id for step in StreamingTTCertified.Steps];suffix=validate_order(ids)
    journal=out/'native-journal.jsonl'
    report=dict(schema='pinwheel.streaming-tt-fanout-native-run.v1',completed=False,qualified=False,
        physical_acceptance_claim=False,native_step_ids=ids,executed_suffix=suffix,status='transforming',
        request_sha256=P.sha(request_path));P.write(out/'native-report.json',report)
    try:
        code=native_command(['openroad','-exit','-python',request['launch']],'transformation',out,journal)
        P.require(code==0,'Native fanout transformation failed')
        transformation=validate_transformation(out/'transformation',request)
        seed=fresh_seed(out/'transformation');P.write(out/'fresh-seed.json',seed)
        report.update(transformation=transformation,transformation_report_sha256=P.sha(out/'transformation/report.json'),
            fresh_seed_sha256=P.sha(out/'fresh-seed.json'),fresh_seed_keys=sorted(seed),status='rerouting')
        P.write(out/'native-report.json',report)
        fresh_route_directory(out)
        argv=route_arguments(sys.executable,request['tag'])
        code=native_command(argv,'route',out,journal)
        if (out/'route/resolved.json').is_file():
            shutil.copyfile(out/'route/resolved.json',out/'resolved.json')
            P.require(P.sha(out/'resolved.json')==P.sha(out/'route/resolved.json'),'Copied resolved configuration changed')
            report['resolved_config_sha256']=P.sha(out/'resolved.json')
        report.update(exit_code=code,status='completed' if code==0 else 'failed',completed=code==0)
        return code
    except BaseException as error:
        report.update(status='failed',error=type(error).__name__+': '+str(error));raise
    finally:
        if journal.is_file():report['native_journal_sha256']=P.sha(journal)
        P.write(out/'native-report.json',report)


def run(path):
    path=P.regular(path).resolve();prepared_hash=P.sha(path);metadata=verify(path);out=path.parent
    P.require(out.resolve()==(P.BASE/metadata['tag']).resolve() and metadata.get('transformation',{}).get('schema')==
        'pinwheel.streaming-tt-fanout-derivative.v1','Wrong fanout derivative output/input')
    for name,digest in metadata['producer_sha256'].items():
        P.require(hashlib.sha256(subprocess.check_output(['git','show',metadata['producer_commit']+':'+name],cwd=P.ROOT,
            timeout=30)).hexdigest()==digest,'Uncommitted fanout producer source')
    output=out/'flow';P.require(not output.exists(),'Preserve earlier fanout native outputs')
    owner=str(uuid.uuid4());lock=P.BASE/'streaming-tt-active.json'
    fd=os.open(lock,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
    with os.fdopen(fd,'w') as stream:json.dump(dict(owner=owner,pid=os.getpid(),tag=metadata['tag']),stream)
    try:output.mkdir(exist_ok=False)
    except BaseException:
        if P.read(lock).get('owner')==owner:lock.unlink()
        raise
    report=dict(schema='pinwheel.streaming-tt-final-run.v1',qualified=False,physical_acceptance_claim=False,
        post_pnr_equivalence_proved=False,status='preflight',tag=metadata['tag'],source_commit=metadata['source_commit'],
        producer_commit=metadata['producer_commit'],prepared_input_sha256=prepared_hash,started_utc=datetime.now(timezone.utc).isoformat(),
        executed_staged_producer=str(Path(__file__).resolve()),ownership_label=owner,cpus=4,memory='6g',memory_swap='6g',network='none',
        input_mount_readonly=True,pdk_mount_readonly=True,from_step=START,stop_step=F.TAIL[-1],
        timeout_seconds=metadata['timeout_seconds'],transformation=metadata['transformation'],boundary=BOUNDARY)
    receipt=out/'report.json';P.write(receipt,report);started=time.monotonic();process=None;coarse=F.common_runner()
    old_handler=signal.getsignal(signal.SIGTERM)
    def interrupt(signum,frame):raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupt)
    with (out/'native.log').open('w') as log:
        try:
            runtime=P.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'));report['runtime']=runtime
            command=['docker','run','--rm','--pull','never','--name','pinwheel-'+metadata['tag'],
                '--label','org.pinwheel.streaming_tt_owner='+owner,'--network','none','--cpus','4','--memory','6g',
                '--memory-swap','6g',
                '--read-only','--tmpfs','/tmp:rw,size=1073741824',
                '--env','PYTHONDONTWRITEBYTECODE=1','--env','PYTHONPATH=/work/inputs:/work/inputs/producer/scripts',
                '--mount','type=bind,source='+str(out/'inputs')+',target=/work/inputs,readonly',
                '--mount','type=bind,source='+metadata['pdk']+',target=/work/pdk,readonly',
                '--mount','type=bind,source='+str(output)+',target=/work/run','--workdir','/work/inputs',runtime['image_id'],
                'python3','-B','/work/inputs/producer/scripts/streaming_tt_fanout_final.py',
                '--native-request','/work/inputs/fanout/request.json']
            report.update(command=command,status='running');P.write(receipt,report)
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            code=process.wait(timeout=metadata['timeout_seconds']);report.update(exit_code=code,status='flow_completed' if code==0 else 'failed')
        except subprocess.TimeoutExpired:report.update(exit_code=124,status='timed_out',stop_reason='wall_time_limit')
        except KeyboardInterrupt as error:report.update(exit_code=130,status='interrupted',error=str(error))
        except (OSError,ValueError,subprocess.CalledProcessError) as error:
            report.update(exit_code=127,status='blocked',error=type(error).__name__+': '+str(error))
        finally:
            report['container_termination']=coarse.cleanup(owner,log)
            if process is not None and process.poll() is None:
                try:process.wait(timeout=5)
                except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGTERM)
            try:
                P.require(P.sha(path)==prepared_hash,'Fanout prepared receipt changed');verify(path)
                if 'runtime' in report:P.require(P.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))==report['runtime'],'Native runtime changed')
                report['inputs_unchanged_after_run']=True
            except (OSError,ValueError) as error:report.update(inputs_unchanged_after_run=False,status='invalidated',closeout_error=str(error))
            try:report['states']=F.collect_states(output,out/'inputs',metadata['pdk'])
            except (OSError,ValueError) as error:report.update(status='invalidated',state_closeout_error=str(error))
            if (output/'native-report.json').is_file():
                report['native_derivative_report_sha256']=P.sha(output/'native-report.json')
                report['native_derivative_status']=P.read(output/'native-report.json').get('status')
                if report.get('exit_code')==0 and P.read(output/'native-report.json').get('completed') is not True:
                    report.update(status='invalidated',closeout_error='Native derivative receipt did not complete')
            elif report.get('exit_code')==0:report.update(status='invalidated',closeout_error='Missing native derivative receipt')
            if report.get('exit_code')==0 and report.get('status')=='flow_completed':
                try:report['native_derivative_closeout']=validate_native_closeout(output,P.read(out/'inputs/fanout/request.json'),
                    request_sha256=P.sha(out/'inputs/fanout/request.json'))
                except (OSError,ValueError,TypeError,KeyError) as error:report.update(status='invalidated',closeout_error=str(error))
            if report['container_termination'].get('status')!='absent':report['status']='cleanup_unconfirmed'
            report.update(elapsed_seconds=round(time.monotonic()-started,3),artifact_sha256={str(item.relative_to(out)):P.sha(item)
                for item in sorted(out.rglob('*')) if item.is_file() and item!=receipt});P.write(receipt,report)
            if report['container_termination'].get('status')=='absent' and P.read(lock)['owner']==owner:lock.unlink()
            signal.signal(signal.SIGTERM,old_handler)
    print(receipt,flush=True);return report.get('exit_code',127) or (3 if report['status']!='flow_completed' else 0)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--native-request',type=Path,required=True)
    raise SystemExit(native(parser.parse_args().native_request))
