"""Separate typed authority and owned runner for one post-antenna repair.

The unchanged original 85%/20ns preparation remains verified by P.verify.
Only a closed parent can supply the exact actual stage35/36 seed. A failed
parent is never a final target. Root must separately select/guard this sole
candidate; source preparation does not authorize a Native launch.
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

sys.dont_write_bytecode=True
import streaming_8x4_prepare as P
import streaming_8x4_run as R
import streaming_8x4_fanout_observe as O
from streaming_8x4_geometry import regular,require,sha
from streaming_tt_intake import dependency_closure
from streaming_tt_physical import inspect_runtime

STEP='OpenROAD.PostAntennaDesignRepair'
FLOW='Streaming8x4PostAntennaRepair'
PLUGIN='physical/streaming_8x4/librelane_plugin_streaming_8x4_repair.py'
OWN='scripts/streaming_8x4_postantenna_repair.py'
SOURCES=(OWN,PLUGIN,'scripts/streaming_8x4_prepare.py','scripts/streaming_8x4_run.py')


def bound(path):return dict(path=str(regular(path).resolve()),sha256=sha(path))


def candidate_delta(threads):
    require(type(threads) is int and threads in (1,2,4),'Explicit repair-only OpenROAD thread selection must be1,2or4')
    return dict(canonical_added_step=STEP,after='OpenROAD.RepairAntennas',before='OpenROAD.STAMidPNR-3',
        initial_state_translation='/work/run/ -> /work/parent/ readonly original flow',
        core_json_byte_unchanged=True,placement_density_pct=85,clock_ns=20,state_bits=6039,drt_opt_iters=64,
        resource_override={'OPENROAD_THREADS':dict(before=4,after=threads)},native_cpu_quota=4,native_memory_gib=6)


def resolved_delta(before,after,threads):
    candidate_delta(threads);expected=dict(before,OPENROAD_THREADS=threads)
    # The class override may be reflected in metadata; every physical variable
    # remains identical except the explicitly selected resource thread count.
    if after.get('meta')!=before.get('meta'):
        require(type(before.get('meta')) is dict and type(after.get('meta')) is dict and
            after['meta']==dict(before['meta'],flow=FLOW),'Undeclared repair resolved metadata change')
        expected['meta']=after['meta']
    require(after==expected and after.get('GRT_DESIGN_REPAIR_RUN_GRT') is True and after.get('DRT_OPT_ITERS')==64 and
        after.get('PL_TARGET_DENSITY_PCT')==85 and after.get('CLOCK_PERIOD')==20,
        'Repair actual resolved config changes physical rules or omits selected thread override')
    return {name:dict(before=before.get(name),after=after.get(name)) for name in sorted(set(before)|set(after)) if before.get(name)!=after.get(name)}


def stop_authority(path,report_path,resource_path,resource):
    """Read Root's immutable pre-signal intent and matching dispatch evidence."""
    path=regular(path).resolve();dispatch=P.read(path)
    require(dispatch.get('schema')=='pinwheel.streaming-8x4-root-stop-authority.v1' and
        dispatch.get('signal_number')==15 and dispatch.get('signal_returncode')==0 and
        type(dispatch.get('signal_returncode')) is int and dispatch.get('signal_sent') is True,
        'Owned stop needs exact successful Root SIGTERM dispatch')
    marker=dispatch['intent'];require(bound(marker['path'])==marker,'Immutable Root stop intent changed')
    intent=P.read(marker['path']);identity=intent.get('identity')
    require(intent.get('schema')=='pinwheel.streaming-8x4-root-stop-intent.v1' and intent.get('root_owned') is True and
        intent.get('parent_report_path')==str(report_path) and intent.get('parent_resource_path')==str(resource_path) and
        intent.get('resource_argv')==resource['argv'] and intent.get('signal_number')==15 and
        type(identity) is dict and set(identity)=={'pid','pgid','birth','command'} and
        type(identity.get('pid')) is int and identity['pid']>1 and identity['pid']==identity['pgid']==resource.get('pid') and
        all(type(identity.get(key)) is str and identity[key].strip() for key in ('birth','command')) and
        dispatch.get('observations')==[identity,identity],
        'Root stop PID/process-group/birth/command/owner observations differ')
    before=datetime.fromisoformat(intent['intent_utc'].replace('Z','+00:00'))
    after=datetime.fromisoformat(dispatch['dispatched_utc'].replace('Z','+00:00'))
    require(before.tzinfo is not None and after.tzinfo is not None and before<=after,'Root stop intent must precede dispatch')
    return dict(dispatch=bound(path),intent=marker,identity=identity,signal_number=15)


def closed_parent(report_path,resource_path,prepared,base,stop_path=None):
    report_path,resource_path=map(lambda p:regular(p).resolve(),(report_path,resource_path))
    report=P.read(report_path);resource=P.read(resource_path)
    require(report.get('schema')=='pinwheel.streaming-8x4-native-run.v1' and report.get('mode')=='full' and
        type(report.get('exit_code')) is int and ((report.get('status')=='flow_completed' and report['exit_code']==0) or
        (report.get('status')=='failed' and report['exit_code']!=0) or
        (report.get('status')=='interrupted' and report['exit_code']==130) or
        (report.get('status')=='timed_out' and report['exit_code']==124 and report.get('stop_reason')=='native_wall_time_limit')) and
        report.get('inputs_pdk_runtime_unchanged') is True and
        report.get('container_termination',{}).get('status')=='absent' and report.get('qualified') is False and
        report.get('physical_acceptance') is False,
        'Original full parent must be terminal with closed unchanged inputs/cleanup; timeout/interruption are seed evidence only')
    require(Path(report['prepared']).resolve()==prepared.resolve() and report['prepared_input_sha256']==sha(prepared/'preparation.json') and
        report['producer_sha256']==base['producer_sha256'] and report['source_ff_bits']==6039 and report['clock_period_ns']==20 and
        report['tiles']=='8x4','Original parent baseline differs')
    require(resource.get('schema')=='pinwheel.streaming-tt-resource-job.v1' and resource.get('cleanup_confirmed') is True and
        resource.get('inputs_unchanged') is True and resource.get('containers_remaining')==[] and
        resource.get('owned_processes_remaining')==[] and resource.get('exit_code')==report['exit_code'],
        'Original parent outer process/container cleanup is not closed')
    argv=resource['argv'];require(argv.count('--output')==1 and
        (P.ROOT/argv[argv.index('--output')+1]).resolve()==report_path.parent,'Parent resource owner targets another output')
    if report['status']=='interrupted':
        require(stop_path is not None and report.get('stop_reason')=='signal 15',
            'Interrupted130 seed requires exact owned Root SIGTERM stop authority')
        stop_authority(stop_path,report_path,resource_path,resource)
    artifacts=report.get('artifact_sha256');require(type(artifacts) is dict and artifacts,'Original parent artifact inventory missing')
    for name,value in artifacts.items():
        path=(report_path.parent/name).resolve()
        require(not Path(name).is_absolute() and '..' not in Path(name).parts and path.is_relative_to(report_path.parent) and
            sha(regular(path))==value,'Original parent closed artifact changed')
    return report


def seed_from_parent(parent_dir,state_path,prepared,pdk):
    flow=(parent_dir/'flow').resolve();state_path=regular(state_path).resolve()
    require(state_path.parent.parent==flow and state_path.name=='state_out.json' and
        re.fullmatch(r'(35-openroad-repairantennas|36-openroad-stamidpnr-3)',state_path.parent.name),
        'Seed must be exact top-level original post-antenna stage35/36')
    state=P.read(state_path);actual35=P.read(flow/'35-openroad-repairantennas/state_out.json')
    mounts={'/work/run':flow,'/work/inputs':prepared/'inputs','/work/pdk':pdk};frozen={}
    def view(value):
        if isinstance(value,dict):return {key:view(child) for key,child in value.items()}
        if isinstance(value,list):return [view(child) for child in value]
        if value is None:return None
        require(type(value) is str,'Unsupported native seed view')
        matches=[(prefix,root) for prefix,root in mounts.items() if value.startswith(prefix+'/')]
        require(len(matches)==1,'Seed view is outside explicit readonly mounts: '+value)
        prefix,root=matches[0];path=(root/value[len(prefix)+1:]).resolve()
        require(path.is_relative_to(root.resolve()),'Seed view escapes readonly mount')
        frozen[value]=bound(path)
        return '/work/parent/'+value[len('/work/run/'):] if prefix=='/work/run' else value
    seed={key:view(value) for key,value in state.items() if key!='metrics'};seed['metrics']=state.get('metrics',{})
    require(type(state.get('odb')) is str and state['odb']==actual35.get('odb') and
        state['odb'].startswith('/work/run/35-openroad-repairantennas/1-openroad-diodeinsertion/') and
        sha(frozen[state['odb']]['path'])==frozen[state['odb']]['sha256'],'Seed does not select the measured actual diode-insertion ODB')
    return seed,frozen


def source_snapshot(inputs):
    closure=dependency_closure(P.ROOT,SOURCES);head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True,timeout=30).strip();sources={}
    for name in closure['files']:
        data=subprocess.check_output(['git','show',head+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(data).hexdigest()==sha(P.ROOT/name),'Commit separate repair producer first: '+name)
        target=inputs/'producer'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);sources[name]=sha(target)
    shutil.copyfile(P.ROOT/PLUGIN,inputs/'librelane_plugin_streaming_8x4_repair.py')
    return head,sources,closure


def prepare(parent_report,parent_resource,prepared,state,observation,native_source,threads,output,stop_path=None):
    delta=candidate_delta(threads)
    prepared=Path(prepared).resolve(strict=True);base=P.verify(prepared)
    parent_report=regular(parent_report).resolve();parent_resource=regular(parent_resource).resolve()
    parent=closed_parent(parent_report,parent_resource,prepared,base,stop_path);state=regular(state).resolve()
    require(parent['artifact_sha256'].get(str(state.relative_to(parent_report.parent)))==sha(state),'Seed state not sealed by closed parent')
    observation=regular(observation).resolve();measured=P.read(observation)
    require(measured.get('schema')=='pinwheel.streaming-8x4-antenna-fanout-observation.v1' and
        measured.get('inputs_unchanged_during_read') is True and measured.get('qualified') is False and
        measured['after']['state']['sha256']==sha(parent_report.parent/'flow/35-openroad-repairantennas/state_out.json') and
        all(sha(path)==pin for path,pin in measured['input_sha256'].items()),'Measured actual diode load evidence differs')
    require({name:(item['before_loads'],item['after_loads']) for name,item in measured['deltas'].items()}==
        {'fanout1772':(6,15),'fanout1699':(8,11)},'Repair is outside the measured two-driver cause')
    for key in ('before','after'):
        observed,_=O.observe(parent_report.parent/'flow',measured[key]['state']['path'])
        require(observed==measured[key],'Fresh exact stage DEF load comparison differs')
    require(all(item['removed']==[] and item['added'] and all(endpoint[1:]==['A','sg13cmos5l_antennanp']
        for endpoint in item['added']) for item in measured['deltas'].values()),'Added loads are not exclusively measured passive diodes')
    native_source=regular(native_source).resolve();intake=P.read(native_source)
    require(intake.get('schema')=='pinwheel.librelane-container-source-copy.v1' and
        intake.get('image_id')==parent['runtime']['image_id'] and intake.get('cad_launched') is False and
        intake.get('container_process_launched') is False,'Pinned native source intake differs')
    for name,value in intake['file_sha256'].items():require(sha(native_source.parent/name)==value,'Native source copy changed')
    resolved=parent_report.parent/'flow/resolved.json';config=P.read(resolved);original=P.read(prepared/'inputs/core.json')
    require(original['CLOCK_PERIOD']==config['CLOCK_PERIOD']==20 and original['PL_TARGET_DENSITY_PCT']==config['PL_TARGET_DENSITY_PCT']==85 and
        original['OPENROAD_THREADS']==config['OPENROAD_THREADS']==4 and config['GRT_DESIGN_REPAIR_RUN_GRT'] is True and
        config['DRT_OPT_ITERS']==64 and config['RUN_POST_GRT_DESIGN_REPAIR'] is True,'Original measured config/routing rules differ')
    seed,views=seed_from_parent(parent_report.parent,state,prepared,Path(base['pdk_root']))
    output=Path(output).absolute();require(not output.exists(),'Preserve earlier separate repair candidate');inputs=output/'inputs';inputs.mkdir(parents=True)
    head,sources,closure=source_snapshot(inputs)
    # Keep native nonfinite metrics as native JSON observations, never coerce
    # them into finite success. The original raw state stays separately sealed.
    (inputs/'seed.json').write_text(json.dumps(seed,indent=2,allow_nan=True)+'\n')
    request=dict(schema='pinwheel.streaming-8x4-postantenna-repair-request.v1',flow=FLOW,added_step=STEP,
        seed_sha256=sha(inputs/'seed.json'),openroad_threads=threads,
        native_package_sha256={name.removeprefix('librelane/'):value for name,value in intake['file_sha256'].items()},
        original_core_sha256=sha(prepared/'inputs/core.json'),qualified=False,physical_acceptance=False)
    P.write(inputs/'request.json',request)
    record=dict(schema='pinwheel.streaming-8x4-postantenna-repair-preparation.v1',prepared_utc=datetime.now(timezone.utc).isoformat(),
        producer_commit=head,producer_sha256=sources,producer_dependency_closure=closure,
        original_preparation=bound(prepared/'preparation.json'),parent_report=bound(parent_report),parent_resource=bound(parent_resource),
        parent_stop_authority=None if stop_path is None else bound(stop_path),
        parent_state=bound(state),parent_seed_views=views,parent_flow=str(parent_report.parent/'flow'),
        measured_fanout=bound(observation),native_source_intake=bound(native_source),original_resolved_config=bound(resolved),
        pdk_root=base['pdk_root'],input_sha256=P.inventory(inputs),request=request,
        delta=delta,
        original_parent_is_not_final_target=True,native_executed=False,qualified=False,physical_acceptance=False,
        boundary='One separately selected canonical post-antenna repair from the exact closed measured prefix. Fresh DRT+ordinary tail and all final gates remain mandatory.')
    P.write(output/'preparation.json',record);verify(output);return record


def verify(output):
    output=Path(output).resolve(strict=True);record=P.read(output/'preparation.json')
    require(record.get('schema')=='pinwheel.streaming-8x4-postantenna-repair-preparation.v1' and
        record.get('native_executed') is False and record.get('qualified') is False and record.get('physical_acceptance') is False and
        record.get('original_parent_is_not_final_target') is True and P.inventory(output/'inputs')==record['input_sha256'],
        'Separate repair preparation changed')
    for name,value in record['producer_sha256'].items():
        require(sha(P.ROOT/name)==value==sha(output/'inputs/producer'/name),'Separate repair producer changed')
        committed=subprocess.check_output(['git','show',record['producer_commit']+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(committed).hexdigest()==value,'Repair staged source differs from its committed producer')
    require(dependency_closure(P.ROOT,SOURCES)==record['producer_dependency_closure'],'Repair source closure changed')
    for key in ('original_preparation','parent_report','parent_resource','parent_state','measured_fanout','native_source_intake','original_resolved_config'):
        item=record[key];require(sha(item['path'])==item['sha256'],'Repair authority changed: '+key)
    prepared=Path(record['original_preparation']['path']).parent;base=P.verify(prepared)
    marker=record.get('parent_stop_authority')
    if marker is not None:require(bound(marker['path'])==marker,'Root stop authority changed after preparation')
    closed_parent(record['parent_report']['path'],record['parent_resource']['path'],prepared,base,None if marker is None else marker['path'])
    seed,views=seed_from_parent(Path(record['parent_report']['path']).parent,record['parent_state']['path'],prepared,Path(base['pdk_root']))
    intake=P.read(record['native_source_intake']['path']);package={name.removeprefix('librelane/'):value for name,value in intake['file_sha256'].items()}
    require((output/'inputs/seed.json').read_text()==json.dumps(seed,indent=2,allow_nan=True)+'\n' and views==record['parent_seed_views'] and
        P.read(output/'inputs/request.json')==record['request'] and record['request']['seed_sha256']==sha(output/'inputs/seed.json') and
        record['request']['original_core_sha256']==sha(prepared/'inputs/core.json') and
        record['request']['native_package_sha256']==package and
        record['delta']==candidate_delta(record['request']['openroad_threads']) and
        sha(output/'inputs/librelane_plugin_streaming_8x4_repair.py')==record['producer_sha256'][PLUGIN],
        'Repair seed/request/core differs')
    require(record['request'].get('flow')==FLOW and record['request'].get('added_step')==STEP and
        record['request'].get('qualified') is False and record['request'].get('physical_acceptance') is False,
        'Repair native flow request differs')
    return record


def select_report(report_path,report_sha256,base_prepared,base_packet):
    """Authenticate only a fresh completed route in this separately typed run."""
    report_path=regular(report_path).resolve();require(sha(report_path)==report_sha256,'Repair run report changed')
    report=P.read(report_path)
    require(report.get('schema')=='pinwheel.streaming-8x4-postantenna-repair-run.v1' and report.get('mode')=='full' and
        type(report.get('exit_code')) is int and ((report.get('status')=='flow_completed' and report['exit_code']==0) or
        (report.get('status')=='failed' and report['exit_code']!=0)) and report.get('inputs_pdk_runtime_unchanged') is True and
        report.get('container_termination',{}).get('status')=='absent' and report.get('qualified') is False and
        report.get('physical_acceptance') is False and report.get('parent_is_not_final_target') is True,
        'Repair final selection requires a closed actual terminal run')
    preparation=report['preparation'];require(sha(preparation['path'])==preparation['sha256'],'Repair preparation changed')
    record=verify(Path(preparation['path']).parent)
    require(record['original_preparation']==report['original_preparation']==bound(Path(base_prepared)/'preparation.json') and
        P.verify(base_prepared)==base_packet and report['delta']==record['delta'],'Repair final baseline/candidate differs')
    require(report.get('actual_resolved_delta')==resolved_delta(P.read(record['original_resolved_config']['path']),
        P.read(report_path.parent/'flow/resolved.json'),record['request']['openroad_threads']),
        'Repair actual resource/physical config delta differs')
    artifacts=report['artifact_sha256'];actual={str(path.relative_to(report_path.parent)):sha(path) for path in report_path.parent.rglob('*')
        if path.is_file() and path!=report_path}
    require(actual==artifacts,'Repair final complete artifact membership/bytes changed')
    order=P.read(report_path.parent/'metadata/flow-order.json')
    require(validate_order(order['original_steps'],order['actual_steps'])=={key:value for key,value in order.items()
        if key not in ('schema','openroad_threads','qualified')} and order['openroad_threads']==record['request']['openroad_threads'],
        'Repair actual flow schedule changed')
    flow=(report_path.parent/'flow').resolve();rows=[];nested=[];ordinals=set()
    for row in report['states']:
        state_path=regular(row['state']).resolve()
        require(state_path.is_relative_to(flow) and state_path.name=='state_out.json' and
            row['state_sha256']==sha(state_path)==artifacts.get(str(state_path.relative_to(report_path.parent))),
            'Repair state is not a closed actual artifact')
        if state_path.parent.parent!=flow:
            nested.append(bound(state_path));continue
        match=re.fullmatch(r'(\d+)-(.+)',row['step_directory'])
        require(match is not None and state_path.parent.name==row['step_directory'] and int(match[1]) not in ordinals,
            'Ambiguous repair top-level state order')
        ordinal=int(match[1]);ordinals.add(ordinal);state=P.read(state_path);view=row.get('views',{}).get('odb')
        require(type(view) is dict and Path(view['path']).resolve().is_relative_to(flow) and
            sha(view['path'])==view['sha256']==artifacts.get(str(Path(view['path']).resolve().relative_to(report_path.parent))) and
            state.get('odb')==view['container']=='/work/run/'+str(Path(view['path']).resolve().relative_to(flow)),
            'Repair state lacks a fresh authenticated actual ODB')
        rows.append((ordinal,row,state_path,Path(view['path']).resolve()))
    repaired=[row for row in rows if row[1]['step_directory'].endswith('-openroad-postantennadesignrepair')]
    routed=[row for row in rows if row[1]['step_directory'].endswith('-openroad-detailedrouting')]
    require(len(repaired)==len(routed)==1 and repaired[0][0]<routed[0][0],
        'No completed unique fresh repair plus DetailedRouting state; failed parent/prefix cannot be promoted')
    require(repaired[0][3].parent==repaired[0][2].parent and routed[0][3].parent==routed[0][2].parent,
        'Completed repair and DRT must each write a fresh actual ODB in their own stage directory')
    latest=max(rows,key=lambda row:row[0]);require(latest[0]>=routed[0][0] and sha(report_path)==report_sha256,'Repair final target changed')
    return dict(schema='pinwheel.streaming-8x4-repair-final-target.v1',physical_report=bound(report_path),
        physical_status=report['status'],physical_exit_code=report['exit_code'],completed_detailed_route_state=bound(routed[0][2]),
        physical_state=bound(latest[2]),actual_odb=bound(latest[3]),latest_step=latest[1]['step_directory'],
        physical_candidate_kind='canonical-postantenna-repair',repair_preparation=preparation,
        original_preparation=record['original_preparation'],original_parent_report=record['parent_report'],
        measured_fanout=record['measured_fanout'],actual_repair_state=bound(repaired[0][2]),
        authenticated_nested_states=nested,target_scope='final-routed-digital-pending-proof',
        physical_acceptance=False,post_pnr_equivalence_proved=False,
        boundary='Fresh actual repaired/routed candidate only. Parent prefix is not promoted; final proof, RC/timing and physical checks remain independent.')


def validate_order(base_ids,actual):
    expected=[]
    for name in base_ids:
        expected.append(name)
        if name=='OpenROAD.RepairAntennas':expected.append(STEP)
    # Scheduled steps include the original gated timing resizer even when it
    # emits no state. State36 being STA is not evidence of schedule adjacency.
    seam=('OpenROAD.RepairAntennas',STEP,'OpenROAD.ResizerTimingPostGRT',
        'OpenROAD.STAMidPNR-3','OpenROAD.DetailedRouting')
    require(actual==expected and len(set(actual))==len(actual) and actual.count(STEP)==1 and
        all(actual.index(left)<actual.index(right) for left,right in zip(seam,seam[1:])) and
        tuple(actual[actual.index('OpenROAD.DetailedRouting'):])==R.TAIL,
        'Repair schedule has an undeclared delta or omits ordinary tail')
    return dict(original_steps=base_ids,actual_steps=actual,added_canonical_step=STEP,execution_start=STEP,
        requested_stop='Misc.ReportManufacturability',ordinary_tail=list(R.TAIL),scheduled_is_not_completed_evidence=True)


def native(inputs,name):
    from librelane.steps import openroad
    from librelane_plugin_streaming_8x4 import Streaming8x4Certified
    from librelane_plugin_streaming_8x4_repair import Streaming8x4PostAntennaRepair,PostAntennaDesignRepair
    inputs=Path(inputs);request=P.read(inputs/'request.json');package=Path(openroad.__file__).resolve().parents[1]
    require(request.get('schema')=='pinwheel.streaming-8x4-postantenna-repair-request.v1' and sha(inputs/'seed.json')==request['seed_sha256'] and
        sha('/work/inputs/core.json')==request['original_core_sha256'],'Native repair inputs differ')
    for relative,value in request['native_package_sha256'].items():require(sha(package/relative)==value,'Pinned native source changed: '+relative)
    require(PostAntennaDesignRepair.__bases__==(openroad.RepairDesignPostGRT,) and
        PostAntennaDesignRepair.get_script_path is openroad.RepairDesignPostGRT.get_script_path and
        PostAntennaDesignRepair.run is openroad.RepairDesignPostGRT.run,'Repair body is not unchanged canonical step')
    order=validate_order([step.id for step in Streaming8x4Certified.Steps],[step.id for step in Streaming8x4PostAntennaRepair.Steps])
    order.update(schema='pinwheel.streaming-8x4-repair-native-order.v1',openroad_threads=request['openroad_threads'],qualified=False)
    R.write('/work/metadata/flow-order.json',order)
    command=[sys.executable,'-B','-m','librelane','--manual-pdk','--pdk-root','/work/pdk','--pdk','ihp-sg13cmos5l',
        '--jobs','4','--flow',FLOW,'--override-config','OPENROAD_THREADS='+str(request['openroad_threads']),
        '--run-tag',name,'--force-run-dir','/work/run','--with-initial-state','/work/repair/seed.json',
        '--from',STEP,'--to','Misc.ReportManufacturability','/work/inputs/core.json']
    os.execv(sys.executable,command)


def run(args):
    workspace=Path(args.workspace).resolve(strict=True) if args.workspace else P.ROOT;P.ROOT=workspace
    preparation=Path(args.preparation).resolve(strict=True);record=verify(preparation)
    worker=preparation/'inputs/producer'/OWN
    if not args.frozen:
        os.execv(sys.executable,[sys.executable,'-B',str(worker),'run','--preparation',str(preparation),'--output',str(Path(args.output).absolute()),
            '--name',args.name,'--timeout',str(args.timeout),'--workspace',str(workspace),'--frozen'])
    require(Path(__file__).resolve()==worker.resolve(),'Repair must execute its exact frozen producer')
    require(type(args.timeout) is int and 1<=args.timeout<=14400 and re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',args.name),'Invalid repair name/budget')
    output=Path(args.output).absolute();require(not output.exists(),'Preserve prior repair run');output.mkdir(parents=True)
    (output/'flow').mkdir();(output/'metadata').mkdir();runtime=inspect_runtime(P.read(workspace/'tools/physical-toolchain.json'));owner=str(uuid.uuid4())
    prepared=Path(record['original_preparation']['path']).parent;pdk=Path(record['pdk_root'])
    command=['docker','run','--rm','--pull','never','--name',args.name,'--label','org.pinwheel.streaming8_owner='+owner,
        '--network','none','--cpus','4','--memory','6g','--memory-swap','6g',
        '--env','PYTHONPATH=/work/repair:/work/inputs:/work/repair/producer/scripts','--env','PYTHONDONTWRITEBYTECODE=1',
        '--mount',f'type=bind,source={prepared/"inputs"},target=/work/inputs,readonly',
        '--mount',f'type=bind,source={preparation/"inputs"},target=/work/repair,readonly',
        '--mount',f'type=bind,source={record["parent_flow"]},target=/work/parent,readonly',
        '--mount',f'type=bind,source={pdk},target=/work/pdk,readonly',
        '--mount',f'type=bind,source={output/"flow"},target=/work/run',
        '--mount',f'type=bind,source={output/"metadata"},target=/work/metadata',
        '--workdir','/work/inputs',runtime['image_id'],'python3','-B','/work/repair/producer/'+OWN,'native',
        '--inputs','/work/repair','--name',args.name]
    receipt=dict(schema='pinwheel.streaming-8x4-postantenna-repair-run.v1',status='running',exit_code=None,mode='full',
        preparation=bound(preparation/'preparation.json'),original_preparation=record['original_preparation'],delta=record['delta'],
        ownership_label=owner,container_name=args.name,runtime=runtime,argv=command,qualified=False,physical_acceptance=False,
        configured_disabled_checks={key:P.read(prepared/'inputs/core.json').get(key) for key in ('RUN_EQY','RUN_KLAYOUT_XOR','RUN_LINTER')
            if P.read(prepared/'inputs/core.json').get(key) is False},
        parent_is_not_final_target=True,started_utc=datetime.now(timezone.utc).isoformat())
    R.write(output/'report.json',receipt);process=None;started=time.monotonic();previous=signal.getsignal(signal.SIGTERM)
    def interrupted(signum,frame):raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    with (output/'native.log').open('w') as log:
        try:
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);code=process.wait(timeout=args.timeout)
            receipt.update(status='flow_completed' if code==0 else 'failed',exit_code=code)
        except subprocess.TimeoutExpired:receipt.update(status='timed_out',exit_code=124)
        except KeyboardInterrupt as error:receipt.update(status='interrupted',exit_code=130,error=str(error))
        except BaseException as error:receipt.update(status='blocked',exit_code=127,error=type(error).__name__+': '+str(error))
        finally:
            receipt['container_termination']=R.cleanup(owner,log)
            if process is not None and process.poll() is None:
                os.killpg(process.pid,signal.SIGTERM)
                try:process.wait(timeout=5)
                except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);process.wait(timeout=5)
            signal.signal(signal.SIGTERM,previous)
            try:
                require(verify(preparation)==record and inspect_runtime(P.read(workspace/'tools/physical-toolchain.json'))==runtime,
                    'Repair input/runtime changed')
                receipt['actual_resolved_delta']=resolved_delta(P.read(record['original_resolved_config']['path']),
                    P.read(output/'flow/resolved.json'),record['request']['openroad_threads'])
                receipt['inputs_pdk_runtime_unchanged']=True
            except BaseException as error:receipt.update(status='invalidated',inputs_pdk_runtime_unchanged=False,closeout_error=str(error))
            if receipt['container_termination']['status']!='absent':receipt['status']='cleanup_unconfirmed'
            try:receipt['states']=R.states(output,prepared,pdk)
            except BaseException as error:receipt.update(status='invalidated',state_inventory_error=type(error).__name__+': '+str(error))
            receipt['elapsed_seconds']=round(time.monotonic()-started,3)
            receipt['artifact_sha256']={str(path.relative_to(output)):sha(path) for path in sorted(output.rglob('*'))
                if path.is_file() and path!=output/'report.json'}
            R.write(output/'report.json',receipt)
    return receipt


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    prep=sub.add_parser('prepare')
    for name in ('parent-report','parent-resource','prepared','state','observation','native-source','output'):prep.add_argument('--'+name,type=Path,required=True)
    prep.add_argument('--threads',type=int,required=True)
    prep.add_argument('--stop-authority',type=Path)
    check=sub.add_parser('verify');check.add_argument('--preparation',type=Path,required=True)
    launch=sub.add_parser('run')
    for name in ('preparation','output'):launch.add_argument('--'+name,type=Path,required=True)
    launch.add_argument('--name',required=True);launch.add_argument('--timeout',type=int,required=True)
    launch.add_argument('--workspace',type=Path);launch.add_argument('--frozen',action='store_true',help=argparse.SUPPRESS)
    nat=sub.add_parser('native');nat.add_argument('--inputs',type=Path,required=True);nat.add_argument('--name',required=True)
    args=parser.parse_args()
    if args.mode=='native':native(args.inputs,args.name);return 0
    if args.mode=='prepare':prepare(args.parent_report,args.parent_resource,args.prepared,args.state,args.observation,args.native_source,args.threads,args.output,args.stop_authority);return 0
    if args.mode=='verify':verify(args.preparation);return 0
    receipt=run(args);print(args.output/'report.json');return 0 if receipt['status']=='flow_completed' else receipt.get('exit_code',3) or 3


if __name__=='__main__':raise SystemExit(main())
