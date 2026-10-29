"""New24 HOST authority around original strict full-terminal Native PSM queries.

Read-only geometric PG connectivity on one closed final 8x4 ODB.

Preparation is HOST only. Native execution requires a separate Root GO and the
campaign resource guard. PSM's short check is a stub: this leaf establishes no
cross-rail short, cell-internal GDS, package delivery, IR-drop or EM claim.
"""
import argparse
import hashlib
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

import process_group
import streaming_8x4_closure24_signoff_execute as V
import streaming_8x4_power_grid as ORIGINAL
from streaming_8x4_geometry import regular, require, sha
from streaming_tt_intake import dependency_closure

P=V.P
R=V.R
COMMIT='dcf36133a369abc8f3c5e5738cd4d82e4903c0e0'
SOURCE_MANIFEST_SHA256='7e20a6c7a1075fb1605fb9a49ec7eb93f84a5c424bc9f56afeb40ae0a2afb012'
ENTRIES=('scripts/streaming_8x4_closure24_power_grid.py','scripts/streaming_tt_export_odb.py','tools/physical-toolchain.json')
LEAF_SECONDS=180
OUTER_SECONDS=240
BOUNDARY=('Geometric same-rail open-path connectivity of all inventoried PG terminals, '
    'under OpenDB/LEF/via semantics. PSM checkShort is a stub. No cross-rail short, '
    'cell-internal GDS, package delivery, IR-drop, activity, EM or full physical acceptance.')
LAUNCHER='from streaming_8x4_power_grid import native\nnative("/work/pg/inputs/request.json")\n'


bound = ORIGINAL.bound


artifacts = ORIGINAL.artifacts


source_evidence = ORIGINAL.source_evidence


expected_rails = ORIGINAL.expected_rails


inventory_totals = ORIGINAL.inventory_totals


def closed_views(path):
    path=regular(path).resolve();report,preparation=V.closed_views(path)
    require(artifacts(path.parent)==report['artifact_sha256'],'Final view artifact membership differs')
    inventory=path.parent/'actual-signal/inventory.json'
    expected_rails(P.read(inventory))
    return report,preparation


def stage_producer(inputs):
    closure=dependency_closure(P.ROOT,ENTRIES)
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True,timeout=30).strip();sources={}
    for name in closure['files']:
        data=subprocess.check_output(['git','show',commit+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(data).hexdigest()==sha(P.ROOT/name),'Commit new PG producer first: '+name)
        target=inputs/'producer'/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        sources[name]=sha(target)
    return commit,sources,closure


def prepare(views_path,source_root,output):
    views_path=regular(views_path).resolve();views,original=closed_views(views_path)
    selected_runtime=P.read(views['target']['physical_report']['path'])['runtime']
    validate_runtime(views['runtime'],selected_runtime)
    source_root=Path(source_root).resolve();source_files=source_evidence(source_root)
    output=V.Q.owned(output,P.ROOT);require(not output.exists(),'Preserve prior PG owner')
    inputs=output/'inputs';inputs.mkdir(parents=True)
    commit,sources,closure=stage_producer(inputs)
    for name in source_files:
        target=inputs/'psm-source'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source_root/name,target)
    for source,name in [(views_path.parent/'actual-signal/inventory.json','inventory.json'),
        (views_path.parent/'inputs/reference.json','reference.json')]:shutil.copyfile(source,inputs/name)
    target=views['target'];source_odb=regular(target['actual_odb']['path']).resolve()
    require(sha(source_odb)==target['actual_odb']['sha256'],'Selected final PG database changed')
    request=dict(schema='pinwheel.streaming-8x4-power-grid-request.v1',source_odb='/work/target.odb',
        source_odb_sha256=sha(source_odb),inventory_sha256=sha(inputs/'inventory.json'),
        reference_sha256=sha(inputs/'reference.json'),top=P.read(inputs/'inventory.json')['top'],
        rails=expected_rails(P.read(inputs/'inventory.json')),openroad_source_commit=COMMIT,
        leaf_timeout_seconds=LEAF_SECONDS,outer_timeout_seconds=OUTER_SECONDS,
        floorplanning=False,dont_require_terminals=False,qualified=False,physical_acceptance=False)
    P.write(inputs/'request.json',request)
    result=dict(schema='pinwheel.closure24-power-grid-preparation.v1',views_report=bound(views_path),
        target=target,physical_candidate=views['physical_candidate'],source_odb=bound(source_odb),
        runtime=selected_runtime,
        source_evidence_root=str(source_root),source_evidence_sha256=source_files,
        producer_commit=commit,producer_sha256=sources,producer_dependency_closure=closure,
        input_sha256=P.inventory(inputs),executed=False,qualified=False,physical_acceptance=False,boundary=BOUNDARY)
    P.write(output/'preparation.json',result);return result


def verify_preparation(output):
    output=V.Q.owned(output,P.ROOT);packet=P.read(output/'preparation.json')
    require(packet.get('schema')=='pinwheel.closure24-power-grid-preparation.v1' and
        packet.get('executed') is False and packet.get('physical_acceptance') is False and
        P.inventory(output/'inputs')==packet['input_sha256'],'PG preparation contract/membership differs')
    path=packet['views_report'];require(sha(path['path'])==path['sha256'],'PG final views receipt changed')
    views,_=closed_views(path['path'])
    require(views['target']==packet['target'] and views['physical_candidate']==packet['physical_candidate'] and
        packet['source_odb']==bound(views['target']['actual_odb']['path']),'PG selected physical candidate differs')
    require(packet['runtime']==P.read(packet['target']['physical_report']['path'])['runtime'],
        'PG selected physical runtime authority changed')
    validate_runtime(views['runtime'],packet['runtime'])
    require(source_evidence(packet['source_evidence_root'])==packet['source_evidence_sha256']==
        source_evidence(output/'inputs/psm-source'),'PG source evidence differs')
    require(dependency_closure(P.ROOT,ENTRIES)==packet['producer_dependency_closure'] and
        set(packet['producer_sha256'])==set(packet['producer_dependency_closure']['files']),
        'PG producer closure membership differs')
    for name,value in packet['producer_sha256'].items():
        require(sha(P.ROOT/name)==value==sha(output/'inputs/producer'/name),'PG producer changed: '+name)
        committed=subprocess.check_output(['git','show',packet['producer_commit']+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(committed).hexdigest()==value,'PG producer differs from its original committed source')
    request=P.read(output/'inputs/request.json')
    require(request==dict(schema='pinwheel.streaming-8x4-power-grid-request.v1',source_odb='/work/target.odb',
        source_odb_sha256=packet['source_odb']['sha256'],inventory_sha256=sha(output/'inputs/inventory.json'),
        reference_sha256=sha(output/'inputs/reference.json'),top=P.read(output/'inputs/inventory.json')['top'],
        rails=expected_rails(P.read(output/'inputs/inventory.json')),openroad_source_commit=COMMIT,
        leaf_timeout_seconds=LEAF_SECONDS,outer_timeout_seconds=OUTER_SECONDS,
        floorplanning=False,dont_require_terminals=False,qualified=False,physical_acceptance=False),'PG request differs')
    return packet


positive_rect = ORIGINAL.positive_rect


pin_shapes = ORIGINAL.pin_shapes


census = ORIGINAL.census


validate_census = ORIGINAL.validate_census


validate_shapes = ORIGINAL.validate_shapes


caught = ORIGINAL.caught


revision_identity = ORIGINAL.revision_identity


observe_revision = ORIGINAL.observe_revision


native = ORIGINAL.native


parse_log = ORIGINAL.parse_log


native_result = ORIGINAL.native_result


native_supervise = ORIGINAL.native_supervise


validate_runtime = ORIGINAL.validate_runtime


def container_command(output,packet,runtime,owner,name):
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name) and str(uuid.UUID(owner))==owner,'Unsafe PG container name/owner')
    validate_runtime(runtime,packet['runtime'])
    return ['docker','run','--rm','--pull','never','--name',name,'--label','org.pinwheel.streaming8_owner='+owner,
        '--network','none','--cpus','1','--memory','2g','--memory-swap','2g','--read-only','--tmpfs','/tmp:rw,size=128m',
        '--env','PYTHONDONTWRITEBYTECODE=1','--env','PYTHONPATH=/work/pg/inputs/producer/scripts',
        '--mount',f'type=bind,source={output},target=/work/pg',
        '--mount',f'type=bind,source={output/"inputs"},target=/work/pg/inputs,readonly',
        '--mount',f'type=bind,source={packet["source_odb"]["path"]},target=/work/target.odb,readonly',
        '--workdir','/work/pg',runtime['image_id'],'python3','-B',
        '/work/pg/inputs/producer/scripts/streaming_8x4_closure24_power_grid.py','native-supervise']


def run(output,name):
    output=V.Q.owned(output,P.ROOT);packet=verify_preparation(output)
    require({path.name for path in output.iterdir()}=={'inputs','preparation.json'},'PG output is not fresh')
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name),'Unsafe PG container name')
    runtime=V.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'));owner=str(uuid.uuid4())
    (output/'launch.py').write_text(LAUNCHER)
    command=container_command(output,packet,runtime,owner,name)
    execution=V.owned_native(command,output,owner,OUTER_SECONDS)
    report=dict(schema='pinwheel.closure24-power-grid-run.v1',preparation=bound(output/'preparation.json'),
        target=packet['target'],physical_candidate=packet['physical_candidate'],runtime=runtime,execution=execution,
        leaf_timeout_seconds=LEAF_SECONDS,outer_timeout_seconds=OUTER_SECONDS,passed=False,
        outer_resource_cleanup_required=True,
        resource_cleanup_join='Separate exact campaign resource-supervisor receipt remains mandatory.',
        geometric_open_path_connectivity=False,shorts_checked=False,ir_drop_qualified=False,
        qualified=False,physical_acceptance=False,boundary=BOUNDARY)
    try:
        require(execution.get('status')=='completed' and execution.get('exit_code')==0 and
            execution.get('timeout_seconds')==OUTER_SECONDS and
            execution.get('container_termination',{}).get('status')=='absent','PG Native execution/cleanup did not close')
        native_value,stats=native_result(output,packet)
        require(verify_preparation(output)==packet and V.inspect_runtime(P.read(P.ROOT/'tools/physical-toolchain.json'))==runtime,
            'PG source/input/runtime changed across execution')
        report.update(passed=True,geometric_open_path_connectivity=True,native=bound(output/'native.json'),
            census_totals={name:{key:row[key] for key in ('iterm_count','bterm_count','bpin_count','swire_count',
                'swire_routing_shapes','swire_vias','skipped_iterms','skipped_bpins')} for name,row in native_value['rails'].items()},
            psm_graph_statistics=stats,inputs_runtime_unchanged=True)
    except BaseException as error:report['error']=type(error).__name__+': '+str(error)
    report['artifact_sha256']=artifacts(output);P.write(output/'report.json',report);return report


def verify(path):
    path=regular(path).resolve();V.Q.owned(path.parent,P.ROOT);report=P.read(path);output=path.parent
    require(report.get('schema')=='pinwheel.closure24-power-grid-run.v1' and report.get('passed') is True and
        report.get('geometric_open_path_connectivity') is True and report.get('shorts_checked') is False and
        report.get('ir_drop_qualified') is False and report.get('physical_acceptance') is False and
        report.get('qualified') is False and report.get('inputs_runtime_unchanged') is True and
        report.get('outer_resource_cleanup_required') is True and
        report.get('leaf_timeout_seconds')==LEAF_SECONDS and report.get('outer_timeout_seconds')==OUTER_SECONDS and
        artifacts(output)==report.get('artifact_sha256'),'PG run/claim/artifact membership is not closed')
    packet=verify_preparation(output);execution=P.read(output/'execution.json')
    command=execution.get('argv');require(type(command) is list and len(command)>6 and
        command==container_command(output,packet,report['runtime'],execution['owner'],command[6]),
        'PG container command/resource/mount contract differs')
    require(report['preparation']==bound(output/'preparation.json') and report['target']==packet['target'] and
        report['physical_candidate']==packet['physical_candidate'] and report['execution']==execution and
        execution.get('status')=='completed' and execution.get('exit_code')==0 and execution.get('timeout_seconds')==OUTER_SECONDS and
        execution.get('container_termination',{}).get('status')=='absent' and report['native']==bound(output/'native.json'),
        'PG execution/target binding differs')
    value,stats=native_result(output,packet)
    require(report['psm_graph_statistics']==stats and report['census_totals']=={name:{key:row[key] for key in
        ('iterm_count','bterm_count','bpin_count','swire_count','swire_routing_shapes','swire_vias','skipped_iterms','skipped_bpins')}
        for name,row in value['rails'].items()},'PG rederived observation differs')
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('prepare')
    for name in ('views-report','source-root','output'):p.add_argument('--'+name,type=Path,required=True)
    p=sub.add_parser('run');p.add_argument('--output',type=Path,required=True);p.add_argument('--container-name',required=True)
    p=sub.add_parser('verify');p.add_argument('--report',type=Path,required=True)
    sub.add_parser('native-supervise')
    args=parser.parse_args()
    if args.mode=='prepare':prepare(args.views_report,args.source_root,args.output)
    elif args.mode=='run':return 0 if run(args.output,args.container_name)['passed'] else 2
    elif args.mode=='native-supervise':return native_supervise()
    else:verify(args.report)
    return 0


if __name__=='__main__':raise SystemExit(main())
