#!/usr/bin/env python3
"""Bounded fresh STA diagnostic on a sealed physical checkpoint.

This intentionally permits a failed physical attempt's last successful ODB.
Every result remains unqualified; final ODB/export/SPEF provenance and wire
annotation need separate acceptance before using these measurements as signoff.
"""
import argparse
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import time
import uuid

from streaming_tt_intake import dependency_closure,stage_sources
from streaming_tt_physical import ROOT,committed,inspect_runtime,verify_pdk
from streaming_tt_signoff import read,regular,require,sha,unchanged,write
from validation_run import fresh_directory


def pdk_identity(report,root,lock):
    if report['schema'] in ('pinwheel.streaming-tt-physical-run.v2','pinwheel.streaming-tt-final-run.v1'):
        from streaming_tt_pdk import verify_complete_pdk
        return verify_complete_pdk(root,lock,read(ROOT/'tools/streaming-tt-signoff.json'))
    return verify_pdk(root,lock)


def read_checkpoint(path,*,producer):
    """Discard inherited metrics before checking the finite identity envelope.

    Native physical receipts can retain unavailable optional metrics as Infinity.
    No inherited metric participates in a fresh STA request or assessment.
    """
    def pairs(items):
        result={}
        for key,value in items:
            require(key not in result,'Duplicate checkpoint JSON key: '+key)
            result[key]=value
        return result
    value=json.loads(regular(path).read_bytes(),object_pairs_hook=pairs)
    require(type(value) is dict,'Expected checkpoint object')
    if producer:
        for state in value.get('states',[]):state.pop('metrics',None)
    else:value.pop('metrics',None)
    def finite(item):
        require(type(item) is not float or math.isfinite(item),'Nonfinite checkpoint identity')
        if type(item) is dict:
            for child in item.values():finite(child)
        elif type(item) is list:
            for child in item:finite(child)
    finite(value);return value


def checkpoint(report_path,state_path):
    report_path=regular(report_path);state_path=regular(state_path)
    report=read_checkpoint(report_path,producer=True);state=read_checkpoint(state_path,producer=False)
    require(report.get('schema') in ('pinwheel.streaming-tt-physical-run.v1','pinwheel.streaming-tt-physical-run.v2',
        'pinwheel.streaming-tt-final-run.v1'),
        'Unknown physical producer receipt')
    require(report.get('inputs_unchanged_after_run') is True and
        report.get('container_termination',{}).get('status')=='absent','Unclosed physical producer inputs')
    roots=report.get('path_map')
    if report['schema']=='pinwheel.streaming-tt-final-run.v1':
        metadata=read(report_path.parent/'inputs.json')
        require(sha(report_path.parent/'inputs.json')==report.get('prepared_input_sha256') and
            metadata.get('schema')=='pinwheel.streaming-tt-final-input.v1' and
            report.get('source_commit')==metadata.get('source_commit') and
            report.get('producer_commit')==metadata.get('producer_commit'), 'Final input identity changed')
        roots={'/work/run':str(report_path.parent/'flow'),'/work/inputs':str(report_path.parent/'inputs'),
            '/work/pdk':metadata['pdk']}
    require(type(roots) is dict and set(roots)=={'/work/run','/work/inputs','/work/pdk'},'Wrong physical mount inventory')
    roots={name:Path(path).resolve() for name,path in roots.items()}
    require(state_path.is_relative_to(roots['/work/run']) and state_path.name=='state_out.json','State outside producer output')
    matches=[row for row in report.get('states',[]) if Path(row['state']).resolve()==state_path]
    require(len(matches)==1 and matches[0]['state_sha256']==sha(state_path),'Changed/unrecorded physical checkpoint')
    odb=state.get('odb');require(type(odb) is str and odb.startswith('/work/run/'),'Missing actual checkpoint ODB')
    host=regular(roots['/work/run']/odb.removeprefix('/work/run/'))
    require(host.is_relative_to(roots['/work/run']) and matches[0]['views']['odb']['sha256']==sha(host),
        'Physical checkpoint ODB changed')
    return report,roots,odb,host


def constraints(report_path,report,roots):
    """Bind fresh constraints to the already closed producer, before freezing."""
    report_path=regular(report_path)
    final=report['schema']=='pinwheel.streaming-tt-final-run.v1'
    metadata_path=report_path.parent/'inputs.json' if final else Path(report['design'])/'inputs.json'
    metadata_path=regular(metadata_path);metadata=read(metadata_path)
    require(sha(metadata_path)==report.get('prepared_input_sha256'), 'Prepared timing input receipt changed')
    config=regular(roots['/work/run']/'resolved.json');sdc=regular(roots['/work/inputs']/'core.sdc')
    config_key=str(config.relative_to(report_path.parent))
    require(report.get('artifact_sha256',{}).get(config_key)==sha(config),
        'Resolved timing configuration differs from closed producer')
    require(metadata.get('input_sha256',{}).get('core.sdc')==sha(sdc),
        'Timing SDC differs from closed prepared input')
    return {str(path):sha(path) for path in (metadata_path,config,sdc)}


def extracted_views(report_path,state_path,report,roots,odb,host,export_path):
    """Use actual ODB re-export and the checkpoint's exact nominal SPEF."""
    code=report.get('exit_code')
    closed=type(code) is int and ((report.get('status')=='flow_completed' and code==0) or
        (report.get('status')=='failed' and code!=0))
    require(report['schema']=='pinwheel.streaming-tt-final-run.v1' and closed and
        report.get('inputs_unchanged_after_run') is True and
        report.get('container_termination',{}).get('status')=='absent',
        'Extracted measurement requires a closed final producer; failed checks remain qualification gaps')
    export_path=regular(export_path);exported=read(export_path)
    require(exported.get('schema')=='pinwheel.streaming-tt-signoff-export.v1' and
        exported.get('completed') is True and exported.get('exit_code')==0 and
        exported.get('inputs_unchanged') is True and exported.get('inherited_netlist') is False and
        exported.get('actual_database_sha256')==sha(host) and
        exported.get('input_sha256_before',{}).get('/work/run/resolved.json')==sha(roots['/work/run']/'resolved.json'),
        'Export does not bind the actual final ODB and resolved configuration')
    frozen={str(export_path):sha(export_path)}
    for name,digest in exported.get('artifacts_sha256',{}).items():
        path=regular(export_path.parent/name)
        require(path.is_relative_to(export_path.parent) and sha(path)==digest,'ODB export artifact changed')
        frozen[str(path)]=digest
    require('implemented.v' in exported.get('artifacts_sha256',{}),'Actual ODB netlist absent')
    spef=read_checkpoint(state_path,producer=False).get('spef')
    require(type(spef) is dict and set(spef)=={'nom_*'} and type(spef['nom_*']) is str and
        spef['nom_*'].startswith('/work/run/'),'Missing exact nominal final SPEF')
    file=regular(roots['/work/run']/spef['nom_*'].removeprefix('/work/run/'))
    require(file.is_relative_to(roots['/work/run']) and report.get('artifact_sha256',{}).get(
        str(file.relative_to(regular(report_path).parent)))==sha(file),'Final SPEF differs from closed producer')
    require(file.stat().st_size>0,'Empty final SPEF');frozen[str(file)]=sha(file)
    return dict(odb=odb,nl='/work/export/implemented.v',spef=spef),frozen,export_path.parent


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--physical-report',required=True,type=Path)
    parser.add_argument('--state',required=True,type=Path)
    parser.add_argument('--tag',required=True)
    parser.add_argument('--mode',choices=('nominal','extracted'),default='nominal')
    parser.add_argument('--odb-export-report',type=Path)
    parser.add_argument('--timeout',type=int,default=300)
    args=parser.parse_args();require(1<=args.timeout<=1800,'STA timeout outside1..1800s')
    report,roots,odb,host=checkpoint(args.physical_report,args.state)
    contract=constraints(args.physical_report,report,roots)
    require((args.odb_export_report is not None)==(args.mode=='extracted'),
        'Only extracted mode requires an actual ODB export receipt')
    views={'odb':odb};export_mount=None
    if args.mode=='extracted':
        views,exported,export_mount=extracted_views(args.physical_report,args.state,report,roots,odb,host,args.odb_export_report)
        contract.update(exported)
    out=fresh_directory(ROOT/'build/streaming-tt-sta',args.tag).resolve()
    lock=read(ROOT/'tools/physical-toolchain.json');runtime=inspect_runtime(lock)
    pdk=pdk_identity(report,roots['/work/pdk'],lock)
    closure=dependency_closure(ROOT,['scripts/run-streaming-tt-sta.py','scripts/streaming_tt_sta.py',
        'tools/physical-toolchain.json','tools/streaming-tt-signoff.json'])
    stage_sources(ROOT,out/'producer',closure['files'],committed)
    frozen={str(path.resolve()):sha(path) for path in (args.physical_report,args.state,host,
        roots['/work/run']/'resolved.json',roots['/work/inputs']/'core.sdc')}
    frozen.update(contract)
    frozen.update({str(out/'producer'/name):sha(out/'producer'/name) for name in closure['files']})
    request=dict(schema='pinwheel.streaming-tt-fresh-sta-request.v1',mode=args.mode,views=views,
        out='/probe/native',config='/work/run/resolved.json',pdk='/work/pdk',design='/work/inputs',
        tech_lef='/work/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef',
        sdc='/work/inputs/core.sdc')
    write(out/'request.json',request);frozen[str(out/'request.json')]=sha(out/'request.json')
    owner=str(uuid.uuid4());label='org.pinwheel.streaming_tt_sta_owner='+owner
    command=['docker','run','--rm','--pull','never','--name','pinwheel-sta-'+args.tag,
        '--label',label,'--network','none','--cpus','1','--memory','2g','--memory-swap','2g','--read-only',
        '--tmpfs','/tmp:rw,size=268435456','--env','PYTHONDONTWRITEBYTECODE=1',
        '--env','PYTHONPATH=/worker/scripts']
    for native,host_root in roots.items():
        command+=['--mount','type=bind,source='+str(host_root)+',target='+native+',readonly']
    if export_mount is not None:
        command+=['--mount','type=bind,source='+str(export_mount)+',target=/work/export,readonly']
    command+=['--mount','type=bind,source='+str(out/'producer')+',target=/worker,readonly',
        '--mount','type=bind,source='+str(out)+',target=/probe','--workdir','/probe',runtime['image_id'],
        'python3','-B','/worker/scripts/streaming_tt_sta.py','--native-request','/probe/request.json']
    receipt=dict(schema='pinwheel.streaming-tt-fresh-sta-host.v1',qualified=False,physical_acceptance_claim=False,
        source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        status='intent',argv=command,input_sha256=frozen,producer_closure=closure,runtime=runtime,
        cpus=1,memory='2g',memory_swap='2g',network='none',physical_source_commit=report['source_commit'],
        mode=args.mode,ownership_label=owner,pdk=pdk,closed_constraint_sha256=contract)
    write(out/'report.json',receipt);started=time.monotonic();process=None
    with (out/'native.log').open('w') as log:
        try:
            receipt['status']='running';write(out/'report.json',receipt)
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            code=process.wait(timeout=args.timeout)
            receipt.update(exit_code=code,status='completed' if code==0 else 'failed')
        except subprocess.TimeoutExpired:
            receipt.update(exit_code=124,status='timed_out')
        except KeyboardInterrupt:
            receipt.update(exit_code=130,status='interrupted')
        finally:
            try:
                query=['docker','container','ls','--all','--no-trunc','--filter','label='+label,'--format','{{.ID}}']
                ids=subprocess.check_output(query,text=True,timeout=15).splitlines()
                require(all(len(value)==64 and set(value)<=set('0123456789abcdef') for value in ids),'Invalid owned container ID')
                for value in ids:subprocess.run(['docker','stop','--time','5',value],stdout=log,stderr=subprocess.STDOUT,timeout=20,check=True)
                require(not subprocess.check_output(query,text=True,timeout=15).strip(),'STA owned container remains')
                receipt['owned_container_absent']=True
                if process is not None and process.poll() is None:
                    os.killpg(process.pid,signal.SIGTERM);process.wait(timeout=10)
                unchanged(frozen);require(pdk_identity(report,roots['/work/pdk'],lock)==pdk,'STA PDK changed')
                require(inspect_runtime(lock)==runtime,'STA runtime changed')
                receipt.update(inputs_unchanged=True)
            except BaseException as error:
                receipt.update(status='closeout_failed',closeout_error=type(error).__name__+': '+str(error))
                raise
            finally:
                receipt.update(elapsed_seconds=round(time.monotonic()-started,3),log_sha256=sha(out/'native.log'))
                write(out/'report.json',receipt)
    if (out/'native/report.json').is_file():
        receipt['native_report_sha256']=sha(out/'native/report.json');write(out/'report.json',receipt)
    print(out/'report.json',flush=True)
    return receipt['exit_code']


if __name__=='__main__':raise SystemExit(main())
