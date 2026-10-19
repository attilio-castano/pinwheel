#!/usr/bin/env python3
"""Export native signoff views from a closed physical checkpoint's actual ODB.

This produces fresh Verilog, power Verilog, CDL and abstract LEF. It does not
claim correspondence, timing, layout legality or physical acceptance.
"""
import argparse
import importlib.util
import os
from pathlib import Path
import re
import signal
import subprocess
import time
import uuid

from streaming_tt_intake import dependency_closure,stage_sources
from streaming_tt_physical import ROOT,committed,inspect_runtime
from streaming_tt_signoff import read,regular,require,sha,unchanged,write
from validation_run import fresh_directory

spec=importlib.util.spec_from_file_location('streaming_tt_export_checkpoint',Path(__file__).with_name('run-streaming-tt-sta.py'))
checkpoint_host=importlib.util.module_from_spec(spec);spec.loader.exec_module(checkpoint_host)
OUTPUTS=('implemented.v','implemented.power.v','implemented.cdl','implemented.lef')
PRODUCER_ENTRIES=('scripts/run-streaming-tt-signoff-export.py','scripts/streaming_tt_export_signoff.py',
    'tools/physical-toolchain.json','tools/streaming-tt-signoff.json')


def check_environment(environment=None):
    environment=os.environ if environment is None else environment
    fixed={'PYTHONPATH','PYTHONHOME','PYTHONSTARTUP','PYTHONPYCACHEPREFIX','LD_PRELOAD','LD_LIBRARY_PATH'}
    prefixes=('DYLD_','OPENROAD_','OPENSTA_')
    bad=sorted(name for name,value in environment.items() if value and (name in fixed or name.startswith(prefixes)))
    require(not bad,'Refuse inherited export loader/compiler overrides: '+', '.join(bad))


def validate_native(out,*,database,config):
    """A successful Docker exit alone cannot prove the requested views exist."""
    out=Path(out);path=regular(out/'report.json');packet=read(path)
    require(packet.get('schema')=='pinwheel.streaming-tt-signoff-export.v1' and
        packet.get('completed') is True and packet.get('status')=='completed' and packet.get('exit_code')==0 and
        packet.get('inputs_unchanged') is True and packet.get('inherited_netlist') is False and
        packet.get('qualified') is False and packet.get('physical_acceptance_claim') is False,
        'Native signoff export has not closed successfully')
    native_odb,host_odb=database;host_config=regular(config)
    require(packet.get('actual_database')==native_odb and packet.get('actual_database_sha256')==sha(host_odb) and
        packet.get('input_sha256_before',{}).get(native_odb)==sha(host_odb) and
        packet.get('input_sha256_before',{}).get('/work/run/resolved.json')==sha(host_config),
        'Native signoff views do not bind the exact checkpoint ODB/configuration')
    resolved=read(host_config)
    require(packet.get('top')==resolved['DESIGN_NAME'],'Native export top differs from the closed configuration')
    argv=packet.get('argv')
    require(type(argv) is list and len(argv)==4 and type(argv[0]) is str and
        Path(argv[0]).is_absolute() and Path(argv[0]).name=='openroad' and
        argv[1:]==['-exit','-no_init','/probe/native/export.tcl'] and
        packet.get('input_sha256_before',{}).get('/probe/native/export.tcl')==sha(out/'export.tcl') and
        packet.get('native_log_sha256')==sha(out/'native.log'),
        'Missing or changed exact native export argv/script/log')
    artifacts=packet.get('artifacts_sha256')
    require(type(artifacts) is dict and set(artifacts)==set(OUTPUTS),'Incomplete or extra native export view inventory')
    for name,digest in artifacts.items():
        item=regular(out/name)
        require(item.stat().st_size>0 and re.fullmatch('[0-9a-f]{64}',digest) and sha(item)==digest,
            'Missing/empty/changed actual ODB export view: '+name)
    return dict(report_sha256=sha(path),artifacts_sha256=artifacts,top=packet['top'],
        actual_database_sha256=packet['actual_database_sha256'],native_argv=argv)


def owned_cleanup(label,log):
    query=['docker','container','ls','--all','--no-trunc','--filter','label='+label,'--format','{{.ID}}']
    ids=subprocess.check_output(query,text=True,timeout=15).splitlines()
    require(all(re.fullmatch('[0-9a-f]{64}',value) for value in ids),'Invalid owned export container ID')
    for value in ids:
        subprocess.run(['docker','stop','--time','5',value],stdout=log,stderr=subprocess.STDOUT,timeout=20,check=True)
    require(not subprocess.check_output(query,text=True,timeout=15).strip(),'Owned export container remains')
    return dict(status='absent',terminated_ids=ids)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--physical-report',required=True,type=Path)
    parser.add_argument('--state',required=True,type=Path)
    parser.add_argument('--tag',required=True)
    parser.add_argument('--timeout',type=int,default=900)
    args=parser.parse_args();require(1<=args.timeout<=1800,'Export timeout outside 1..1800 seconds')
    check_environment()
    report,roots,odb,host=checkpoint_host.checkpoint(args.physical_report,args.state)
    contract=checkpoint_host.constraints(args.physical_report,report,roots)
    lock=read(ROOT/'tools/physical-toolchain.json');runtime=inspect_runtime(lock)
    pdk=checkpoint_host.pdk_identity(report,roots['/work/pdk'],lock)
    closure=dependency_closure(ROOT,PRODUCER_ENTRIES)
    producer=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip()
    out=fresh_directory(ROOT/'build/streaming-tt-signoff-exports',args.tag).resolve()
    stage_sources(ROOT,out/'producer',closure['files'],committed)
    require(subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip()==producer,
        'Producer commit changed during export snapshot')
    frozen={str(regular(path)):sha(path) for path in (args.physical_report,args.state,host)}
    frozen.update(contract)
    for name in closure['files']:
        for path in (ROOT/name,out/'producer'/name):frozen[str(path.resolve())]=sha(path)
    owner=str(uuid.uuid4());label='org.pinwheel.streaming_tt_export_owner='+owner
    command=['docker','run','--rm','--pull','never','--name','pinwheel-export-'+args.tag,
        '--label',label,'--network','none','--cpus','1','--memory','2g','--memory-swap','2g','--read-only',
        '--tmpfs','/tmp:rw,size=268435456','--env','PYTHONDONTWRITEBYTECODE=1',
        '--env','PYTHONPATH=/worker/scripts']
    for native,host_root in roots.items():
        command+=['--mount','type=bind,source='+str(host_root)+',target='+native+',readonly']
    command+=['--mount','type=bind,source='+str(out/'producer')+',target=/worker,readonly',
        '--mount','type=bind,source='+str(out)+',target=/probe',
        '--mount','type=bind,source='+str(out/'producer')+',target=/probe/producer,readonly',
        '--workdir','/probe',runtime['image_id'],
        'python3','-B','/worker/scripts/streaming_tt_export_signoff.py',
        '--database',odb,'--config','/work/run/resolved.json','--out','/probe/native']
    receipt=dict(schema='pinwheel.streaming-tt-signoff-export-host.v1',completed=False,qualified=False,
        physical_acceptance_claim=False,producer_commit=producer,physical_source_commit=report['source_commit'],
        physical_producer_commit=report.get('producer_commit'),status='intent',argv=command,input_sha256=frozen,
        producer_closure=closure,runtime=runtime,pdk=pdk,closed_constraint_sha256=contract,
        cpus=1,memory='2g',memory_swap='2g',network='none',read_only_rootfs=True,ownership_label=owner,
        actual_database=odb,actual_database_sha256=sha(host),
        boundary='Fresh actual ODB-derived views. Functional correspondence, extracted timing, physical power, DRC/LVS/antenna and official precheck remain separate mandatory gates.')
    write(out/'report.json',receipt);started=time.monotonic();process=None
    with (out/'native.log').open('w') as log:
        try:
            receipt['status']='running';write(out/'report.json',receipt)
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            code=process.wait(timeout=args.timeout);receipt['exit_code']=code
            require(code==0,'Native ODB signoff export command failed')
            receipt['native_export']=validate_native(out/'native',database=(odb,host),config=roots['/work/run']/'resolved.json')
            receipt.update(status='completed',completed=True)
        except subprocess.TimeoutExpired:
            receipt.update(exit_code=124,status='timed_out')
        except KeyboardInterrupt:
            receipt.update(exit_code=130,status='interrupted')
        except BaseException as error:
            receipt.update(status='failed',error=type(error).__name__+': '+str(error));raise
        finally:
            try:
                receipt['container_termination']=owned_cleanup(label,log)
                if process is not None and process.poll() is None:
                    os.killpg(process.pid,signal.SIGTERM);process.wait(timeout=10)
                unchanged(frozen)
                require(checkpoint_host.pdk_identity(report,roots['/work/pdk'],lock)==pdk,'Export PDK changed')
                require(inspect_runtime(lock)==runtime,'Export runtime changed')
                receipt.update(inputs_unchanged=True)
            except BaseException as error:
                receipt.update(completed=False,status='closeout_failed',closeout_error=type(error).__name__+': '+str(error));raise
            finally:
                receipt.update(elapsed_seconds=round(time.monotonic()-started,3),log_sha256=sha(out/'native.log'))
                write(out/'report.json',receipt)
    print(out/'report.json',flush=True)
    return receipt['exit_code']


if __name__=='__main__':raise SystemExit(main())
