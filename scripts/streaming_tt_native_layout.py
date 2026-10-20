"""Bounded native antenna and transistor LVS checks on actual checkpoint GDS.

Execution and report interpretation are separate. These measurements never
grant physical acceptance without the remaining source, timing and TT gates.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import time
import uuid

from streaming_tt_intake import dependency_closure,stage_sources
from streaming_tt_physical import ROOT,committed,inspect_runtime
from streaming_tt_signoff import read,regular,require,sha,unchanged,write
from validation_run import fresh_directory


def timing_host():
    spec=importlib.util.spec_from_file_location('_streaming_tt_layout_intake',
        Path(__file__).with_name('run-streaming-tt-sta.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


def actual_inputs(report_path,state_path,export_path):
    host=timing_host();report,roots,odb,database=host.checkpoint(report_path,state_path)
    frozen=host.constraints(report_path,report,roots)
    report_path,state_path,export_path=map(regular,(report_path,state_path,export_path))
    state=host.read_checkpoint(state_path,producer=False)
    native=state.get('gds')
    require(type(native) is str and native.startswith('/work/run/'),'Actual checkpoint GDS absent')
    gds=regular(roots['/work/run']/native.removeprefix('/work/run/'))
    require(gds.is_relative_to(roots['/work/run']) and
        report.get('artifact_sha256',{}).get(str(gds.relative_to(report_path.parent)))==sha(gds),
        'Actual GDS differs from closed producer')
    exported=read(export_path)
    require(exported.get('schema')=='pinwheel.streaming-tt-signoff-export.v1' and
        exported.get('completed') is True and exported.get('exit_code')==0 and
        exported.get('inputs_unchanged') is True and exported.get('inherited_netlist') is False and
        exported.get('actual_database_sha256')==sha(database) and
        exported.get('input_sha256_before',{}).get('/work/run/resolved.json')==sha(roots['/work/run']/'resolved.json'),
        'LVS reference is not exported from the actual checkpoint ODB/configuration')
    top=exported.get('top');require(top in ('tt_um_pinwheel_streaming_ready_d2','tt_um_pinwheel_streaming_ready_d4'),
        'Unexpected actual layout top')
    require(read(roots['/work/run']/'resolved.json')['DESIGN_NAME']==top,'GDS/ODB export top differs')
    cdl=regular(export_path.parent/'implemented.cdl')
    require(exported.get('artifacts_sha256',{}).get('implemented.cdl')==sha(cdl) and cdl.stat().st_size>0,
        'Actual ODB CDL changed or absent')
    frozen.update({str(path):sha(path) for path in (report_path,state_path,export_path,database,gds,cdl)})
    return report,roots,top,gds,cdl,frozen


def cleanup(label,log):
    query=['docker','container','ls','--all','--no-trunc','--filter','label='+label,'--format','{{.ID}}']
    ids=subprocess.check_output(query,text=True,timeout=15).splitlines()
    require(all(len(value)==64 and set(value)<=set('0123456789abcdef') for value in ids),
        'Malformed owned layout container ID')
    for value in ids:
        subprocess.run(['docker','stop','--time','5',value],stdout=log,stderr=subprocess.STDOUT,timeout=20,check=True)
    require(not subprocess.check_output(query,text=True,timeout=15).strip(),'Owned layout container remains')
    return dict(owned_container_absent=True,stopped_owned_ids=ids)


def run_command(command,label,timeout,out,name):
    row=dict(argv=command,status='intent',timeout_seconds=timeout)
    write(out/(name+'-journal.json'),row);start=time.monotonic();process=None
    with (out/(name+'.stdout.log')).open('w') as log:
        try:
            row['status']='running';write(out/(name+'-journal.json'),row)
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            row.update(exit_code=process.wait(timeout=timeout),status='completed')
        except subprocess.TimeoutExpired:
            row.update(exit_code=124,status='timed_out')
        except KeyboardInterrupt:
            row.update(exit_code=130,status='interrupted')
        finally:
            try:
                row.update(cleanup(label,log))
                if process is not None and process.poll() is None:
                    os.killpg(process.pid,signal.SIGTERM);process.wait(timeout=10)
            except BaseException as error:
                row.update(status='cleanup_unconfirmed',cleanup_error=type(error).__name__+': '+str(error))
            row.update(elapsed_seconds=round(time.monotonic()-start,3),log_sha256=sha(out/(name+'.stdout.log')))
            write(out/(name+'-journal.json'),row)
    require(row.get('owned_container_absent') is True,'Layout container cleanup unconfirmed')
    require(row.get('exit_code')==0 and row.get('status')=='completed','Native layout execution failed: '+name)
    return row


def run(report_path,state_path,export_path,tag,timeout):
    require(1<=timeout<=3600,'Native layout timeout outside1..3600s')
    report,roots,top,gds,cdl,frozen=actual_inputs(report_path,state_path,export_path)
    out=fresh_directory(ROOT/'build/streaming-tt-layout',tag).resolve()
    lock=read(ROOT/'tools/physical-toolchain.json');runtime=inspect_runtime(lock)
    host=timing_host();pdk=host.pdk_identity(report,roots['/work/pdk'],lock)
    closure=dependency_closure(ROOT,['scripts/streaming_tt_native_layout.py','scripts/streaming_tt_layout.py',
        'scripts/run-streaming-tt-sta.py','tools/physical-toolchain.json','tools/streaming-tt-signoff.json'])
    stage_sources(ROOT,out/'producer',closure['files'],committed)
    frozen.update({str(out/'producer'/name):sha(out/'producer'/name) for name in closure['files']})
    # This exact unchanged deck inventory was exercised by positive and
    # connected-metal negative native controls. No per-design exclusions.
    categories=[['Ant.a'],['Ant.c'],*[[f'Ant.{rule}_{layer}'] for layer in
        ('Metal1','Metal2','Metal3','Metal4','TopMetal1') for rule in ('b','e')],
        *[[f'Ant.{rule}_{layer}'] for layer in ('Via1','Via2','Via3','TopVia1') for rule in ('d','f')],
        ['Ant.g'],['Ant.h'],['Ant.i']]
    write(out/'antenna-categories.json',categories);frozen[str(out/'antenna-categories.json')]=sha(out/'antenna-categories.json')
    receipt=dict(schema='pinwheel.streaming-tt-native-layout-host.v1',measurements_completed=False,
        passed=False,qualified=False,physical_acceptance_claim=False,top=top,status='intent',
        container_name='pinwheel-layout-'+tag,cpus=1,memory='2g',memory_swap='2g',network='none',
        input_sha256=frozen,producer_closure=closure,runtime=runtime,pdk=pdk,
        physical_source_commit=report['source_commit'],source_commit=subprocess.check_output(
            ['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),commands=[],
        boundary='Native full-deck antenna and transistor LVS measurements on exact GDS and ODB-derived CDL. Source correspondence, extracted timing, DRC, power and official TT acceptance remain separate.')
    write(out/'report.json',receipt)
    def command(arguments):
        owner=str(uuid.uuid4());label='org.pinwheel.streaming_tt_layout_owner='+owner
        argv=['docker','run','--rm','--pull','never','--name','pinwheel-layout-'+tag,
            '--network','none','--cpus','1','--memory','2g','--memory-swap','2g',
            '--read-only','--tmpfs','/tmp:rw,size=268435456','--label',label,
            '--env','PYTHONDONTWRITEBYTECODE=1','--env','PYTHONPATH=/worker/scripts']
        for source,target in [(roots['/work/pdk'],'/pdk'),(out/'producer','/worker'),
                (gds,'/input/actual.gds'),(cdl,'/input/actual.cdl')]:
            argv+=['--mount','type=bind,source='+str(source)+',target='+target+',readonly']
        return argv+['--mount','type=bind,source='+str(out)+',target=/out',
            '--mount','type=bind,source='+str(out/'producer')+',target=/out/producer,readonly',
            '--workdir','/out',runtime['image_id'],*arguments],label
    started=time.monotonic()
    try:
        for kind,deck in [('antenna','drc/rule_decks/antenna.drc'),('lvs','lvs/sg13cmos5l.lvs')]:
            extension='xml' if kind=='antenna' else 'lvsdb'
            argv=['klayout','-b','-zz','-r','/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/'+deck,
                '-rd','input=/input/actual.gds','-rd','topcell='+top,'-rd','run_mode=deep',
                '-rd',f'report=/out/{kind}.{extension}','-rd',f'log=/out/{kind}.native.log']
            if kind=='lvs':argv+=['-rd','schematic=/input/actual.cdl','-rd','target_netlist=/out/lvs.extracted.spice']
            argv,label=command(argv);row=run_command(argv,label,timeout,out,kind)
            receipt['commands'].append(row);write(out/'report.json',receipt)
            argv=['python3','-B','/worker/scripts/streaming_tt_layout.py','--kind',
                'geometry' if kind=='antenna' else 'lvs','--report',f'/out/{kind}.{extension}',
                '--top',top,'--out',f'/out/{kind}-result.json']
            if kind=='antenna':argv+=['--expected-categories','/out/antenna-categories.json']
            argv,label=command(argv);row=run_command(argv,label,120,out,kind+'-interpret')
            receipt['commands'].append(row);parsed=read(out/(kind+'-result.json'))
            require(parsed.get('schema')=='pinwheel.streaming-tt-layout-result.v1' and
                parsed.get('report_sha256')==sha(out/(kind+'.'+extension)) and
                parsed.get('reader_sha256')==sha(out/'producer/scripts/streaming_tt_layout.py') and
                parsed.get('top',parsed.get('result',{}).get('top'))==top,
                'Native layout interpretation does not bind the actual report/reader/top')
            receipt[kind]=parsed['result']
            write(out/'report.json',receipt)
        receipt.update(measurements_completed=True,passed=all(receipt[kind]['passed'] for kind in ('antenna','lvs')),
            status='completed')
    except BaseException as error:
        receipt.update(status='failed',error=type(error).__name__+': '+str(error));raise
    finally:
        try:
            unchanged(frozen);require(host.pdk_identity(report,roots['/work/pdk'],lock)==pdk,'Layout PDK changed')
            require(inspect_runtime(lock)==runtime,'Layout runtime changed');receipt['inputs_unchanged']=True
        except BaseException as error:
            receipt.update(status='closeout_failed',passed=False,closeout_error=type(error).__name__+': '+str(error));raise
        finally:
            receipt.update(elapsed_seconds=round(time.monotonic()-started,3),artifacts_sha256={
                str(path.relative_to(out)):sha(path) for path in sorted(out.rglob('*')) if path.is_file() and path!=out/'report.json'})
            write(out/'report.json',receipt)
    return out/'report.json'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('physical-report','state','odb-export-report'):parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--tag',required=True);parser.add_argument('--timeout',type=int,default=1800)
    args=parser.parse_args();print(run(args.physical_report,args.state,args.odb_export_report,args.tag,args.timeout))


if __name__=='__main__':main()
