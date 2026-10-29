"""Fresh read-only fixed-target8x4 ODB geometry/LEF/GDS export.

Consumes one authenticated completed probe checkpoint. It performs no
placement, routing, clock/logic repair or shared-PDK changes. Root must admit
the native run under the campaign's single-heavy-job supervisor.
"""
import argparse
from datetime import datetime,timezone
import fnmatch
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

import streaming_8x4_prepare as P
import streaming_8x4_run as R
from streaming_8x4_geometry import regular,require,sha


def source_target(report_path,prepared):
    report_path=regular(report_path);report=P.read(report_path)
    require(report.get('schema')=='pinwheel.streaming-8x4-native-run.v1' and report.get('mode')=='probe' and
        report.get('status')=='flow_completed' and type(report.get('exit_code')) is int and report['exit_code']==0 and
        report.get('inputs_pdk_runtime_unchanged') is True and report.get('container_termination',{}).get('status')=='absent' and
        report.get('prepared_input_sha256')==sha(prepared/'preparation.json') and Path(report['prepared']).resolve()==prepared.resolve(),
        '8x4 probe parent is not closed on exact prepared inputs')
    rows=[row for row in report.get('states',[]) if row['step_directory'].endswith('-odb-applydeftemplate')]
    require(len(rows)==1,'No unique actual post-template8x4 checkpoint')
    row=rows[0];state=regular(row['state']);view=row.get('views',{}).get('odb')
    require(type(view) is dict and set(view)>={'path','sha256','container'},'Missing actual8x4 ODB binding')
    odb=regular(view['path']);flow=report_path.parent/'flow';resolved=regular(flow/'resolved.json')
    for path,expected in [(state,row['state_sha256']),(odb,view['sha256'])]:
        require(path.resolve().is_relative_to(flow.resolve()) and sha(path)==expected and
            report.get('artifact_sha256',{}).get(str(path.relative_to(report_path.parent)))==expected,
            'Closed8x4 native checkpoint binding differs')
    require(report['artifact_sha256'].get('flow/resolved.json')==sha(resolved),'Closed8x4 resolved config changed')
    native=P.read(state).get('odb')
    require(native==view['container'] and native.startswith('/work/run/') and
        native=='/work/run/'+str(odb.relative_to(flow)),'Actual8x4 state does not select bound ODB')
    relative=str(odb.relative_to(flow))
    require(re.fullmatch(r'[A-Za-z0-9_./-]+',relative) and '..' not in Path(relative).parts,'Unsafe fixed8x4 ODB path')
    return report,flow,odb,resolved


def prepare(report_path,prepared,output):
    from streaming_tt_intake import dependency_closure
    prepared=Path(prepared).resolve(strict=True);packet=P.verify(prepared)
    report,flow,odb,resolved=source_target(report_path,prepared)
    closure=dependency_closure(P.ROOT,['scripts/streaming_8x4_export.py','scripts/streaming_tt_lef_format.py'])
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip();sources={}
    for name in closure['files']:
        data=subprocess.check_output(['git','show',head+':'+name],cwd=P.ROOT,timeout=30)
        require(hashlib.sha256(data).hexdigest()==sha(P.ROOT/name),'Commit fixed8x4 export producer: '+name)
        sources[name]=sha(P.ROOT/name)
    output=Path(output).absolute();require(not output.exists(),'Preserve earlier8x4 fixed-target export')
    inputs=output/'inputs';inputs.mkdir(parents=True)
    for name in sources:
        target=inputs/'producer'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(P.ROOT/name,target)
    request=dict(schema='pinwheel.streaming-8x4-fixed-export-request.v1',source_odb='/work/source/'+str(odb.relative_to(flow)),
        source_odb_sha256=sha(odb),resolved_config='/work/source/resolved.json',resolved_config_sha256=sha(resolved),
        input_sha256=packet['input_sha256'],top='tt_um_pinwheel_streaming_ready_d2',qualified=False,physical_acceptance=False)
    P.write(inputs/'request.json',request)
    preparation=dict(schema='pinwheel.streaming-8x4-fixed-export-preparation.v1',producer_commit=head,producer_sha256=sources,
        producer_dependency_closure=closure,input_sha256=P.inventory(inputs),request_sha256=sha(inputs/'request.json'),
        parent_report=dict(path=str(regular(report_path)),sha256=sha(report_path)),prepared=str(prepared),
        prepared_input_sha256=sha(prepared/'preparation.json'),source_flow=str(flow),source_odb=dict(path=str(odb),sha256=sha(odb)),
        resolved_config=dict(path=str(resolved),sha256=sha(resolved)),pdk_root=packet['pdk_root'],native_executed=False,
        qualified=False,physical_acceptance=False,physical_target_unchanged=True)
    P.write(output/'preparation.json',preparation)
    return preparation


def validate_prepared(output,workspace):
    output=Path(output).absolute();packet=P.read(output/'preparation.json')
    require(packet.get('schema')=='pinwheel.streaming-8x4-fixed-export-preparation.v1' and
        packet.get('physical_target_unchanged') is True and P.inventory(output/'inputs')==packet.get('input_sha256'),
        'Frozen8x4 export input contract differs')
    require(sha(packet['parent_report']['path'])==packet['parent_report']['sha256'],'8x4 probe parent report changed')
    prepared=Path(packet['prepared']);P.ROOT=workspace
    P.verify(prepared);source_target(packet['parent_report']['path'],prepared)
    for name,expected in packet['producer_sha256'].items():
        require(sha(workspace/name)==expected==sha(output/'inputs/producer'/name),'8x4 export producer changed')
    for name in ('source_odb','resolved_config'):
        require(sha(packet[name]['path'])==packet[name]['sha256'],'Fixed8x4 export target changed')
    return packet


def native(request_path):
    import librelane
    request_path=regular(request_path);request=P.read(request_path);out=Path('/work/export')
    require(request.get('schema')=='pinwheel.streaming-8x4-fixed-export-request.v1' and
        sha(request['source_odb'])==request['source_odb_sha256'] and sha(request['resolved_config'])==request['resolved_config_sha256'],
        'Fixed8x4 native target changed')
    for name,expected in request['input_sha256'].items():
        require(sha('/work/inputs/'+name)==expected,'Original prepared8x4 input changed before export')
    events=[];start=time.monotonic()
    def run(argv,name):
        executable=Path(shutil.which(argv[0]) or argv[0]).resolve(strict=True)
        row=dict(name=name,argv=argv,executable=str(executable),executable_sha256=sha(executable))
        with (out/(name+'.log')).open('w') as log:
            result=subprocess.run(argv,stdout=log,stderr=subprocess.STDOUT,timeout=max(1,360-(time.monotonic()-start)))
        row.update(exit_code=result.returncode,executable_sha256_after=sha(executable),log_sha256=sha(out/(name+'.log')))
        events.append(row);P.write(out/'native-journal.json',events)
        require(row['executable_sha256']==row['executable_sha256_after'] and result.returncode==0,'Fixed8x4 export phase failed: '+name)
    launcher=out/'readback-launch.py'
    launcher.write_text('import sys\nsys.path.insert(0,"/work/inputs")\nfrom streaming_8x4_readback import native\nnative('+repr(request['source_odb'])+',"/work/inputs","/work/export/native-geometry.json")\n')
    run(['openroad','-exit','-no_init','-python',str(launcher)],'geometry')
    commands=['read_db {'+request['source_odb']+'}','write_def {/work/export/design.def}',
        'write_abstract_lef {/work/export/design.lef}']
    lines=['set journal [open {/work/export/tcl-status.txt} w]']
    for index,command in enumerate(commands):
        lines += ['set code [catch {'+command+'} result]',f'puts $journal "{index} $code"','flush $journal',
                  'if {$code != 0} {puts stderr $result;close $journal;exit 1}']
    lines += ['close $journal']
    (out/'export.tcl').write_text('\n'.join(lines)+'\n')
    run(['openroad','-exit','-no_init','-threads','4',str(out/'export.tcl')],'views')
    require((out/'tcl-status.txt').read_text().splitlines()==[f'{index} 0' for index in range(len(commands))],
        'Fixed8x4 Tcl export status incomplete')
    config=P.read(request['resolved_config']);scripts=Path(librelane.__file__).resolve().parent/'scripts'
    argv=[sys.executable,str(scripts/'klayout/stream_out.py'),'/work/export/design.def','--output','/work/export/design.gds',
        '--top',request['top'],'--conflict-resolution','RenameCell']
    for key,flag in [('KLAYOUT_PROPERTIES','--lyp'),('KLAYOUT_TECH','--lyt'),('KLAYOUT_DEF_LAYER_MAP','--lym')]:argv += [flag,config[key]]
    tech=[path for pattern,path in config['TECH_LEFS'].items() if fnmatch.fnmatch(config['DEFAULT_CORNER'],pattern)]
    require(len(tech)==1 and not config.get('MACROS'),'Unsupported8x4 export view closure')
    consumed={}
    for path in tech+(config.get('CELL_LEFS') or [])+(config.get('EXTRA_LEFS') or [])+(config.get('PAD_LEFS') or []):
        argv += ['--input-lef',path];consumed[path]=sha(path)
    for path in (config.get('CELL_GDS') or [])+(config.get('EXTRA_GDS') or [])+(config.get('PAD_GDS') or []):
        argv += ['--with-gds-file',path];consumed[path]=sha(path)
    consumed[str(scripts/'klayout/stream_out.py')]=sha(scripts/'klayout/stream_out.py')
    run(argv,'streamout')
    require(all(sha(path)==value for path,value in consumed.items()) and
        sha(request['source_odb'])==request['source_odb_sha256'] and sha(request['resolved_config'])==request['resolved_config_sha256'],
        'Fixed8x4 source/export view inputs changed')
    P.write(out/'native-report.json',dict(schema='pinwheel.streaming-8x4-fixed-export-native.v1',completed=True,
        request_sha256=sha(request_path),source_odb_sha256=request['source_odb_sha256'],source_odb_unchanged=True,
        consumed_sha256=consumed,events=events,elapsed_seconds=time.monotonic()-start,
        generated_files_sha256={name:sha(out/name) for name in ('design.def','design.lef','design.gds','native-geometry.json')},
        qualified=False,physical_acceptance=False,physical_target_unchanged=True))


def run_export(output,name,timeout,workspace):
    from streaming_tt_physical import inspect_runtime
    output=Path(output).absolute();workspace=Path(workspace).resolve(strict=True)
    packet=validate_prepared(output,workspace)
    require(set(path.name for path in output.iterdir())=={'inputs','preparation.json'},'Export output is not fresh')
    require(1<=timeout<=900,'Fixed8x4 export timeout outside1..900seconds')
    runtime=inspect_runtime(P.read(workspace/'tools/physical-toolchain.json'));owner=str(uuid.uuid4())
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name),'Unsafe8x4 export container name')
    command=['docker','run','--rm','--pull','never','--name',name,'--label','org.pinwheel.streaming8_owner='+owner,
        '--network','none','--cpus','4','--memory','6g','--memory-swap','6g','--env','PYTHONDONTWRITEBYTECODE=1',
        '--env','PYTHONPATH=/work/export/inputs/producer/scripts:/work/inputs',
        '--mount',f'type=bind,source={output},target=/work/export',
        '--mount',f'type=bind,source={output/"inputs"},target=/work/export/inputs,readonly',
        '--mount',f'type=bind,source={Path(packet["prepared"])/"inputs"},target=/work/inputs,readonly',
        '--mount',f'type=bind,source={packet["source_flow"]},target=/work/source,readonly',
        '--mount',f'type=bind,source={packet["pdk_root"]},target=/work/pdk,readonly',
        '--workdir','/work/export',runtime['image_id'],'python3','-B',
        '/work/export/inputs/producer/scripts/streaming_8x4_export.py','native','--request','/work/export/inputs/request.json']
    started=time.monotonic();receipt=dict(schema='pinwheel.streaming-8x4-fixed-export-run.v1',status='running',argv=command,
        started_utc=datetime.now(timezone.utc).isoformat(),owner=owner,runtime=runtime,preparation_sha256=sha(output/'preparation.json'),
        timeout_seconds=timeout,qualified=False,physical_acceptance=False)
    R.write(output/'report.json',receipt)
    previous=signal.getsignal(signal.SIGTERM)
    def interrupted(signum,frame):raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    with (output/'container.log').open('w') as log:
        try:
            result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
            receipt.update(exit_code=result.returncode,status='export_completed' if result.returncode==0 else 'failed')
        except subprocess.TimeoutExpired:receipt.update(exit_code=124,status='timed_out')
        except KeyboardInterrupt as error:receipt.update(exit_code=130,status='interrupted',stop_reason=str(error))
        except (OSError,ValueError,subprocess.CalledProcessError) as error:
            receipt.update(exit_code=127,status='blocked',error=type(error).__name__+': '+str(error))
        finally:
            receipt['container_termination']=R.cleanup(owner,log)
            signal.signal(signal.SIGTERM,previous)
            try:
                require(validate_prepared(output,workspace)==packet,'Fixed8x4 export input preparation changed')
                require(inspect_runtime(P.read(workspace/'tools/physical-toolchain.json'))==runtime,'Fixed8x4 runtime changed')
                receipt['inputs_pdk_runtime_unchanged']=True
            except (OSError,ValueError) as error:receipt.update(status='invalidated',closeout_error=str(error))
            if receipt['container_termination']['status']!='absent':receipt['status']='cleanup_unconfirmed'
            receipt['elapsed_seconds']=time.monotonic()-started
            if receipt.get('exit_code')==0 and receipt['status']=='export_completed':
                try:
                    from streaming_tt_lef_format import canonicalize
                    native_report=P.read(output/'native-report.json')
                    require(native_report.get('completed') is True and native_report.get('physical_target_unchanged') is True and
                        native_report.get('request_sha256')==sha(output/'inputs/request.json') and
                        [row.get('name') for row in native_report.get('events',[])]==['geometry','views','streamout'] and
                        all(row.get('exit_code')==0 and row.get('executable_sha256')==row.get('executable_sha256_after') and
                            row.get('log_sha256')==sha(output/(row['name']+'.log')) for row in native_report['events']),
                        'Fixed8x4 native export did not complete')
                    for name,value in native_report['generated_files_sha256'].items():
                        require(name in {'design.def','design.lef','design.gds','native-geometry.json'} and sha(output/name)==value,
                            'Fixed8x4 generated export changed')
                    require(set(native_report['generated_files_sha256'])=={'design.def','design.lef','design.gds','native-geometry.json'},
                        'Fixed8x4 generated export membership differs')
                    formatted,formatting=canonicalize((output/'design.lef').read_text())
                    (output/'official-format.lef').write_text(formatted);P.write(output/'lef-format.json',formatting)
                    receipt['native_report_sha256']=sha(output/'native-report.json')
                except (OSError,ValueError,KeyError) as error:
                    receipt.update(status='invalidated',exit_code=2,closeout_error=type(error).__name__+': '+str(error))
            receipt['artifact_sha256']={str(path.relative_to(output)):sha(path) for path in sorted(output.rglob('*')) if path.is_file() and path!=output/'report.json'}
            R.write(output/'report.json',receipt)
    print(output/'report.json',flush=True)
    return receipt.get('exit_code',127) or (0 if receipt['status']=='export_completed' else 3)


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    pre=sub.add_parser('prepare')
    for name in ('parent-report','prepared','output'):pre.add_argument('--'+name,type=Path,required=True)
    run=sub.add_parser('run')
    run.add_argument('--output',type=Path,required=True);run.add_argument('--name',required=True)
    run.add_argument('--timeout-seconds',type=int,default=600);run.add_argument('--workspace',type=Path,default=P.ROOT)
    nat=sub.add_parser('native');nat.add_argument('--request',type=Path,required=True)
    args=parser.parse_args()
    if args.mode=='prepare':prepare(args.parent_report,args.prepared,args.output);print(args.output/'preparation.json');return 0
    if args.mode=='native':native(args.request);return 0
    return run_export(args.output,args.name,args.timeout_seconds,args.workspace)


if __name__=='__main__':raise SystemExit(main())
