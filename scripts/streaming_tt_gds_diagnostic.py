#!/usr/bin/env python3
"""Export actual ODB signoff/DEF/GDS views without rerouting or qualification.

The original producer's failed checks remain failed. Only the unchanged
KLayout.StreamOut native flow step runs, using a fresh actual ODB-derived DEF.
"""
import argparse
from datetime import datetime,timezone
import fnmatch
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
from types import SimpleNamespace
import uuid

import streaming_tt_export_signoff as E
import streaming_tt_physical as P
from streaming_tt_intake import dependency_closure,stage_sources
from streaming_tt_signoff import decode,read,regular,require,sha,unchanged,write
from validation_run import fresh_directory

STEP='KLayout.StreamOut'
BOUNDARY=('Diagnostic view export from the exact closed producer actual ODB. No routing/check step is '
    'rerun or disabled. Original failed/skipped/missing checks remain mandatory gaps; this export grants '
    'no candidate flow completion, universal digital proof, extracted timing or physical acceptance.')
ENTRIES=('scripts/streaming_tt_gds_diagnostic.py','scripts/streaming_tt_export_signoff.py',
    'tools/physical-toolchain.json','tools/streaming-tt-signoff.json')


def checkpoint_api():
    spec=importlib.util.spec_from_file_location('_streaming_tt_gds_checkpoint',Path(__file__).with_name('run-streaming-tt-sta.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def export_api():
    spec=importlib.util.spec_from_file_location('_streaming_tt_gds_export',Path(__file__).with_name('run-streaming-tt-signoff-export.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def terminal(report):
    status,code=report.get('status'),report.get('exit_code')
    require(type(code) is int and ((status=='flow_completed' and code==0) or
        (status in ('failed','timed_out') and code!=0)) and
        report.get('inputs_unchanged_after_run') is True and
        report.get('container_termination',{}).get('status')=='absent',
        'Diagnostic view export requires a terminal closed physical producer')


def latest_state(report,state,root):
    """Native ordinal paths retain nested subflow order; mtime is not evidence."""
    root=Path(root).resolve();state=regular(state).resolve();ordered=[]
    for row in report.get('states',[]):
        path=regular(row['state']).resolve()
        require(path.is_relative_to(root) and path.name=='state_out.json' and
            row.get('state_sha256')==sha(path),'Changed/escaping recorded native state')
        parts=path.relative_to(root).parts[:-1]
        ordinal=tuple(int(match[1]) for part in parts if (match:=re.fullmatch(r'(\d+)-.+',part)))
        require(ordinal,'No actual native step ordinal for checkpoint')
        ordered.append((ordinal,path))
    require(ordered and len({ordinal for ordinal,path in ordered})==len(ordered) and
        max(ordered)[1]==state,'Export requires the exact latest successful recorded native state')


def intake(report_path,state_path):
    host=checkpoint_api();report,roots,odb,database=host.checkpoint(report_path,state_path)
    terminal(report);latest_state(report,state_path,roots['/work/run'])
    report_path,state_path=map(lambda path:regular(path).resolve(),(report_path,state_path))
    for path in (state_path,database):
        require(report.get('artifact_sha256',{}).get(str(path.relative_to(report_path.parent)))==sha(path),
            'Actual checkpoint differs from the closed producer artifact inventory')
    frozen=host.constraints(report_path,report,roots)
    metadata_path=report_path.parent/'inputs.json' if report['schema']=='pinwheel.streaming-tt-final-run.v1' else Path(report['design'])/'inputs.json'
    metadata=read(metadata_path)
    for name,value in metadata['input_sha256'].items():
        relative=P.relative_path(name);path=regular(roots['/work/inputs']/relative).resolve()
        require(path.is_relative_to(roots['/work/inputs']) and sha(path)==value,'Closed physical input changed: '+name)
        frozen[str(path)]=value
    frozen.update({str(path):sha(path) for path in (report_path,state_path,database)})
    return report,roots,odb,database,frozen


def flow_arguments(tag):
    return ['--manual-pdk','--pdk-root','/work/pdk','--pdk','ihp-sg13cmos5l','--jobs','1',
        '--run-tag',tag,'--force-run-dir','/probe/streamout','--with-initial-state','/probe/fresh-seed.json',
        '--from',STEP,'--to',STEP,'/work/run/resolved.json']


def prepare_flow_directory(out):
    directory=Path(out)/'streamout';directory.mkdir(exist_ok=False);return directory


def append_event(path,event):
    with Path(path).open('a') as stream:
        stream.write(json.dumps(event,sort_keys=True,allow_nan=False)+'\n');stream.flush();os.fsync(stream.fileno())


def observe_command(argv,name,journal,log,call):
    argv=[str(value) for value in argv];declared=Path(argv[0])
    if not declared.is_absolute():declared=Path(shutil.which(argv[0]) or '')
    executable=regular(declared.resolve());require(declared.is_absolute(),'Missing native executable')
    row=dict(name=name,argv=[str(declared),*argv[1:]],resolved_executable=str(executable),
        executable_sha256_before=sha(executable))
    paths=[Path(value) for value in row['argv'] if Path(value).is_absolute() and Path(value).is_file()]
    row['argv_file_sha256_before']={str(path):sha(path.resolve()) for path in paths}
    append_event(journal,dict(event='intent',**row));start=time.monotonic()
    try:
        result=call(row['argv']);code=result.returncode if hasattr(result,'returncode') else result['returncode']
        row['exit_code']=code
        return result
    except BaseException as error:
        row.update(exit_code=getattr(error,'returncode',-1),error=type(error).__name__+': '+str(error));raise
    finally:
        if hasattr(log,'flush'):log.flush()
        logfile=Path(log.name if hasattr(log,'name') else log)
        row.update(executable_sha256_after=sha(executable),elapsed_seconds=round(time.monotonic()-start,3),
            log_sha256=sha(logfile) if logfile.is_file() else None,
            argv_file_sha256_after={str(path):sha(path.resolve()) for path in paths})
        append_event(journal,dict(event='result',**row))
        require(declared.resolve()==executable and row['executable_sha256_before']==row['executable_sha256_after'],
            'Native executable or declared alias changed')
        require(row['argv_file_sha256_before']==row['argv_file_sha256_after'],'Native argv input changed during execution')


def def_commands(database,top):
    return ['read_db '+E.literal(database),
        'if {[[ord::get_db_block] getName] ne '+E.literal(top)+'} {error "Actual ODB top differs"}',
        'write_def {/probe/def/implemented.def}']


def def_script(commands):
    lines=['set _pw_journal [open {/probe/def/tcl-status.txt} w]']
    for index,command in enumerate(commands):
        lines+=['set _pw_status [catch {'+command+'} _pw_result]',
            'puts $_pw_journal "'+str(index)+' $_pw_status"','flush $_pw_journal',
            'if {$_pw_status ne "0"} {puts stderr $_pw_result; close $_pw_journal; exit 1}']
    return '\n'.join(lines+['close $_pw_journal'])+'\n'


def validate_tcl(path,commands):
    rows=regular(path).read_text().splitlines()
    require(rows==[str(index)+' 0' for index in range(len(commands))],
        'Missing or failed exact external native DEF Tcl catch status')
    return [dict(command=command,tcl_catch_status='0') for command in commands]


def signoff_subprocess_proxy(run):
    return SimpleNamespace(run=run,STDOUT=subprocess.STDOUT)


def streamout_state(out):
    out=Path(out).resolve();states=list((out/'streamout').rglob('state_out.json'))
    require(len(states)==1 and re.fullmatch(r'\d+-klayout-streamout',states[0].parent.name),
        'Diagnostic flow executed missing/extra native step states')
    state=read(states[0]);active={key:value for key,value in state.items() if key!='metrics' and value is not None}
    require(set(active)=={'def','gds','klayout_gds'} and state.get('metrics')=={} and
        active['def']=='/probe/def/implemented.def','Diagnostic streamout inherited stale views/metrics')
    files={}
    for key in ('gds','klayout_gds'):
        native=active[key];require(type(native) is str and native.startswith('/probe/streamout/'),'Escaping actual streamed GDS')
        file=regular(out/native.removeprefix('/probe/')).resolve()
        require(file.is_relative_to((out/'streamout').resolve()) and file.stat().st_size>0,'Empty/escaping streamed GDS')
        files[key]=dict(native=native,relative=str(file.relative_to(out)),sha256=sha(file))
    require(files['gds']['sha256']==files['klayout_gds']['sha256'],'Primary and KLayout actual GDS differ')
    return dict(state_relative=str(states[0].relative_to(out)),state_sha256=sha(states[0]),views=files)


def native(request_path):
    request=read(regular(request_path));require(request.get('schema')=='pinwheel.streaming-tt-gds-view-request.v1' and
        request.get('flow_arguments')==flow_arguments(request['tag']),'Unapproved diagnostic streamout CLI')
    out=Path('/probe');database=regular(request['database']);config=regular('/work/run/resolved.json')
    require(sha(database)==request['actual_database_sha256'] and sha(config)==request['resolved_config_sha256'],
        'Native actual ODB/resolved configuration differs')
    top=read(config)['DESIGN_NAME'];require(read(config)['PRIMARY_GDSII_STREAMOUT_TOOL']=='klayout','Primary native GDS tool differs')
    journal=out/'native-journal.jsonl';report=dict(schema='pinwheel.streaming-tt-gds-view-native.v1',qualified=False,
        physical_acceptance_claim=False,view_export_completed=False,candidate_flow_completed=False,status='intent',
        request_sha256=sha(request_path),actual_database_sha256=sha(database),resolved_config_sha256=sha(config),
        flow_arguments=flow_arguments(request['tag']),boundary=BOUNDARY)
    write(out/'native-report.json',report)
    try:
        # The unchanged four-view exporter gets an observer-only subprocess
        # proxy. Its native Tcl, inputs and receipt format remain unchanged.
        original=E.subprocess
        def export_run(argv,**kwargs):
            return observe_command(argv,'signoff-export',journal,kwargs['stdout'],
                lambda actual:subprocess.run(actual,**kwargs))
        E.subprocess=signoff_subprocess_proxy(export_run)
        try:exported=E.export(database,config,out/'native',timeout=request['timeout_seconds'])
        finally:E.subprocess=original
        require(exported['completed'] is True,'Actual ODB signoff views absent')
        (out/'def').mkdir();commands=def_commands(database,top);script=out/'def/export.tcl';script.write_text(def_script(commands))
        before={str(path):sha(path) for path in (database,config,script,regular(__file__))}
        with (out/'def/native.log').open('w') as log:
            result=observe_command(['openroad','-exit','-no_init',str(script)],'def-export',journal,log,
                lambda argv:subprocess.run(argv,stdout=log,stderr=subprocess.STDOUT,timeout=request['timeout_seconds']))
        require(result.returncode==0,'Native actual ODB DEF export failed')
        statuses=validate_tcl(out/'def/tcl-status.txt',commands);definition=regular(out/'def/implemented.def')
        require(definition.stat().st_size>0,'Empty actual ODB DEF');unchanged(before)
        seed={'def':'/probe/def/implemented.def','metrics':{}};write(out/'fresh-seed.json',seed)
        from librelane.steps import Step
        import librelane.__main__ as cli
        original_step=Step.run_subprocess
        def observe_step(step,argv,*args,**kwargs):
            require(step.id==STEP,'Diagnostic flow attempted an unauthorized native step')
            logfile=kwargs.get('log_to') or (args[0] if args else None) or step.get_log_path()
            return observe_command(argv,'klayout-streamout',journal,logfile,
                lambda actual:original_step(step,actual,*args,**kwargs))
        Step.run_subprocess=observe_step
        cli_file=regular(cli.__file__);cli_hash=sha(cli_file)
        prepare_flow_directory(out)
        try:cli.cli.main(args=flow_arguments(request['tag']),prog_name='python3 -m librelane',standalone_mode=False)
        finally:Step.run_subprocess=original_step
        require(sha(cli_file)==cli_hash,'Native full-flow CLI source changed')
        views=streamout_state(out);unchanged(before)
        require(sha(out/'streamout/resolved.json')==sha(config) or read(out/'streamout/resolved.json')==read(config),
            'Streamout re-resolved configuration differs from the closed actual recipe')
        report.update(status='views_exported',view_export_completed=True,exit_code=0,top=top,
            inherited_views=False,inputs_unchanged=True,signoff_export_report_sha256=sha(out/'native/report.json'),
            fresh_def_sha256=sha(definition),def_tcl_commands=statuses,def_script_sha256=sha(script),
            fresh_seed_sha256=sha(out/'fresh-seed.json'),streamout=views,
            cli_entrypoint=dict(path=str(cli_file),sha256=cli_hash),
            native_journal_sha256=sha(journal))
        return 0
    except BaseException as error:
        report.update(status='failed',exit_code=1,error=type(error).__name__+': '+str(error));raise
    finally:write(out/'native-report.json',report)


def validate_streamout_argv(argv,config,*,output=None):
    require(type(argv) is list and len(argv)>4 and Path(argv[0]).is_absolute() and
        argv[1].endswith('/klayout/stream_out.py') and argv[2]=='/probe/def/implemented.def',
        'Changed native KLayout executable/script/fresh DEF')
    for key,flag in [('KLAYOUT_DEF_LAYER_MAP','--lym'),('KLAYOUT_TECH','--lyt'),('KLAYOUT_PROPERTIES','--lyp'),('DESIGN_NAME','--top')]:
        require(argv.count(flag)==1 and argv.index(flag)+1<len(argv) and argv[argv.index(flag)+1]==config[key],
            'Native KLayout argument differs from exact closed configuration: '+flag)
    if output is not None:
        require(argv.count('--output')==1 and argv[argv.index('--output')+1]==output,
            'Native KLayout output differs from the actual recorded GDS')
    require(not config.get('MACROS'),'Unsupported macro view closure in diagnostic streamout')
    def selected(flag):return [argv[index+1] for index,value in enumerate(argv[:-1]) if value==flag]
    tech=[value for pattern,value in config['TECH_LEFS'].items() if fnmatch.fnmatch(config['DEFAULT_CORNER'],pattern)]
    require(len(tech)==1 and selected('--input-lef')==tech+(config.get('CELL_LEFS') or [])+
        (config.get('EXTRA_LEFS') or [])+(config.get('PAD_LEFS') or []),'Native KLayout LEFs differ from closed recipe')
    require(selected('--with-gds-file')==(config.get('CELL_GDS') or [])+(config.get('EXTRA_GDS') or [])+
        (config.get('PAD_GDS') or []),'Native KLayout master GDS differs from closed recipe')


def validate_native(out,request,*,config_path):
    out=Path(out);packet=read(regular(out/'native-report.json'))
    config=read(regular(config_path));require(sha(config_path)==request['resolved_config_sha256'],
        'Closed streamout configuration changed')
    require(packet.get('schema')=='pinwheel.streaming-tt-gds-view-native.v1' and packet.get('view_export_completed') is True and
        packet.get('status')=='views_exported' and type(packet.get('exit_code')) is int and packet['exit_code']==0 and
        packet.get('candidate_flow_completed') is False and packet.get('qualified') is False and
        packet.get('physical_acceptance_claim') is False and packet.get('inputs_unchanged') is True and
        packet.get('inherited_views') is False and packet.get('request_sha256')==sha(out/'request.json') and
        packet.get('actual_database_sha256')==request['actual_database_sha256'] and
        packet.get('resolved_config_sha256')==request['resolved_config_sha256'] and
        packet.get('flow_arguments')==flow_arguments(request['tag']) and packet.get('top')==config['DESIGN_NAME'],
        'Native diagnostic GDS views are not closed')
    commands=def_commands(request['database'],packet['top'])
    require(packet.get('def_tcl_commands')==validate_tcl(out/'def/tcl-status.txt',commands) and
        packet.get('def_script_sha256')==sha(out/'def/export.tcl') and
        (out/'def/export.tcl').read_text()==def_script(commands) and
        packet.get('fresh_def_sha256')==sha(out/'def/implemented.def') and
        packet.get('fresh_seed_sha256')==sha(out/'fresh-seed.json') and
        read(out/'fresh-seed.json')=={'def':'/probe/def/implemented.def','metrics':{}},'Fresh actual ODB DEF/seed changed')
    views=streamout_state(out);require(packet.get('streamout')==views,'Actual streamed GDS/state changed')
    journal=regular(out/'native-journal.jsonl');events=[read_line(line) for line in journal.read_text().splitlines()]
    require(len(events)==6 and packet.get('native_journal_sha256')==sha(journal),'Incomplete native view-export journal')
    for index,name in enumerate(('signoff-export','def-export','klayout-streamout')):
        intent,result=events[2*index:2*index+2]
        hashes=intent.get('argv_file_sha256_before')
        require(type(hashes) is dict and hashes and all(type(key) is str and Path(key).is_absolute() and
            type(value) is str and re.fullmatch('[0-9a-f]{64}',value) for key,value in hashes.items()) and
            type(intent.get('executable_sha256_before')) is str and
            re.fullmatch('[0-9a-f]{64}',intent['executable_sha256_before']),
            'Missing actual native executable/script/input hashes')
        require(intent.get('event')=='intent' and result.get('event')=='result' and intent.get('name')==result.get('name')==name and
            intent.get('argv')==result.get('argv') and type(result.get('exit_code')) is int and result['exit_code']==0 and
            intent.get('resolved_executable')==result.get('resolved_executable') and
            intent.get('executable_sha256_before')==result.get('executable_sha256_before')==result.get('executable_sha256_after') and
            intent.get('argv_file_sha256_before')==result.get('argv_file_sha256_before')==result.get('argv_file_sha256_after'),
            'Native actual argv/executable/result differs')
        argv=result['argv'];require(argv and Path(argv[0]).is_absolute(),'Nonabsolute actual native executable')
        if index<2:
            expected=['-exit','-no_init','/probe/'+('native' if index==0 else 'def')+'/export.tcl']
            require(Path(argv[0]).name=='openroad' and argv[1:]==expected,'Changed native actual ODB export argv')
            require(result.get('log_sha256')==sha(out/('native' if index==0 else 'def')/'native.log'),'Native ODB export log changed')
        else:
            validate_streamout_argv(argv,config,output=views['views']['klayout_gds']['native'])
            require(argv[1] in hashes and hashes.get('/probe/def/implemented.def')==sha(out/'def/implemented.def'),
                'Native executed KLayout script or exact fresh DEF hash absent')
            logs=list((out/Path(views['state_relative']).parent).glob('*.log'))
            require(any(sha(path)==result.get('log_sha256') for path in logs),'Native actual KLayout log changed')
    require(packet.get('signoff_export_report_sha256')==sha(out/'native/report.json'),'Fresh actual ODB signoff receipt changed')
    return views


def read_line(line):
    return decode(line)


def run(report_path,state_path,tag,timeout):
    require(1<=timeout<=1800,'Diagnostic view timeout outside1..1800s');api=export_api();api.check_environment()
    report,roots,odb,database,frozen=intake(report_path,state_path)
    lock=read(P.ROOT/'tools/physical-toolchain.json');runtime=P.inspect_runtime(lock)
    pdk=checkpoint_api().pdk_identity(report,roots['/work/pdk'],lock)
    closure=dependency_closure(P.ROOT,ENTRIES);producer=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip()
    out=fresh_directory(P.ROOT/'build/streaming-tt-gds-exports',tag).resolve()
    stage_sources(P.ROOT,out/'producer',closure['files'],P.committed)
    require(subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip()==producer,'GDS producer changed during snapshot')
    for name in closure['files']:
        for path in (P.ROOT/name,out/'producer'/name):frozen[str(path.resolve())]=sha(path)
    request=dict(schema='pinwheel.streaming-tt-gds-view-request.v1',tag=tag,database=odb,actual_database_sha256=sha(database),
        resolved_config_sha256=sha(roots['/work/run']/'resolved.json'),timeout_seconds=timeout,flow_arguments=flow_arguments(tag))
    write(out/'request.json',request);frozen[str(out/'request.json')]=sha(out/'request.json')
    owner=str(uuid.uuid4());label='org.pinwheel.streaming_tt_gds_owner='+owner
    argv=['docker','run','--rm','--pull','never','--name','pinwheel-gds-'+tag,'--label',label,
        '--network','none','--cpus','1','--memory','1024m','--memory-swap','1024m','--read-only','--cap-drop','ALL',
        '--security-opt','no-new-privileges','--tmpfs','/tmp:rw,size=268435456',
        '--env','PYTHONDONTWRITEBYTECODE=1','--env','PYTHONPATH=/work/inputs:/worker/scripts']
    for native_root,host in roots.items():argv+=['--mount','type=bind,source='+str(host)+',target='+native_root+',readonly']
    argv+=['--mount','type=bind,source='+str(out/'producer')+',target=/worker,readonly',
        '--mount','type=bind,source='+str(out)+',target=/probe',
        '--mount','type=bind,source='+str(out/'producer')+',target=/probe/producer,readonly',
        '--mount','type=bind,source='+str(out/'request.json')+',target=/probe/request.json,readonly',
        '--workdir','/probe',runtime['image_id'],'python3','-B','/worker/scripts/streaming_tt_gds_diagnostic.py',
        '--native-request','/probe/request.json']
    receipt=dict(schema='pinwheel.streaming-tt-gds-view-host.v1',status='intent',view_export_completed=False,
        candidate_flow_completed=False,qualified=False,physical_acceptance_claim=False,producer_commit=producer,
        physical_source_commit=report['source_commit'],physical_producer_commit=report.get('producer_commit'),
        physical_report=str(regular(report_path).resolve()),physical_state=str(regular(state_path).resolve()),
        original_physical_status=report['status'],original_physical_exit_code=report['exit_code'],
        actual_database=odb,actual_database_sha256=sha(database),resolved_config_sha256=request['resolved_config_sha256'],
        producer_closure=closure,input_sha256_before=frozen,runtime=runtime,pdk=pdk,argv=argv,cpus=1,memory='1024m',memory_swap='1024m',
        network='none',read_only_rootfs=True,ownership_label=owner,started_utc=datetime.now(timezone.utc).isoformat(),boundary=BOUNDARY)
    write(out/'report.json',receipt);start=time.monotonic();process=None
    with (out/'container.log').open('w') as log:
        try:
            receipt['status']='running';write(out/'report.json',receipt)
            process=subprocess.Popen(argv,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            code=process.wait(timeout=timeout);receipt['exit_code']=code;require(code==0,'Native diagnostic GDS export failed')
            views=validate_native(out,request,config_path=roots['/work/run']/'resolved.json')
            receipt['signoff_views']=api.validate_native(out/'native',database=(odb,database),config=roots['/work/run']/'resolved.json')
            receipt.update(status='views_exported',view_export_completed=True,streamout=views,native_report_sha256=sha(out/'native-report.json'))
        except subprocess.TimeoutExpired:receipt.update(exit_code=124,status='timed_out')
        except KeyboardInterrupt:receipt.update(exit_code=130,status='interrupted')
        except BaseException as error:receipt.update(status='failed',error=type(error).__name__+': '+str(error));raise
        finally:
            try:
                receipt['container_termination']=api.owned_cleanup(label,log)
                if process is not None and process.poll() is None:os.killpg(process.pid,signal.SIGTERM);process.wait(timeout=10)
                unchanged(frozen);require(checkpoint_api().pdk_identity(report,roots['/work/pdk'],lock)==pdk,'Diagnostic GDS PDK changed')
                require(P.inspect_runtime(lock)==runtime,'Diagnostic GDS runtime changed')
                receipt.update(inputs_unchanged=True,input_sha256_after=frozen,runtime_unchanged=True,pdk_unchanged=True)
            except BaseException as error:
                receipt.update(view_export_completed=False,status='closeout_failed',closeout_error=type(error).__name__+': '+str(error));raise
            finally:
                receipt.update(elapsed_seconds=round(time.monotonic()-start,3),container_log_sha256=sha(out/'container.log'),
                    artifact_sha256={str(path.relative_to(out)):sha(path) for path in sorted(out.rglob('*'))
                        if path.is_file() and not path.is_relative_to(out/'producer') and path!=out/'report.json'})
                write(out/'report.json',receipt)
    print(out/'report.json',flush=True);return receipt['exit_code']


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--native-request',type=Path)
    for name in ('physical-report','state'):parser.add_argument('--'+name,type=Path)
    parser.add_argument('--tag');parser.add_argument('--timeout',type=int,default=900);args=parser.parse_args()
    if args.native_request is not None:return native(args.native_request)
    if args.physical_report is None or args.state is None or args.tag is None:parser.error('Exact closed physical report/state and fresh tag required')
    return run(args.physical_report,args.state,args.tag,args.timeout)


if __name__=='__main__':raise SystemExit(main())
