"""Run unchanged complete public-wire diagnostics for a fresh 8x4 authority.

Root must separately authorize and launch this leaf under the campaign resource
guard. This new owner consumes final_authority.verify, never historical target
schemas. Fourteen actual native processes and every canonical trace are required.
No timing, electrical, universal M or tapeout acceptance follows.
"""
import argparse
import hashlib
from pathlib import Path
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode=True
import streaming_8x4_final_authority as A

R=A.R
ROOT=Path(__file__).resolve().parents[1]
ENTRIES=('scripts/streaming_8x4_final_wire.py','scripts/run-streaming-tt-wire.py',
    'scripts/check-streaming-tt-wire.py','scripts/check-streaming-uart.py')


def committed_producer():
    # The canonical owners intentionally provide variable-path load APIs, so
    # the physical producer's static AST resolver cannot model this closure.
    # Bind every actual loaded HOST helper plus explicit selected worker entry
    # points, while the authority independently seals the complete Git archive.
    names=set(ENTRIES)
    for module in tuple(sys.modules.values()):
        name=getattr(module,'__file__',None)
        if name:
            path=Path(name).resolve()
            if path.is_relative_to(ROOT/'scripts'):names.add(str(path.relative_to(ROOT)))
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip();sources={}
    for name in sorted(names):
        data=subprocess.check_output(['git','show',commit+':'+name],cwd=ROOT,timeout=30)
        R.need(hashlib.sha256(data).hexdigest()==R.digest(ROOT/name),'Commit fresh final-wire producer first: '+name)
        sources[name]=R.digest(ROOT/name)
    return commit,sources,dict(kind='actual-loaded-HOST-modules-and-explicit-worker-entries',files=sorted(names),
        complete_selected_archive_independently_verified=True)


def worker_result(value,config):
    R.need(value.get('passed') is True and value.get('qualified') is False and
        value.get('physical_acceptance_claim') is False and value.get('source_commit')==config['source_commit'] and
        value.get('producer_commit')==config['producer_commit'] and value.get('physical_ff_bits')==6039 and
        type(value.get('native_processes')) is int and value['native_processes']==14 and
        value.get('inputs_unchanged') is True and value.get('generated_inputs_unchanged') is True and
        value.get('clock_contraction') is False and value.get('stage')=='closed' and
        value.get('physical_stage')==config['physical_stage'],
        'Fresh final public-wire worker contract did not close')


def run(authority_path,output,timeout):
    R.need(type(timeout) is int and 1<=timeout<=7200,'Final-wire leaf needs an explicit bounded allowance up to7200s')
    authority_path=R.regular(authority_path).resolve();authority_sha=R.digest(authority_path);authority=A.verify(authority_path)
    config_path=Path(authority['worker_config']['path']);config=R.read(config_path)
    selected=Path(authority['selected_source']['root']);source_map=authority['selected_source']['sha256']
    wire=R.load('_streaming8_final_wire_owner_api',selected/'scripts/run-streaming-tt-wire.py');wire.check_environment()
    gate=R.load('_streaming8_final_wire_worker_api',selected/'scripts/check-streaming-tt-wire.py');gate.check_environment()
    commit,sources,closure=committed_producer()
    raw=R.load('_streaming8_final_wire_runtime',selected/'scripts/check-streaming-uart.py')
    helpers=raw.helpers();manifest=R.read(selected/'tools/hardware-toolchain.json');tools=config['tools']
    identity=raw.tool_identity(helpers,tools,manifest)
    R.need(identity==config['tool_identity'],'Final-wire actual native runtime differs from authority')
    for item in config['corners'].values():R.need(R.digest(item['path'])==item['sha256'],'Final-wire pinned Liberty changed')
    frozen={str(authority_path):authority_sha,str(config_path):R.digest(config_path),
        **{str(ROOT/name):value for name,value in sources.items()}}
    for key in ('selected_archive','semantic_state_map','sampler_binding','runtime_report','export_report','M_intake'):
        item=authority[key];frozen[item['path']]=item['sha256']
    binding=R.read(config['sampler_binding']['path']);frozen[config['sampler_binding']['path']]=config['sampler_binding']['sha256']
    frozen.update({item['path']:item['sha256'] for item in binding['semantic_basis'].values()})
    frozen.update({item['path']:item['sha256'] for item in config['corners'].values()})
    def unchanged():
        R.need(all(R.digest(path)==pin for path,pin in frozen.items()) and A.verify(authority_path)==authority,
            'Fresh final-wire authority/producer/input changed')
        R.need(wire.membership(selected,authority['selected_source']['tree'],authority['selected_source']['object_format'])==source_map,
            'Selected final-wire archive membership changed')
        R.need(raw.tool_identity(helpers,tools,manifest)==identity,'Final-wire native runtime changed')
        # Dynamic canonical validators must resolve to the exact selected bytes,
        # even when a same-name HOST helper was imported earlier in this process.
        for module in tuple(sys.modules.values()):
            name=getattr(module,'__file__',None)
            if not name:continue
            path=Path(name).resolve()
            if path.is_relative_to(ROOT/'scripts'):
                relative=str(path.relative_to(ROOT))
                R.need(relative in sources or (relative in source_map and R.digest(path)==source_map[relative]),
                    'Unbound HOST final-wire helper: '+relative)
    unchanged()
    output=Path(output).absolute();R.need(not output.exists(),'Preserve earlier final public-wire attempt');output.mkdir(parents=True)
    argv=[tools['python'],'-B',str(selected/'scripts/check-streaming-tt-wire.py'),'--worker-config',str(config_path),
        '--worker-config-sha256',R.digest(config_path),'--out',str(output/'worker')]
    report=dict(schema='pinwheel.streaming-8x4-final-wire-run.v1',passed=False,status='intent',qualified=False,
        physical_acceptance=False,final_correspondence_proved=False,authority=A.bind(authority_path),target=authority['target'],
        physical_candidate=authority['physical_candidate'],
        producer_commit=commit,producer_sha256=sources,producer_dependency_closure=closure,
        selected_worker_commit=config['producer_commit'],worker_config=A.bind(config_path),argv=argv,
        frozen_before_spawn=frozen,tool_identity_before=identity,timeout_seconds=timeout,
        outer_resource_cleanup_required=True,
        boundary='Finite complete D2 public-wire corpus on the exact final ODB Boolean connectivity. No SDF, qualified RC/timing, electrical, universal M or tapeout acceptance.')
    report_path=output/'report.json';wire.write(report_path,report);start=time.monotonic()
    process_group=R.load('_streaming8_final_wire_process_group',selected/'scripts/process_group.py')
    previous=signal.getsignal(signal.SIGTERM)
    def interrupted(signum,frame):raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    try:
        report['status']='running';wire.write(report_path,report)
        native=process_group.run_captured(argv,cwd=selected,timeout=timeout,log_path=output/'worker.stdout.log')
        report['native_exit_code']=native.returncode
        R.need(native.returncode==0,'Fresh final public-wire worker failed; preserve per-protocol receipts')
        result=R.read(output/'worker/report.json');worker_result(result,config)
        R.need(result.get('configuration')==dict(path=str(config_path),sha256=R.digest(config_path)) and
            type(result.get('input_sha256_before')) is dict and bool(result['input_sha256_before']) and
            result['input_sha256_before'].get(str(config_path.resolve()))==R.digest(config_path),
            'Actual final-wire worker did not bind the exact nonempty configuration/input set')
        sys.path.insert(0,str(selected/'scripts'))
        gate.validate_native(result,output/'worker',tools)
        R.need(wire.native_journal(output/'worker/native.jsonl',result['native_runs'])==result.get('native_journal',{}).get('sha256'),
            'Final-wire14process journal differs from worker pin')
        artifacts={str(path.relative_to(output/'worker')):R.digest(path) for path in sorted((output/'worker').rglob('*'))
            if path.is_file() and path!=output/'worker/report.json'}
        R.need(artifacts==result.get('artifact_sha256') and all(R.digest(path)==pin for path,pin in
            result.get('input_sha256_before',{}).items()),'Final-wire worker input/artifact membership changed')
        unchanged()
        report.update(passed=True,status='completed',worker_report=A.bind(output/'worker/report.json'),
            native_journal=A.bind(output/'worker/native.jsonl'),physical_edges=result['physical_edges'],native_processes=14,
            tool_identity_after=identity,sources_unchanged=True,inputs_runtime_unchanged=True)
    except BaseException as error:
        report.update(passed=False,status='failed_or_interrupted',error=type(error).__name__+': '+str(error))
        if isinstance(error,subprocess.TimeoutExpired):report.update(native_exit_code=124,
            process_group_stopped=getattr(error,'process_group_stopped',False))
    finally:
        signal.signal(signal.SIGTERM,previous);report['elapsed_seconds']=round(time.monotonic()-start,3)
        if (output/'worker.stdout.log').is_file():report['worker_stdout_sha256']=R.digest(output/'worker.stdout.log')
        report['retained_protocol_reports']={str(path.relative_to(output)):R.digest(path) for path in
            sorted((output/'worker').rglob('report.json')) if path.is_file()}
        wire.write(report_path,report)
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('authority','output'):parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--timeout',type=int,default=1800);args=parser.parse_args()
    report=run(args.authority,args.output,args.timeout);print(args.output/'report.json');return 0 if report['passed'] else 2


if __name__=='__main__':raise SystemExit(main())
