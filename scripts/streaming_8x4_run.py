"""Owned bounded native8x4 producer; completion never implies qualification.

Root must launch through the campaign's single-heavy-job supervisor. This
worker seals and reexecutes its producer, mounts design/PDK read only, binds
the ordinary flow order, preserves every failed attempt and cleans its owner.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import uuid

import streaming_8x4_prepare as prep
from streaming_8x4_geometry import regular, require, sha

TAIL = tuple('''OpenROAD.DetailedRouting
Odb.RemoveRoutingObstructions
OpenROAD.CheckAntennas-1
Checker.TrDRC
Odb.ReportDisconnectedPins
Checker.DisconnectedPins
Odb.ReportWireLength
Checker.WireLength
OpenROAD.FillInsertion
Odb.CellFrequencyTables
OpenROAD.RCX
OpenROAD.STAPostPNR
OpenROAD.IRDropReport
Magic.StreamOut
KLayout.StreamOut
KLayout.Render
Magic.WriteLEF
Odb.CheckDesignAntennaProperties
KLayout.XOR
Checker.XOR
Magic.DRC
KLayout.DRC
Checker.MagicDRC
Checker.KLayoutDRC
Magic.SpiceExtraction
Checker.IllegalOverlap
Netgen.LVS
Checker.LVS
Yosys.EQY
Checker.SetupViolations
Checker.HoldViolations
Checker.MaxSlewViolations
Checker.MaxCapViolations
Misc.ReportManufacturability'''.splitlines())
EXCLUDED = frozenset(('Yosys.Synthesis','Checker.YosysUnmappedCells','Checker.YosysSynthChecks','Checker.NetlistAssignStatements'))
STOPS = {'probe':'Odb.ApplyDEFTemplate','coarse':'OpenROAD.STAMidPNR-3','full':'Misc.ReportManufacturability'}


def write(path,value):
    path=Path(path);temporary=path.with_name(path.name+'.tmp')
    temporary.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');temporary.replace(path)


def receipt_value(value):
    """Encode native nonfinite observations without inventing finite metrics.

    Native state bytes remain authoritative and hash-bound. These tagged
    objects are diagnostic observations, never successful timing/signoff.
    """
    if isinstance(value,float) and not math.isfinite(value):
        label='NaN' if math.isnan(value) else ('+Infinity' if value>0 else '-Infinity')
        return dict(type='pinwheel.native-nonfinite-float.v1',value=label,qualified=False)
    if isinstance(value,dict):return {key:receipt_value(child) for key,child in value.items()}
    if isinstance(value,list):return [receipt_value(child) for child in value]
    return value


def validate_order(classic_ids,ids,stop):
    require(type(classic_ids) is list and type(ids) is list and len(ids) == len(set(ids)) and
            ids == [name for name in classic_ids if name not in EXCLUDED], '8x4 native flow changes ordinary scheduled steps')
    require('OpenROAD.DetailedRouting' in ids and tuple(ids[ids.index('OpenROAD.DetailedRouting'):]) == TAIL,
            '8x4 ordinary full flow tail changed or omitted')
    require(stop in STOPS.values() and stop in ids, '8x4 requested native checkpoint unavailable')
    require(ids.index('OpenROAD.GeneratePDN') < ids.index(STOPS['probe']) < ids.index('OpenROAD.GlobalPlacement'),
            '8x4 short probe does not follow actual PDN and DEF application')
    return dict(classic_steps=classic_ids,actual_steps=ids,excluded_synthesis_steps=sorted(EXCLUDED),
        full_tail=list(TAIL),requested_stop=stop,ordinary_full_tail_preserved=True)


def native(args):
    from librelane.flows.classic import Classic
    from librelane_plugin_streaming_8x4 import Streaming8x4Certified
    stop=STOPS[args.mode]
    report=validate_order([step.id for step in Classic.Steps],[step.id for step in Streaming8x4Certified.Steps],stop)
    report.update(schema='pinwheel.streaming-8x4-native-flow-order.v1',mode=args.mode,qualified=False)
    report['scope']='Scheduled ordinary step order only; disabled/skipped steps are not successful checks.'
    write('/work/metadata/flow-order.json',report)
    command=[sys.executable,'-B','-m','librelane','--manual-pdk','--pdk-root','/work/pdk','--pdk','ihp-sg13cmos5l',
        '--jobs','4','--run-tag',args.name,'--force-run-dir','/work/run','--with-initial-state','/work/inputs/seed.json',
        '--to',stop,'/work/inputs/core.json']
    os.execv(sys.executable,command)


def container_command(prepared,output,pdk,image_id,name,owner,mode):
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+',name) and re.fullmatch(r'[0-9a-f-]{36}',owner), 'Unsafe8x4 owner/name')
    require(mode in STOPS and image_id.startswith('sha256:'), 'Invalid8x4 native command')
    return ['docker','run','--rm','--pull','never','--name',name,'--label','org.pinwheel.streaming8_owner='+owner,
        '--network','none','--cpus','4','--memory','6g','--memory-swap','6g',
        '--env','PYTHONPATH=/work/inputs:/work/inputs/producer/scripts','--env','PYTHONDONTWRITEBYTECODE=1',
        '--mount',f'type=bind,source={prepared / "inputs"},target=/work/inputs,readonly',
        '--mount',f'type=bind,source={pdk},target=/work/pdk,readonly',
        '--mount',f'type=bind,source={output / "flow"},target=/work/run',
        '--mount',f'type=bind,source={output / "metadata"},target=/work/metadata',
        '--workdir','/work/inputs',image_id,'python3','-B','/work/inputs/producer/scripts/streaming_8x4_run.py',
        '--native','--mode',mode,'--name',name]


def cleanup(owner,log):
    query=['docker','container','ls','--all','--no-trunc','--filter',
           'label=org.pinwheel.streaming8_owner='+owner,'--format','{{.ID}}']
    result=dict(status='unconfirmed',ownership_label=owner)
    try:
        response=subprocess.run(query,capture_output=True,text=True,timeout=10)
        require(response.returncode == 0,'Owned8x4 container query failed')
        identities=response.stdout.splitlines()
        require(all(re.fullmatch('[0-9a-f]{64}',identity) for identity in identities),'Malformed owned8x4 container ID')
        result['owned_container_ids']=identities
        for identity in identities:
            stopped=subprocess.run(['docker','stop','--time','10',identity],stdout=log,stderr=subprocess.STDOUT,timeout=30)
            require(stopped.returncode == 0,'Owned8x4 container stop failed')
        response=subprocess.run(query,capture_output=True,text=True,timeout=10)
        require(response.returncode == 0,'Final owned8x4 query failed')
        result.update(status='absent' if not response.stdout.strip() else 'unconfirmed',remaining=response.stdout.splitlines())
    except (OSError,ValueError,subprocess.TimeoutExpired) as error:result['error']=type(error).__name__+': '+str(error)
    return result


def states(output,prepared,pdk):
    roots={'/work/run':output/'flow','/work/inputs':prepared/'inputs','/work/pdk':pdk}
    def resolve(value):
        if isinstance(value,dict): return {key:resolve(child) for key,child in value.items()}
        if isinstance(value,list): return [resolve(child) for child in value]
        if not isinstance(value,str): return receipt_value(value)
        for prefix,root in roots.items():
            if value.startswith(prefix+'/'):
                path=(root/value[len(prefix)+1:]).resolve()
                require(path.is_relative_to(root.resolve()),'Native8x4 view escapes mount')
                if path.is_file():return dict(container=value,path=str(path),sha256=sha(path))
        return value
    return [dict(state=str(path),state_sha256=sha(path),step_directory=path.parent.name,
        metrics=receipt_value(prep.read(path).get('metrics',{})),views=resolve({key:value for key,value in prep.read(path).items() if key!='metrics'}),
        native_nonfinite_encoding='pinwheel.native-nonfinite-float.v1; raw state bytes/hash remain authoritative; no acceptance follows',
        authoritative_physical_view='odb',carried_netlist_requires_ODB_reexport=True)
        for path in sorted((output/'flow').rglob('state_out.json'))]


def run(args):
    from streaming_tt_physical import inspect_runtime
    workspace=Path(args.workspace).resolve(strict=True) if args.workspace else prep.ROOT
    prep.ROOT=workspace
    prepared=Path(args.prepared).resolve(strict=True)
    packet=prep.verify(prepared)
    worker=regular(prepared/'inputs/producer/scripts/streaming_8x4_run.py')
    require(sha(worker) == packet['producer_sha256']['scripts/streaming_8x4_run.py'],'Frozen8x4 worker differs')
    if not args.frozen:
        os.execv(sys.executable,[sys.executable,'-B',str(worker),'--prepared',str(prepared),'--output',str(Path(args.output).absolute()),
            '--name',args.name,'--mode',args.mode,'--timeout-seconds',str(args.timeout_seconds),'--workspace',str(workspace),'--frozen'])
    require(Path(__file__).resolve() == worker.resolve(),'8x4 worker is not actual selected frozen producer')
    for name,expected in packet['producer_sha256'].items():
        data=subprocess.check_output(['git','show',packet['producer_commit']+':'+name],cwd=workspace,timeout=30)
        require(hashlib.sha256(data).hexdigest() == expected,'Frozen8x4 producer is not its committed source')
    require(1 <= args.timeout_seconds <= 21600,'8x4 native timeout outside1..21600seconds')
    output=Path(args.output).absolute()
    require(not output.exists(),'Preserve earlier8x4 native attempt')
    output.mkdir(parents=True);(output/'flow').mkdir();(output/'metadata').mkdir()
    owner=str(uuid.uuid4())
    receipt=dict(schema='pinwheel.streaming-8x4-native-run.v1',mode=args.mode,status='preflight',exit_code=None,
        started_utc=datetime.now(timezone.utc).isoformat(),prepared_input_sha256=sha(prepared/'preparation.json'),
        prepared=str(prepared),producer_commit=packet['producer_commit'],producer_sha256=packet['producer_sha256'],
        executed_staged_producer=str(worker),ownership_label=owner,container_name=args.name,
        native_timeout_seconds=args.timeout_seconds,source_ff_bits=6039,clock_period_ns=20,tiles='8x4',
        cpu_limit=4,memory_bytes=6*1024**3,memory_plus_swap_bytes=6*1024**3,network='none',
        input_mount_readonly=True,pdk_mount_readonly=True,qualified=False,physical_acceptance=False,
        post_pnr_equivalence_proved=False,extraction_model_qualified=False,
        configured_disabled_checks={name:prep.read(prepared/'inputs/core.json').get(name)
            for name in ('RUN_EQY','RUN_KLAYOUT_XOR','RUN_LINTER')
            if prep.read(prepared/'inputs/core.json').get(name) is False},
        scheduled_tail_is_not_completed_check_evidence=True,
        boundary='Actual bounded8x4 flow execution only. Ordinary flow completion does not establish final correspondence or any missing/failed/unsupported signoff gate.')
    process=None;started=time.monotonic();previous=signal.getsignal(signal.SIGTERM)
    def interrupted(signum,frame):raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    write(output/'report.json',receipt)
    with (output/'native.log').open('w') as log:
        try:
            runtime=inspect_runtime(prep.read(workspace/'tools/physical-toolchain.json'))
            command=container_command(prepared,output,Path(packet['pdk_root']),runtime['image_id'],args.name,owner,args.mode)
            receipt.update(status='running',runtime=runtime,argv=command);write(output/'report.json',receipt)
            process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
            code=process.wait(timeout=args.timeout_seconds)
            receipt.update(exit_code=code,status='flow_completed' if code==0 else 'failed')
        except subprocess.TimeoutExpired:receipt.update(exit_code=124,status='timed_out',stop_reason='native_wall_time_limit')
        except KeyboardInterrupt as error:receipt.update(exit_code=130,status='interrupted',stop_reason=str(error))
        except (OSError,ValueError,subprocess.CalledProcessError) as error:receipt.update(exit_code=127,status='blocked',error=type(error).__name__+': '+str(error))
        finally:
            write(output/'report.json',receipt)
            receipt['container_termination']=cleanup(owner,log)
            if process is not None and process.poll() is None:
                try:process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid,signal.SIGTERM)
                    try:process.wait(timeout=5)
                    except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGKILL);process.wait(timeout=5)
            signal.signal(signal.SIGTERM,previous)
            if receipt['container_termination']['status']!='absent':receipt['status']='cleanup_unconfirmed'
            try:
                require(prep.verify(prepared)==packet,'Prepared8x4 contract changed during native execution')
                require(inspect_runtime(prep.read(workspace/'tools/physical-toolchain.json'))==receipt.get('runtime'),'8x4 runtime changed')
                receipt['inputs_pdk_runtime_unchanged']=True
            except (OSError,ValueError,subprocess.CalledProcessError) as error:
                receipt.update(inputs_pdk_runtime_unchanged=False,status='invalidated',closeout_error=str(error))
            try:receipt['states']=states(output,prepared,Path(packet['pdk_root']))
            except (OSError,ValueError) as error:receipt.update(status='invalidated',state_inventory_error=str(error))
            receipt['elapsed_seconds']=round(time.monotonic()-started,3)
            receipt['artifact_sha256']={str(path.relative_to(output)):sha(path) for path in sorted(output.rglob('*')) if path.is_file() and path!=output/'report.json'}
            write(output/'report.json',receipt)
    print(output/'report.json',flush=True)
    return receipt.get('exit_code',127) or (0 if receipt['status']=='flow_completed' else 3)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode',choices=STOPS,default='full')
    parser.add_argument('--name',required=True)
    parser.add_argument('--native',action='store_true',help=argparse.SUPPRESS)
    parser.add_argument('--frozen',action='store_true',help=argparse.SUPPRESS)
    parser.add_argument('--workspace',type=Path)
    parser.add_argument('--prepared',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--timeout-seconds',type=int,default=14400)
    args=parser.parse_args()
    if args.native:return native(args)
    require(args.prepared is not None and args.output is not None,'Missing8x4 prepared/output roots')
    return run(args)


if __name__=='__main__':raise SystemExit(main())
