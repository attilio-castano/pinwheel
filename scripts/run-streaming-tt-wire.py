#!/usr/bin/env python3
"""Run the complete D2 public-wire corpus from a fresh committed source archive.

The exact closed physical ODB, native readback, state/sampler mapping, tools and
all selected source bytes are frozen before the guarded worker starts. This
finite zero-delay diagnostic never grants physical or functional acceptance.
"""
import argparse
from hashlib import sha256,new as new_hash
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time

ROOT=Path(__file__).resolve().parents[1]
# The fresh selected tree must remain exactly its committed membership even
# when this coordinator is invoked without the optional interpreter -B flag.
sys.dont_write_bytecode=True


def need(value,message):
    if not value:raise ValueError(message)


def regular(path):
    path=Path(path);need(path.is_file() and not path.is_symlink(),'Regular wire handoff input required: '+str(path))
    return path.resolve()


def digest(path):return sha256(regular(path).read_bytes()).hexdigest()


def decode(payload):
    def pairs(items):
        result={}
        for key,value in items:
            need(key not in result,'Duplicate wire handoff JSON key: '+key);result[key]=value
        return result
    def invalid(value):raise ValueError('Nonfinite wire handoff JSON value: '+value)
    return json.loads(payload,object_pairs_hook=pairs,parse_constant=invalid)


def read(path):return decode(regular(path).read_bytes())


def write(path,value):
    path=Path(path);temporary=path.with_name(path.name+'.tmp')
    with temporary.open('x') as stream:
        stream.write(json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n');stream.flush();os.fsync(stream.fileno())
    temporary.replace(path)


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec)
    sys.modules[name]=module;spec.loader.exec_module(module);return module


def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,timeout=60)


def check_environment(environment=None):
    environment=os.environ if environment is None else environment
    fixed={'PYTHONPATH','PYTHONHOME','PYTHONSTARTUP','PYTHONPYCACHEPREFIX','LEAN_PATH','LEAN_SRC_PATH',
        'LEAN_SYSROOT','LAKE_HOME','LAKE_PACKAGES_DIR','LAKE_CACHE_DIR','LD_PRELOAD','LD_LIBRARY_PATH'}
    prefixes=('DYLD_','YOSYS_','ABC_','Z3_','CIRCT_','VVP_','IVERILOG_','IVL_','VPI_')
    bad=sorted(name for name,value in environment.items() if value and (name in fixed or name.startswith(prefixes)))
    need(not bad,'Refuse inherited public-wire compiler/cache/loader overrides: '+', '.join(bad))


def actual_export(host_path,*,physical_report,state,checkpoint_host,exporter_sha256):
    """Refuse a readback from an unclosed or different physical database."""
    physical_report,state,host_path=map(regular,(physical_report,state,host_path))
    producer,roots,_,database=checkpoint_host.checkpoint(physical_report,state)
    frozen=checkpoint_host.constraints(physical_report,producer,roots)
    packet=read(host_path)
    need(packet.get('schema')=='pinwheel.streaming-tt-odb-export-run.v1' and packet.get('passed') is True and
        packet.get('status')=='exported' and packet.get('exit_code')==0 and packet.get('native_export_binding') is True and
        packet.get('inputs_unchanged') is True and packet.get('staged_inputs_unchanged') is True and
        packet.get('runtime_unchanged') is True and packet.get('container_termination',{}).get('status')=='absent',
        'Actual ODB readback producer is not successfully closed')
    need(regular(packet['physical_report'])==physical_report and regular(packet['actual_odb'])==database and
        packet.get('actual_odb_sha256')==digest(database) and
        packet.get('input_sha256',{}).get(str(physical_report))==digest(physical_report) and
        packet.get('input_sha256',{}).get(str(state))==digest(state),
        'Native readback does not bind the exact physical checkpoint')
    reference=regular(packet['reference']);directory=host_path.parent/'native/export'
    native=read(directory/'receipt.json')
    need(native.get('schema')=='pinwheel.streaming-tt-odb-export.v1' and native.get('read_only_database') is True and
        native.get('top')=='tt_um_pinwheel_streaming_ready_d2' and native.get('database_sha256')==digest(database) and
        native.get('reference_sha256')==digest(reference) and native.get('source_sha256')==exporter_sha256 and
        set(native.get('artifacts_sha256',{}))=={'connectivity.json','inventory.json'},
        'Native readback differs from actual ODB/reference/selected exporter')
    actual={str(path.relative_to(host_path.parent)):digest(path) for path in sorted((host_path.parent/'native').rglob('*')) if path.is_file()}
    need(actual==packet.get('artifact_sha256'),'Native readback artifact membership or bytes changed')
    for name,expected in native['artifacts_sha256'].items():
        need(digest(directory/name)==expected,'Native connectivity readback changed: '+name)
    frozen.update({str(path):digest(path) for path in (physical_report,state,host_path,database,reference,
        directory/'receipt.json',directory/'connectivity.json',directory/'inventory.json')})
    return producer,roots,database,reference,directory,frozen


def canonical_cell(value):
    path=json.loads(value)
    need(type(path) is list and len(path)==1 and type(path[0]) is str and path[0] and
        json.dumps(path,separators=(',',':'))==value,'Noncanonical actual flat FF path')
    return path[0]


def sampler_binding(binding_path,map_path,*,candidate,database,connectivity):
    binding_path,map_path,candidate,database,connectivity=map(regular,
        (binding_path,map_path,candidate,database,connectivity))
    binding,mapping,document=read(binding_path),read(map_path),read(connectivity)
    need(binding.get('schema')=='pinwheel.streaming-tt-sampler-binding.v1' and
        binding.get('top')=='tt_um_pinwheel_streaming_ready_d2' and
        binding.get('connectivity_sha256')==mapping.get('connectivity_sha256')==digest(connectivity) and
        mapping.get('database_sha256')==digest(database) and mapping.get('source_candidate_sha256')==digest(candidate),
        'Semantic sampler map differs from exact source candidate/ODB/connectivity')
    body=document['modules'][binding['top']];rows=mapping.get('rows')
    need(type(rows) is list and len(rows)==6039 and len({row['semantic'] for row in rows})==6039 and
        len({row['actual_ff'] for row in rows})==6039,'Full unique 6039-bit semantic/actual state mapping required')
    actual_ff={name for name,cell in body['cells'].items() if
        {'Q','D','CLK','RESET_B'}<=set(cell.get('connections',{}))}
    need({canonical_cell(row['actual_ff']) for row in rows}==actual_ff,'Actual full FF inventory differs from semantic map')
    for row in rows:
        cell=body['cells'][canonical_cell(row['actual_ff'])]
        need(cell['type']==row['actual_cell'] and all(cell['connections'][pin]==[row[key]] for pin,key in
            [('Q','actual_q'),('D','actual_d'),('CLK','actual_clock'),('RESET_B','actual_reset_b')]),
            'Actual FF Q/D/clock/reset pins differ from full semantic mapping')
    need(set(binding.get('bindings',{}))=={'stage1','stage2'},'Both real sampled-input stages required')
    for stage,item in binding['bindings'].items():
        matches=[row for row in rows if row['semantic']=='core-d2:r_'+stage+':0']
        need(len(matches)==1 and item.get('component')=='core-d2' and item.get('register')=='r_'+stage and
            item.get('index')==0 and item.get('cell')==matches[0]['actual_ff'] and
            all(item.get(field)==matches[0][key] for field,key in
                [('q','actual_q'),('d','actual_d'),('clock','actual_clock'),('reset_b','actual_reset_b')]),
            'Sampler witness differs from exact actual semantic FF endpoints')
        item['cell']=canonical_cell(item['cell'])
    basis=binding.get('semantic_basis')
    need(type(basis) is dict and basis and all(type(item) is dict and set(item)=={'path','sha256'} and
        digest(item['path'])==item['sha256'] for item in basis.values()),'Unclosed external semantic sampler basis')
    basis['actual-state-pairing']={'path':str(map_path),'sha256':digest(map_path)}
    basis['original-canonical-binding']={'path':str(binding_path),'sha256':digest(binding_path)}
    return binding


def archive_sources(out,commit):
    tree={}
    for entry in git('ls-tree','-rz','--full-tree',commit).decode().split('\0'):
        if not entry:continue
        head,name=entry.split('\t',1);mode,kind,oid=head.split()
        need(kind=='blob' and mode in ('100644','100755') and name not in tree and
            not Path(name).is_absolute() and '..' not in Path(name).parts,'Nonregular/escaping selected Git source')
        tree[name]=oid
    archive=out/'selected-source.tar'
    with archive.open('xb') as stream:
        subprocess.run(['git','archive','--format=tar',commit],cwd=ROOT,stdout=stream,check=True,timeout=60)
    selected=out/'selected';selected.mkdir()
    with tarfile.open(archive,'r:') as stream:
        for member in stream.getmembers():
            need((member.isdir() or member.isfile()) and not Path(member.name).is_absolute() and
                '..' not in Path(member.name).parts,'Nonregular/escaping selected archive member')
        stream.extractall(selected,filter='data')
    need(not any((selected/name).exists() for name in ('.git','.lake','build')),'Selected source archive contains cache/build state')
    return selected,archive,tree,git('rev-parse','--show-object-format').decode().strip()


def membership(selected,tree,algorithm):
    actual={str(path.relative_to(selected)) for path in selected.rglob('*') if path.is_file()}
    need(actual==set(tree),'Selected source archive membership changed')
    result={}
    for name,oid in tree.items():
        path=regular(selected/name);data=path.read_bytes()
        need(new_hash(algorithm,b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid,
            'Selected source differs from committed Git blob: '+name)
        result[name]=sha256(data).hexdigest()
    return result


def native_journal(path,records):
    events=[decode(line) for line in regular(path).read_text().splitlines()]
    need(len(records)==14 and len(events)==28,'Missing/extra actual public-wire native journal events')
    for index,record in enumerate(records):
        intent,result=events[2*index:2*index+2]
        expected={key:record[key] for key in ('index','scope','argv','executable_sha256_before')}
        need(intent==dict(event='intent',**expected) and result==dict(event='result',**record),
            'Actual public-wire native intent/result disagrees with worker receipt')
    return digest(path)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('physical-report','state','odb-export-report','sampler-binding','state-map','candidate',
            'tool-config','tool-identity-report'):
        parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--tag',required=True);parser.add_argument('--timeout',type=int,default=7200)
    args=parser.parse_args();need(re.fullmatch('[A-Za-z0-9_-]+',args.tag) and 1<=args.timeout<=14400,
        'Safe fresh tag and bounded timeout required')
    check_environment()
    commit=git('rev-parse','HEAD').decode().strip()
    need(git('show',commit+':scripts/run-streaming-tt-wire.py')==regular(__file__).read_bytes(),
        'Commit the actual public-wire coordinator before running it')
    out=ROOT/'build/validation'/('streaming-tt-wire-'+args.tag);out.mkdir(parents=True,exist_ok=False)
    selected,archive,tree,algorithm=archive_sources(out,commit);hashes=membership(selected,tree,algorithm)
    sys.path.insert(0,str(selected/'scripts'))
    gate=load('_streaming_tt_selected_wire',selected/'scripts/check-streaming-tt-wire.py');gate.check_environment()
    checkpoint_host=load('_streaming_tt_wire_checkpoint',selected/'scripts/run-streaming-tt-sta.py')
    producer,roots,database,reference,export,frozen=actual_export(args.odb_export_report,
        physical_report=args.physical_report,state=args.state,checkpoint_host=checkpoint_host,
        exporter_sha256=hashes['scripts/streaming_tt_export_odb.py'])
    binding=sampler_binding(args.sampler_binding,args.state_map,candidate=args.candidate,database=database,
        connectivity=export/'connectivity.json')
    tools_config=read(args.tool_config);tools=tools_config['tools'];identity_receipt=read(args.tool_identity_report)
    need(identity_receipt.get('passed') is True and identity_receipt.get('source_commit')==tools_config.get('source_commit') and
        identity_receipt.get('worker_config_sha256_before_use')==digest(args.tool_config) and
        type(identity_receipt.get('tool_identity_after')) is dict,'Closed qualified source-tool identity receipt required')
    raw=load('_streaming_tt_wire_selected_raw',selected/'scripts/check-streaming-uart.py');helpers=raw.helpers()
    tool_manifest=read(selected/'tools/hardware-toolchain.json');identity=raw.tool_identity(helpers,tools,tool_manifest)
    need(identity==identity_receipt['tool_identity_after'],'Actual native tools differ from closed source-tool identity')
    libroot=roots['/work/pdk']/'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lib'
    corners={name:dict(path=str(libroot/('sg13cmos5l_stdcell_'+suffix+'.lib')),sha256=pin) for name,suffix,pin in [
        ('typ','typ_1p20V_25C','34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad'),
        ('fast','fast_1p32V_m40C','af12d75a72d19648fa690027d29843fbae550aa91f4e40dd3339c7116d6e425d'),
        ('slow','slow_1p08V_125C','3ee222c580ba33acb2131ac2bf224ff8ee9700751835b73aaec72b670bb31d3c')]}
    for item in corners.values():need(digest(item['path'])==item['sha256'],'Pinned physical Liberty changed')
    inputs=out/'inputs';inputs.mkdir();binding_path=inputs/'sampler-binding.json';write(binding_path,binding)
    config=dict(schema='pinwheel.streaming-tt-wire-request.v1',source_commit=commit,producer_commit=commit,
        root=str(selected),source_sha256=hashes,physical_stage='actual-closed-checkpoint-'+args.state.parent.name,
        tools=tools,tool_identity=identity,corners=corners,compile_timeout=300,
        export=dict(directory=str(export),receipt_sha256=digest(export/'receipt.json'),
            database=str(database),reference=str(reference)),
        sampler_binding=dict(path=str(binding_path),sha256=digest(binding_path)))
    config_path=out/'worker-config.json';write(config_path,config)
    for path in (archive,args.sampler_binding,args.state_map,args.candidate,args.tool_config,args.tool_identity_report,
            binding_path,config_path,regular(__file__)):
        frozen[str(regular(path))]=digest(path)
    frozen.update({str(regular(item['path'])):digest(item['path']) for item in binding['semantic_basis'].values()})
    need(digest(__file__)==hashes['scripts/run-streaming-tt-wire.py'],'Actual coordinator changed after selecting source')
    report=dict(schema='pinwheel.streaming-tt-wire-handoff.v2',passed=False,qualified=False,
        physical_acceptance_claim=False,status='intent',source_commit=commit,producer_commit=commit,
        physical_source_commit=producer['source_commit'],physical_report=str(regular(args.physical_report)),
        physical_stage=config['physical_stage'],source_tree=tree,source_object_format=algorithm,
        source_sha256_before=hashes,selected_archive=dict(path=str(archive),sha256=digest(archive)),
        worker_config=dict(path=str(config_path),sha256=digest(config_path)),frozen_before_spawn=frozen,
        tool_identity_before=identity,inherited_override_guard_checked_before_spawn=True,
        boundary='Finite complete D2 public-wire corpus on actual closed ODB connectivity. No SDF, extracted timing, electrical, DRC/LVS/antenna or universal functional acceptance claim.')
    argv=[tools['python'],'-B',str(selected/'scripts/check-streaming-tt-wire.py'),
        '--worker-config',str(config_path),'--worker-config-sha256',digest(config_path),'--out',str(out/'worker')]
    report.update(argv=argv,started_at_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
    path=out/'orchestration-report.json';write(path,report);started=time.monotonic()
    process_group=load('_streaming_tt_wire_process_group',selected/'scripts/process_group.py')
    try:
        report['status']='running';write(path,report)
        native=process_group.run_captured(argv,cwd=selected,timeout=args.timeout,log_path=out/'worker.stdout.log')
        report.update(native_exit_code=native.returncode,status='completed' if native.returncode==0 else 'failed')
        need(native.returncode==0,'Actual-checkpoint public-wire worker failed; preserve all per-protocol receipts')
        result=read(out/'worker/report.json')
        need(result.get('passed') is True and result.get('qualified') is False and result.get('source_commit')==commit and
            result.get('producer_commit')==commit and result.get('physical_ff_bits')==6039 and result.get('native_processes')==14 and
            result.get('inputs_unchanged') is True and result.get('generated_inputs_unchanged') is True and
            result.get('clock_contraction') is False and result.get('stage')=='closed',
            'Actual-checkpoint public-wire worker contract did not close')
        gate.validate_native(result,out/'worker',tools)
        need(native_journal(out/'worker/native.jsonl',result['native_runs'])==result.get('native_journal',{}).get('sha256'),
            'Actual native journal differs from closed worker pin')
        artifacts={str(item.relative_to(out/'worker')):digest(item) for item in sorted((out/'worker').rglob('*'))
            if item.is_file() and item!=out/'worker/report.json'}
        need(artifacts==result.get('artifact_sha256') and all(digest(file)==expected for file,expected in
            result.get('input_sha256_before',{}).items()),'Closed worker input/artifact bytes or membership changed')
        need(membership(selected,tree,algorithm)==hashes and all(digest(file)==expected for file,expected in frozen.items()),
            'Frozen selected source or handoff input changed during public-wire diagnostics')
        after=raw.tool_identity(helpers,tools,tool_manifest);need(after==identity,'Native runtime changed during public-wire diagnostics')
        report.update(passed=True,worker_report=dict(path=str(out/'worker/report.json'),sha256=digest(out/'worker/report.json')),
            tool_identity_after=after,sources_unchanged=True,intake_unchanged=True,physical_edges=result['physical_edges'],native_processes=14)
    except BaseException as error:
        report.update(passed=False,status='failed_or_interrupted',error=type(error).__name__+': '+str(error))
        if isinstance(error,subprocess.TimeoutExpired):
            report.update(native_exit_code=124,process_group_stopped=getattr(error,'process_group_stopped',False))
        raise
    finally:
        report.update(elapsed_seconds=round(time.monotonic()-started,3))
        if (out/'worker.stdout.log').is_file():report['worker_stdout_sha256']=digest(out/'worker.stdout.log')
        report['retained_protocol_reports']={str(item.relative_to(out)):digest(item) for item in
            sorted((out/'worker').rglob('report.json')) if item.is_file()}
        write(path,report)
    print(path,flush=True)


if __name__=='__main__':main()
