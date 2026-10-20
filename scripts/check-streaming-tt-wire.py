#!/usr/bin/env python3
"""Fresh actual-OpenDB public-wire diagnostics; no physical acceptance flag.

The parent must bind the selected committed source archive and actual physical
stage. This worker freezes that explicit input set before native compilation,
keeps every physical clock/cell, and retains all public-pin edge traces.
"""
from hashlib import sha256
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import sys
import time
import traceback

SCHEMA='pinwheel.streaming-tt-public-wire.v1'
REQUIRED_SOURCE=('scripts/check-streaming-tt-wire.py','scripts/streaming_tt_simulation.py',
    'scripts/streaming_tt_certificate.py','scripts/streaming_tt_ties.py','scripts/streaming_tt_export_odb.py',
    'scripts/streaming_mapped_liberty.py','scripts/streaming_mapped_netlist.py','scripts/streaming_mapped_certificate.py',
    'scripts/streaming_mapped_simulation.py','scripts/streaming_mapped_device.py','scripts/streaming_ready_wrapper.py',
    'scripts/streaming_mapped_runtime.py',
    'scripts/streaming_uart_legacy_cases.py','scripts/streaming_ready_wire_cases.py','scripts/streaming_uart_wire_cases.py',
    'scripts/streaming_wire_cases.py','scripts/streaming_rtl.py','scripts/streaming_ready_transport.py',
    'scripts/streaming_transport.py','scripts/streaming_uart_compile.py','scripts/streaming_ready_compile.py',
    'scripts/streaming_compile.py','scripts/streaming_ready_peers.py','scripts/streaming_peers.py','scripts/pad_io.py',
    'scripts/check-streaming-uart.py','scripts/check-buffered-rtl-session.py','tools/hardware-toolchain.json')
TRACE_FORMAT=('u32 cycle; u8 initialize,csn,sck,mosi,peerLevels,peerEnabled,links,pullups,'
    'preMiso,postReady,postBusy,postLevels,postEnabled,postWires,postKnown,preRaw')


def require(value,message):
    if not value:raise ValueError(message)


def regular(path):
    path=Path(path).absolute()
    require(path.is_file() and not path.is_symlink(),'Regular staged input required: '+str(path))
    return path


def digest(path):return sha256(regular(path).read_bytes()).hexdigest()


def read(path):
    data=regular(path).read_bytes()
    def unique(items):
        value={}
        for key,item in items:
            require(key not in value,'Duplicate JSON key');value[key]=item
        return value
    def invalid(value):raise ValueError('Nonfinite JSON number is unsupported: '+value)
    value=json.loads(data,object_pairs_hook=unique,parse_constant=invalid)
    require(regular(path).read_bytes()==data,'Input changed during read')
    return value


def write_json(path,value):path.write_text(json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n')


def write_durable(path,value):
    """Close each protocol result on disk before opening the next simulator."""
    path=Path(path);temporary=path.with_name(path.name+'.tmp')
    with temporary.open('x') as stream:
        stream.write(json.dumps(value,sort_keys=True,indent=2,allow_nan=False)+'\n')
        stream.flush();os.fsync(stream.fileno())
    temporary.replace(path)
    descriptor=os.open(path.parent,os.O_RDONLY)
    try:os.fsync(descriptor)
    finally:os.close(descriptor)


def run_legacy_durable(vvp,executable,directory,*,depth):
    from streaming_uart_legacy_cases import WORKLOADS,SCHEMA,ready_image,check_legacy_cases
    from streaming_wire_cases import run_stream
    require(type(depth) is int and depth in (2,4),'Expected a declared queue depth')
    for protocol,_ in WORKLOADS:ready_image(protocol)
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=False);rows=[]
    progress=dict(schema='pinwheel.streaming-tt-legacy-progress.v1',completed=False,passed=False,
        qualified=False,depth=depth,workloads=[dict(protocol=name,bits=bits) for name,bits in WORKLOADS],cases=[])
    try:
        for protocol,bits in WORKLOADS:
            progress.update(status='running',current_protocol=protocol)
            write_durable(directory/'progress.json',progress)
            row=run_stream(vvp,executable,directory/protocol,protocol=protocol,bits=bits,depth=depth)
            write_durable(directory/protocol/'report.json',row)
            rows.append(row);progress['cases'].append(dict(protocol=protocol,passed=row.get('passed') is True,
                report=str(directory/protocol/'report.json'),sha256=digest(directory/protocol/'report.json')))
            progress['status']='between_protocols';write_durable(directory/'progress.json',progress)
        result=dict(schema=SCHEMA,passed=all(row.get('passed') is True for row in rows),depth=depth,cases=rows,
            physical_edges=sum(row.get('physical_edges',0) for row in rows))
        write_durable(directory/'report.json',result)
        check_legacy_cases(result)
        progress.update(completed=True,passed=True,status='completed');write_durable(directory/'progress.json',progress)
        return result
    except BaseException as error:
        progress.update(status='failed_or_interrupted',error=type(error).__name__+': '+str(error))
        write_durable(directory/'progress.json',progress);raise


def run_i2c_durable(vvp,executable,directory,*,depth):
    import streaming_ready_wire_cases as cases
    original=cases.run_i2c_case
    def recorded(vvp,executable,path,**options):
        result=original(vvp,executable,path,**options)
        write_durable(Path(path)/'report.json',result)
        return result
    cases.run_i2c_case=recorded
    try:return cases.run_i2c_cases(vvp,executable,directory,depth=depth)
    finally:cases.run_i2c_case=original


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec)
    sys.modules[name]=module;spec.loader.exec_module(module);return module


def check_environment(environment=None):
    environment=os.environ if environment is None else environment
    fixed={'PYTHONPATH','PYTHONHOME','PYTHONSTARTUP','PYTHONPYCACHEPREFIX',
        'LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LAKE_HOME','LAKE_PACKAGES_DIR','LAKE_CACHE_DIR',
        'LD_PRELOAD','LD_LIBRARY_PATH'}
    prefixes=('DYLD_','YOSYS_','ABC_','Z3_','CIRCT_','VVP_','IVERILOG_','IVL_','VPI_')
    bad=sorted(name for name,value in environment.items() if value and
        (name in fixed or name.startswith(prefixes)))
    require(not bad,'Refuse inherited compiler/cache/loader overrides: '+', '.join(bad))


def source_snapshot(config):
    root=Path(config['root']);expected=config.get('source_sha256',{})
    require(type(expected) is dict and set(REQUIRED_SOURCE)<=expected.keys(),
        'Missing selected producer/helper source closure')
    require(root.is_absolute() and root.resolve()==Path(__file__).resolve().parents[1],
        'Worker must execute from the supplied selected source root')
    require(all(type(name) is str and not Path(name).is_absolute() and '..' not in Path(name).parts and
        re.fullmatch('[0-9a-f]{64}',value) for name,value in expected.items()),'Malformed selected source map')
    actual={name:digest(root/name) for name in expected}
    require(actual==expected,'Selected source changed before/during native diagnostics')
    return actual


def validate_trace(path,receipt,edges):
    path=regular(path);before=path.stat()
    require(type(edges) is int and edges>0 and type(receipt) is dict and receipt.get('edges')==edges and
        receipt.get('bytes')==edges*20 and receipt.get('format')==TRACE_FORMAT and
        re.fullmatch('[0-9a-f]{64}',receipt.get('sha256','')),'Missing exact complete public trace receipt')
    require(before.st_nlink==1 and before.st_size==edges*20,'Truncated, oversized or aliased public trace')
    hashed=sha256();count=0
    with path.open('rb') as stream:
        while block:=stream.read(20*8192):
            require(len(block)%20==0,'Partial public trace edge')
            hashed.update(block)
            for offset in range(0,len(block),20):
                count+=1
                require(struct.unpack_from('<I',block,offset)[0]==count,'Public trace edge indices omitted/reordered')
    after=path.stat()
    require(count==edges and hashed.hexdigest()==receipt['sha256'] and
        (before.st_ino,before.st_dev,before.st_size,before.st_mtime_ns)==
        (after.st_ino,after.st_dev,after.st_size,after.st_mtime_ns),'Trace bytes changed during validation')
    return dict(path=str(path),sha256=hashed.hexdigest(),edges=edges,bytes=before.st_size)


def validate_native(result,out,tools):
    from streaming_mapped_simulation import check_uart_cases
    from streaming_uart_legacy_cases import check_legacy_cases
    from streaming_ready_wire_cases import check_i2c_cases
    check_uart_cases(result['uart']);check_legacy_cases(result['legacy']);check_i2c_cases(result['i2c'])
    require(all(row.get('depth')==2 and type(row.get('depth')) is int
        for row in (result['uart'],result['legacy'],result['i2c'])),'Only the complete physical D2 chip is accepted')
    records=result.get('native_runs');require(type(records) is list and len(records)==14,'Actual14 native processes required')
    cases=[]
    for index,row in enumerate(result['uart']['native_runs']):
        label=('unchanged','sampler-ff-pin')[index]
        cases.append(('uart',out/'uart'/(label+'.bin'),row,result['executables'][label]))
    for row in result['legacy']['cases']:
        cases.append(('legacy',out/'legacy'/row['protocol']/'wire.bin',row,result['executables']['unchanged']))
    for row in result['i2c']['cases']:
        # Case identity is checked independently by the frozen I2C checker.
        name=row['direction']+'-'+row['profile']
        cases.append(('i2c',out/'i2c'/name/'wire.bin',row,result['executables']['unchanged']))
    require(len(cases)==14,'Native trace/process inventory differs')
    traces=[]
    for index,(record,(scope,path,row,executable)) in enumerate(zip(records,cases)):
        argv=[str(tools['vvp']),str(executable)]
        require(record.get('index')==index and type(record.get('index')) is int and record.get('scope')==scope and record.get('argv')==record.get('actual_argv')==argv and
            record.get('native_exit_code')==0 and type(record.get('native_exit_code')) is int and
            record.get('client_succeeded') is True and
            record.get('executable_sha256_before')==record.get('executable_sha256_after')==digest(executable) and
            type(record.get('physical_edges')) is int and record.get('physical_edges')==row.get('physical_edges'),
            'Native process/actual executable/trace binding differs')
        traces.append(validate_trace(path,row.get('trace'),record['physical_edges']))
    require(result.get('physical_edges')==sum(record['physical_edges'] for record in records)==
        sum(result[key]['physical_edges'] for key in ('uart','legacy','i2c')),'Physical edge aggregate differs')
    require(result['uart']['cases'][-1].get('mutation')==result['sampler_mutation'],
        'Public sampler witness does not bind the actual mutated FF')
    return traces


def run_worker(config,out,*,config_path=None,config_sha256=None):
    check_environment()
    require(type(config) is dict and config.get('schema')=='pinwheel.streaming-tt-wire-request.v1',
        'Explicit physical wire request required')
    require(all(type(config.get(key)) is str and re.fullmatch('[0-9a-f]{40}',config[key])
        for key in ('source_commit','producer_commit')) and config['source_commit']==config['producer_commit'],
        'Exact same selected source/producer commit required')
    before_source=source_snapshot(config);root=Path(config['root']);out=Path(out).absolute()
    require(not out.exists(),'Preserve any previous physical diagnostic attempt')
    tools=config['tools'];export=config['export']
    require(type(config.get('physical_stage')) is str and config['physical_stage'],
        'Explicit physical stage label required; no stale NL inference')
    require(type(config.get('compile_timeout',300)) is int and 1<=config.get('compile_timeout',300)<=900,
        'Bounded explicit native compilation timeout required')
    input_paths=[root/name for name in before_source]
    if config_path is not None:
        require(digest(config_path)==config_sha256,'Worker configuration changed before native use')
        input_paths.append(config_path)
    input_paths += [*tools.values(),export['database'],export['reference'],
        Path(export['directory'])/'receipt.json',Path(export['directory'])/'connectivity.json',
        Path(export['directory'])/'inventory.json',config['sampler_binding']['path']]
    input_paths += [item['path'] for item in config['corners'].values()]
    binding_input=read(config['sampler_binding']['path'])
    basis=binding_input.get('semantic_basis',{})
    require(type(basis) is dict and basis and all(type(item) is dict and set(item)=={'path','sha256'} and
        digest(item['path'])==item['sha256'] for item in basis.values()),
        'Externally bound actual semantic sampler correspondence required')
    input_paths += [item['path'] for item in basis.values()]
    frozen={str(regular(path)):digest(path) for path in input_paths}
    require(digest(config['sampler_binding']['path'])==config['sampler_binding']['sha256'],
        'Externally pinned sampler binding changed')
    out.mkdir(parents=True)
    report=dict(schema=SCHEMA,passed=False,qualified=False,physical_acceptance_claim=False,
        source_commit=config['source_commit'],producer_commit=config['producer_commit'],
        physical_stage=config['physical_stage'],input_sha256_before=frozen,commands=[],stage='preflight',
        configuration=dict(path=str(config_path) if config_path is not None else None,sha256=config_sha256),
        started_at_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        boundary='Finite public-wire simulation of actual ODB signal connectivity with zero-delay pinned Liberty functions. '
            'Every functional instance/FF/clock is retained. No SDF, extracted timing, electrical, power, CDC, routing or tapeout qualification. '
            'Parent independently binds selected source/archive and the actual physical stage.')
    report_path=out/'report.json';started=time.monotonic()
    def save():report['elapsed_seconds']=time.monotonic()-started;write_json(report_path,report)
    def unchanged():
        require(source_snapshot(config)==before_source and all(digest(path)==value for path,value in frozen.items()),
            'Physical/source/native input changed during diagnostics')
    def journal(path,value):
        with path.open('a') as stream:
            stream.write(json.dumps(value,sort_keys=True,allow_nan=False)+'\n');stream.flush();os.fsync(stream.fileno())
    save()
    try:
        sys.path.insert(0,str(root/'scripts'))
        import streaming_tt_simulation as simulation
        from streaming_ready_wrapper import bridge_source
        from streaming_mapped_device import NativeAudit
        from streaming_mapped_runtime import audit as runtime_audit
        from streaming_mapped_simulation import run_uart_cases
        raw=load('_streaming_tt_wire_raw_helpers',root/'scripts/check-streaming-uart.py');h=raw.helpers()
        loaded={}
        for name,module in tuple(sys.modules.items()):
            if name.startswith('streaming_') or name=='pad_io':
                path=getattr(module,'__file__',None)
                if path:
                    path=Path(path).resolve()
                    require(path.is_relative_to(root/'scripts') and str(path.relative_to(root)) in before_source and
                        digest(path)==before_source[str(path.relative_to(root))],
                        'Loaded helper is outside the frozen selected source: '+name)
                    loaded[name]=str(path)
        report['loaded_helpers']=loaded
        hardware=read(root/'tools/hardware-toolchain.json')
        identity=raw.tool_identity(h,tools,hardware)
        require(identity==config['tool_identity'],'Native tool/runtime differs from externally pinned identity')
        report['tool_identity_before']=identity
        report['cad_runtime_archive_membership']=runtime_audit(identity,hardware,tools)
        save()
        document,inventory,export_identity=simulation.verify_export(export['directory'],
            receipt_sha256=export['receipt_sha256'],database=export['database'],reference=export['reference'],
            exporter_sha256=before_source['scripts/streaming_tt_export_odb.py'])
        body=document['modules'][simulation.TOP]
        library,liberty=simulation.libraries(config['corners'],{cell['type'] for cell in body['cells'].values()})
        report.update(export=export_identity,liberty=liberty);save()
        actual,actual_inventory=simulation.structural_verilog(document,library)
        binding=read(config['sampler_binding']['path'])
        require(binding.get('schema')=='pinwheel.streaming-tt-sampler-binding.v1' and binding.get('top')==simulation.TOP and
            binding.get('connectivity_sha256')==digest(Path(export['directory'])/'connectivity.json') and
            type(binding.get('semantic_basis')) is dict and binding['semantic_basis'],
            'Physical sampler binding is not linked to this exact actual export')
        mutant,mutation=simulation.sampler_mutation(document,library,binding['bindings'])
        mutant_sv,mutant_inventory=simulation.structural_verilog(mutant,library)
        require(actual_inventory['physical_ff_bits']==6039 and
            len(actual_inventory['instances'])==inventory['signal_model_instances']==len(mutant_inventory['instances']),
            'Actual physical all-instance/full-state inventory differs')
        files={'unchanged.sv':actual,'sampler-ff-pin.sv':mutant_sv,
            'cells.sv':simulation.cell_models(library,set(library.cells)),'bridge.sv':bridge_source(2)}
        for name,text in files.items():(out/name).write_text(text)
        write_json(out/'actual-instance-inventory.json',actual_inventory)
        write_json(out/'sampler-ff-pin.json',mutant)
        write_json(out/'sampler-mutation.json',mutation)
        report['sampler_mutation']=mutation
        generated={str(out/name):digest(out/name) for name in files}
        generated.update({str(out/name):digest(out/name) for name in
            ('actual-instance-inventory.json','sampler-ff-pin.json','sampler-mutation.json')})
        write_json(out/'compile-inputs.json',dict(input_sha256=frozen,generated_sha256=generated,
            tool_identity_sha256=sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
        report['compile_inputs']=dict(path=str(out/'compile-inputs.json'),sha256=digest(out/'compile-inputs.json'))
        report['generated_sha256_before']=generated;report['stage']='native-compile';save()
        executables={}
        for label in ('unchanged','sampler-ff-pin'):
            unchanged();require(all(digest(path)==value for path,value in generated.items()),'Generated native input changed')
            executable=out/(label+'.vvp');argv=[tools['iverilog'],'-g2012','-s','streaming_quad_host_bridge',
                '-o',str(executable),str(out/(label+'.sv')),str(out/'cells.sv'),str(out/'bridge.sv')]
            item=dict(label=label,argv=argv,compiler_sha256_before=digest(tools['iverilog']),
                compile_inputs_sha256=report['compile_inputs']['sha256'])
            journal(out/'compile.jsonl',dict(event='intent',**item));save()
            log=out/(label+'-compile.log');before=time.monotonic()
            with log.open('w') as stream:
                native=subprocess.run(argv,cwd=root,stdout=stream,stderr=subprocess.STDOUT,timeout=config.get('compile_timeout',300))
            item.update(exit_code=native.returncode,log=str(log),log_sha256=digest(log),elapsed_seconds=time.monotonic()-before,
                compiler_sha256_after=digest(tools['iverilog']))
            if executable.is_file():item['executable_sha256']=digest(executable)
            journal(out/'compile.jsonl',dict(event='result',**item));report['commands'].append(item);save()
            require(native.returncode==0 and item['compiler_sha256_before']==item['compiler_sha256_after'],
                'Actual physical simulator compilation failed or compiler changed')
            executables[label]=str(executable)
        report.update(stage='public-wire',executables=executables);save()
        native_journal=out/'native.jsonl'
        with NativeAudit(native_journal,tools['vvp'],executables.values()) as audit:
            audit.scope='uart'
            report['uart']=run_uart_cases(tools['vvp'],executables['unchanged'],out/'uart',depth=2,
                mutant=executables['sampler-ff-pin'],mutation=mutation);save()
            write_durable(out/'uart/report.json',report['uart'])
            audit.scope='legacy'
            report['legacy']=run_legacy_durable(tools['vvp'],executables['unchanged'],out/'legacy',depth=2);save()
            audit.scope='i2c'
            report['i2c']=run_i2c_durable(tools['vvp'],executables['unchanged'],out/'i2c',depth=2);save()
            write_durable(out/'i2c/report.json',report['i2c'])
        report.update(native_runs=audit.records,native_journal=dict(path=str(native_journal),sha256=digest(native_journal)),
            physical_edges=sum(report[key]['physical_edges'] for key in ('uart','legacy','i2c')))
        report['traces']=validate_native(report,out,tools)
        unchanged();require(all(digest(path)==value for path,value in generated.items()),'Interpreted native source changed')
        after_identity=raw.tool_identity(h,tools,hardware)
        require(after_identity==identity,'Native/runtime identity changed during physical wire diagnostics')
        report.update(passed=True,stage='closed',tool_identity_after=after_identity,inputs_unchanged=True,
            generated_inputs_unchanged=True,all_actual_instances_retained=True,clock_contraction=False,
            physical_ff_bits=6039,actual_functional_instances=len(actual_inventory['instances']),
            positive_cases=35,actual_sampler_mutants=1,native_processes=14,
            artifact_sha256={str(path.relative_to(out)):digest(path) for path in sorted(out.rglob('*'))
                if path.is_file() and path!=report_path})
    except BaseException as error:
        report.update(passed=False,error=type(error).__name__+': '+str(error),traceback=traceback.format_exc());save();raise
    save();return report


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker-config',required=True);parser.add_argument('--worker-config-sha256',required=True)
    parser.add_argument('--out',required=True);args=parser.parse_args(argv)
    payload=regular(args.worker_config).read_bytes()
    require(sha256(payload).hexdigest()==args.worker_config_sha256,'Worker configuration differs from pre-spawn pin')
    config=read(args.worker_config)
    require(regular(args.worker_config).read_bytes()==payload,'Worker configuration changed while parsing')
    result=run_worker(config,args.out,config_path=regular(args.worker_config),config_sha256=args.worker_config_sha256)
    require(regular(args.worker_config).read_bytes()==payload,'Worker configuration changed during use')
    print(json.dumps({key:result[key] for key in ('passed','qualified','physical_edges','native_processes')},sort_keys=True))


if __name__=='__main__':main()
