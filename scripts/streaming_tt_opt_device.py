"""Whole-device substitution for the exact constant-specialized TT candidate.

This worker reconstructs package/pad functions from the actual assembled JSON,
not from the desired interface. The master still owns committed-archive and
tool/runtime qualification. The local manifest is never a qualification flag.
"""
from copy import deepcopy
from hashlib import sha256
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

from streaming_mapped_campaign import audit_source, read_json
from streaming_mapped_composition import generate as mapped_factory
from streaming_mapped_cost import measure
from streaming_mapped_device import JOIN_THEOREMS
from streaming_mapped_flow import quoted
from streaming_mapped_flow import state_inventory
from streaming_mapped_liberty import require, load_library
from streaming_mapped_netlist import parse_mapped
from streaming_mapped_uart_timing import generate as timing_factory, THEOREMS as TIMING_THEOREMS
from streaming_mapped_wrapper import (PADS, ENGINE, CUT_PREFIX, check_ports, complete_hierarchy,
    package_source, wrapper_source, prepare_wrapper, prepare_package)
from streaming_tt_optimize import canonical, produce
from streaming_tt_opt_proof import certify

SCHEMA='pinwheel.streaming-tt-optimized-device.v1'
TOP='tt_um_pinwheel_streaming_ready_d2'
PACKAGE='pinwheel_streaming_ready_quad_d2'
SESSION='StreamingOptimizedSessionD2'
NAMESPACE='Pinwheel.Artifact.'+SESSION


def digest(path): return sha256(Path(path).read_bytes()).hexdigest()


def regular_input(path):
    path=Path(path).absolute()
    require(path.is_file() and not path.is_symlink(),'Regular staged input required: '+str(path))
    return path.resolve()


def generate():
    """Same source/session proof bodies, actual optimized component imports."""
    source=mapped_factory(1)['StreamingMappedSessionD2']
    replacements={
        'MappedCoreD2Proof':'OptimizedCoreD2Proof', 'MappedFrontendProof':'OptimizedFrontendProof',
        'StreamingMappedPackageD2':'StreamingOptimizedPackageD2',
        'StreamingMappedTinyD2':'StreamingOptimizedTinyD2',
        'StreamingMappedSessionD2':SESSION,
        'Pinwheel.Artifact.StreamingMappedFrontend.':'Pinwheel.Artifact.StreamingOptimizedFrontend.',
        'Pinwheel.Artifact.StreamingMappedCoreD2.':'Pinwheel.Artifact.StreamingOptimizedCoreD2.'}
    for old,new in replacements.items():
        require(old in source,'Whole-device factory seam changed: '+old)
        source=source.replace(old,new)
    timing=timing_factory(1)['StreamingMappedUARTTimingD2'].replace('StreamingMappedSessionD2',SESSION)
    require('import MappedFrontend' not in source and 'import MappedCore' not in source and
        'StreamingMappedPackageD2' not in source and 'StreamingMappedTinyD2' not in source,
        'Whole-device factory retained a previous component certificate')
    return {SESSION:source,'StreamingOptimizedUARTTimingD2':timing}


def cut_outer(candidate,library):
    """Actual mapped outer wire cut; every residual gate is interpreted next."""
    require(TOP in candidate.get('modules',{}),'Missing actual candidate TT top')
    body=deepcopy(candidate['modules'][TOP])
    check_ports(body.get('ports'),PADS)
    require(not body.get('memories') and not body.get('processes') and
        not body.get('parameter_default_values'),'Behavioral outer boundary')
    children=[(name,cell) for name,cell in body.get('cells',{}).items() if cell.get('type')==PACKAGE]
    require(len(children)==1,'One actual engine package is required')
    instance,engine=children[0]
    require(engine.get('parameters')=={} and engine.get('port_directions')==
        {pin:shape[0] for pin,shape in ENGINE.items()},'Changed engine interface')
    check_ports({pin:dict(direction=engine['port_directions'][pin],bits=bits)
        for pin,bits in engine['connections'].items()},ENGINE)
    require(engine['connections']['clk']==body['ports']['clk']['bits'],'Engine clock is not direct top clk')
    del body['cells'][instance]
    require(all(cell.get('type') in library.cells and not library.cells[cell['type']].sequential
        for cell in body['cells'].values()),'Unexpected state or unknown outer logic')
    clock=body['ports'].pop('clk')
    for pin,bits in engine['connections'].items():
        if pin=='clk':continue
        name=CUT_PREFIX+pin
        require(name not in body['ports'],'Outer cut port collision')
        body['ports'][name]=dict(direction='output' if ENGINE[pin][0]=='input' else 'input',bits=bits)
    cut=dict(modules={TOP:body})
    graph=parse_mapped(cut,TOP,library,combinational=True)
    return cut,graph,dict(engine_instance=instance,clock=clock)


def semantic_q_map(candidate,library,inventories):
    """Bijection between typed register bits and actual complete candidate Qs.

    Names propose a pairing only. Inventory and whole component certificates
    separately check the actual Q/D/clock graph; the whole candidate is expanded
    again here, and every physical FF must occur exactly once in this table.
    """
    _,_,outer=cut_outer(candidate,library)
    graph=parse_mapped(candidate,TOP,library)
    actual={ff.name:ff for ff in graph.flipflops}
    rows=[]
    for label,child in [('frontend','frontend'),('core-d2','core')]:
        inventory=inventories[label]
        module=candidate['modules'][candidate['modules'][PACKAGE]['cells'][child]['type']]
        for value in inventory['registers']:
            local=json.loads(value['mapped_cell'])
            require(type(local) is list and len(local)==1 and type(local[0]) is str and
                type(value['index']) is int and value['index']>=0 and value['register'] in module['netnames'] and
                value['index']<len(module['netnames'][value['register']]['bits']) and
                module['netnames'][value['register']]['bits'][value['index']]==value['mapped_q'],
                'Malformed or relabeled semantic component FF path')
            component_cell=module['cells'][local[0]]
            require(component_cell['type'] in library.cells and library.cells[component_cell['type']].sequential and
                component_cell['connections']['Q']==[value['mapped_q']] and
                component_cell['connections']['D']==[value['mapped_d']],
                'Semantic component inventory differs from actual Q/D wiring')
            name=json.dumps([outer['engine_instance'],child,*local],separators=(',',':'))
            require(name in actual,'Actual complete candidate lost a declared semantic FF')
            ff=actual[name]
            rows.append(dict(component=label,register=value['register'],index=value['index'],
                source_q=value['source_q'],component_q=value['mapped_q'],component_d=value['mapped_d'],
                component_ff=value['mapped_cell'],candidate_ff=name,candidate_q=ff.q,candidate_d=ff.d,
                candidate_clock=ff.clock,candidate_cell=ff.cell))
    require(len(rows)==6039 and len({(r['component'],r['register'],r['index']) for r in rows})==6039 and
        len({r['candidate_q'] for r in rows})==6039 and {r['candidate_q'] for r in rows}==graph.state_bits and
        {r['candidate_ff'] for r in rows}==set(actual),'Candidate semantic Q map is not a full6039-bit bijection')
    return dict(schema='pinwheel.streaming-tt-semantic-q-map.v1',top=TOP,physical_ff_bits=6039,
        candidate_sha256=sha256((canonical(candidate)+'\n').encode()).hexdigest(),rows=rows)


def required_source():
    lines=['import '+SESSION,'import StreamingOptimizedUARTTimingD2',
        'open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady',
        'namespace Pinwheel.Artifact.StreamingOptimizedRequired',
        f'example : Package.Correct {NAMESPACE}.components := {NAMESPACE}.components_correct',
        f'example (s : Package.State 1) (i : TinyWiring.Pins) : {NAMESPACE}.physicalStep s i =',
        '    s.step (Package.Components.typed 1) (TinyWiring.Description.enginePins (TinyWiring.canonical 1) i) :=',
        f'  {NAMESPACE}.physical_step_correct s i',
        f'example (s : Package.State 1) (i : TinyWiring.Pins) (p : TinyWiring.Pad) : {NAMESPACE}.physicalObserve s i p =',
        '    TinyWiring.Description.pads (TinyWiring.canonical 1) i',
        '      (s.observe (Package.Components.typed 1) (TinyWiring.Description.enginePins (TinyWiring.canonical 1) i)) p :=',
        f'  {NAMESPACE}.physical_observe_correct s i p',
        f'example (s : Package.State 1) (inputs : List TinyWiring.Pins) : {NAMESPACE}.physicalRun s inputs =',
        '    s.run (Package.Components.typed 1) (inputs.map (TinyWiring.Description.enginePins (TinyWiring.canonical 1))) :=',
        f'  {NAMESPACE}.physical_run_correct s inputs']
    lines += ['#check '+NAMESPACE+'.'+name for name in (*JOIN_THEOREMS,*TIMING_THEOREMS)]
    return '\n'.join([*lines,'end Pinwheel.Artifact.StreamingOptimizedRequired',''])


def library_preflight_source():
    imports={name for text in generate().values() for name in
        re.findall(r'(?m)^import (Pinwheel\.[A-Za-z0-9_.]+)\s*$',text)}
    imports.update(('Pinwheel.Hardware.StreamingMapped.Ports','Pinwheel.Hardware.StreamingMapped.Word',
        'Pinwheel.Hardware.StreamingMapped.Ripple','Pinwheel.Hardware.StreamingMapped.Clauses',
        'Pinwheel.Hardware.StreamingMapped.TinyWiring','Pinwheel.Hardware.StreamingReady.Wiring'))
    return '\n'.join('import '+name for name in sorted(imports))+'\n'


def ordered_raw_sources(sources):
    """Order real generated dependencies independently of JSON key ordering."""
    require(type(sources) is dict and sources,'Missing actual raw proof source closure')
    texts={name:Path(path).read_text() for name,path in sources.items()}
    dependencies={name:{dep for dep in re.findall(r'(?m)^import ([A-Za-z0-9_.]+)\s*$',text)
        if dep in texts} for name,text in texts.items()}
    ordered={}
    while len(ordered)<len(sources):
        available=sorted(name for name,deps in dependencies.items() if name not in ordered and deps<=ordered.keys())
        require(available,'Cyclic supplied raw proof imports')
        for name in available:ordered[name]=sources[name]
    return ordered


def device_sources(candidate,library):
    cut,graph,boundary=cut_outer(candidate,library)
    package=dict(modules={PACKAGE:deepcopy(candidate['modules'][PACKAGE])})
    texts={
        'StreamingOptimizedPackageD2':package_source(package,PACKAGE,1,
            namespace='Pinwheel.Artifact.StreamingOptimizedPackageD2',netlist_sha256=sha256((canonical(package)+'\n').encode()).hexdigest()),
        'StreamingOptimizedTinyD2':wrapper_source(graph,1,namespace='Pinwheel.Artifact.StreamingOptimizedTinyD2',
            netlist_sha256=sha256((canonical(cut)+'\n').encode()).hexdigest())}
    texts.update(generate())
    texts['StreamingOptimizedRequired']=required_source()
    return texts,cut,package,boundary


def run_worker(config,out):
    """Fresh staged-input worker; master must independently seal provenance.

    Required config fields: source_commit, producer_commit, library, tools,
    components[frontend/core-d2] (the ordinary raw proof/source descriptors),
    device[2]{tiny,package}. Run from the selected source root after its complete
    library build/import preflight. No previous mapped artifact is consumed.
    """
    out=Path(out).resolve()
    require(not out.exists(),'Preserve an earlier optimized-device attempt')
    require(all(type(config.get(key)) is str and re.fullmatch('[0-9a-f]{40}',config[key])
        for key in ('source_commit','producer_commit')),'Exact source and producer identities required')
    require(config['source_commit']==config['producer_commit'],'Fresh candidate source and producer must match')
    require(set(config.get('components',{}))=={'frontend','core-d2'},'Exactly D2 and frontend inputs required')
    config=deepcopy(config)
    inputs=[config['library'],*config['tools'].values()]
    for component in config['components'].values():
        inputs.extend([component['raw_json'],component['sv'],*component['raw_sources'].values()])
    inputs.extend(config['device']['2'][key] for key in ('tiny','package'))
    for path in inputs:regular_input(path)
    out.mkdir(parents=True)
    native_executor=None
    if 'fresh_foundation' in config:
        from streaming_tt_fresh_foundation import FreshNativeExecutor
        native_executor=FreshNativeExecutor(config,out)
    report=dict(schema=SCHEMA,passed=False,qualified=False,source_commit=config['source_commit'],
        producer_commit=config['producer_commit'],stage='initialization',commands=[],components={})
    frozen={}
    def freeze(path):
        path=regular_input(path)
        value=digest(path);require(str(path) not in frozen or frozen[str(path)]==value,'Consumed input changed')
        frozen[str(path)]=value
    def save():
        (out/'report.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    def run(argv,log):
        log=Path(log);log.parent.mkdir(parents=True,exist_ok=True)
        report['commands'].append(dict(argv=list(map(str,argv)),log=str(log),status='running'));save()
        if native_executor is None:
            with log.open('w') as stream:
                result=subprocess.run(list(map(str,argv)),stdout=stream,stderr=subprocess.STDOUT,timeout=600)
        else:
            result=native_executor.run(argv,log,timeout=600)
            report['commands'][-1].update(argv=result.native_argv,native_journal_index=result.native_journal_index)
        report['commands'][-1].update(exit_code=result.returncode,status='completed',log_sha256=digest(log));save()
        require(result.returncode==0,'Native candidate operation failed: '+str(log))
        return log.read_text()
    start=time.monotonic();save()
    try:
        for path in [config['library'],*config['tools'].values()]:freeze(path)
        for cfg in config['components'].values():
            for path in [cfg['raw_json'],cfg['sv'],*cfg['raw_sources'].values()]:freeze(path)
        device=config['device']['2']
        for key in ('tiny','package'):freeze(device[key])
        for component in config['components'].values():
            component['raw_sources']=ordered_raw_sources(component['raw_sources'])
        report['stage']='fresh-library-preflight';save()
        run([config['tools']['lake'],'build','Pinwheel'],out/'library-build.log')
        preflight=out/'StreamingOptimizedLibraryImports.lean'
        preflight.write_text(library_preflight_source());freeze(preflight)
        run([config['tools']['lake'],'env','lean','--root='+str(out),'-DwarningAsError=true',preflight],
            out/'library-import-preflight.log')
        report['library_import_preflight']=dict(source=str(preflight),sha256=digest(preflight),passed=True)
        proof_paths=[];inventories={}
        for label,top in [('frontend','pinwheel_streaming_quad_frontend'),('core-d2','pinwheel_streaming_ready_core_d2')]:
            report['stage']='component-'+label;save()
            cfg=config['components'][label];directory=out/label
            mapping=produce(cfg['raw_json'],top,config['library'],config['tools']['yosys'],config['tools']['abc'],directory,
                **({'native_executor':native_executor} if native_executor is not None else {}))
            proof=out/(label+'-proof')
            result=certify(label,directory,config,proof,
                **({'native_executor':native_executor} if native_executor is not None else {}))
            require(result.get('passed') is True,'Component kernel proof did not close')
            proof_paths.append(proof)
            inventories[label]=state_inventory(read_json(cfg['raw_json']),read_json(directory/'mapped.json'),
                top,load_library(config['library']))
            require(inventories[label]==read_json(directory/'state-inventory.json'),
                'Retained semantic state inventory differs from independent recomputation')
            for generated in [*directory.rglob('*'),*proof.rglob('*')]:
                if generated.is_file():freeze(generated)
            report['components'][label]=dict(mapping_report=str(directory/'report.json'),proof_report=str(proof/'report.json'),
                mapped_json=str(directory/'mapped.json'),mapping=mapping,proof=result);save()
        report['stage']='actual-wrapper';save()
        outer=prepare_wrapper(out/'outer',addr_bits=1,tiny=device['tiny'],package=device['package'],
            liberty=config['library'],yosys=config['tools']['yosys'],abc=config['tools']['abc'],run=run)
        package=prepare_package(out/'package',addr_bits=1,package=device['package'],
            frontend=config['components']['frontend']['sv'],core=config['components']['core-d2']['sv'],
            yosys=config['tools']['yosys'],run=run)
        library=load_library(config['library'])
        candidate=complete_hierarchy(read_json(outer['restored_json']),read_json(package['package_json']),
            read_json(out/'core-d2/mapped.json'),read_json(out/'frontend/mapped.json'),addr_bits=1,library=library)
        full=out/'candidate.json';full.write_text(canonical(candidate)+'\n');freeze(full)
        cost=measure(full,TOP,config['library'],6039,complete=True)
        (out/'cost.json').write_text(json.dumps(cost,sort_keys=True,indent=2)+'\n')
        qmap=semantic_q_map(candidate,library,inventories)
        (out/'semantic-q-map.json').write_text(canonical(qmap)+'\n')
        texts,cut,actual_package,boundary=device_sources(candidate,library)
        (out/'actual-outer-cut.json').write_text(canonical(cut)+'\n')
        (out/'actual-package.json').write_text(canonical(actual_package)+'\n')
        report.update(stage='device-kernel',outer=outer,package=package,cost=cost,boundary=boundary);save()
        proof=out/'device-proof';proof.mkdir()
        imports=[]
        for label in ('frontend','core-d2'):
            imports.extend(value['module'] for value in report['components'][label]['proof']['modules'])
        imports=list(dict.fromkeys([*imports,*texts]))
        report['audit_owner_modules']=imports
        texts['StreamingOptimizedAudit']=audit_source(imports)
        lean_path=':'.join(map(str,[proof,*proof_paths,Path('.lake/build/lib/lean').resolve()]))
        env=dict(os.environ,LEAN_PATH=lean_path)
        for name,text in texts.items():
            path=proof/(name+'.lean');path.write_text(text);freeze(path)
            argv=[config['tools']['lean'],'--root='+str(proof),'-DwarningAsError=true','-o',str(proof/(name+'.olean')),str(path)]
            report['commands'].append(dict(argv=argv,log=str(proof/(name+'.log')),status='running'));save()
            if native_executor is None:
                with (proof/(name+'.log')).open('w') as stream:
                    native=subprocess.run(argv,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=600)
            else:
                native=native_executor.run(['env','LEAN_PATH=' + ':'.join(map(str,[proof,*proof_paths])),*argv],
                    proof/(name+'.log'),timeout=600)
                report['commands'][-1].update(argv=native.native_argv,native_journal_index=native.native_journal_index)
            report['commands'][-1].update(exit_code=native.returncode,status='completed',log_sha256=digest(proof/(name+'.log')));save()
            require(native.returncode==0,'Whole-device kernel proof failed: '+name)
        script=out/'emit.ys';script.write_text('\n'.join(['read_json '+quoted(full),
            'read_liberty -lib '+quoted(config['library']),'hierarchy -check -top '+TOP,
            'check -assert','write_verilog -noattr -noexpr '+quoted(out/'candidate.sv')])+'\n');freeze(script)
        run([config['tools']['yosys'],'-Q','-T','-s',script],out/'emit.log')
        require(all(digest(path)==value for path,value in frozen.items()),'Candidate inputs changed at closeout')
        if native_executor is not None:
            report.update(fresh_foundation=config['fresh_foundation'],fresh_optimized_native=native_executor.closeout())
        report.update(passed=True,stage='complete',physical_ff_bits=6039,all_state_device_kernel_join=True,
            api_qnames=[NAMESPACE+'.'+name for name in (*JOIN_THEOREMS,*TIMING_THEOREMS)],
            elapsed_seconds=time.monotonic()-start,input_sha256=frozen,
            boundary='Native kernel whole-device result. The external master must independently prove committed source/producer/archive/runtime membership; no routed or timing qualification follows.')
        report['artifact_sha256']={str(path.resolve()):digest(path) for path in out.rglob('*')
            if path.is_file() and path!=out/'report.json'}
        save();return report
    except BaseException as error:
        report.update(passed=False,error=type(error).__name__+': '+str(error),elapsed_seconds=time.monotonic()-start)
        save();raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker-config',required=True)
    parser.add_argument('--worker-config-sha256',required=True)
    args=parser.parse_args()
    path=Path(args.worker_config)
    require(path.is_file() and not path.is_symlink(),'Regular worker configuration required')
    payload=path.read_bytes()
    require(re.fullmatch('[0-9a-f]{64}',args.worker_config_sha256) and
        sha256(payload).hexdigest()==args.worker_config_sha256,'Worker configuration bytes differ before use')
    def pairs(items):
        result={}
        for key,value in items:
            require(key not in result,'Duplicate worker configuration key')
            result[key]=value
        return result
    config=json.loads(payload,object_pairs_hook=pairs)
    require(Path(config['root']).resolve()==Path.cwd().resolve(),'Run from the selected current source archive')
    report=run_worker(config,config['worker_out'])
    require(path.read_bytes()==payload,'Worker configuration changed during execution')
    print(json.dumps(dict(passed=report['passed'],source_commit=report['source_commit'],
        report=str(Path(config['worker_out'])/'report.json')),sort_keys=True))


if __name__=='__main__':main()
