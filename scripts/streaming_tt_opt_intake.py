"""Independent parent intake for bounded optimized-candidate CAD measurements.

Recheck committed source archives, raw correspondence, native tools, generated
proof sources, the complete state map and a fresh SV reimport. This permits
diagnostic CAD only; final frozen Lean replay and post-PNR proof remain gates.
"""
from copy import deepcopy
from collections import Counter
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import time

from streaming_tt_signoff import read, regular, require, sha, unchanged, write
from validation_run import fresh_directory
import streaming_clean_source as clean_source

ROOT=Path(__file__).resolve().parents[1]
BASELINE='787260b07c7dffc06799feeee6fd604e0b290fe7'


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


def artifacts(directory,exclude=(),*,absolute=False):
    directory=Path(directory).resolve();result={}
    for path in sorted(directory.rglob('*')):
        require(not path.is_symlink(),'Aliased parent-intake artifact')
        if path.is_file() and path not in exclude:
            result[str(path if absolute else path.relative_to(directory))]=sha(path)
    return result


def archive_membership(path,expected):
    actual={}
    with tarfile.open(regular(path)) as archive:
        for member in archive:
            relative=Path(member.name)
            require(not relative.is_absolute() and '..' not in relative.parts,'Escaping source archive')
            if member.isdir():continue
            require(member.isfile() and member.name not in actual,'Aliased/duplicate source archive member')
            actual[member.name]=hashlib.sha256(archive.extractfile(member).read()).hexdigest()
    require(actual==expected,'Source archive membership differs from committed files')


def named_connectivity(graph):
    """Exact structural identity independent of importer numeric wire IDs."""
    drivers={}
    def add(wire,identity):
        require(type(wire) is int and wire not in drivers,'Ambiguous named connectivity driver')
        drivers[wire]=identity
    for name,bits in graph.inputs.items():
        for index,wire in enumerate(bits):add(wire,('input',name,index))
    for ff in graph.flipflops:add(ff.q,('ff',ff.name,'Q'))
    for gate in graph.gates:add(gate.output,('gate',gate.name,graph.library.cells[gate.cell].output))
    def wire(value):
        if type(value) is str:
            require(value in ('0','1'),'Unknown named connectivity literal')
            return ('literal',value)
        require(value in drivers,'Undriven named connectivity wire')
        return drivers[value]
    return dict(inputs={name:len(bits) for name,bits in graph.inputs.items()},
        outputs={name:[wire(value) for value in bits] for name,bits in graph.outputs.items()},
        flops={ff.name:dict(cell=ff.cell,d=wire(ff.d),q=wire(ff.q),clock=wire(ff.clock),reset=ff.reset_b)
            for ff in graph.flipflops},
        gates={gate.name:dict(cell=gate.cell,pins={pin:wire(value) for pin,value in gate.connections.items()})
            for gate in graph.gates})


def structural_connectivity(graph,state_labels,pool):
    """Exact shared tuples; auto names/numeric IDs supply no equivalence.

    The independent semantic Q map binds every state leaf. Interning uses full
    Python tuple equality, so there is no digest-only cone comparison. Actual
    cell/pin structures are counted, including gates outside public D cones.
    """
    require(set(state_labels)==graph.state_bits and len(set(state_labels.values()))==len(state_labels),
        'Incomplete/aliased structural state binding')
    def intern(key):
        if key not in pool:pool[key]=len(pool)
        return pool[key]
    values={}
    for name,bits in graph.inputs.items():
        for index,bit in enumerate(bits):values[bit]=intern(('input',name,index))
    for bit,label in state_labels.items():values[bit]=intern(('state',*label))
    def wire(bit):
        if type(bit) is str:return intern(('literal',bit))
        require(bit in values,'Missing topological structural driver')
        return values[bit]
    cells=Counter()
    for gate in graph.gates:
        model=graph.library.cells[gate.cell]
        key=('cell',gate.cell,model.output,tuple((pin,wire(gate.connections[pin]))
            for pin in sorted(model.directions) if model.directions[pin]=='input'))
        identity=intern(key);values[gate.output]=identity;cells[identity]+=1
    return dict(inputs={name:len(bits) for name,bits in graph.inputs.items()},cells=cells,
        flops={state_labels[ff.q]:dict(cell=ff.cell,d=wire(ff.d),clock=wire(ff.clock),reset=ff.reset_b)
            for ff in graph.flipflops},outputs={name:tuple(wire(bit) for bit in bits) for name,bits in graph.outputs.items()})


def q_labels(qmap):
    return {row['candidate_q']:(row['component'],row['register'],row['index']) for row in qmap['rows']}


def restore_port_order(candidate,outer,top):
    """Recover generator iteration order from the actual sealed outer graph.

    Canonical JSON sorts keys; the worker generated independent definitions
    before that serialization. Values and complete membership must agree.
    """
    ports=candidate['modules'][top]['ports'];original=outer['modules'][top]['ports']
    require(ports==original,'Actual outer port values differ from candidate')
    require(candidate['modules'][top]==outer['modules'][top],
        'Actual complete outer module differs from candidate')
    ordered=deepcopy(candidate)
    # The cut also iterates actual child connection dictionaries. Restore all
    # nested insertion orders only after exact complete module equality.
    ordered['modules'][top]=deepcopy(outer['modules'][top])
    return ordered


def validate_raw(raw_path,source_commit, *, source_mode='historical'):
    raw_path=regular(raw_path);directory=raw_path.parent
    report=read(raw_path);config=read(directory/'worker-config.json')
    require(report.get('passed') is True and report.get('stage')=='components' and
        report.get('source_commit')==report.get('producer_commit')==source_commit,
        'Raw source gate has not closed at the selected commit')
    require(source_mode in ('historical','clean-v1'), 'Unknown raw source admission mode')
    if source_mode == 'historical':
        require(subprocess.run(['git','merge-base','--is-ancestor',BASELINE,source_commit],cwd=ROOT).returncode==0,
            'Raw source is outside the approved campaign lineage')
    else:
        clean_source.admit(ROOT, source_commit)
    h=load('_streaming_tt_intake_archive',ROOT/'scripts/check-buffered-rtl-sim.py')
    gate=load('_streaming_tt_intake_raw_gate',ROOT/'scripts/check-streaming-uart.py')
    algorithm=subprocess.check_output(['git','rev-parse','--show-object-format'],cwd=ROOT,text=True).strip()
    tree=h.parse_tree(subprocess.check_output(['git','ls-tree','-r','-z',source_commit],cwd=ROOT,text=True))
    require(config['source_tree']==tree and config['object_format']==algorithm,'Wrong selected source Git inventory')
    snapshot=Path(config['snapshot']).resolve()
    actual=h.membership(snapshot,tree,algorithm)
    require(actual==report['source_sha256']==config['source_sha256'],'Raw source archive bytes changed')
    producer_tree={name:tree[name] for name in gate.PRODUCER}
    require(config['producer_tree']==producer_tree and
        h.membership(directory/'producer',producer_tree,algorithm)==report['producer_sha256']==config['producer_sha256'],
        'Raw producer archive bytes changed')
    archive_membership(directory/'selected-source.tar',actual)
    archive_membership(directory/'producer-source.tar',report['producer_sha256'])
    gate.archive_closeout(h,directory,report)
    require(sha(directory/'worker-config.json')==report['worker_config_sha256_before_use'],
        'Raw worker configuration changed')
    child_path=directory/'worker/worker-report.json';child=read(child_path)
    require(sha(child_path)==report['worker_report_sha256'] and child==report['worker'],'Raw child receipt changed')
    gate.validate_worker(child,config,closeout=True)
    require(artifacts(child_path.parent,exclude=(child_path,))==child['artifact_sha256'],'Raw artifact tree changed')
    require(report.get('committed_archive_membership_verified_before') is True and
        report.get('committed_archive_membership_verified_after') is True and
        report['tool_identity_before']==report['tool_identity_after']==config['tool_identity'] and
        gate.tool_identity(h,report['tool_paths'],read(snapshot/'tools/hardware-toolchain.json'))==config['tool_identity'],
        'Raw runtime/source identity did not close')
    if any('fresh_foundation' in value for value in (report, config, child)):
        from streaming_tt_fresh_foundation import validate_raw_binding
        validate_raw_binding(report, config, child, ROOT)
    if source_mode == 'clean-v1':
        clean_source.admit(ROOT, source_commit, actual)
    return report,config,child,snapshot,actual


def regenerated_sources(config,worker,out):
    """Regenerate every positive interpreted source without editing its receipt."""
    from streaming_tt_opt_proof import generate_words,generate_joins
    from streaming_tt_opt_device import device_sources,ordered_raw_sources,TOP
    from streaming_mapped_campaign import required_source,audit_source
    from streaming_mapped_liberty import load_library
    import streaming_ready_readback
    library=load_library(config['library']);modules=[];identities={}
    for label,suffix in [('frontend','Frontend'),('core-d2','CoreD2')]:
        cfg=config['components'][label];prefix='Optimized'+suffix;namespace='Pinwheel.Artifact.StreamingOptimized'+suffix
        directory=out/label;proof=out/(label+'-proof')
        texts,specs=generate_words(directory/'mapped.json',read(directory/'words.json'),library,prefix=prefix,namespace=namespace)
        texts.update({name:Path(path).read_text() for name,path in ordered_raw_sources(cfg['raw_sources']).items()})
        rb=streaming_ready_readback.backend('frontend' if label=='frontend' else 'core',1)
        joins,_=generate_joins(rb,cfg['raw_json'],directory/'mapped.json',library,specs,namespace=namespace,
            raw_module=cfg['raw_module'],raw_namespace=cfg['raw_namespace'],prefix=prefix)
        texts.update(joins);texts[prefix+'Required']=required_source(rb,next(reversed(joins)),namespace)
        texts[prefix+'Audit']=audit_source(list(texts))
        records=worker['components'][label]['proof']['modules']
        require([row['module'] for row in records]==list(texts),'Component native module order differs')
        for name,text in texts.items():
            path=proof/(name+'.lean')
            require(regular(path).read_text()==text,'Regenerated component proof differs: '+name)
            require(next(row for row in records if row['module']==name)['source_sha256']==sha(path),
                'Native component source record differs: '+name)
            identities[str(path)]=sha(path);modules.append(dict(module=name,path=str(path),sha256=sha(path)))
    candidate=restore_port_order(read(out/'candidate.json'),read(worker['outer']['restored_json']),TOP)
    texts,_,_,_=device_sources(candidate,library)
    owners=list(dict.fromkeys([row['module'] for row in modules]+list(texts)))
    require(worker['audit_owner_modules']==owners,'Whole-device audit omits generated owner modules')
    texts['StreamingOptimizedAudit']=audit_source(owners)
    for name,text in texts.items():
        path=out/'device-proof'/(name+'.lean')
        require(regular(path).read_text()==text,'Regenerated device proof differs: '+name)
        identities[str(path)]=sha(path);modules.append(dict(module=name,path=str(path),sha256=sha(path)))
    return modules,identities


def issue(raw_path,worker_config_path,worker_path,tag, *, source_mode='historical'):
    raw_path=regular(raw_path)
    worker_config_path=regular(worker_config_path);worker_path=regular(worker_path)
    config=read(worker_config_path);worker=read(worker_path);out=worker_path.parent
    commit=config['source_commit']
    require(re.fullmatch('[0-9a-f]{40}',commit) and config['producer_commit']==commit,
        'Exact identical selected source/producer commits required')
    raw,raw_config,raw_child,snapshot,source_hashes=validate_raw(raw_path,commit,source_mode=source_mode)
    source_identity = (clean_source.admit(ROOT, commit, source_hashes) if source_mode == 'clean-v1' else None)
    require(Path(config['root']).resolve()==snapshot and Path(config['worker_out']).resolve()==out and
        {'yosys','abc','lean','lake'}<=set(config['tools']) and
        all(raw['tool_paths'].get(name)==path for name,path in config['tools'].items()),
        'Optimized worker escapes its fresh raw source/runtime')
    # Every interpreter used below must be the actual committed generator.
    names=set(p.name for p in (ROOT/'scripts').glob('streaming_mapped_*.py'))
    names.update(p.name for p in (ROOT/'scripts').glob('streaming_ready*.py'))
    names.update(('streaming_tt_optimize.py','streaming_tt_opt_certificate.py','streaming_tt_opt_proof.py','streaming_tt_opt_device.py'))
    for name in names:
        relative='scripts/'+name
        require(relative in source_hashes and sha(ROOT/relative)==source_hashes[relative],
            'Intake interpreter differs from candidate producer: '+relative)
    require(worker.get('schema')=='pinwheel.streaming-tt-optimized-device.v1' and worker.get('passed') is True and
        worker.get('qualified') is False and worker.get('stage')=='complete' and
        worker.get('all_state_device_kernel_join') is True and worker.get('physical_ff_bits')==6039 and
        worker.get('source_commit')==worker.get('producer_commit')==commit,'Optimized whole-device kernel join incomplete')
    require(artifacts(out,exclude=(worker_path,),absolute=True)==worker['artifact_sha256'],'Optimized artifact tree changed')
    unchanged(worker['input_sha256'])
    require(worker.get('commands') and all(row.get('status')=='completed' and row.get('exit_code')==0
        for row in worker['commands']),'Incomplete optimized native operation')
    for row in worker['commands']:require(sha(regular(row['log']))==row['log_sha256'],'Native log differs')
    modules,generated=regenerated_sources(config,worker,out)
    if any('fresh_foundation' in value for value in (raw_config, config, worker)):
        from streaming_tt_fresh_foundation import validate_optimized_native
        validate_optimized_native(raw_config, config, worker, out)
    from streaming_tt_opt_device import TOP,semantic_q_map,NAMESPACE
    from streaming_mapped_device import JOIN_THEOREMS
    from streaming_mapped_uart_timing import THEOREMS
    from streaming_mapped_flow import state_inventory,quoted
    from streaming_mapped_liberty import load_library,LIBRARY_SHA256
    from streaming_mapped_netlist import parse_mapped
    from streaming_mapped_cost import measure
    library=load_library(config['library'])
    require(sha(config['library'])==LIBRARY_SHA256,'Candidate Liberty differs from pinned function model')
    candidate=read(out/'candidate.json');inventories={}
    for label,top in [('frontend','pinwheel_streaming_quad_frontend'),('core-d2','pinwheel_streaming_ready_core_d2')]:
        cfg=config['components'][label]
        for path in (cfg['raw_json'],cfg['sv'],*cfg['raw_sources'].values()):
            path=regular(path);relative=str(path.relative_to(Path(raw_path).parent/'worker'))
            require(raw_child['artifact_sha256'].get(relative)==sha(path),'Optimized raw input is outside accepted raw artifacts')
        inventories[label]=state_inventory(read(cfg['raw_json']),read(out/label/'mapped.json'),top,library)
        proof=worker['components'][label]['proof']
        require(proof.get('passed') is True and proof.get('all_state_kernel_join') is True and
            proof.get('strict_private_axiom_audit') is True and proof.get('inputs_unchanged') is True and
            all(row.get('exit_code')==0 for row in proof['modules']),'Incomplete native component kernel join')
    original_qmap=semantic_q_map(candidate,library,inventories)
    require(original_qmap==read(out/'semantic-q-map.json'),'Independent semantic state map differs')
    cost=measure(out/'candidate.json',TOP,config['library'],6039,complete=True)
    require(cost==read(out/'cost.json')==worker['cost'],'Independent complete candidate cost differs')
    require(worker['api_qnames']==[NAMESPACE+'.'+name for name in (*JOIN_THEOREMS,*THEOREMS)],'Missing required device APIs')
    for label in ('frontend-proof','core-d2-proof','device-proof'):
        logs=list((out/label).glob('*Audit.log'))
        require(len(logs)==1 and len(re.findall(r'Mapped audit: [1-9][0-9]* declarations, [1-9][0-9]* theorems; standard axioms only\.',logs[0].read_text()))==1,
            'Missing unambiguous private-declaration audit')
    parent=fresh_directory(ROOT/'build/streaming-tt-optimization','parent-intake-'+tag).resolve()
    report=dict(schema='pinwheel.streaming-tt-optimized-intake.v1',purpose='bounded_physical_measurement',
        passed=False,qualified=False,physical_acceptance_claim=False,source_commit=commit,producer_commit=commit,
        parent_source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        worker_report=dict(path=str(worker_path),sha256=sha(worker_path)),
        worker_config=dict(path=str(worker_config_path),sha256=sha(worker_config_path)),
        raw_gate_report=dict(path=str(Path(raw_path).resolve()),sha256=sha(raw_path)),
        frozen_lean_replay=dict(status='pending',path=None,sha256=None),generated_module_count=len(modules),
        generated_sources_sha256=generated,checked={},artifacts={})
    if source_identity is not None:
        report['source_admission'] = source_identity
    write(parent/'report.json',report)
    # Reimport the exact physical SV. The writer may rename $auto cells/wires.
    # Reconstruct actual register-index Q bindings and compare all cell/pin
    # structures, every D root and every output. No optimization/SAT is used.
    script=parent/'reimport.ys';imported=parent/'reimport.json'
    script.write_text('\n'.join(('read_liberty -lib '+quoted(config['library']),
        'read_verilog -sv '+quoted(out/'candidate.sv'),'hierarchy -check -top '+TOP,
        'check -assert','write_json '+quoted(imported)))+'\n')
    frozen={str(path):sha(path) for path in (out/'candidate.sv',out/'candidate.json',script,
        Path(config['library']),Path(config['tools']['yosys']),worker_config_path,worker_path)}
    command=[config['tools']['yosys'],'-Q','-T','-s',str(script)]
    report.update(native_reimport=dict(argv=command,status='intent',input_sha256_before=frozen));write(parent/'report.json',report)
    with (parent/'reimport.log').open('w') as log:
        process=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=180)
    report['native_reimport'].update(status='completed',exit_code=process.returncode,log_sha256=sha(parent/'reimport.log'))
    write(parent/'report.json',report)
    require(process.returncode==0,'Native SV reimport failed')
    reimported=read(imported);new_inventories={}
    for label,top in [('frontend','pinwheel_streaming_quad_frontend'),('core-d2','pinwheel_streaming_ready_core_d2')]:
        new_inventories[label]=state_inventory(read(config['components'][label]['raw_json']),reimported,top,library)
    reimported_qmap=semantic_q_map(reimported,library,new_inventories)
    pool={}
    original_structure=structural_connectivity(parse_mapped(candidate,TOP,library),q_labels(original_qmap),pool)
    imported_structure=structural_connectivity(parse_mapped(reimported,TOP,library),q_labels(reimported_qmap),pool)
    require(original_structure==imported_structure,
        'Physical SV differs from the kernel-interpreted complete JSON')
    write(parent/'reimport-semantic-q-map.json',reimported_qmap)
    report['native_reimport'].update(exact_tuple_interning=True,all_actual_cell_pin_structures_compared=True,
        all_ff_d_and_public_outputs_compared=True,semantic_ff_bits=6039,structural_nodes=len(pool),
        semantic_q_map_sha256=sha(parent/'reimport-semantic-q-map.json'))
    unchanged(frozen)
    for key,name in [('candidate_json','candidate.json'),('candidate_sv','candidate.sv'),
            ('semantic_q_map','semantic-q-map.json'),('cost','cost.json')]:
        report['artifacts'][key]=dict(path=str(out/name),sha256=sha(out/name))
    if source_identity is not None:
        require(clean_source.admit(ROOT, commit, source_hashes) == source_identity, 'Clean source changed during intake')
    report.update(passed=True,checked={name:True for name in ('fresh_raw_source_gate','archive_membership',
        'worker_kernel_join','private_axiom_audit','tool_identity','input_closeout','semantic_ff_bijection',
        'independent_proof_source_regeneration','physical_sv_reimport')},cost=cost,
        execution_limit='Diagnostic CAD through post-global-route STA only; detailed route needs new parent admission.')
    write(parent/'report.json',report);write(parent/'native-replay-plan.json',dict(modules=modules,source_commit=commit))
    print(parent/'report.json',flush=True)
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('raw-gate','worker-config','worker-report','tag'):parser.add_argument('--'+name,required=True)
    parser.add_argument('--source-mode', choices=('historical','clean-v1'), default='historical')
    args=parser.parse_args()
    require(regular(__file__).read_bytes()==subprocess.check_output(['git','show','HEAD:scripts/streaming_tt_opt_intake.py'],cwd=ROOT),
        'Commit the parent intake producer before use')
    issue(args.raw_gate,args.worker_config,args.worker_report,args.tag,source_mode=args.source_mode)


if __name__=='__main__':main()
