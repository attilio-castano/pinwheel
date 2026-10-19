#!/usr/bin/env python3
"""Bind a closed final checkpoint's actual FFs to original source semantics.

The original admitted source and actual derivative database have separate
provenance. A name/function/pin mapping witness does not prove transitions.
"""
import argparse
import hashlib
import importlib.util
from pathlib import Path
import re
import subprocess

import streaming_tt_wire_binding as W

P=W.P
ENTRIES=('scripts/streaming_tt_wire_binding_final.py','scripts/streaming_tt_export_odb.py')


def wire_api():
    spec=importlib.util.spec_from_file_location('_streaming_tt_final_binding_wire',Path(__file__).with_name('run-streaming-tt-wire.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def checkpoint_api():
    spec=importlib.util.spec_from_file_location('_streaming_tt_final_binding_checkpoint',Path(__file__).with_name('run-streaming-tt-sta.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def source_selection(metadata,explicit):
    if 'transformation' in metadata:
        change=metadata['transformation']
        P.require(type(change) is dict and change.get('schema')=='pinwheel.streaming-tt-fanout-derivative.v1',
            'Unknown final transformation/source-selection contract')
        source=W.F.bound(change['source_readback_host'])
        P.require(explicit is None or P.regular(explicit).resolve()==source,'Explicit source export differs from frozen fanout lineage')
        return source
    P.require(explicit is not None,'Ordinary detailed routing requires an independent --source-export-host')
    return P.regular(explicit).resolve()


def derivative(report,metadata,*,admission_path,admission_sha256,source_commit,source_odb_sha256,initial_snapshot_sha256=None):
    code=report.get('exit_code');status=report.get('status');change=metadata.get('transformation',{})
    P.require(report.get('schema')=='pinwheel.streaming-tt-final-run.v1' and type(code) is int and
        ((status=='flow_completed' and code==0) or (status in ('failed','timed_out') and code!=0)) and
        report.get('inputs_unchanged_after_run') is True and report.get('container_termination',{}).get('status')=='absent',
        'Actual derivative producer is not terminal and closed')
    P.require(metadata.get('schema')=='pinwheel.streaming-tt-final-input.v1' and
        P.regular(metadata['admission']).resolve()==P.regular(admission_path).resolve() and
        metadata.get('admission_sha256')==admission_sha256 and
        report.get('source_commit')==metadata.get('source_commit')==source_commit and
        report.get('producer_commit')==metadata.get('producer_commit'),
        'Actual derivative differs from the original admitted source/physical lineage')
    if 'transformation' in metadata:
        P.require(type(change) is dict and change.get('schema')=='pinwheel.streaming-tt-fanout-derivative.v1' and
            change.get('source_odb_sha256')==source_odb_sha256 and change.get('inherited_metrics') is False and
            change.get('inherited_parasitics') is False,'Unknown or changed fanout source/seed lineage')
        return 'admitted-fanout-derivative'
    P.require(initial_snapshot_sha256==source_odb_sha256 and type(source_odb_sha256) is str and
        report.get('from_step')=='OpenROAD.DetailedRouting' and report.get('stop_step')==W.F.TAIL[-1],
        'Ordinary detailed route lost its exact original initial ODB or native range')
    W.F.validate_order(report.get('native_step_ids'))
    command=report.get('command');P.require(type(command) is list and command.count('python3')==1,
        'Ordinary final producer lacks its actual native flow CLI')
    expected=['python3','-B','-m','librelane','--manual-pdk','--pdk-root','/work/pdk','--pdk','ihp-sg13cmos5l',
        '--jobs','4','--run-tag',metadata['tag'],'--force-run-dir','/work/run',
        '--with-initial-state','/work/inputs/seed.json','--from','OpenROAD.DetailedRouting',
        '--to',W.F.TAIL[-1],'/work/inputs/core.json']
    P.require(command[command.index('python3'):]==expected,'Ordinary native flow changed its exact initial seed/config/range')
    return 'admitted-detailed-routing'


def initial_snapshot(metadata,root):
    root=Path(root).resolve();frozen={}
    P.require({str(path.relative_to(root)) for path in root.rglob('*') if path.is_file()}==set(metadata['input_sha256']),
        'Final prepared input membership differs from its complete frozen inventory')
    for name,value in metadata['input_sha256'].items():
        path=P.regular(root/P.relative_path(name)).resolve()
        P.require(path.is_relative_to(root) and P.sha(path)==value,'Final frozen metadata/checkpoint input changed')
        frozen[str(path)]=value
    snapshot=root/'producer'
    P.require(W.F.dependency_closure(snapshot,list(metadata['producer_sha256']))==metadata['producer_dependency_closure'],
        'Final frozen producer dependency closure differs')
    for name,value in metadata['producer_sha256'].items():
        path=P.regular(snapshot/P.relative_path(name));content=subprocess.check_output(
            ['git','show',metadata['producer_commit']+':'+name],cwd=P.ROOT,timeout=30)
        P.require(P.sha(path)==hashlib.sha256(content).hexdigest()==value,'Final producer snapshot differs from committed native source')
    seed_path=P.regular(root/'seed.json');seed=checkpoint_api().read_checkpoint(seed_path,producer=False)
    native=seed.get('odb');P.require(type(native) is str and native.startswith('/work/inputs/checkpoint/') and
        metadata.get('authoritative_odb')==native,'Final native initial seed lost the exact checkpoint ODB')
    path=P.regular(root/P.relative_path(native.removeprefix('/work/inputs/'))).resolve()
    P.require(path.is_relative_to(root/'checkpoint') and frozen.get(str(path))==P.sha(path),'Final initial ODB differs from frozen checkpoint map')
    return path,frozen


def latest(report,state,root):
    root=Path(root).resolve();ordered=[]
    for row in report.get('states',[]):
        path=P.regular(row['state']).resolve();P.require(path.is_relative_to(root) and row['state_sha256']==P.sha(path),
            'Changed final recorded state')
        key=tuple(int(match[1]) for part in path.relative_to(root).parts[:-1] if (match:=re.fullmatch(r'(\d+)-.+',part)))
        P.require(key,'Final state lacks native ordinal');ordered.append((key,path))
    P.require(ordered and len({key for key,path in ordered})==len(ordered) and
        max(ordered)[1]==P.regular(state).resolve(),'Final wire binder requires the latest actual closed state')


def run(admission,admission_sha256,physical_report,state,export_host,out,source_export_host=None):
    closure=W.dependency_closure(P.ROOT,ENTRIES)
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip()
    producer={name:hashlib.sha256(P.committed(P.ROOT/name)).hexdigest() for name in closure['files']}
    admitted,entries,design=W.F.admission(admission,admission_sha256)
    wire,checkpoint=wire_api(),checkpoint_api()
    physical_report,state,export_host=[P.regular(path).resolve() for path in (physical_report,state,export_host)]
    actual,roots,database,reference,export,frozen=wire.actual_export(export_host,physical_report=physical_report,
        state=state,checkpoint_host=checkpoint,exporter_sha256=producer['scripts/streaming_tt_export_odb.py'])
    for path in (state,database):
        P.require(actual.get('artifact_sha256',{}).get(str(path.relative_to(physical_report.parent)))==P.sha(path),
            'Final wire input differs from actual closed producer artifact membership')
    latest(actual,state,roots['/work/run'])
    metadata_path=physical_report.parent/'inputs.json';metadata=P.read(metadata_path)
    source_host=source_selection(metadata,source_export_host)
    _,_,source_database,_,_,source_frozen=wire.actual_export(source_host,physical_report=entries['coarse_report'],
        state=entries['state'],checkpoint_host=checkpoint,exporter_sha256=producer['scripts/streaming_tt_export_odb.py'])
    initial=None
    if 'transformation' not in metadata:
        initial,prepared_frozen=initial_snapshot(metadata,roots['/work/inputs']);frozen.update(prepared_frozen)
    kind=derivative(actual,metadata,admission_path=admission,admission_sha256=admission_sha256,
        source_commit=admitted['source_commit'],source_odb_sha256=P.sha(source_database),
        initial_snapshot_sha256=None if initial is None else P.sha(initial))
    frozen.update(source_frozen)
    parent=P.read(entries['parent_intake']);prepared=P.read(entries['prepared_input'])
    candidate=entries['candidate_json'];source_qmap=W.F.bound(parent['artifacts']['semantic_q_map'])
    P.require(W.F.bound(parent['artifacts']['candidate_json'])==candidate,'Original source candidate identity differs')
    flat=design/'inputs/physical-verilog/flat-reimport.json';flatmap=flat.with_name('flat-reimport-semantic-q-map.json')
    library_path=P.regular(prepared['candidate']['library']).resolve()
    for path in (flat,flatmap):
        P.require(prepared['input_sha256'].get(str(path.relative_to(design/'inputs')))==P.sha(path),
            'Original flat semantic input differs from original closed prepared receipt')
    P.require(P.sha(reference)==P.sha(flat) and prepared['candidate']['consumed_sha256'].get(str(library_path))==P.sha(library_path),
        'Actual export reference/original pinned Liberty differs')
    frozen.update({str(P.regular(path).resolve()):P.sha(path) for path in
        (Path(admission).resolve(),metadata_path,flat,flatmap,library_path,source_qmap,candidate,*entries.values())})
    documents=[P.read(path) for path in (candidate,flat,export/'connectivity.json')]
    used={cell['type'] for doc in documents for module in doc['modules'].values() for cell in module.get('cells',{}).values()
        if cell['type'].startswith('sg13cmos5l_')}
    library=W.read_library(library_path,used);graphs=[W.parse_graph(doc,W.TOP,library) for doc in documents]
    original=W.labels(graphs[0],P.read(source_qmap)['rows'],source=True)
    flattened=W.labels(graphs[1],P.read(flatmap)['rows'])
    P.require(set(original)==set(flattened) and all(W.signature(library.cells[original[key].cell])==
        W.signature(library.cells[flattened[key].cell]) for key in original),'Original source/flat semantic or sequential behavior differs')
    rows,resized=W.actual_rows(graphs[2],flattened,library)
    out=Path(out).absolute();out.mkdir(parents=True,exist_ok=False)
    P.write(out/'producer.json',dict(schema='pinwheel.streaming-tt-wire-binding-producer.v1',producer_commit=commit,
        producer_dependency_closure=closure,producer_sha256=producer,qualified=False,boundary=W.BOUNDARY))
    basis_paths={'original-source-admission':Path(admission).resolve(),'original-source-q-map':source_qmap,
        'original-flat-q-map':flatmap,'original-flat-netlist':flat,'original-source-candidate':candidate,
        'original-pinned-Liberty':library_path,'original-closed-physical-report':entries['coarse_report'],
        'original-closed-native-readback':source_host,'actual-derivative-input':metadata_path,
        'actual-closed-physical-report':physical_report,'actual-closed-native-export':export_host,
        'original-binding-helper':P.ROOT/'scripts/streaming_tt_wire_binding.py',
        'final-binding-helper':P.ROOT/'scripts/streaming_tt_wire_binding_final.py','producer-closure':out/'producer.json'}
    if initial is not None:
        basis_paths.update({'actual-native-initial-seed':roots['/work/inputs']/'seed.json',
            'actual-native-initial-odb':initial})
    basis={name:dict(path=str(P.regular(path).resolve()),sha256=P.sha(path)) for name,path in basis_paths.items()}
    P.write(out/'semantic-state-map.json',dict(schema='pinwheel.streaming-tt-semantic-state-map.v1',qualified=False,
        physical_acceptance_claim=False,database_sha256=P.sha(database),connectivity_sha256=P.sha(export/'connectivity.json'),
        source_candidate_sha256=P.sha(candidate),rows=rows,boundary=W.BOUNDARY))
    P.write(out/'sampler-binding.json',W.make_binding(rows,basis,P.sha(export/'connectivity.json')))
    wire.sampler_binding(out/'sampler-binding.json',out/'semantic-state-map.json',candidate=candidate,
        database=database,connectivity=export/'connectivity.json')
    P.require(all(P.sha(P.regular(path))==value for path,value in frozen.items()) and
        all(P.sha(P.ROOT/name)==value and hashlib.sha256(subprocess.check_output(['git','show',commit+':'+name],
            cwd=P.ROOT,timeout=30)).hexdigest()==value for name,value in producer.items()),'Final mapping source/input changed during use')
    P.write(out/'report.json',dict(schema='pinwheel.streaming-tt-final-wire-binding-run.v1',passed=True,qualified=False,
        physical_acceptance_claim=False,universal_digital_correspondence_proved=False,producer_commit=commit,
        producer_sha256=producer,producer_dependency_closure=closure,input_sha256_before=frozen,input_sha256_after=frozen,
        inputs_unchanged=True,producer_unchanged=True,state_bits=len(rows),original_admission_sha256=admission_sha256,
        original_source_odb_sha256=P.sha(source_database),actual_odb_sha256=P.sha(database),
        lineage_kind=kind,initial_snapshot_odb_sha256=None if initial is None else P.sha(initial),
        actual_physical_report=str(physical_report),actual_physical_state=str(state),actual_producer_status=actual['status'],
        actual_producer_exit_code=actual['exit_code'],parsed_sequential_resize_correspondence=resized,
        artifact_sha256={path.name:P.sha(path) for path in sorted(out.iterdir()) if path.is_file()},boundary=W.BOUNDARY))
    return out/'report.json'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('admission','physical-report','state','export-host','out'):parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--source-export-host',type=Path)
    parser.add_argument('--admission-sha256',required=True);args=parser.parse_args()
    print(run(args.admission,args.admission_sha256,args.physical_report,args.state,args.export_host,args.out,args.source_export_host),flush=True)


if __name__=='__main__':main()
