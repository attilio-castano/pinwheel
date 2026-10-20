#!/usr/bin/env python3
"""Bind all actual state bits and both samplers for finite public-wire replay.

Instance names only propose a bijection. This mapping checks native pin facts
and pinned sequential cell functions; it is not a universal digital proof.
"""
import argparse
import ast
from dataclasses import asdict
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

import streaming_tt_final as F
import streaming_tt_physical as P
from streaming_tt_certificate import instance_label, parse_graph, read_library

TOP='tt_um_pinwheel_streaming_ready_d2'
WIRE_API_SHA256='123b3d963ab94b6d58657e868e27f3f950270b748d85bb03fc15b43b7b7eb054'
BOUNDARY=('Exact source/flat/actual state-name bijection, actual FF pin readback and parsed pinned-Liberty '
    'sequential master correspondence for finite public-wire replay only. No all-state transition/output '
    'contraction, kernel acceptance, extracted timing or physical acceptance is claimed.')


def dependency_closure(root,entries):
    """Resolve static and literal dynamic imports for the selected mapping APIs.

    The wire coordinator's archive dispatcher is unused here. Its entire exact
    committed module is sealed, including the two selected non-dispatching APIs.
    """
    root=Path(root).resolve();pending=list(entries);files=set();external=set();dynamic={}
    while pending:
        name=pending.pop();path=root/name
        P.require(not Path(name).is_absolute() and '..' not in Path(name).parts and path.is_file() and
            not path.is_symlink() and path.resolve().is_relative_to(root),'Invalid mapping producer dependency')
        if name in files:continue
        files.add(name)
        if path.suffix!='.py' or not name.startswith(('scripts/','physical/')):continue
        tree=ast.parse(path.read_bytes());targets=[]
        isolated=name=='scripts/run-streaming-tt-wire.py'
        if isolated:
            P.require(P.sha(path)==WIRE_API_SHA256,'Review changed wire coordinator API before mapping')
        for node in ast.walk(tree):
            if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and node.func.attr in ('spec_from_file_location','run_path'):
                if isolated:continue
                arity,index=(2,1) if node.func.attr=='spec_from_file_location' else (1,0)
                P.require(len(node.args)==arity and not node.keywords,'Unresolved mapping dynamic import')
                value=node.args[index]
                if isinstance(value,ast.Call) and isinstance(value.func,ast.Name) and value.func.id=='str' and len(value.args)==1 and not value.keywords:value=value.args[0]
                if isinstance(value,ast.BinOp) and isinstance(value.left,ast.Name) and value.left.id=='ROOT' and isinstance(value.op,ast.Div) and isinstance(value.right,ast.Constant) and type(value.right.value) is str:target=value.right.value
                elif isinstance(value,ast.Call) and isinstance(value.func,ast.Attribute) and value.func.attr=='with_name' and len(value.args)==1 and not value.keywords and isinstance(value.args[0],ast.Constant) and type(value.args[0].value) is str and isinstance(value.func.value,ast.Call) and isinstance(value.func.value.func,ast.Name) and value.func.value.func.id=='Path' and len(value.func.value.args)==1 and isinstance(value.func.value.args[0],ast.Name) and value.func.value.args[0].id=='__file__':
                    P.require(Path(value.args[0].value).name==value.args[0].value,'Escaping mapping import');target=str(Path(name).with_name(value.args[0].value))
                else:raise ValueError('Unresolved mapping producer import: '+name)
                P.require(target.startswith('scripts/') and target.endswith('.py') and '..' not in Path(target).parts,'Escaping mapping import')
                pending.append(target);targets.append(target)
        if targets:dynamic[name]=sorted(set(targets))
        for node in ast.walk(tree):
            modules=[]
            if isinstance(node,ast.Import):modules=[item.name for item in node.names]
            if isinstance(node,ast.ImportFrom):
                P.require(node.level==0,'Relative mapping import unresolved')
                if node.module:modules=[node.module]
            if isinstance(node,ast.Call):
                call=node.func.id if isinstance(node.func,ast.Name) else node.func.attr if isinstance(node.func,ast.Attribute) else ''
                P.require(call not in ('__import__','import_module','SourceFileLoader') and
                    (call!='exec_module' or targets or isolated),'Unresolved mapping import mechanism')
            for module in modules:
                local=root/'scripts'/(module.replace('.','/')+'.py')
                if local.is_file():pending.append(str(local.relative_to(root)))
                else:external.add(module)
    return dict(files=sorted(files),external_imports=sorted(external),dynamic_imports=dynamic,
        selected_wire_api=dict(module='scripts/run-streaming-tt-wire.py',sha256=WIRE_API_SHA256,
            functions=['actual_export','sampler_binding'],unused_dispatchers=['main','load']),
        boundary='Complete committed module bytes and recursively resolved selected API imports; standard library remains external.')


def signature(cell):
    return {key:value for key,value in asdict(cell).items() if key not in ('name','function_text')}


def semantic(row):
    P.require(type(row) is dict and row.get('component') in ('frontend','core-d2') and
        type(row.get('register')) is str and re.fullmatch(r'r_[A-Za-z0-9_]+',row['register']) and
        type(row.get('index')) is int and row['index']>=0,'Malformed semantic register bit')
    return row['component']+':'+row['register']+':'+str(row['index'])


def labels(graph,rows,*,source=False,count=6039):
    P.require(type(rows) is list and len(rows)==count,'Incomplete semantic state table')
    hints={};semantics=set()
    for row in rows:
        key=semantic(row);name=row.get('candidate_ff' if source else 'ff')
        P.require(type(name) is str and name,'Missing semantic FF instance')
        label=instance_label(name)
        P.require(label not in hints and key not in semantics,'Aliased FF or semantic register label')
        hints[label]=(key,row);semantics.add(key)
    result={};seen=set()
    for ff in graph.flipflops:
        label=instance_label(ff.name)
        P.require(label in hints and label not in seen,'Unknown or aliased actual semantic FF')
        key,row=hints[label];seen.add(label)
        fields=(('candidate_q','q'),('candidate_d','d'),('candidate_clock','clock'),('candidate_cell','cell')) if source else (
            ('q','q'),('d','d'),('clock','clock'),('cell','cell'))
        P.require(all(type(row.get(field)) is type(getattr(ff,attr)) and row[field]==getattr(ff,attr)
            for field,attr in fields),'Semantic map differs from actual Q/D/clock/master')
        result[key]=ff
    P.require(len(result)==count and seen==set(hints),'Missing physical or semantic FF')
    return result


def actual_rows(actual,flat,library,*,count=6039):
    by_label={};seen_q=set()
    for key,ff in flat.items():
        label=instance_label(ff.name)
        P.require(label not in by_label,'Aliased flat physical FF names');by_label[label]=(key,ff)
    rows=[];seen=set();resized=[]
    for ff in actual.flipflops:
        label=instance_label(ff.name)
        P.require(label in by_label and label not in seen and ff.q not in seen_q,'Unknown or aliased actual FF')
        key,reference=by_label[label];seen.add(label);seen_q.add(ff.q)
        P.require(reference.cell in library.cells and ff.cell in library.cells and
            library.cells[reference.cell].sequential is True and library.cells[ff.cell].sequential is True and
            signature(library.cells[reference.cell])==signature(library.cells[ff.cell]),
            'Actual resized FF has different parsed sequential behavior')
        parts=json.loads(ff.name)
        P.require(type(parts) is list and len(parts)==1 and type(parts[0]) is str and
            json.dumps(parts,separators=(',',':'))==ff.name,'Noncanonical actual flat FF name')
        rows.append(dict(semantic=key,actual_ff=ff.name,actual_q=ff.q,actual_d=ff.d,
            actual_clock=ff.clock,actual_reset_b=ff.reset_b,actual_cell=ff.cell))
        if ff.cell!=reference.cell:resized.append(dict(semantic=key,actual_ff=ff.name,
            reference_master=reference.cell,actual_master=ff.cell,parsed_sequential_functions_equal=True))
    P.require(len(rows)==count and len({row['semantic'] for row in rows})==count and seen==set(by_label),
        'Actual FF inventory is not an exact full semantic bijection')
    return sorted(rows,key=lambda row:row['semantic']),resized


def make_binding(rows,basis,connectivity_sha256):
    bindings={}
    for stage in ('stage1','stage2'):
        found=[row for row in rows if row['semantic']=='core-d2:r_'+stage+':0']
        P.require(len(found)==1,'Missing exact physical sampler semantic bit')
        row=found[0];bindings[stage]=dict(component='core-d2',register='r_'+stage,index=0,cell=row['actual_ff'],
            q=row['actual_q'],d=row['actual_d'],clock=row['actual_clock'],reset_b=row['actual_reset_b'])
    P.require(bindings['stage1']['cell']!=bindings['stage2']['cell'],'Sampler stages alias')
    return dict(schema='pinwheel.streaming-tt-sampler-binding.v1',top=TOP,qualified=False,
        connectivity_sha256=connectivity_sha256,bindings=bindings,semantic_basis=basis,boundary=BOUNDARY)


def run(admission,admission_sha256,export_host,out):
    closure=dependency_closure(P.ROOT,['scripts/streaming_tt_wire_binding.py',
        'scripts/run-streaming-tt-wire.py','scripts/run-streaming-tt-sta.py','scripts/streaming_tt_export_odb.py'])
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P.ROOT,text=True).strip()
    producer={name:hashlib.sha256(P.committed(P.ROOT/name)).hexdigest() for name in closure['files']}
    spec=importlib.util.spec_from_file_location('_streaming_tt_binding_wire',Path(__file__).with_name('run-streaming-tt-wire.py'))
    wire=importlib.util.module_from_spec(spec);spec.loader.exec_module(wire)
    spec=importlib.util.spec_from_file_location('_streaming_tt_binding_sta',Path(__file__).with_name('run-streaming-tt-sta.py'))
    checkpoint=importlib.util.module_from_spec(spec);spec.loader.exec_module(checkpoint)
    admitted,entries,design=F.admission(admission,admission_sha256)
    _,_,database,reference,export,frozen=wire.actual_export(export_host,physical_report=entries['coarse_report'],
        state=entries['state'],checkpoint_host=checkpoint,exporter_sha256=producer['scripts/streaming_tt_export_odb.py'])
    parent=P.read(entries['parent_intake']);prepared=P.read(entries['prepared_input'])
    source_qmap=F.bound(parent['artifacts']['semantic_q_map']);candidate=entries['candidate_json']
    P.require(F.bound(parent['artifacts']['candidate_json'])==candidate,'Source semantic parent candidate differs')
    flat=design/'inputs/physical-verilog/flat-reimport.json'
    flatmap=design/'inputs/physical-verilog/flat-reimport-semantic-q-map.json'
    libpath=P.regular(prepared['candidate']['library']).resolve()
    P.require(reference==flat.resolve(),'Native export reference differs from exact admitted flat netlist')
    for path in (flat,flatmap):
        P.require(prepared['input_sha256'].get(str(path.relative_to(design/'inputs')))==P.sha(path),
            'Flat semantic/library input differs from closed prepared receipt')
    P.require(prepared['candidate']['consumed_sha256'].get(str(libpath))==P.sha(libpath),
        'Semantic Liberty differs from admitted closed candidate input')
    bound_paths=[Path(admission).resolve(),source_qmap,flat,flatmap,libpath,candidate,*entries.values()]
    frozen.update({str(P.regular(path).resolve()):P.sha(path) for path in bound_paths})
    documents=[P.read(path) for path in (candidate,flat,export/'connectivity.json')]
    used={cell['type'] for doc in documents for module in doc['modules'].values() for cell in module.get('cells',{}).values()
        if cell['type'].startswith('sg13cmos5l_')}
    library=read_library(libpath,used);graphs=[parse_graph(doc,TOP,library) for doc in documents]
    original=labels(graphs[0],P.read(source_qmap)['rows'],source=True)
    flattened=labels(graphs[1],P.read(flatmap)['rows'])
    P.require(set(original)==set(flattened) and all(signature(library.cells[original[key].cell])==
        signature(library.cells[flattened[key].cell]) for key in original),'Source/flat semantic state or FF behavior differs')
    rows,resized=actual_rows(graphs[2],flattened,library)
    out=Path(out).absolute();out.mkdir(parents=True,exist_ok=False)
    producer_path=out/'producer.json'
    P.write(producer_path,dict(schema='pinwheel.streaming-tt-wire-binding-producer.v1',producer_commit=commit,
        producer_dependency_closure=closure,producer_sha256=producer,qualified=False,boundary=BOUNDARY))
    named={'source-semantic-q-map':source_qmap,'flat-semantic-q-map':flatmap,'source-candidate':candidate,
        'flat-netlist':flat,'pinned-library':libpath,'source-admission':Path(admission).resolve(),
        'closed-physical-report':entries['coarse_report'],'closed-native-export-host':Path(export_host).resolve(),
        'helper-producer':P.ROOT/'scripts/streaming_tt_wire_binding.py','producer-closure':producer_path}
    basis={name:dict(path=str(P.regular(path).resolve()),sha256=P.sha(path)) for name,path in named.items()}
    mapping=dict(schema='pinwheel.streaming-tt-semantic-state-map.v1',qualified=False,physical_acceptance_claim=False,
        database_sha256=P.sha(database),connectivity_sha256=P.sha(export/'connectivity.json'),
        source_candidate_sha256=P.sha(candidate),rows=rows,boundary=BOUNDARY)
    P.write(out/'semantic-state-map.json',mapping)
    P.write(out/'sampler-binding.json',make_binding(rows,basis,P.sha(export/'connectivity.json')))
    wire.sampler_binding(out/'sampler-binding.json',out/'semantic-state-map.json',candidate=candidate,
        database=database,connectivity=export/'connectivity.json')
    P.require(all(P.sha(P.regular(path))==value for path,value in frozen.items()),'Wire mapping input changed during use')
    P.require(all(P.sha(P.ROOT/name)==value and hashlib.sha256(subprocess.check_output(
        ['git','show',commit+':'+name],cwd=P.ROOT,timeout=30)).hexdigest()==value for name,value in producer.items()),
        'Wire mapping producer changed during use')
    P.write(out/'report.json',dict(schema='pinwheel.streaming-tt-wire-binding-run.v1',passed=True,qualified=False,
        physical_acceptance_claim=False,universal_digital_correspondence_proved=False,producer_commit=commit,
        producer_sha256=producer,producer_dependency_closure=closure,input_sha256_before=frozen,input_sha256_after=frozen,
        inputs_unchanged=True,producer_unchanged=True,physical_report=str(entries['coarse_report']),
        actual_odb_sha256=P.sha(database),state_bits=len(rows),parsed_sequential_resize_correspondence=resized,
        artifact_sha256={path.name:P.sha(path) for path in sorted(out.iterdir()) if path.is_file()},boundary=BOUNDARY))
    return out/'report.json'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('admission','export-host','out'):parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--admission-sha256',required=True);args=parser.parse_args()
    print(run(args.admission,args.admission_sha256,args.export_host,args.out),flush=True)


if __name__=='__main__':raise SystemExit(main())
