#!/usr/bin/env python3
"""Reject actual serial RTL faults with complete, active kernel graph witnesses."""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import time
import typed_circuit_readback as readback
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory,sha
ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location('serial_artifact_positive',ROOT/'scripts/check-processor-serial-artifact.py')
positive=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(positive)
CONTROLS=('lose-tx-bypass','duplicate-frame','complete-during-reset','drop-rx-refill','clear-new-framing','invalid-selector-success')
FLAGS=positive.FLAGS

def sources():
    return dict(sorted({**positive.sources(),'scripts/check-processor-serial-artifact-negatives.py':sha(Path(__file__)),
                       'test/test_processor_serial_artifact.py':sha(ROOT/'test/test_processor_serial_artifact.py')}.items()))

def contained(base, name):
    if type(name) is not str or not name or PurePosixPath(name).is_absolute() or \
            PurePosixPath(name).as_posix() != name or ".." in PurePosixPath(name).parts:
        raise ValueError("Artifact must have a canonical relative path")
    path = base / name
    if path.is_symlink() or not path.resolve().is_relative_to(base.resolve()):
        raise ValueError("Artifact escapes its receipt bundle")
    return path


def verify_positive(receipt,manifest,tools_hash):
    report=json.loads(receipt.read_text())
    if type(report.get('schema')) is not int or report['schema']!=1 or report.get('status')!='passed' or report.get('source_sha256')!=positive.sources() or report.get('tool_sha256')!=tools_hash or report.get('tool_manifest')!=manifest:
        raise ValueError('Require passed source/tool-current complete serial certificate')
    rows=report.get('configurations')
    if type(rows) is not list or [r.get('divisor') for r in rows]!=list(positive.checks.MATRIX):raise ValueError('Missing complete ordered serial matrix')
    for row in rows:
        if type(row.get('divisor')) is not int or any(row.get(flag) is not True for flag in FLAGS) or any(type(row.get(k)) is not int or row[k]!=v for k,v in (('typed_registers',14),('typed_outputs',13),('endpoints',27))):raise ValueError('Missing serial endpoint/trace/event/reset evidence')
    commands=report.get('commands')
    if type(commands) is not list or not commands or any(type(x) is not dict or type(x.get('exit_code')) is not int or x['exit_code']!=0 or x.get('error') or x.get('expected_failure') for x in commands):raise ValueError('Missing or failed positive command evidence')
    hashes=report.get('artifact_sha256')
    if type(hashes) is not dict or not hashes:raise ValueError('Missing artifact identities')
    inventory={str(p.relative_to(receipt.parent)) for p in receipt.parent.rglob('*') if p.is_file() and p.resolve()!=receipt.resolve()}
    if inventory!=set(hashes):raise ValueError('Incomplete artifact inventory')
    for name,digest in hashes.items():
        if type(digest) is not str or not re.fullmatch(r'[0-9a-f]{64}',digest) or sha(contained(receipt.parent,name))!=digest:raise ValueError('Artifact changed: '+name)
    for row in rows:
        base=f"serial-{row['divisor']}/"
        required=['serial.mlir','serial.sv','interface.json','before-pmuxtree.json','import.json','import.ys']
        for module in ('Design','Graphs','LocalProofs','Links','Proof','SerialTrace','Audit'):
            required.extend(module+suffix for suffix in ('.lean','.olean','.log'))
        units=row.get('local_proof_units')
        if type(units) is not int or units<1:raise ValueError('Missing local proof units')
        for n in range(units):required.extend(f'LocalProofs{n:03d}'+suffix for suffix in ('.lean','.olean','.log'))
        if any(base+name not in hashes for name in required):raise ValueError('Missing typed source/proof/audit evidence')
        if 'standard axioms only' not in (receipt.parent/base/'Audit.log').read_text():raise ValueError('Missing standard axiom audit')
        positive.checks.validate_descriptor(json.loads((receipt.parent/base/'interface.json').read_text()),row['divisor'])
    return receipt.parent/'serial-4'


def mutation(text,descriptor,name):
    if name not in CONTROLS:raise ValueError('Unknown serial control')
    matches=[changed for label,changed in positive.checks.mutations(text,descriptor) if label==name]
    if len(matches)!=1:raise ValueError('Missing actual RTL mutation')
    endpoint_kind={
      'lose-tx-bypass':('register_roles','tx_active','next'),
      'duplicate-frame':('register_roles','held_tx_active','next'),
      'complete-during-reset':('roles','tx_complete','output'),
      'drop-rx-refill':('register_roles','held_rx_data','next'),
      'clear-new-framing':('register_roles','framing','next'),
      'invalid-selector-success':('roles','response_code','output'),
    }
    group,role,kind=endpoint_kind[name]
    return matches[0],descriptor[group][role],kind


def witness_case(name):
    ref=positive.checks.reference
    pins=ref.row(request_valid=True,gpio_input=0xabcdef01)
    state=[0x12345678,0xffffffff,0,0x96,0,0x3c,0,0,0,0,0x96,0,0,0xc3]
    if name=='lose-tx-bypass':
        pins.update(device=2,word=1,write=True,data=0x93)
        expected,corrupted,description=1,0,'Accepted UART TX write must start the frame on this same edge, with no prior held slot'
    elif name=='duplicate-frame':
        pins.update(device=2,word=1,write=True,data=0x93)
        state[2]=state[8]=1;state[9]=39
        expected,corrupted,description=0,1,'Busy TX write faults on the closing edge; completion must clear the old slot so it cannot repeat'
    elif name=='complete-during-reset':
        pins.update(reset=True,device=2,word=1,write=True,data=0x93)
        state[2]=state[8]=1;state[9]=39
        expected,corrupted,description=0,1,'Reset aborts the final TX period without emitting a completion event'
    elif name=='drop-rx-refill':
        pins.update(device=2,word=2)
        state[4]=1;state[11:14]=[1,37,0xc3]
        expected,corrupted,description=0xc3,0x3c,'Read consumes old held RX byte while a stop-sampled new byte refills the slot'
    elif name=='clear-new-framing':
        pins.update(device=2,word=3,write=True,data=8,rx=False)
        state[11:14]=[1,37,0xc3]
        expected,corrupted,description=1,0,'Accepted W1C coincides with bad stop; newly observed framing error wins'
    elif name=='invalid-selector-success':
        pins.update(device=3,word=1,write=True,data=0x93)
        expected,corrupted,description=2,0,'Invalid raw device3 is an explicit register-hole fault, never a successful typed request'
    else:raise ValueError('Unknown control')
    return pins,state,expected,corrupted,description


def graph_value(graph,name,namespace):
    node=graph.nodes[name]
    if node.op in ('input','reg','lit'):
        return graph.expression(node,None).replace('i (','witnessInputs (').replace('s (','witnessState (')
    return f'{namespace}.{name} witnessInputs witnessState'


def witness(directory,descriptor,name,endpoint,kind):
    reader=readback.importer(descriptor);source=reader.read_hints(directory/'serial.mlir');actual=reader.read_rtl(directory/'import.json')
    pins,state,expected,corrupted,description=witness_case(name)
    ref=positive.checks.reference;ref.validate_row(pins);ref.restore(4,state)
    ins=[int(pins[role]) for role in ref.INPUT_ROLES]
    outputs=ref.output(4,pins,state);next_state=ref.step(4,pins,state)
    index=next(k for k,p in enumerate(descriptor['outputs' if kind=='output' else 'registers']) if p['name']==endpoint)
    if (outputs if kind=='output' else next_state)[index]!=expected or expected==corrupted:raise AssertionError('Inactive/incorrect numeric witness')
    mutated_outputs=outputs.copy()
    if kind=='output':mutated_outputs[index]=corrupted
    def encoded(items,family):
        result='0'
        for k,v in reversed(list(enumerate(items))):
            if v:result=f'if ({family}.position _p).val = {k} then {v} else ({result})'
        return result
    lhs=graph_value(source,(source.outputs if kind=='output' else source.next)[endpoint],'Source')
    rhs=graph_value(actual,(actual.outputs if kind=='output' else actual.next)[endpoint],'RTL')
    conditions=[f'witnessInputs input_{k} = {v}' for k,v in enumerate(ins)]
    conditions += [f'witnessState register_{k} = {v}' for k,v in enumerate(state)]
    for graph,namespace,values in ((source,'Source',outputs),(actual,'RTL',mutated_outputs)):
        for port,value in zip(descriptor['outputs'],values,strict=True):
            conditions.append(f"({graph_value(graph,graph.outputs[port['name']],namespace)}) = {value}")
    text=f'''import Lean
import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact.MutationControl
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def witnessInputs : Values Input := fun {{w}} _p => BitVec.ofNat w ({encoded(ins,'inputs')})
def witnessState : Values Register := fun {{w}} _p => BitVec.ofNat w ({encoded(state,'registers')})
theorem active_condition : {' ∧ '.join(conditions)} := by decide +kernel
theorem correct_value : ({lhs}) = {expected} := by decide +kernel
theorem corrupted_value : ({rhs}) = {corrupted} := by decide +kernel
theorem semantic_mutation : ({lhs}) ≠ ({rhs}) := by decide +kernel
end Pinwheel.TypedArtifact.MutationControl
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.TypedArtifact.MutationControl." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved serial witness axioms in {{name}}: {{bad}}"
  if count < 6 then throwError "Incomplete serial mutation audit"
  logInfo m!"Serial mutation audit: {{count}} declarations, standard axioms only."
'''
    return text,dict(inputs=ins,registers=state,input_roles=pins,register_roles=dict(zip(ref.REGISTER_ROLES,state,strict=True)),
                     source_outputs=outputs,mutant_outputs=mutated_outputs,source_next_state_oracle=next_state,
                     source_endpoint_value=expected,mutant_endpoint_value=corrupted,active_condition=description,
                     kernel_checked_input_register_conditions=len(ins)+len(state),kernel_checked_output_conditions=2*len(outputs),
                     independent_oracle_checked=True)


def semantic_errors(log):
    errors=re.findall(r'^.*?\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$',log,re.M)
    allowed=('`grind` failed','unsolved goals','Tactic `decide` proved that the proposition')
    if not errors or any(not any(marker in error for marker in allowed) for error in errors):raise RuntimeError('Failure was not a semantic theorem rejection')
    return errors


def control(run,tools,out,baseline,name):
    directory=out/name;directory.mkdir()
    for filename in ('serial.mlir','serial.sv','interface.json'):shutil.copyfile(baseline/filename,directory/filename)
    descriptor=positive.checks.validate_descriptor(json.loads((directory/'interface.json').read_text()),4)
    rtl=directory/'serial.sv';before=sha(rtl)
    changed,endpoint,kind=mutation(rtl.read_text(),descriptor,name);rtl.write_text(changed)
    try:positive.certify(run,tools,directory,descriptor,rtl)
    except RuntimeError as error:
        match=re.match(r'(LocalProofs(?:[0-9]+)?) certificate failed:',str(error))
        if not match:raise
        stage=match[1];errors=semantic_errors((directory/(stage+'.log')).read_text())
        if run.records[-1].get('exit_code')!=1 or run.records[-1].get('error'):raise RuntimeError('Missing ordinary Lean semantic failure')
        run.records[-1]['expected_failure']=True
    else:raise AssertionError('Corrupted serial received artifact certificate')
    text,details=witness(directory,descriptor,name,endpoint,kind)
    (directory/'MutationWitness.lean').write_text(text);compile_modules(run,directory,['MutationWitness'])
    audit=re.search(r'Serial mutation audit: (\d+) declarations, standard axioms only\.',(directory/'MutationWitness.log').read_text())
    if not audit:raise AssertionError('Missing standard-only witness audit')
    return dict(control=name,stage=stage,rejection=errors,endpoint=endpoint,endpoint_kind=kind,witness=details,
                kernel_checked_counterexample=True,audited_witness_declarations=int(audit[1]),rtl_before_sha256=before,rtl_after_sha256=sha(rtl))


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--tag',required=True);p.add_argument('--positive-report',type=Path,required=True);args=p.parse_args()
    out=fresh_directory(ROOT/'build/processor-serial-artifact-negatives',args.tag)
    report=dict(schema=1,status='running',commands=[],controls=[],boundary='Six actual serial RTL faults must fail semantic LocalProofs and yield standard-only kernel counterexamples with every raw input/register value and all actual outputs. Parser, unknown-bit, timeout and tool failures never count. No analog/CDC or physical timing claim.')
    run,started=positive.rr.Commands(out,report['commands']),time.monotonic()
    try:
        report['source_sha256']=sources();manifest,tools,paths=positive.rr.selected_tools()
        cad=ROOT/'build/tools'/manifest['packages']['oss-cad-suite']['directory'];tools['z3']=cad/'bin/z3';paths += [cad/'bin/z3',cad/'libexec/z3']
        report['tool_manifest']=manifest;report['tool_sha256']=positive.rr.tool_hashes(paths)
        run(['python3','test/test_processor_serial_artifact.py'],'negative-driver-tests')
        receipt=args.positive_report.resolve();baseline=verify_positive(receipt,manifest,report['tool_sha256'])
        report['positive_report']=dict(path=str(receipt),sha256=sha(receipt));shutil.copyfile(receipt,out/'positive-report.json')
        for name in CONTROLS:report['controls'].append(control(run,tools,out,baseline,name))
        if sources()!=report['source_sha256'] or positive.rr.tool_hashes(paths)!=report['tool_sha256']:raise RuntimeError('Negative sources/tools changed')
        verify_positive(receipt,manifest,report['tool_sha256'])
        if sha(receipt)!=report['positive_report']['sha256'] or sha(out/'positive-report.json')!=report['positive_report']['sha256']:raise RuntimeError('Positive receipt changed')
        if [x['control'] for x in report['controls']]!=list(CONTROLS):raise AssertionError('Incomplete controls')
        report['status']='passed'
    except BaseException as error:
        report['status'],report['error']='failed',f'{type(error).__name__}: {error}';raise
    finally:
        report['seconds']=round(time.monotonic()-started,3)
        report['artifact_sha256']={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
