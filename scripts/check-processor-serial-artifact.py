#!/usr/bin/env python3
"""Kernel-check all 27 serial RTL endpoints, scoped digital histories and actual events."""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import time
import typed_circuit_readback as readback
from readback_control_proofs import split_two_bit_controls
from readback_slice_proofs import prove_slice_bounds
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory,sha
ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location('serial_checks',ROOT/'scripts/check-processor-serial.py')
checks=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(checks)
rr=checks.rr
FLAGS=('valid_state_trace_checked','projected_final_state_checked','initialized_trace_checked','initialized_final_state_checked',
       'reset_clears_registers_checked','reset_masks_outputs_checked','actual_response_checked','admitted_actual_event_replay_checked',
       'reset_event_replay_checked','reset_event_checked','invalid_selector_fault_checked')

def sources():
    result=checks.source_hashes()
    for name in ('scripts/check-processor-serial-artifact.py','scripts/readback_control_proofs.py','scripts/readback_slice_proofs.py',
                 'Pinwheel/Hardware/Processor/SerialRefinement.lean','test/ProcessorSerialRefinement.lean'):
        result[name]=sha(ROOT/name)
    result.update({str(p.relative_to(ROOT)):sha(p) for p in readback.source_paths()})
    return dict(sorted(result.items()))

def profile(d):
    return f'''import Pinwheel.Hardware.Processor.SerialRefinement
def timing : Uart.Timing := ⟨{d},by decide +kernel,by decide +kernel⟩
abbrev Input := Processor.SerialInterface.Input
abbrev Register := Processor.SerialCircuit.Register timing
abbrev Output := Processor.SerialInterface.Output
abbrev circuit := Processor.SerialCircuit.circuit timing
abbrev inputs := Processor.SerialInterface.inputs
abbrev registers := Processor.SerialCircuit.registers timing
abbrev outputs := Processor.SerialInterface.outputs
'''

def trace_module():
    return '''import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
open Processor.SerialInterface Processor.SerialCircuit

theorem projected_trace (s : Values Register) (hs : Valid timing s) (traffic : List (Values Input)) :
    rtlComponent.trace s traffic = (spec timing).trace (view s) traffic :=
  (implementation timing).artifact_trace_eq correspondence s hs traffic

theorem projected_final_state (s : Values Register) (hs : Valid timing s) (traffic : List (Values Input)) :
    view (rtlComponent.run s traffic) = (spec timing).run (view s) traffic :=
  (implementation timing).artifact_run_eq correspondence s hs traffic

theorem initialized_trace (s : Values Register) (i : Values Input) (h : i reset = 1)
    (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic = (spec timing).trace Processor.SerialModel.initial traffic :=
  (resetCertificate timing).artifact_trace_after_reset (implementation timing) reset correspondence i s h traffic

theorem initialized_final_state (s : Values Register) (i : Values Input) (h : i reset = 1)
    (traffic : List (Values Input)) :
    view (rtlComponent.run (rtlComponent.step i s) traffic) = (spec timing).run Processor.SerialModel.initial traffic :=
  (resetCertificate timing).artifact_run_after_reset (implementation timing) reset correspondence i s h traffic

theorem reset_clears_registers (s : Values Register) (i : Values Input) (h : i reset = 1)
    (r : Register b) : rtlComponent.step i s r = 0 :=
  (congrFun (congrFun (correspondence.step_eq i s) b) r).trans (reset_eq i s h r)

theorem reset_masks_outputs (s : Values Register) (i : Values Input) (h : i reset = 1)
    (o : Output b) : rtlComponent.observe i s o = resetValues o :=
  (congrFun (congrFun (correspondence.output_eq i s) b) o).trans (reset_outputs i s h o)

theorem actual_response (i : Values Input) (s : Values Register) (hs : Valid timing s) :
    Processor.SerialRefinement.observedResponse rtlComponent i s =
      Processor.MmioInterface.response (mmioPins timing i (view s)) (view s).mmio :=
  (Processor.SerialRefinement.observedResponse_eq correspondence i s).trans (observedResponse_eq i s hs.1)

theorem invalid_selector_fault (i : Values Input) (s : Values Register)
    (hr : i reset ≠ 1) (hi : invalid i) :
    Processor.SerialRefinement.observedResponse rtlComponent i s = some (.fault .registerHole) :=
  (Processor.SerialRefinement.observedResponse_eq correspondence i s).trans (invalid_response i s hr hi)

theorem actual_event_replay (s : Values Register) (hs : Valid timing s) (traffic : List (Values Input))
    (legal : rtlComponent.Legal (fun i _ => Admitted i) s traffic) :
    Processor.MmioModel.replay (view s).mmio
      (rtlComponent.eventTrace (Processor.SerialRefinement.events rtlComponent) s traffic) =
      some (view (rtlComponent.run s traffic)).mmio :=
  Processor.SerialRefinement.replay_trace correspondence s hs traffic legal

theorem reset_actual_event_replay (s : Values Register) (i : Values Input) (h : i reset = 1)
    (traffic : List (Values Input))
    (legal : rtlComponent.Legal (fun j _ => Admitted j) (rtlComponent.step i s) traffic) :
    Processor.MmioModel.replay Processor.MmioModel.initial
      (rtlComponent.eventTrace (Processor.SerialRefinement.events rtlComponent) (rtlComponent.step i s) traffic) =
      some (view (rtlComponent.run (rtlComponent.step i s) traffic)).mmio :=
  Processor.SerialRefinement.replay_after_reset correspondence i s h traffic legal

theorem reset_event (s : Values Register) (i : Values Input) (h : i reset = 1) :
    Processor.SerialRefinement.events rtlComponent i s = [.reset] :=
  Processor.SerialRefinement.reset_events rtlComponent i s h
end Pinwheel.TypedArtifact
'''

def certify(run,tools,directory,descriptor,rtl):
    d=descriptor['divisor']; checks.validate_descriptor(descriptor,d)
    imported,script=directory/'import.json',directory/'import.ys'
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {descriptor['module']}\nflatten -noscopeinfo\nproc\nwrite_json {rr.yosys_quote(directory/'before-pmuxtree.json')}\npmuxtree\nopt_clean\ncheck -assert\nwrite_json {rr.yosys_quote(imported)}\n")
    run([tools['yosys'],'-Q','-T','-s',script],directory.name+'-import')
    modules,evidence=readback.generate(directory,descriptor,directory/'serial.mlir',imported,tools['z3'],profile=profile(d))
    evidence['finite_control_proof_search']=split_two_bit_controls(directory,modules)
    evidence['slice_bound_proof_search']=prove_slice_bounds(directory,modules)
    (directory/'SerialTrace.lean').write_text(trace_module())
    audit=directory/'Audit.lean';audit.write_text(audit.read_text().replace('import Proof','import SerialTrace'))
    modules.insert(-1,'SerialTrace');compile_modules(run,directory,modules)
    if 'standard axioms only' not in (directory/'Audit.log').read_text():raise AssertionError('Missing serial axiom audit')
    if evidence['endpoints']!=27:raise AssertionError('Incomplete serial certificate')
    return {**evidence,'typed_registers':14,'typed_outputs':13,**{flag:True for flag in FLAGS}}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--tag',required=True);args=p.parse_args()
    out=fresh_directory(ROOT/'build/processor-serial-artifact',args.tag)
    report=dict(schema=1,status='running',commands=[],configurations=[],boundary='Complete unsynthesized binary RTL next/output correspondence for every raw state. Digital model traces require UART bounds and TX-slot ownership; synchronous reset establishes both from arbitrary raw state. Actual response and UART-pin event replay additionally requires admitted selectors; selector3 remains a checked all-state wrapper fault. No analog/CDC/baud tolerance, CPU retirement, synthesis-preservation or physical timing claim. Yosys proc/pmuxtree and restricted JSON interpretation remain trusted.')
    run,started=rr.Commands(out,report['commands']),time.monotonic()
    try:
        report['source_sha256']=sources();manifest,tools,paths=rr.selected_tools()
        cad=ROOT/'build/tools'/manifest['packages']['oss-cad-suite']['directory'];tools['z3']=cad/'bin/z3'
        paths += [cad/'bin/z3',cad/'libexec/z3'];report['tool_manifest']=manifest;report['tool_sha256']=rr.tool_hashes(paths)
        run(['lake','build','Pinwheel.Hardware.Processor.SerialRefinement','Pinwheel.Hardware.Emit','Pinwheel.Hardware.Readback.Boolean'],'build',timeout=900)
        audit=run(['lake','env','lean','-DwarningAsError=true','--run','test/ProcessorSerialRefinement.lean'],'event-transport-tests',timeout=900)
        if 'standard axioms only' not in audit:raise AssertionError('Missing event transport audit')
        for d in checks.MATRIX:
            directory=out/f'serial-{d}';directory.mkdir()
            run(['lake','env','lean','-DwarningAsError=true','--run','test/ProcessorSerialEmit.lean',str(d),directory],f'd{d}-emit')
            descriptor=checks.validate_descriptor(json.loads((directory/'interface.json').read_text()),d)
            rtl=directory/'serial.sv'
            rtl.write_text(run([tools['circt'],directory/'serial.mlir','--canonicalize','--lower-seq-to-sv','--lower-hw-to-sv','--hw-legalize-modules','--export-verilog','-o','/dev/null'],f'd{d}-lower'))
            report['configurations'].append(dict(divisor=d,**certify(run,tools,directory,descriptor,rtl)))
        if sources()!=report['source_sha256'] or rr.tool_hashes(paths)!=report['tool_sha256']:raise RuntimeError('Artifact sources/tools changed')
        report['status']='passed'
    except BaseException as error:
        report['status'],report['error']='failed',f'{type(error).__name__}: {error}';raise
    finally:
        report['seconds']=round(time.monotonic()-started,3)
        report['artifact_sha256']={str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
