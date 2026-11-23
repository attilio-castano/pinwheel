#!/usr/bin/env python3
"""Certify every MMIO RTL endpoint, reset and admitted actual-response event history."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import time

import typed_circuit_readback as readback
from readback_control_proofs import split_two_bit_controls
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("mmio_checks", ROOT / "scripts/check-processor-mmio.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)
rr = checks.rr


def sources():
    result = checks.source_hashes()
    for name in ("scripts/check-processor-mmio-artifact.py", "scripts/readback_control_proofs.py",
                 "Pinwheel/Hardware/Processor/MmioRefinement.lean", "test/ProcessorMmioRefinement.lean"):
        result[name] = sha(ROOT / name)
    result.update({str(path.relative_to(ROOT)): sha(path) for path in readback.source_paths()})
    return dict(sorted(result.items()))


def profile():
    return """import Pinwheel.Hardware.Processor.MmioRefinement
abbrev Input := Processor.MmioInterface.Input
abbrev Register := Processor.MmioCircuit.Register
abbrev Output := Processor.MmioInterface.Output
abbrev circuit := Processor.MmioCircuit.circuit
abbrev inputs := Processor.MmioInterface.inputs
abbrev registers := Processor.MmioCircuit.registers
abbrev outputs := Processor.MmioInterface.outputs
"""


def trace_module():
    return """import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
open Processor.MmioInterface Processor.MmioCircuit

theorem projected_trace (s : Values Register) (traffic : List (Values Input)) :
    rtlComponent.trace s traffic = spec.trace (view s) traffic :=
  implementation.artifact_trace_eq correspondence s trivial traffic

theorem projected_final_state (s : Values Register) (traffic : List (Values Input)) :
    view (rtlComponent.run s traffic) = spec.run (view s) traffic :=
  implementation.artifact_run_eq correspondence s trivial traffic

theorem initialized_trace (s : Values Register) (i : Values Input) (h : i reset = 1)
    (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic = spec.trace Processor.MmioModel.initial traffic :=
  resetCertificate.artifact_trace_after_reset implementation reset correspondence i s h traffic

theorem initialized_final_state (s : Values Register) (i : Values Input) (h : i reset = 1)
    (traffic : List (Values Input)) :
    view (rtlComponent.run (rtlComponent.step i s) traffic) = spec.run Processor.MmioModel.initial traffic :=
  resetCertificate.artifact_run_after_reset implementation reset correspondence i s h traffic

theorem reset_clears_registers (s : Values Register) (i : Values Input) (h : i reset = 1)
    (r : Register b) : rtlComponent.step i s r = 0 :=
  (congrFun (congrFun (correspondence.step_eq i s) b) r).trans (reset_eq i s h r)

theorem reset_masks_outputs (s : Values Register) (i : Values Input) (h : i reset = 1)
    (o : Output b) : rtlComponent.observe i s o = 0 :=
  (congrFun (congrFun (correspondence.output_eq i s) b) o).trans (reset_outputs i s h o)

theorem actual_response (i : Values Input) (s : Values Register) :
    Processor.MmioRefinement.observedResponse rtlComponent i s = response i (view s) :=
  (Processor.MmioRefinement.observedResponse_eq correspondence i s).trans (observedResponse_eq i s)

theorem actual_event_replay (s : Values Register) (traffic : List (Values Input))
    (legal : rtlComponent.Legal (fun i _ => Admitted i) s traffic) :
    Processor.MmioModel.replay (view s)
      (rtlComponent.eventTrace (Processor.MmioRefinement.events rtlComponent) s traffic) =
      some (view (rtlComponent.run s traffic)) :=
  Processor.MmioRefinement.replay_trace correspondence s traffic legal

theorem reset_actual_event_replay (s : Values Register) (i : Values Input) (h : i reset = 1)
    (traffic : List (Values Input))
    (legal : rtlComponent.Legal (fun j _ => Admitted j) (rtlComponent.step i s) traffic) :
    Processor.MmioModel.replay Processor.MmioModel.initial
      (rtlComponent.eventTrace (Processor.MmioRefinement.events rtlComponent) (rtlComponent.step i s) traffic) =
      some (view (rtlComponent.run (rtlComponent.step i s) traffic)) :=
  Processor.MmioRefinement.replay_after_reset correspondence i s h traffic legal

theorem reset_event (s : Values Register) (i : Values Input) (h : i reset = 1) :
    Processor.MmioRefinement.events rtlComponent i s = [.reset] :=
  Processor.MmioRefinement.reset_events rtlComponent i s h

end Pinwheel.TypedArtifact
"""


def certify(run, tools, directory, descriptor, rtl):
    imported, script = directory / "import.json", directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
        f"hierarchy -check -top {descriptor['module']}\nflatten -noscopeinfo\nproc\n"
        f"write_json {rr.yosys_quote(directory / 'before-pmuxtree.json')}\npmuxtree\nopt_clean\ncheck -assert\n"
        f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    modules, evidence = readback.generate(directory, descriptor, directory / "mmio.mlir", imported,
        tools["z3"], profile=profile())
    evidence["finite_control_proof_search"] = split_two_bit_controls(directory, modules)
    (directory / "MmioTrace.lean").write_text(trace_module())
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import MmioTrace"))
    modules.insert(-1, "MmioTrace")
    compile_modules(run, directory, modules)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise AssertionError("Missing MMIO artifact/event/reset axiom audit")
    if len(descriptor["registers"]) != 8 or len(descriptor["outputs"]) != 7 or evidence["endpoints"] != 15:
        raise AssertionError("Incomplete MMIO artifact certificate")
    return {**evidence, "typed_registers": 8, "typed_outputs": 7,
            "arbitrary_raw_state_trace_checked": True, "projected_final_state_checked": True,
            "initialized_trace_checked": True, "initialized_final_state_checked": True,
            "reset_clears_registers_checked": True, "reset_masks_outputs_checked": True,
            "actual_response_checked": True, "admitted_actual_event_replay_checked": True,
            "reset_event_replay_checked": True, "reset_event_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/processor-mmio-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Complete imported unsynthesized binary state/output correspondence, including all raw "
            "device selectors and inactive byte metadata. Actual response/event replay is restricted to admitted "
            "selectors; selector3 remains an explicit functional-wrapper fault. Serial frontend events are external "
            "inputs, not wire-level UART behavior. No processor refinement, synthesis-preservation or timing claim. "
            "Yosys proc/pmuxtree and restricted JSON interpretation remain trusted; pre-normalization JSON retained."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Processor.MmioRefinement", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        audit = run(["lake", "env", "lean", "-DwarningAsError=true", "test/ProcessorMmioRefinement.lean"],
                    "event-transport-tests", timeout=900)
        if "standard axioms only" not in audit:
            raise AssertionError("Missing actual-response transport audit")
        directory = out / "mmio"
        directory.mkdir()
        run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/ProcessorMmioEmit.lean", directory], "mmio-emit")
        descriptor = json.loads((directory / "interface.json").read_text())
        checks.validate_descriptor(descriptor)
        rtl = directory / "mmio.sv"
        rtl.write_text(run([tools["circt"], directory / "mmio.mlir", "--canonicalize", "--lower-seq-to-sv",
            "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], "mmio-lower"))
        report["configurations"].append({"configuration": [32], **certify(run, tools, directory, descriptor, rtl)})
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("MMIO artifact sources/tools changed")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic()-started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
