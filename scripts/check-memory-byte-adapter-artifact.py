#!/usr/bin/env python3
"""Certify byte RAM RTL through raw-state projection and memory-preserving reset."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import time

import typed_circuit_readback as readback
from readback_control_proofs import split_two_bit_controls
from readback_byte_slices import prepare_byte_slices
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("byte_adapter_checks", ROOT / "scripts/check-memory-byte-adapter.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)
rr = checks.rr


def sources():
    result = checks.source_hashes()
    for name in ("scripts/check-memory-byte-adapter-artifact.py", "scripts/readback_control_proofs.py",
                 "scripts/readback_byte_slices.py", "test/test_readback_byte_slices.py",
                 "Pinwheel/Hardware/Memory/ByteAdapterRefinement.lean", "test/MemoryByteAdapterRefinement.lean"):
        result[name] = sha(ROOT / name)
    result.update({str(path.relative_to(ROOT)): sha(path) for path in readback.source_paths()})
    return dict(sorted(result.items()))


def profile(a):
    return f"""import Pinwheel.Hardware.Memory.ByteAdapterRefinement
abbrev Input := Memory.ByteAdapterInterface.Input {a}
abbrev Register := Memory.ByteAdapterCircuit.Register {a}
abbrev Output := Memory.ByteAdapterInterface.Output
abbrev circuit := Memory.ByteAdapterCircuit.circuit {a}
abbrev inputs := Memory.ByteAdapterInterface.inputs {a}
abbrev registers := Memory.ByteAdapterCircuit.registers {a}
abbrev outputs := Memory.ByteAdapterInterface.outputs
"""


def trace_module(a):
    return f"""import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
open Memory.ByteAdapterInterface Memory.ByteAdapterCircuit

theorem projected_trace (s : Values Register) (traffic : List (Values Input)) :
    rtlComponent.trace s traffic = (Memory.ByteAdapterInterface.spec {a}).trace (view s) traffic :=
  (implementation {a}).artifact_trace_eq correspondence s trivial traffic

theorem projected_final_state (s : Values Register) (traffic : List (Values Input)) :
    view (rtlComponent.run s traffic) = (Memory.ByteAdapterInterface.spec {a}).run (view s) traffic :=
  (implementation {a}).artifact_run_eq correspondence s trivial traffic

theorem state_preserving_reset_trace (s : Values Register) (i : Values Input)
    (h : i reset = 1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Memory.ByteAdapterInterface.spec {a}).trace (Memory.ByteAdapterModel.resetState (view s)) traffic :=
  (resetCertificate {a}).artifact_trace_after_reset (implementation {a}) reset correspondence i s h traffic

theorem reset_final_state (s : Values Register) (i : Values Input)
    (h : i reset = 1) (traffic : List (Values Input)) :
    view (rtlComponent.run (rtlComponent.step i s) traffic) =
      (Memory.ByteAdapterInterface.spec {a}).run (Memory.ByteAdapterModel.resetState (view s)) traffic :=
  (resetCertificate {a}).artifact_run_after_reset (implementation {a}) reset correspondence i s h traffic

theorem reset_preserves_memory_and_q (s : Values Register) (i : Values Input)
    (h : i reset = 1) (r : Memory.CommandFlops.Register {a} 32 b) :
    rtlComponent.step i s (.left r) = s (.left r) := by
  exact (congrFun (congrFun (correspondence.step_eq i s) b) (.left r)).trans
    (reset_memory i s h r)

theorem reset_preserves_metadata (s : Values Register) (i : Values Input)
    (h : i reset = 1) (r : Metadata {a} b)
    (hk : ((metadataPorts {a}).interface.position r).val ≠ 6) :
    rtlComponent.step i s (.right r) = s (.right r) := by
  exact (congrFun (congrFun (correspondence.step_eq i s) b) (.right r)).trans
    (reset_metadata i s h r hk)

theorem reset_clears_pending (s : Values Register) (i : Values Input) (h : i reset = 1) :
    rtlComponent.step i s pending = 0 := by
  exact (congrFun (congrFun (correspondence.step_eq i s) 1) pending).trans
    (reset_pending i s h)

theorem reset_masks_outputs (s : Values Register) (i : Values Input)
    (h : i reset = 1) (o : Output b) : rtlComponent.observe i s o = 0 := by
  exact (congrFun (congrFun (correspondence.output_eq i s) b) o).trans
    (reset_outputs i s h o)

theorem reset_establishes_snapshot (s : Values Register) (i : Values Input)
    (h : i reset = 1) (traffic : List (Values Input)) :
    Memory.ByteAdapterModel.Valid (view (rtlComponent.run (rtlComponent.step i s) traffic)) := by
  rw [correspondence.run_eq, correspondence.step_eq]
  exact snapshot_valid_after_reset i s h traffic

theorem actual_event_replay (s : Values Register) (valid : Memory.ByteAdapterModel.Valid (view s))
    (traffic : List (Values Input)) :
    Memory.ByteAdapterEffects.replay (view s).memory.contents
      (rtlComponent.eventTrace (Memory.ByteAdapterRefinement.artifactEvents rtlComponent) s traffic) =
      some (view (rtlComponent.run s traffic)).memory.contents :=
  Memory.ByteAdapterRefinement.artifact_replay_trace correspondence s valid traffic

theorem reset_actual_event_replay (s : Values Register) (i : Values Input)
    (h : i reset = 1) (traffic : List (Values Input)) :
    Memory.ByteAdapterEffects.replay (view s).memory.contents
      (rtlComponent.eventTrace (Memory.ByteAdapterRefinement.artifactEvents rtlComponent)
        (rtlComponent.step i s) traffic) =
      some (view (rtlComponent.run (rtlComponent.step i s) traffic)).memory.contents :=
  Memory.ByteAdapterRefinement.artifact_replay_after_reset correspondence i s h traffic

theorem reset_emits_no_completion (s : Values Register) (i : Values Input) (h : i reset = 1) :
    Memory.ByteAdapterRefinement.artifactEvents rtlComponent i s = [] :=
  Memory.ByteAdapterRefinement.artifact_reset_events correspondence i s h

end Pinwheel.TypedArtifact
"""


def certify(run, tools, directory, descriptor, a, rtl):
    imported, script = directory / "import.json", directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
        f"hierarchy -check -top {descriptor['module']}\nflatten -noscopeinfo\nproc\n"
        f"write_json {rr.yosys_quote(directory / 'before-pmuxtree.json')}\npmuxtree\nopt_clean\ncheck -assert\n"
        f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    modules, evidence = readback.generate(directory, descriptor, directory / "byte-adapter.mlir", imported,
        tools["z3"], profile=profile(a))
    evidence["finite_control_proof_search"] = split_two_bit_controls(directory, modules)
    evidence["byte_slice_proof_search"] = prepare_byte_slices(directory, modules)
    (directory / "ByteTrace.lean").write_text(trace_module(a))
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import ByteTrace"))
    modules.insert(-1, "ByteTrace")
    compile_modules(run, directory, modules)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise AssertionError("Missing byte adapter artifact/trace/final-state axiom audit")
    if evidence["endpoints"] != len(descriptor["registers"]) + len(descriptor["outputs"]):
        raise AssertionError("Incomplete byte adapter artifact certificate")
    return {**evidence, "typed_registers": len(descriptor["registers"]), "typed_outputs": len(descriptor["outputs"]),
            "arbitrary_raw_state_trace_checked": True, "projected_final_state_checked": True,
            "state_preserving_reset_trace_checked": True, "reset_final_state_checked": True,
            "reset_preserves_memory_q_metadata_checked": True, "reset_clears_pending_checked": True,
            "reset_masks_outputs_checked": True, "reset_establishes_snapshot_checked": True,
            "actual_completion_event_replay_checked": True, "reset_event_replay_checked": True,
            "reset_emits_no_completion_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", type=int, action="append", help="Optional distinct address widths from the RTL matrix")
    args = parser.parse_args()
    configurations = args.config or list(checks.MATRIX)
    if len(set(configurations)) != len(configurations) or not set(configurations) <= set(checks.MATRIX):
        parser.error("Require distinct address widths from the complete RTL matrix")
    out = fresh_directory(ROOT / "build/memory-byte-adapter-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "All imported unsynthesized binary state/output equations, including full RAM/Q and retained "
            "metadata. Projection permits multiple raw states per logical state; reset preserves words/Q/metadata "
            "and clears pending. No initial memory image, MMIO semantics or physical qualification. "
            "Actual output/request completion events reconstruct final RAM contents under snapshot validity; "
            "reset establishes this separately from arbitrary-state functional correspondence. "
            "Yosys proc/pmuxtree and restricted JSON interpretation remain trusted; pre-normalization JSON retained."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["python3", "test/test_readback_byte_slices.py"], "byte-slice-tests", timeout=120)
        run(["lake", "build", "Pinwheel.Hardware.Memory.ByteAdapterRefinement", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.DecodedImplementation", "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        result = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryByteAdapterRefinement.lean"],
                     "event-refinement-tests", timeout=900)
        if "standard axioms only" not in result:
            raise AssertionError("Missing hardware event refinement axiom audit")
        for a in configurations:
            directory = out / f"byte-{a}"
            directory.mkdir()
            run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryByteAdapterEmit.lean", a, directory],
                directory.name + "-emit")
            descriptor = json.loads((directory / "interface.json").read_text())
            checks.validate_descriptor(descriptor, a)
            rtl = directory / "byte-adapter.sv"
            rtl.write_text(run([tools["circt"], directory / "byte-adapter.mlir", "--canonicalize", "--lower-seq-to-sv",
                "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], directory.name + "-lower"))
            report["configurations"].append({"configuration": [a, 32],
                **certify(run, tools, directory, descriptor, a, rtl)})
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during byte adapter artifact certification")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
