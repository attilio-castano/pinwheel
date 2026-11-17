#!/usr/bin/env python3
"""Certify host accelerator RTL, preserved-memory reset, and final state."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import time

import typed_circuit_readback as readback
from readback_control_proofs import split_two_bit_controls
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("transfer_host_checks", ROOT / "scripts/check-memory-transfer-host.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)
rr = checks.rr


def sources():
    result = checks.source_hashes()
    for name in ("scripts/check-memory-transfer-host-artifact.py", "scripts/readback_control_proofs.py",
                 "Pinwheel/Hardware/RunRefinement.lean"):
        result[name] = sha(ROOT / name)
    result.update({str(path.relative_to(ROOT)): sha(path) for path in readback.source_paths()})
    return dict(sorted(result.items()))


def profile(a, wi, wo):
    return f"""import Pinwheel.Hardware.Memory.TransferHostCircuitProofs
import Pinwheel.Hardware.RunRefinement
import MemoryTransferSupport
abbrev Input := Memory.TransferHostInterface.Input {a} {wi} {wo}
abbrev Register := Memory.TransferHostCircuit.Register {a} {wi} {wo}
abbrev Output := Memory.TransferHostInterface.Output {wi} {wo}
abbrev transform := MemoryTransferSupport.transform {wi} {wo}
abbrev circuit := Memory.TransferHostCircuit.circuit (a := {a}) transform
abbrev inputs := Memory.TransferHostInterface.inputs {a} {wi} {wo}
abbrev registers := Memory.TransferHostCircuit.registers {a} {wi} {wo}
abbrev outputs := Memory.TransferHostInterface.outputs {wi} {wo}
"""


def certify(run, tools, directory, config, descriptor, rtl):
    a, wi, wo = config
    imported, script = directory / "import.json", directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
        f"hierarchy -check -top {descriptor['module']}\nflatten -noscopeinfo\nproc\n"
        f"write_json {rr.yosys_quote(directory / 'before-pmuxtree.json')}\npmuxtree\nopt_clean\ncheck -assert\n"
        f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    shutil.copyfile(ROOT / "test/MemoryTransferSupport.lean", directory / "MemoryTransferSupport.lean")
    compile_modules(run, directory, ["MemoryTransferSupport"])
    modules, evidence = readback.generate(directory, descriptor, directory / "transfer-host.mlir", imported,
        tools["z3"], profile=profile(a, wi, wo))
    evidence["finite_control_proof_search"] = split_two_bit_controls(directory, modules)
    (directory / "HostTrace.lean").write_text(f"""import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
theorem encoded_trace (s : Memory.TransferModel.State {a} {wi} {wo}) (h : s.control.Valid)
    (traffic : List (Values Input)) :
    rtlComponent.trace (Memory.TransferHostCircuit.encode s) traffic =
      (Memory.TransferHostInterface.spec transform).trace s traffic :=
  (trace_eq _ traffic).trans (Memory.TransferHostCircuit.trace_correct transform s h traffic)

theorem encoded_final_state (s : Memory.TransferModel.State {a} {wi} {wo}) (h : s.control.Valid)
    (traffic : List (Values Input)) :
    @Eq (Values Register) (rtlComponent.run (Memory.TransferHostCircuit.encode s) traffic)
      (Memory.TransferHostCircuit.encode ((Memory.TransferHostInterface.spec transform).run s traffic)) :=
  correspondence.encoded_run (Memory.TransferHostCircuit.implementation transform) s h traffic

theorem reset_state (s : Values Register) (i : Values Input)
    (h : i Memory.TransferHostInterface.reset = 1) :
    @Eq (Values Register) (rtlComponent.step i s)
      (Memory.TransferHostCircuit.encode (Memory.TransferHostCircuit.resetState s)) := by
  rw [correspondence.step_eq]
  exact funext fun b => funext fun r => Memory.TransferHostCircuit.reset_eq transform i s h (b := b) r

theorem state_preserving_reset_trace (s : Values Register) (i : Values Input)
    (h : i Memory.TransferHostInterface.reset = 1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Memory.TransferHostInterface.spec transform).trace (Memory.TransferHostCircuit.resetState s) traffic := by
  rw [trace_eq, correspondence.step_eq]
  exact Memory.TransferHostCircuit.trace_after_reset transform i s h traffic

theorem reset_final_state (s : Values Register) (i : Values Input)
    (h : i Memory.TransferHostInterface.reset = 1) (traffic : List (Values Input)) :
    @Eq (Values Register) (rtlComponent.run (rtlComponent.step i s) traffic)
      (Memory.TransferHostCircuit.encode ((Memory.TransferHostInterface.spec transform).run
        (Memory.TransferHostCircuit.resetState s) traffic)) := by
  rw [reset_state s i h]
  apply encoded_final_state
  simp [Memory.TransferHostCircuit.resetState, Memory.TransferModel.initialState,
    Memory.TransferModel.initialControl, Memory.TransferModel.Control.Valid, Memory.TransferModel.emptyConfig]

theorem recovery_trace (s : Values Register) (i : Values Input)
    (hr : i Memory.TransferHostInterface.reset = 0) (hp : s (.left .phase) = 3)
    (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Memory.TransferHostInterface.spec transform).trace (Memory.TransferHostCircuit.recoveryState s) traffic := by
  rw [trace_eq, correspondence.step_eq]
  exact Memory.TransferHostCircuit.trace_after_recovery transform i s hr hp traffic
end Pinwheel.TypedArtifact
""")
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import HostTrace"))
    modules.insert(-1, "HostTrace")
    compile_modules(run, directory, modules)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise AssertionError("Missing host artifact/trace/final-state axiom audit")
    if evidence["endpoints"] != len(descriptor["registers"]) + len(descriptor["outputs"]):
        raise AssertionError("Incomplete host accelerator artifact certificate")
    return {**evidence, "typed_registers": len(descriptor["registers"]), "typed_outputs": len(descriptor["outputs"]),
            "encoded_trace_checked": True, "encoded_final_state_checked": True,
            "state_preserving_reset_trace_checked": True, "reset_final_state_checked": True,
            "reserved_phase_recovery_trace_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer-host-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "All imported unsynthesized binary state/output equations, including both full memories/Q/pending. "
                    "Reset/recovery traces preserve arbitrary memory contents; encoded and post-reset final state "
                    "matches the host model. No implicit program/data initialization or physical qualification. "
                    "Yosys proc/pmuxtree and restricted JSON interpretation remain trusted; pre-normalization JSON retained."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.TransferHostCircuitProofs", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.RunRefinement", "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        checks.controller.prepare_support(run, out)
        for a, wi, wo in checks.MATRIX:
            directory = out / f"host-{a}-{wi}-{wo}"
            directory.mkdir()
            run(checks.controller.lean_command(out, "--run", "test/MemoryTransferHostEmit.lean", a, wi, wo, directory),
                directory.name + "-emit")
            descriptor = json.loads((directory / "interface.json").read_text())
            checks.validate_descriptor(descriptor, a, wi, wo)
            rtl = directory / "transfer-host.sv"
            rtl.write_text(run([tools["circt"], directory / "transfer-host.mlir", "--canonicalize", "--lower-seq-to-sv",
                "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], directory.name + "-lower"))
            report["configurations"].append({"configuration": [a, wi, wo],
                **certify(run, tools, directory, (a, wi, wo), descriptor, rtl)})
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during host artifact certification")
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
