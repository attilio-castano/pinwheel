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
import typed_circuit_hierarchy as hierarchy
import typed_module_checks as module_checks
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
    for path in (*hierarchy.source_paths(), *module_checks.source_paths(), ROOT / "scripts/readback_miter.py"):
        result[str(path.relative_to(ROOT))] = sha(path)
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
    imported, script = directory / "import.json", directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
        f"hierarchy -check -top {descriptor['module']}\nflatten -noscopeinfo\nproc\n"
        f"write_json {rr.yosys_quote(directory / 'before-pmuxtree.json')}\npmuxtree\nopt_clean\ncheck -assert\n"
        f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    return prove_imported(run, tools, directory, config, descriptor, directory / "transfer-host.mlir")


def prove_imported(run, tools, directory, config, descriptor, mlir, *, profile_text=None, path_checks=""):
    a, wi, wo = config
    shutil.copyfile(ROOT / "test/MemoryTransferSupport.lean", directory / "MemoryTransferSupport.lean")
    compile_modules(run, directory, ["MemoryTransferSupport"])
    modules, evidence = readback.generate(directory, descriptor, mlir, directory / "import.json",
        tools["z3"], profile=profile_text or profile(a, wi, wo), interface_checks=path_checks)
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


def certify_hierarchy(run, tools, directory, config, descriptor, canonical, *, miswire):
    a, wi, wo = config
    leaves = hierarchy.lower_leaves(run, tools, directory, descriptor)
    imported = hierarchy.import_assembly(run, tools, directory, descriptor, leaves, normalize_muxes=True)
    if imported != canonical:
        raise ValueError("Imported hierarchy has a different canonical port mapping")
    startup, rows, coverage = checks.reference.stimulus(a, wi, wo)
    frames, events, ledger = checks.reference.oracle(a, wi, wo, startup, rows)
    for filename, data in (("startup.json", startup), ("traffic.json", rows), ("expected.json", frames),
                           ("events.json", events), ("ledger.json", ledger)):
        (directory / filename).write_text(json.dumps(data, indent=2) + "\n")
    tb, executable = directory / "tb.sv", directory / "replay.vvp"
    tb.write_text(checks.testbench(descriptor, startup, rows, registers=True))
    run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable,
         directory / "hierarchical.sv", tb], directory.name + "-compile-replay")
    replay = run([tools["vvp"], executable], directory.name + "-replay")
    (directory / "replay.txt").write_text(replay)
    checks.memory.check_trace(replay, checks.controller.expected(frames, True))

    top = json.dumps(descriptor["module"])
    profile_text = (profile(a, wi, wo) + "import Pinwheel.Hardware.Memory.TransferHostExport\n"
                    + f"abbrev assembly := Memory.TransferHostExport.hierarchy transform {a} {top}\n")
    paths = hierarchy.path_checks(descriptor, "assembly")
    mlir = directory / "flat.mlir"
    evidence = prove_imported(run, tools, directory, config, imported, mlir,
                              profile_text=profile_text, path_checks=paths)
    if miswire:
        evidence["miswire"] = hierarchy.check_miswire(
            run, tools, directory, descriptor, leaves, mlir, profile_text, paths,
            ("source", "destination"), "req_data", normalize_muxes=True,
            proof_search=split_two_bit_controls, extra_lean_paths=(directory,),
        )
    return {**evidence, "replay_cycles": len(rows), "replay_coverage": coverage}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--hierarchy", action="store_true", help="Check the smallest three-instance accelerator")
    parser.add_argument("--miswire", action="store_true", help="Swap the two memory write-data connections")
    args = parser.parse_args()
    if args.miswire and not args.hierarchy:
        parser.error("--miswire requires --hierarchy")
    family = "memory-transfer-host-hierarchy" if args.hierarchy else "memory-transfer-host-artifact"
    out = fresh_directory(ROOT / "build" / family, args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "All imported unsynthesized binary state/output equations, including both full memories/Q/pending. "
                    "Reset/recovery traces preserve arbitrary memory contents; encoded and post-reset final state "
                    "matches the host model. No implicit program/data initialization or physical qualification. "
                    "Yosys proc/pmuxtree and restricted JSON interpretation remain trusted; pre-normalization JSON retained."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = module_checks.tool_config()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.TransferHostCircuitProofs", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.RunRefinement", "Pinwheel.Hardware.Readback.Boolean",
             "Pinwheel.Hardware.Memory.TransferHostExport"], "build", timeout=900)
        checks.controller.prepare_support(run, out)
        configs = checks.MATRIX[:1] if args.hierarchy else checks.MATRIX
        for a, wi, wo in configs:
            directory = out / f"host-{a}-{wi}-{wo}"
            directory.mkdir()
            flags = ["--hierarchy"] if args.hierarchy else []
            run(checks.controller.lean_command(out, "--run", "test/MemoryTransferHostEmit.lean",
                                               *flags, a, wi, wo, directory), directory.name + "-emit")
            descriptor = json.loads((directory / "interface.json").read_text())
            config = (a, wi, wo)
            if args.hierarchy:
                canonical = hierarchy.normalize_descriptor(descriptor)
                checks.validate_descriptor(canonical, *config)
                evidence = certify_hierarchy(run, tools, directory, config, descriptor, canonical,
                                             miswire=args.miswire)
            else:
                checks.validate_descriptor(descriptor, *config)
                rtl = directory / "transfer-host.sv"
                rtl.write_text(run([tools["circt"], directory / "transfer-host.mlir", "--canonicalize",
                    "--lower-seq-to-sv", "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog",
                    "-o", "/dev/null"], directory.name + "-lower"))
                evidence = certify(run, tools, directory, config, descriptor, rtl)
            report["configurations"].append({"configuration": config, **evidence})
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
