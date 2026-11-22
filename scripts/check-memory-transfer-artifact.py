#!/usr/bin/env python3
"""Certify every imported transfer-controller state/output endpoint and trace."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import time

import typed_circuit_readback as readback
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("transfer_checks", ROOT / "scripts/check-memory-transfer.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)
rr = checks.rr


def sources():
    result = checks.source_hashes()
    result["scripts/check-memory-transfer-artifact.py"] = sha(Path(__file__))
    result.update({str(path.relative_to(ROOT)): sha(path) for path in readback.source_paths()})
    return dict(sorted(result.items()))


def profile(a, wi, wo):
    return f"""import Pinwheel.Hardware.Memory.TransferCircuitProofs
import MemoryTransferSupport
abbrev Input := Memory.TransferInterface.Input {a} {wi}
abbrev Register := Memory.TransferCircuit.Register {a}
abbrev Output := Memory.TransferInterface.Output {a} {wo}
abbrev transform := MemoryTransferSupport.transform {wi} {wo}
abbrev circuit := Memory.TransferCircuit.circuit (a := {a}) transform
abbrev inputs := Memory.TransferInterface.inputs {a} {wi}
abbrev registers := Memory.TransferCircuit.registers {a}
abbrev outputs := Memory.TransferInterface.outputs {a} {wo}
"""


def certify(run, tools, directory, config, descriptor, rtl):
    a, wi, wo = config
    imported, script = directory / "import.json", directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
        f"hierarchy -check -top {descriptor['module']}\nflatten -noscopeinfo\nproc\n"
        f"write_json {rr.yosys_quote(directory / 'before-pmuxtree.json')}\npmuxtree\nopt_clean\ncheck -assert\n"
        f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    # Compile from the hashed source into this certificate's own import directory.
    shutil.copyfile(ROOT / "test/MemoryTransferSupport.lean", directory / "MemoryTransferSupport.lean")
    compile_modules(run, directory, ["MemoryTransferSupport"])
    modules, evidence = readback.generate(directory, descriptor, directory / "transfer.mlir", imported,
        tools["z3"], profile=profile(a, wi, wo))
    (directory / "Initialized.lean").write_text(f"""import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
theorem initialized_trace (s : Values Register) (i : Values Input)
    (h : i Memory.TransferInterface.reset = 1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Memory.TransferInterface.spec transform).trace (Memory.TransferModel.initialControl {a}) traffic :=
  correspondence.initialized_trace
    (Memory.TransferCircuit.implementation (a := {a}) transform)
    Memory.TransferInterface.reset
    (Memory.TransferCircuit.resetCertificate (a := {a}) transform)
    i s h traffic
end Pinwheel.TypedArtifact
""")
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import Initialized"))
    modules.insert(-1, "Initialized")
    compile_modules(run, directory, modules)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise AssertionError("Missing final artifact/trace axiom audit")
    if evidence["endpoints"] != len(descriptor["registers"]) + len(descriptor["outputs"]):
        raise AssertionError("Incomplete transfer artifact certificate")
    return {**evidence, "typed_registers": len(descriptor["registers"]), "typed_outputs": len(descriptor["outputs"]),
            "initialized_trace_checked": True,
            "scope": "Every binary input/state valuation, including phase3 and memory_reset; initialized open-controller traces"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Kernel-checked imported unsynthesized two-state RTL correspondence for every controller register "
                    "and output; composed reset-initialized open-controller trace theorem. External memory semantics, "
                    "whole-accelerator correctness, synthesis preservation and physical timing are separate gates. "
                    "Yosys proc/pmuxtree normalization and the restricted JSON interpretation remain trusted; "
                    "pre-normalization JSON is retained. Z3 only proposes cuts."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.TransferCircuitProofs", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.Artifact", "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        checks.prepare_support(run, out)
        for a, wi, wo in checks.MATRIX:
            directory = out / f"transfer-{a}-{wi}-{wo}"
            directory.mkdir()
            run(checks.lean_command(out, "--run", "test/MemoryTransferEmit.lean", a, wi, wo, directory), directory.name + "-emit")
            descriptor = json.loads((directory / "interface.json").read_text())
            checks.validate_descriptor(descriptor, a, wi, wo)
            rtl = directory / "transfer.sv"
            rtl.write_text(run([tools["circt"], directory / "transfer.mlir", "--canonicalize", "--lower-seq-to-sv",
                "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], directory.name + "-lower"))
            report["configurations"].append({"configuration": [a, wi, wo],
                **certify(run, tools, directory, (a, wi, wo), descriptor, rtl)})
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during transfer certification")
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
