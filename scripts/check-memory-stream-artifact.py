#!/usr/bin/env python3
"""Prove imported stream RAM transitions, arbitrary-state traces and memory-preserving reset."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import time

import typed_circuit_readback as readback
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("stream_memory_validation", ROOT / "scripts/check-memory-stream.py")
memory = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(memory)
rr = memory.rr


def sources():
    result = memory.sources()
    for path in ("scripts/check-memory-stream-artifact.py", "scripts/typed_circuit_readback.py",
                 "scripts/backend_readback.py", "scripts/typed_artifact_runner.py",
                 "scripts/readback_boolean_abstraction.py",
                 "Pinwheel/Hardware/Artifact.lean", "Pinwheel/Hardware/Readback/Boolean.lean"):
        result[path] = sha(ROOT / path)
    result.update({str(path.relative_to(ROOT)): sha(path) for path in readback.source_paths()})
    return dict(sorted(result.items()))


def profile(a, w):
    return f"""import Pinwheel.Hardware.Memory.StreamFlopsProofs
abbrev Input := Memory.StreamInterface.Input {a} {w}
abbrev Register := Memory.StreamFlops.Register {a} {w}
abbrev Output := Memory.StreamInterface.Output {w}
abbrev circuit := Memory.StreamFlops.circuit {a} {w}
abbrev inputs := Memory.StreamInterface.inputs {a} {w}
abbrev registers := Memory.StreamFlops.registers {a} {w}
abbrev outputs := Memory.StreamInterface.outputs {w}
"""


def certify(run, tools, directory, descriptor, a, w, rtl):
    imported, script = directory / "import.json", directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
        f"hierarchy -check -top {descriptor['module']}\nflatten -noscopeinfo\nproc\nopt_clean\ncheck -assert\n"
        f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    modules, evidence = readback.generate(directory, descriptor, directory / "memory.mlir", imported,
                                          tools["z3"], profile=profile(a, w))
    (directory / "MemoryTrace.lean").write_text("""import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
theorem memory_trace (s : Values Register) (traffic : List (Values Input)) :
    rtlComponent.trace s traffic =
      (Memory.StreamInterface.spec _ _).trace (Memory.StreamFlops.view s) traffic :=
  (trace_eq s traffic).trans (Memory.StreamFlops.trace_correct s traffic)

theorem state_preserving_reset_trace (s : Values Register) (i : Values Input)
    (h : i Memory.StreamInterface.reset = 1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Memory.StreamInterface.spec _ _).trace ⟨(Memory.StreamFlops.view s).memory, false⟩ traffic := by
  rw [trace_eq, correspondence.step_eq]
  exact Memory.StreamFlops.trace_after_reset i s h traffic

theorem reset_preserves_memory (s : Values Register) (i : Values Input)
    (h : i Memory.StreamInterface.reset = 1) (r : Memory.CommandFlops.Register _ _ b) :
    rtlComponent.step i s (.left r) = s (.left r) := by
  exact (congrFun (congrFun (correspondence.step_eq i s) b) (.left r)).trans
    (Memory.StreamFlops.reset_memory i s h r)

theorem reset_clears_pending (s : Values Register) (i : Values Input)
    (h : i Memory.StreamInterface.reset = 1) :
    rtlComponent.step i s Memory.StreamFlops.pending = 0 := by
  exact (congrFun (congrFun (correspondence.step_eq i s) 1) Memory.StreamFlops.pending).trans
    (Memory.StreamFlops.reset_pending i s h)
end Pinwheel.TypedArtifact
""")
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import MemoryTrace"))
    modules.insert(-1, "MemoryTrace")
    compile_modules(run, directory, modules)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise AssertionError("Missing composed stream-memory artifact audit")
    if evidence["endpoints"] != len(descriptor["registers"]) + len(descriptor["outputs"]):
        raise AssertionError("Certificate omitted a typed endpoint")
    return {**evidence, "all_state_trace_checked": True, "reset_preserves_memory_and_q_checked": True,
            "reset_clears_pending_checked": True, "state_preserving_reset_trace_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-stream-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "Lean checks all imported state/output equations and stream memory traces from arbitrary "
        "initial words/Q/pending. Reset clears pending and preserves every word and Q; no fixed memory initialization. Yosys and restricted JSON interpretation remain trusted. No synthesis, four-state or physical qualification."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Memory.StreamFlopsProofs", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.Artifact", "Pinwheel.Hardware.Readback.Boolean"], "build")
        for a, w in memory.command.CONFIGS:
            directory = out / f"memory-{a}-{w}"
            directory.mkdir()
            run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/MemoryStreamEmit.lean", a, w, directory], directory.name + "-emit")
            descriptor = json.loads((directory / "interface.json").read_text())
            memory.validate_descriptor(descriptor, a, w)
            rtl = directory / "memory.sv"
            rtl.write_text(run([tools["circt"], directory / "memory.mlir", "--canonicalize", "--lower-seq-to-sv",
                "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], directory.name + "-lower"))
            evidence = certify(run, tools, directory, descriptor, a, w, rtl)
            report["configurations"].append({"configuration": [a, w], **evidence})
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during certification")
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
