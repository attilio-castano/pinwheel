#!/usr/bin/env python3
"""Certify the imported shared-selection switch and its reset-initialized traces.

The profile names the candidate circuit itself. Every emitted source-hint
endpoint must reduce to that circuit by rfl; a certificate for the old selector
cannot substitute for this artifact correspondence.
"""
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
SPEC = importlib.util.spec_from_file_location("shared_candidate_checks", ROOT / "scripts/check-switch-shared-selection.py")
candidate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(candidate)
sw, rr = candidate.sw, candidate.rr


def sources():
    result = candidate.source_hashes()
    for name in ("scripts/check-switch-shared-artifact.py", "scripts/typed_circuit_readback.py",
                 "scripts/backend_readback.py", "scripts/typed_artifact_runner.py",
                 "scripts/readback_boolean_abstraction.py", "Pinwheel/Hardware/Readback/Boolean.lean"):
        result[name] = sha(ROOT / name)
    result.update({str(path.relative_to(ROOT)): sha(path) for path in readback.source_paths()})
    return dict(sorted(result.items()))


def profile(config, dw):
    n, m, d, w = config
    return f"""import Pinwheel.Hardware.Switch.SharedSelectionCandidate
abbrev encoding : Switch.Physical.DestinationEncoding {m} := ⟨{dw}, by decide +kernel, by decide +kernel⟩
abbrev Input := Switch.Physical.In {n-1} {m-1} {dw} {w}
abbrev Register := Switch.Structural.Register {n-1} {m-1} {dw} {w} {d}
abbrev Output := Switch.Physical.Out {n-1} {m-1} {w}
abbrev circuit := Switch.SharedSelectionCandidate.circuit encoding {n-1} {w} {d}
abbrev inputs := Switch.Physical.inputInterface {n-1} {m-1} {dw} {w}
abbrev registers := Switch.Structural.registers {n-1} {m-1} {dw} {w} {d}
abbrev outputs := Switch.Physical.outputInterface {n-1} {m-1} {w}
"""


def certify(run, tools, directory, config, descriptor, rtl):
    imported, script = directory / "import.json", directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
                      f"hierarchy -check -top {descriptor['module']}\n"
                      "flatten -noscopeinfo\nproc\nopt_clean\ncheck -assert\n"
                      f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    modules, evidence = readback.generate(directory, descriptor, directory / "switch.mlir", imported,
                                          tools["z3"], profile=profile(config, descriptor["destination_width"]))
    n, _, d, w = config
    (directory / "Initialized.lean").write_text(f"""import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
theorem initialized_trace (s : Values Register) (i : Values Input)
    (h : i Switch.Physical.reset = 1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Switch.Physical.component encoding {d}).trace Switch.initial traffic :=
  correspondence.initialized_trace
    (Switch.SharedSelectionCandidate.implementation encoding {n-1} {w} {d} (by decide +kernel))
    Switch.Physical.reset
    (Switch.SharedSelectionCandidate.resetCertificate encoding {n-1} {w} {d} (by decide +kernel))
    i s h traffic
end Pinwheel.TypedArtifact
""")
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import Initialized"))
    modules.insert(-1, "Initialized")
    compile_modules(run, directory, modules)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise AssertionError("Missing final artifact and initialized-trace axiom audit")
    expected_endpoints = len(descriptor["registers"]) + len(descriptor["outputs"])
    if evidence["endpoints"] != expected_endpoints:
        raise AssertionError("Certificate omitted a typed register or output")
    return {**evidence, "typed_registers": len(descriptor["registers"]),
            "typed_outputs": len(descriptor["outputs"]), "initialized_trace_checked": True,
            "candidate_source_hints_checked_by": "rfl at every typed next-state/output endpoint",
            "correspondence_scope": "All binary inputs and register states; no legal-cursor assumption",
            "protocol_trace_scope": "Arbitrary binary initial state, followed by a reset edge and arbitrary traffic"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", type=sw.model_checks.parse_config)
    args = parser.parse_args()
    configs = args.config or sw.MATRIX
    if len(configs) != len(set(configs)):
        parser.error("Configurations must be distinct")
    out = fresh_directory(ROOT / "build/switch-shared-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
              "boundary": "Lean checks every imported candidate register/output equation for arbitrary binary "
                          "inputs/state and composes that correspondence with the candidate implementation/reset "
                          "certificate to prove reset-initialized protocol traces. Source hints reduce to the "
                          "candidate circuit itself by rfl. Z3 proposes cuts; Lean checks generated obligations. "
                          "Yosys import and restricted JSON interpretation remain trusted. This certifies the "
                          "imported unsynthesized two-state RTL interpretation; no post-synthesis, four-state, "
                          "physical area/timing or fabrication claim.",
              "tool_hash_scope": "Selected launchers, executables, Z3, ABC and Icarus backend; "
                                 "not complete host dynamic-library closure."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Switch.SharedSelectionCandidate", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        for config in configs:
            directory = out / ("shared-" + "-".join(map(str, config)))
            directory.mkdir()
            emission = run(["lake", "env", "lean", "-DwarningAsError=true", "--run",
                            "test/SwitchSharedSelectionEmit.lean", *config, directory], directory.name + "-emit")
            if "Shared switch audit:" not in emission or "standard axioms only" not in emission:
                raise AssertionError("Missing shared candidate proof audit")
            descriptor = sw.descriptor(directory / "interface.json", config)
            rtl = directory / "switch.sv"
            rtl.write_text(run([tools["circt"], directory / "switch.mlir", "--canonicalize", "--lower-seq-to-sv",
                               "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"],
                              directory.name + "-lower"))
            report["configurations"].append({"configuration": config,
                **certify(run, tools, directory, config, descriptor, rtl)})
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during certification; use a fresh tag")
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
