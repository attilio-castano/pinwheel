#!/usr/bin/env python3
"""Certify every buffered merge state/output equation and initialized trace."""
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
SPEC = importlib.util.spec_from_file_location("merge_checks", ROOT / "scripts/check-buffered-merge.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)
rr = checks.rr


def sources():
    result = checks.source_hashes()
    result["scripts/check-buffered-merge-artifact.py"] = sha(Path(__file__))
    result.update({str(path.relative_to(ROOT)): sha(path) for path in readback.source_paths()})
    return dict(sorted(result.items()))


def profile(n, w):
    return f"""import Pinwheel.Hardware.Stream.BufferedMerge.Proofs
abbrev Input := Stream.BufferedMerge.Physical.In {n-1} {w}
abbrev Register := Stream.BufferedMerge.Structural.Register {n-1} {w}
abbrev Output := Stream.BufferedMerge.Physical.Out {n-1} {w}
abbrev circuit := Stream.BufferedMerge.Structural.circuit {n-1} {w}
abbrev inputs := Stream.BufferedMerge.Physical.inputInterface {n-1} {w}
abbrev registers := Stream.BufferedMerge.Structural.registers {n-1} {w}
abbrev outputs := Stream.BufferedMerge.Physical.outputInterface {n-1} {w}
"""


def certify(run, tools, directory, config, descriptor, rtl):
    n, w = config
    imported, script = directory / "import.json", directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
        f"hierarchy -check -top {descriptor['module']}\nflatten -noscopeinfo\nproc\nopt_clean\ncheck -assert\n"
        f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    modules, evidence = readback.generate(directory, descriptor, directory / "merge.mlir", imported,
        tools["z3"], profile=profile(n, w))
    # Eight-way winner trees exceed grind's default term-generation depth.
    # Expand bitwise operations first, then search more deeply. Only tactics
    # change: every raw-state proposition and the standard-axiom audit remain.
    for module in modules:
        if module.startswith("LocalProofs"):
            path = directory / (module + ".lean")
            path.write_text(path.read_text().replace("  | rfl\n", "  | rfl\n"
                "  | (simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ,\n"
                "      BitVec.getElem_and, BitVec.getElem_not];\n"
                "      all_goals grind (splits := 64) (gen := 16))\n"))
    (directory / "Initialized.lean").write_text(f"""import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
theorem initialized_trace (s : Values Register) (i : Values Input)
    (h : i Stream.BufferedMerge.Physical.reset = 1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Stream.BufferedMerge.Physical.component {n-1} {w}).trace Stream.BufferedMerge.initial traffic :=
  correspondence.initialized_trace
    (Stream.BufferedMerge.Structural.implementation {n-1} {w})
    Stream.BufferedMerge.Physical.reset
    (Stream.BufferedMerge.Structural.resetCertificate {n-1} {w}) i s h traffic
end Pinwheel.TypedArtifact
""")
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import Initialized"))
    modules.insert(-1, "Initialized")
    compile_modules(run, directory, modules)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise AssertionError("Missing buffered merge artifact/initialized-trace axiom audit")
    if evidence["endpoints"] != len(descriptor["registers"]) + len(descriptor["outputs"]):
        raise AssertionError("Incomplete buffered merge artifact certificate")
    return {**evidence, "typed_registers": len(descriptor["registers"]), "typed_outputs": len(descriptor["outputs"]),
        "initialized_trace_checked": True,
        "correspondence_scope": "All binary inputs/registers, including arbitrary cursor bits",
        "protocol_trace_scope": "Arbitrary register state followed by reset and arbitrary raw input traffic"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", type=checks.parse_config)
    args = parser.parse_args()
    configs = args.config or checks.MATRIX
    if len(configs) != len(set(configs)):
        parser.error("Configurations must be distinct")
    out = fresh_directory(ROOT / "build/buffered-merge-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "boundary": "All imported unsynthesized binary register/output equations, composed with generic "
                    "implementation and reset certificates. Source endpoints reduce to the declared circuit "
                    "by rfl. Yosys and restricted JSON interpretation remain trusted. No four-state, "
                    "post-synthesis proof, physical timing or fabrication claim."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Stream.BufferedMerge.Proofs", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        for n, w in configs:
            directory = out / f"merge-{n}-{w}"
            directory.mkdir()
            run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/BufferedMergeEmit.lean", n, w, directory],
                directory.name + "-emit")
            descriptor = json.loads((directory / "interface.json").read_text())
            checks.validate_descriptor(descriptor, n, w)
            rtl = directory / "merge.sv"
            rtl.write_text(run([tools["circt"], directory / "merge.mlir", "--canonicalize", "--lower-seq-to-sv",
                "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], directory.name + "-lower"))
            report["configurations"].append({"configuration": [n, w],
                **certify(run, tools, directory, (n, w), descriptor, rtl)})
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during buffered merge artifact certification")
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
