#!/usr/bin/env python3
"""Certify and synthesize the same 2x2 depth-three switch with both FIFO layouts."""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path

import typed_circuit_readback as readback
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("switch_checks", ROOT / "scripts/check-switch-artifact.py")
switch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(switch)
rr = switch.rr
BACKENDS = {"shift": "Stream.BackendAPI.shift 5 3 (by decide +kernel)",
            "circular": "Stream.CircularFifo3.backend 5"}


def source_hashes():
    hashes = switch.sources(("test/SwitchFifoEmit.lean",))
    hashes[str(Path(__file__).resolve().relative_to(ROOT))] = sha(Path(__file__))
    return hashes


def profile(kind):
    return f"""import Pinwheel.Hardware.Switch.Backend
import Pinwheel.Hardware.Stream.CircularFifo3
abbrev encoding : Switch.Physical.DestinationEncoding 2 := ⟨1, by decide +kernel, by decide +kernel⟩
abbrev fifo := {BACKENDS[kind]}
abbrev Input := Switch.Physical.In 1 1 1 4
abbrev Output := Switch.Physical.Out 1 1 4
abbrev Register := Switch.WithFifo.Register 1 1 4 fifo.Register
abbrev circuit : Circuit Input Register Output := Switch.WithFifo.circuit (w := 4) (depth := 3) encoding fifo 1
abbrev inputs := Switch.Physical.inputInterface 1 1 1 4
abbrev outputs := Switch.Physical.outputInterface 1 1 4
abbrev registers := Switch.WithFifo.registers fifo 1 1 4
"""


TRACE = """import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
theorem initialized_trace (r : Values Register) (i : Values Input) (h : i Switch.Physical.reset = 1)
    (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i r) traffic =
      (Switch.Physical.component encoding 3).trace Switch.initial traffic :=
  Switch.WithFifo.artifact_initialized_trace (w := 4) (depth := 3) encoding fifo rtlComponent correspondence i r h traffic
end Pinwheel.TypedArtifact
"""


def configuration(run, tools, out, kind):
    directory = out / kind
    directory.mkdir()
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/SwitchFifoEmit.lean",
         kind, directory], kind + "-emit")
    descriptor = json.loads((directory / "interface.json").read_text())
    name = descriptor["module"]
    mlir, rtl = directory / "switch.mlir", directory / "switch.sv"
    rtl.write_text(run([tools["circt"], mlir, "--lower-seq-to-sv",
                        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog",
                        "-o", "/dev/null"], kind + "-lower"))
    imported, mapped = directory / "import.json", directory / "mapped.json"
    script = directory / "compare.ys"
    front = f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {name}\n"
    script.write_text(front + "proc\npmuxtree\nopt_clean\ncheck -assert\n"
                      + f"write_json {rr.yosys_quote(imported)}\ndesign -reset\n"
                      + front + f"synth -top {name}\ncheck -assert\nwrite_json {rr.yosys_quote(mapped)}\n")
    run([tools["yosys"], "-Q", "-s", script], kind + "-yosys")
    cells = Counter(c["type"] for c in json.loads(mapped.read_text())["modules"][name]["cells"].values())
    modules, evidence = readback.generate(directory, descriptor, mlir, imported, tools["z3"], profile=profile(kind))
    (directory / "Initialized.lean").write_text(TRACE)
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import Initialized"))
    modules.insert(-1, "Initialized")
    compile_modules(run, directory, modules)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise RuntimeError("Missing Lean axiom audit")
    return {**evidence, "registers": len(descriptor["registers"]), "outputs": len(descriptor["outputs"]),
            "rtl_state_bits": sum(p["width"] for p in descriptor["registers"]),
            "mapped_cells": cells.total(), "mapped_flip_flops": sum(v for k, v in cells.items() if "DFF" in k),
            "mapped_cell_types": dict(sorted(cells.items())), "initialized_trace_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/switch-fifo-backends", args.tag)
    report = {"status": "running", "commands": [], "configurations": {}}
    run = rr.Commands(out, report["commands"])
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [tools["z3"], cad / "libexec/z3"]
        report["tool_sha256"] = rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Switch.Backend", "Pinwheel.Hardware.Stream.CircularFifo3",
             "Pinwheel.Hardware.Emit", "Pinwheel.Hardware.Readback.Boolean"], "build")
        for kind in BACKENDS:
            report["configurations"][kind] = configuration(run, tools, out, kind)
        if report["source_sha256"] != source_hashes() or report["tool_sha256"] != rr.tool_hashes(paths):
            raise RuntimeError("Campaign inputs changed during run")
        report["status"] = "passed"
    except BaseException as error:
        report.update(status="failed", error=str(error))
        raise
    finally:
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
