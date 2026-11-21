#!/usr/bin/env python3
"""Check imported switch RTL against every structural state/output expression."""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import time

import process_group
import typed_circuit_readback as readback
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("selector_tools", ROOT / "scripts/check-round-robin-circuit.py")
rr = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(rr)


def sources():
    pending = [ROOT / "test/SwitchCircuitEmit.lean", ROOT / "Pinwheel/Hardware/Switch/Certified.lean"]
    found = set()
    while pending:
        path = pending.pop()
        if path in found:
            continue
        found.add(path)
        for module in re.findall(r"^import (Pinwheel\.[A-Za-z0-9_.]+)$", path.read_text(), re.M):
            pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    found.update(ROOT / path for path in (
        "scripts/check-switch-artifact.py", "scripts/typed_circuit_readback.py", "scripts/backend_readback.py",
        "scripts/check-round-robin-circuit.py", "scripts/validation_run.py", "scripts/process_group.py",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain", "tools/hardware-toolchain.json",
        "Pinwheel/Hardware/Readback/Boolean.lean"))
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(found)}


def profile(config, dw):
    n, m, d, w = config
    return f"""import Pinwheel.Hardware.Switch.Certified
abbrev encoding : Switch.Physical.DestinationEncoding {m} := ⟨{dw}, by decide +kernel, by decide +kernel⟩
abbrev Input := Switch.Physical.In {n-1} {m-1} {dw} {w}
abbrev Register := Switch.Structural.Register {n-1} {m-1} {dw} {w} {d}
abbrev Output := Switch.Physical.Out {n-1} {m-1} {w}
abbrev circuit := Switch.Structural.circuit encoding {n-1} {w} {d}
abbrev inputs := Switch.Physical.inputInterface {n-1} {m-1} {dw} {w}
abbrev registers := Switch.Structural.registers {n-1} {m-1} {dw} {w} {d}
abbrev outputs := Switch.Physical.outputInterface {n-1} {m-1} {w}
"""


def certify(run, tools, directory, config, descriptor, rtl):
    imported = directory / "import.json"
    script = directory / "import.ys"
    script.write_text(f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
                      f"hierarchy -check -top {descriptor['module']}\n"
                      "flatten -noscopeinfo\nproc\nopt_clean\ncheck -assert\n"
                      f"write_json {rr.yosys_quote(imported)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    modules, evidence = readback.generate(directory, descriptor, directory / "switch.mlir", imported,
                                         tools["z3"], profile=profile(config, descriptor["destination_width"]))
    n, m, d, w = config
    (directory / "Initialized.lean").write_text(f"""import Proof
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
theorem initialized_trace (s : Values Register) (i : Values Input)
    (h : i Switch.Physical.reset = 1) (traffic : List (Values Input)) :
    rtlComponent.trace (rtlComponent.step i s) traffic =
      (Switch.Physical.component encoding {d}).trace Switch.initial traffic :=
  Switch.Structural.artifact_initialized_trace encoding {n-1} {w} {d} (by decide +kernel)
    rtlComponent correspondence i s h traffic
end Pinwheel.TypedArtifact
""")
    # The final audit imports the composed reset/trace theorem as well.
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import Initialized"))
    modules.insert(-1, "Initialized")
    for module in modules:
        lean_path = str(directory) + os.pathsep + str(ROOT / ".lake/build/lib/lean")
        argv = ["env", "LEAN_PATH=" + lean_path, "lake", "env", "lean", "-DwarningAsError=true", "-o", directory / f"{module}.olean",
                directory / f"{module}.lean"]
        log = directory / f"{module}.log"
        started = time.monotonic()
        record = {"argv": list(map(str, argv)), "label": directory.name + "-" + module, "timeout_seconds": 300}
        run.records.append(record)
        result = process_group.run_captured(list(map(str, argv)), cwd=ROOT, timeout=300, log_path=log)
        record.update(exit_code=result.returncode, seconds=round(time.monotonic() - started, 3))
        if result.returncode:
            raise RuntimeError(f"{module} certificate failed: {log}\n{result.stdout[-3000:]}{result.stderr[-1000:]}")
        print(f"{directory.name}/{module}: checked", flush=True)
    return evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", help="INPUTS,OUTPUTS,DEPTH,WIDTH")
    args = parser.parse_args()
    configs = [tuple(map(int, c.split(","))) for c in args.config] if args.config else [(1, 1, 1, 1), (2, 3, 2, 8)]
    if any(len(c) != 4 or min(c) <= 0 for c in configs):
        parser.error("Configurations must contain four positive integers")
    out = fresh_directory(ROOT / "build/switch-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
              "boundary": "Lean checks all imported register/output equations and reset-initialized traces. "
                          "Yosys and restricted JSON interpretation are trusted; no physical timing claim."}
    run = rr.Commands(out, report["commands"])
    started = time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, tool_paths = rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        tool_paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(tool_paths)
        run(["lake", "build", "Pinwheel.Hardware.Switch.Certified", "Pinwheel.Hardware.Emit",
             "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        for config in configs:
            directory = out / ("switch-" + "-".join(map(str, config)))
            directory.mkdir()
            run(["lake", "env", "lean", "--run", "test/SwitchCircuitEmit.lean", *config, directory],
                directory.name + "-emit")
            descriptor = json.loads((directory / "interface.json").read_text())
            rtl = directory / "switch.sv"
            rtl.write_text(run([tools["circt"], directory / "switch.mlir", "--canonicalize", "--lower-seq-to-sv",
                               "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"],
                              directory.name + "-lower"))
            evidence = certify(run, tools, directory, config, descriptor, rtl)
            report["configurations"].append({"configuration": config, **evidence})
        if sources() != report["source_sha256"] or rr.tool_hashes(tool_paths) != report["tool_sha256"]:
            raise RuntimeError("Sources/tools changed during certification; rerun under a fresh tag")
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
