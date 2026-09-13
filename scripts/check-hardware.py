#!/usr/bin/env python3
"""Reproduce Lean/RTL countdown checks, negative fixtures, and generic synthesis."""
import collections
import hashlib
import json
import platform
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "build/hardware"
MANIFEST = ROOT / "tools/hardware-toolchain.json"


def run(args, *, log=None, reject=None):
    result = subprocess.run([str(x) for x in args], cwd=ROOT, text=True, capture_output=True)
    text = result.stdout + result.stderr
    if log:
        (OUT / log).write_text(text)
    if reject:
        if result.returncode == 0 or "FATAL:" not in text or reject not in text:
            raise RuntimeError(f"Negative fixture was not rejected for {reject}:\n{text}")
    elif result.returncode:
        raise RuntimeError(f"Command failed: {args}\n{text}")
    return text


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "report.json").unlink(missing_ok=True)
    manifest = json.loads(MANIFEST.read_text())
    circt = ROOT / "build/tools" / manifest["packages"]["circt"]["directory"] / "bin/circt-opt"
    suite = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"] / "bin"
    for binary in [circt, suite / "iverilog", suite / "vvp", suite / "yosys"]:
        if not binary.is_file():
            raise SystemExit("Run python3 scripts/install-hardware-tools.py first")
    lake = shutil.which("lake")
    if not lake:
        raise SystemExit("The pinned Lean toolchain must be installed and on PATH")
    versions = {
        "circt": run([circt, "--version"], log="circt-version.log").strip(),
        "yosys": run([suite / "yosys", "-V"], log="yosys-version.log").strip(),
        "iverilog": run([suite / "iverilog", "-V"], log="iverilog-version.log").splitlines()[0],
    }
    print("Checking Lean proofs and executable contracts", flush=True)
    run([lake, "build"], log="lean-build.log")
    for name in ["Encoding", "Hardware"]:
        print(run([lake, "env", "lean", "-DwarningAsError=true", "--run", f"test/{name}.lean"],
                  log=f"{name.lower()}-checks.log").strip(), flush=True)

    axioms = [
        "byte_decrement_wrap",
        "Encoding.decode_encode", "Encoding.encode_decode", "Encoding.checked_exact",
        "Raw.step_encoded", "Raw.run_encoded", "Raw.malformed_fault",
        "Countdown.tick_refines", "Countdown.boundary_refines", "Countdown.countdown",
        "Countdown.boundary_exact", "Countdown.completed_exact", "Countdown.engine_countdown",
        "Countdown.reset_priority", "Countdown.load_priority",
    ]
    (OUT / "Axioms.lean").write_text("import Pinwheel\n" + "\n".join(
        f"#print axioms Pinwheel.Hardware.{name}" for name in axioms) + "\n")
    audit = run([lake, "env", "lean", "-DwarningAsError=true", "build/hardware/Axioms.lean"],
                log="axioms.log")
    # Fail closed if the printed audit acquires any nonstandard axiom name.
    import re
    dependencies = re.findall(r"depends on axioms: \[([^]]*)\]", audit)
    if len(dependencies) != len(axioms):
        raise RuntimeError("Incomplete axiom audit")
    for group in dependencies:
        if set(filter(None, (x.strip() for x in group.split(",")))) - {
            "propext", "Classical.choice", "Quot.sound"
        }:
            raise RuntimeError(f"Unexpected proof assumptions: {group}")

    # In this CIRCT release, export-verilog is an opt pass writing Verilog to stdout.
    rtl = run([circt, "build/hardware/countdown.mlir", "--canonicalize", "--lower-seq-to-sv",
               "--lower-hw-to-sv", "--export-verilog", "-o", "/dev/null"])
    (OUT / "countdown.sv").write_text(rtl)

    def simulate(source, name, reject=None):
        executable = f"build/hardware/{name}.vvp"
        run([suite / "iverilog", "-g2012", "-s", "countdown_tb", "-o", executable,
             source, "test/countdown_tb.sv"], log=f"{name}-compile.log")
        return run([suite / "vvp", executable, f"+trace=build/hardware/{name}.csv"],
                   log=f"{name}.log", reject=reject)

    print(simulate("build/hardware/countdown.sv", "countdown-rtl").strip(), flush=True)
    lean_trace, rtl_trace = OUT / "countdown-lean.csv", OUT / "countdown-rtl.csv"
    if lean_trace.read_bytes() != rtl_trace.read_bytes():
        raise RuntimeError("Lean/RTL trace mismatch")
    edges = len(rtl_trace.read_text().splitlines()) - 1

    mutations = {
        "wrong-decrement": ("r_remaining - 8'h1", "r_remaining - 8'h2", "STATE edge"),
        "early-boundary": ("r_remaining == 8'h0", "r_remaining == 8'h1", "BOUNDARY edge"),
        "load-over-reset": ("reset ? 8'h0", "(reset & ~load) ? 8'h0", "STATE edge"),
    }
    for name, (before, after, failure) in mutations.items():
        if rtl.count(before) != 1:
            raise RuntimeError(f"Review {name} fixture for changed CIRCT output")
        source = OUT / f"{name}.sv"
        source.write_text(rtl.replace(before, after))
        simulate(source.relative_to(ROOT), name, reject=failure)
    print("Rejected all three intentionally faulty RTL fixtures", flush=True)

    commands = "; ".join([
        "read_verilog -sv build/hardware/countdown.sv",
        "hierarchy -check -top pinwheel_countdown", "synth -top pinwheel_countdown",
        "check -assert", "stat", "write_json build/hardware/countdown-netlist.json",
        "write_verilog -noattr build/hardware/countdown-netlist.v",
    ])
    (OUT / "synthesis.ys").write_text(commands.replace("; ", "\n") + "\n")
    run([suite / "yosys", "-Q", "-T", "-s", "build/hardware/synthesis.ys"], log="synthesis.log")
    module = json.loads((OUT / "countdown-netlist.json").read_text())["modules"]["pinwheel_countdown"]
    cells = dict(sorted(collections.Counter(c["type"] for c in module["cells"].values()).items()))
    artifacts = [
        "Pinwheel/Hardware/Circuit.lean", "Pinwheel/Hardware/Countdown.lean",
        "Pinwheel/Hardware/Emit.lean", "test/Hardware.lean", "test/countdown_tb.sv",
        "scripts/check-hardware.py", "tools/hardware-toolchain.json",
        "build/hardware/countdown.mlir", "build/hardware/countdown.sv",
        "build/hardware/countdown-lean.csv", "build/hardware/countdown-rtl.csv",
        "build/hardware/countdown-netlist.json", "build/hardware/countdown-netlist.v",
    ]
    report = {
        "host": f"{platform.system()} {platform.machine()}", "versions": versions,
        "toolchain": manifest, "trace_edges": edges, "traces_identical": True,
        "negative_fixtures_rejected": list(mutations), "standard_axioms_only": True,
        "generic_cells": cells, "total_generic_cells": sum(cells.values()),
        "sha256": {p: sha256(ROOT / p) for p in artifacts},
        "boundary": "Lean circuit proofs; RTL simulation; generic synthesis. No translation proof, gate equivalence, technology area, or timing result.",
    }
    (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Matched {edges} edges; synthesized {sum(cells.values())} generic cells. See build/hardware/report.json.")


if __name__ == "__main__":
    main()
