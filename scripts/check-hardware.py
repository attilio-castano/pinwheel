#!/usr/bin/env python3
"""Reproduce Lean/RTL countdown checks, negative fixtures, and generic synthesis."""
import collections
import copy
import hashlib
import json
import platform
import shutil
import subprocess
from pathlib import Path

from countdown_import import interpret, lean_source

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

    # Read back the actual emitted RTL. The parser is trusted; the generated
    # theorem proves the interpreted transition, not a second emitter output.
    def validate_artifact(source, label, reject=False):
        imported = OUT / f"{label}-import.json"
        command = (f"read_verilog -sv {source}; hierarchy -check -top pinwheel_countdown; "
                   f"proc; opt_clean; check -assert; write_json {imported.relative_to(ROOT)}")
        run([suite / "yosys", "-Q", "-T", "-p", command], log=f"{label}-import.log")
        proof = OUT / f"{label}-Artifact.lean"
        proof.write_text(lean_source(imported))
        result = subprocess.run([lake, "env", "lean", "-DwarningAsError=true", str(proof)],
                                cwd=ROOT, text=True, capture_output=True)
        audit = result.stdout + result.stderr
        (OUT / f"{label}-proof.log").write_text(audit)
        if reject:
            if result.returncode == 0 or "unsolved goals" not in audit:
                raise RuntimeError(f"Corrupt RTL did not fail the correspondence theorem: {audit}")
        else:
            if result.returncode:
                raise RuntimeError(f"RTL interpretation proof failed: {audit}")
            groups = re.findall(r"depends on axioms: \[([^]]*)\]", audit)
            if len(groups) != 2 or any(set(x.strip() for x in g.split(",")) - {
                    "propext", "Classical.choice", "Quot.sound"} for g in groups):
                raise RuntimeError(f"Incomplete or untrusted artifact proof: {audit}")
        return imported, proof

    imported, artifact_proof = validate_artifact("build/hardware/countdown.sv", "countdown")
    malformed = {}
    raw = json.loads(imported.read_text())
    for label in ("clock", "constant-clock", "driven-clock", "unknown-cell", "signed", "unknown-bit", "missing-state", "port-width"):
        bad_json = copy.deepcopy(raw)
        m = bad_json["modules"]["pinwheel_countdown"]
        ff = next(c for c in m["cells"].values() if c["type"] == "$dff")
        op = next(c for c in m["cells"].values() if c["type"] == "$and")
        if label == "clock": ff["parameters"]["CLK_POLARITY"] = "0"
        elif label == "constant-clock":
            m["ports"]["clk"]["bits"] = ["0"]
            for cell in m["cells"].values():
                if cell["type"] == "$dff": cell["connections"]["CLK"] = ["0"]
        elif label == "driven-clock": op["connections"]["Y"] = m["ports"]["clk"]["bits"]
        elif label == "unknown-cell": op["type"] = "$unsupported"
        elif label == "signed": op["parameters"]["A_SIGNED"] = "1"
        elif label == "unknown-bit": ff["connections"]["D"][0] = "x"
        elif label == "missing-state":
            del m["cells"][next(n for n, c in m["cells"].items() if c is ff)]
        else: m["ports"]["duration"]["bits"].pop()
        path = OUT / f"reject-import-{label}.json"
        path.write_text(json.dumps(bad_json, indent=2) + "\n")
        try:
            interpret(path)
        except (ValueError, KeyError) as error:
            malformed[label] = str(error)
        else:
            raise RuntimeError(f"Unsafe artifact shape was accepted: {label}")
    for label in mutations:
        validate_artifact(f"build/hardware/{label}.sv", label, reject=True)

    equivalence = "\n".join([
        "read_verilog -sv build/hardware/countdown.sv", "proc", "rename pinwheel_countdown gold",
        "read_verilog build/hardware/countdown-netlist.v", "proc", "rename pinwheel_countdown gate",
        "equiv_make gold gate equiv", "hierarchy -check -top equiv", "equiv_simple",
        "equiv_status -assert", "",
    ])
    (OUT / "equivalence.ys").write_text(equivalence)
    proof_log = run([suite / "yosys", "-Q", "-T", "-s", "build/hardware/equivalence.ys"],
                    log="equivalence.log")
    comparison = re.search(r"Of those cells (\d+) are proven and 0 are unproven", proof_log)
    if not comparison or int(comparison[1]) < 19:
        raise RuntimeError("Missing complete state/output equivalence evidence")
    # A valid but corrupted implementation must fail the same equivalence gate.
    mutant_eq = equivalence.replace("read_verilog build/hardware/countdown-netlist.v",
                                    "read_verilog -sv build/hardware/wrong-decrement.sv")
    (OUT / "reject-equivalence.ys").write_text(mutant_eq)
    bad = subprocess.run([suite / "yosys", "-Q", "-T", "-s", "build/hardware/reject-equivalence.ys"],
                         cwd=ROOT, text=True, capture_output=True)
    (OUT / "reject-equivalence.log").write_text(bad.stdout + bad.stderr)
    if bad.returncode == 0 or "unproven" not in bad.stdout + bad.stderr:
        raise RuntimeError("Corrupted implementation did not fail equivalence")
    print("Kernel-checked RTL transition/trace; all RTL/gate points proved; corrupt artifacts rejected", flush=True)
    module = json.loads((OUT / "countdown-netlist.json").read_text())["modules"]["pinwheel_countdown"]
    cells = dict(sorted(collections.Counter(c["type"] for c in module["cells"].values()).items()))
    artifacts = [
        "Pinwheel/Hardware/Circuit.lean", "Pinwheel/Hardware/Countdown.lean",
        "Pinwheel/Hardware/CountdownContract.lean", "scripts/countdown_import.py",
        "Pinwheel/Hardware/Emit.lean", "test/Hardware.lean", "test/countdown_tb.sv",
        "scripts/check-hardware.py", "tools/hardware-toolchain.json",
        "build/hardware/countdown.mlir", "build/hardware/countdown.sv",
        "build/hardware/countdown-lean.csv", "build/hardware/countdown-rtl.csv",
        "build/hardware/countdown-netlist.json", "build/hardware/countdown-netlist.v",
        str(imported.relative_to(ROOT)), str(artifact_proof.relative_to(ROOT)),
        "build/hardware/countdown-proof.log", "build/hardware/equivalence.ys", "build/hardware/equivalence.log",
    ]
    report = {
        "host": f"{platform.system()} {platform.machine()}", "versions": versions,
        "toolchain": manifest, "trace_edges": edges, "traces_identical": True,
        "negative_fixtures_rejected": list(mutations), "standard_axioms_only": True,
        "generic_cells": cells, "total_generic_cells": sum(cells.values()),
        "rtl_interpretation": {"kernel_checked": True, "standard_axioms_only": True,
            "initial_relation": "Equal arbitrary two-state register values; reset establishes zero state",
            "claim": "Every transition and all pre/post-edge observations for arbitrary input histories",
            "rejected_mutations": list(mutations), "rejected_import_shapes": malformed},
        "gate_equivalence": {"proven_points": int(comparison[1]), "unproven_points": 0,
            "tool": "Yosys equiv_simple/equiv_status", "mutation_rejected": True,
            "initial_relation": "Corresponding countdown register bits are equal"},
        "sha256": {p: sha256(ROOT / p) for p in artifacts},
        "boundary": "Lean kernel checks the read-back RTL transition and trace. Trusted: Yosys Verilog/proc frontend, "
                    "restricted JSON interpreter, and Yosys RTL-to-generic-gates equivalence. "
                    "No universal emitter/CIRCT proof, four-state equivalence, technology mapping, or physical timing claim.",
    }
    (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Matched {edges} edges; synthesized {sum(cells.values())} generic cells. See build/hardware/report.json.")


if __name__ == "__main__":
    main()
