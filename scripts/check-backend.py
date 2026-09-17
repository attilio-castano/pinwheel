#!/usr/bin/env python3
"""Check the composed general backend with preserved artifact identities."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOP = "pinwheel_atomic_small_dense_cached"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def readback_identity(receipt, out):
    receipt = receipt.resolve()
    evidence = json.loads(receipt.read_text())
    if (evidence.get("standard_axioms_only") is not True or
            (evidence.get("register_fields"), evidence.get("register_bits"), evidence.get("outputs")) != (607, 6233, 33)):
        raise RuntimeError("Incomplete read-back proof receipt")
    for name in ("composed.mlir", "composed.sv"):
        expected = evidence["artifact_sha256"][name]
        if sha(out / name) != expected or sha(receipt.parent / name) != expected:
            raise RuntimeError("Read-back receipt does not match this emission")
    for name, expected in evidence["artifact_sha256"].items():
        artifact = (receipt.parent / name).resolve()
        if not artifact.is_relative_to(receipt.parent) or sha(artifact) != expected:
            raise RuntimeError(f"Read-back artifact identity changed: {name}")
    for name, expected in evidence["source_sha256"].items():
        source = (ROOT / name).resolve()
        if not source.is_relative_to(ROOT) or sha(source) != expected:
            raise RuntimeError(f"Read-back source identity changed: {name}")
    return {"path": str(receipt.relative_to(ROOT)), "sha256": sha(receipt)}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--tag", required=True)
    p.add_argument("--readback-report", type=Path,
                   help="Bind a completed Lean RTL read-back receipt to this exact emission")
    a = p.parse_args()
    if not a.tag.replace("-", "").replace("_", "").isalnum():
        p.error("Use letters, numbers, hyphens or underscores")
    out = ROOT / "build/backend" / a.tag
    if out.exists():
        raise RuntimeError("Choose a fresh tag to retain earlier evidence")
    out.mkdir(parents=True)
    sources = sorted((ROOT / "Pinwheel").rglob("*.lean")) + [ROOT / n for n in (
        "Pinwheel.lean", "test/Backend.lean", "lakefile.toml", "lean-toolchain",
        "scripts/check-backend.py", "scripts/measure-storage-variant.py")]
    hashes = {str(f.relative_to(ROOT)): sha(f) for f in sources}
    started = time.monotonic()

    def run(command, label, timeout=300):
        result = subprocess.run(list(map(str, command)), cwd=ROOT, capture_output=True,
                                text=True, timeout=timeout)
        text = result.stdout + result.stderr
        (out / f"{label}.log").write_text(text)
        if result.returncode:
            raise RuntimeError(f"{label} failed:\n{text[-5000:]}")
        print(label + ": passed", flush=True)
        return text

    run(["lake", "build"], "library")
    run(["lake", "env", "lean", "-DwarningAsError=true", "test/ProofAudit.lean"], "axioms")
    run(["lake", "build", "backend_emit"], "emitter-build")
    run([ROOT / ".lake/build/bin/backend_emit", out], "emit")
    circt = ROOT / "build/tools/firtool-1.159.0/bin/circt-opt"
    yosys = ROOT / "build/tools/oss-cad-suite/bin/yosys"
    versions = {"circt": run([circt, "--version"], "circt-version").strip(),
                "yosys": run([yosys, "-V"], "yosys-version").strip()}
    for name in ("composed", "baseline"):
        rtl = run([circt, out / f"{name}.mlir", "--canonicalize", "--lower-seq-to-sv",
                   "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], name)
        (out / f"{name}.sv").write_text(rtl)

    readback = readback_identity(a.readback_report, out) if a.readback_report else None

    def equivalence(gold, gate, label):
        script = "\n".join([
            f"read_verilog -sv {gold}", "proc", "rename -hide w:_GEN*", f"rename {TOP} gold",
            f"read_verilog -sv {gate}", "proc", "rename -hide w:_GEN*", f"rename {TOP} gate",
            "equiv_make gold gate equiv", "hierarchy -check -top equiv", "equiv_simple",
            "equiv_induct -seq 1", "equiv_status -assert", "",
        ])
        path = out / f"{label}.ys"
        path.write_text(script)
        log = run([yosys, "-Q", "-T", "-s", path], label)
        counts = re.search(r"Of those cells (\d+) are proven and 0 are unproven", log)
        if not counts or int(counts[1]) < 6233:
            raise RuntimeError("Missing complete register/output comparison")
        return int(counts[1])

    baseline_points = equivalence(out / "baseline.sv", out / "composed.sv", "baseline-equivalence")
    synthesis = out / "synthesis.ys"
    synthesis.write_text("\n".join([f"read_verilog -sv {out}/composed.sv", f"synth -top {TOP}",
        "check -assert", f"write_json {out}/gates.json", f"write_verilog -noattr {out}/gates.v", ""]))
    run([yosys, "-Q", "-T", "-s", synthesis], "synthesis")
    gate_points = equivalence(out / "composed.sv", out / "gates.v", "gate-equivalence")
    # Reuse the existing independent atomic-loader workload and dense/cache checks.
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/Loader.lean"], "loader-fixtures")
    run([sys.executable, "scripts/loader-vectors.py"], "loader-vectors")
    run([sys.executable, "scripts/measure-storage-variant.py", "small-dense-cached", "--ff", "6226",
         "--mlir", out / "composed.mlir", "--output", out / "measured"], "independent-regression-and-mapping")
    for f in sources:
        if sha(f) != hashes[str(f.relative_to(ROOT))]:
            raise RuntimeError(f"Source changed during validation: {f}")
    artifacts = [f for f in out.rglob("*") if f.is_file() and f.suffix in {".sv", ".v", ".mlir", ".ys", ".json", ".log"}]
    report = {"source_sha256": hashes, "versions": versions,
        "artifact_sha256": {str(f.relative_to(ROOT)): sha(f) for f in artifacts},
        "baseline_equivalence_points": baseline_points, "gate_equivalence_points": gate_points,
        "equivalence_method": "Direct SAT plus one-step induction; all comparison points discharged",
        "initial_relation": "Matching comparison/state points, including constants for eliminated register bits; not independent arbitrary power-up values",
        "standard_axioms_only": True, "elapsed_seconds": round(time.monotonic() - started, 3),
        "readback_receipt": readback,
        "boundary": "Lean proves the exact netlist's initialized, cycle-exact refinement. "
            "Yosys proves old/new RTL and RTL/generic-gate equivalence under matching register states. "
            "Independent atomic traces and mapped-corner measurements are separate evidence. "
            + ("The Lean RTL read-back receipt matches these exact sources, MLIR and RTL. " if readback else
               "Lean RTL read-back is a separate gate; this receipt does not run it. ")
            + "No physical closure or default promotion."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Composed backend passed: {out / 'report.json'}", flush=True)


if __name__ == "__main__":
    main()
