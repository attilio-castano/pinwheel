#!/usr/bin/env python3
"""Bind a bank-selection RTL proof to equivalence, independent traces and mapping."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
import time

from validation_run import Commands, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("backend_check", ROOT / "scripts/check-backend.py")
backend = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(backend)
TOP = backend.TOP


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--readback-report", type=Path, required=True)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.tag): parser.error("Invalid tag")
    proof = json.loads(args.readback_report.read_text())
    variant = proof.get("variant")
    if variant not in ("command-split", "late-bank", "enable-split"): raise RuntimeError("Expected a backend-variant proof")
    out = ROOT / "build/backend" / args.tag
    if out.exists(): raise RuntimeError("Choose a fresh tag to retain earlier evidence")
    out.mkdir(parents=True)
    sources = [*sorted((ROOT / "Pinwheel").rglob("*.lean")), Path(__file__).resolve(),
               ROOT / "scripts/check-backend.py", ROOT / "scripts/measure-storage-variant.py",
               ROOT / "test/BankSelect.lean", ROOT / "scripts/loader-vectors.py",
               ROOT / "scripts/reactive-core-vectors.py", ROOT / "scripts/execution-vectors.py",
               ROOT / "tools/technology-library.json", ROOT / "tools/hardware-toolchain.json",
               ROOT / "physical/experiments/command-split-results.json", args.readback_report]
    sources += [ROOT / "scripts/validation_run.py", ROOT / "scripts/process_group.py"]
    hashes = {str(p.resolve().relative_to(ROOT)): sha(p) for p in sources}
    commands = []
    started = time.monotonic()

    run = Commands(ROOT, out, commands, default_timeout=300)

    run(["lake", "build", "bank_select_emit"], "build")
    run([ROOT / ".lake/build/bin/bank_select_emit", out, variant], "emit")
    circt = ROOT / "build/tools/firtool-1.159.0/bin/circt-opt"
    yosys = ROOT / "build/tools/oss-cad-suite/bin/yosys"
    versions = {"circt": run([circt, "--version"], "circt-version").strip(),
                "yosys": run([yosys, "-V"], "yosys-version").strip()}
    for name in ("composed", "baseline"):
        rtl = run([circt, out / f"{name}.mlir", "--canonicalize", "--lower-seq-to-sv",
                   "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], name)
        (out / f"{name}.sv").write_text(rtl)
    bound_proof = backend.readback_identity(args.readback_report, out)
    frozen = json.loads((ROOT / "physical/experiments/command-split-results.json").read_text())["rtl_sha256"]
    if sha(out / "baseline.sv") != frozen:
        raise RuntimeError("Regenerated legacy command-split RTL differs from the frozen control")

    def equivalence(gold, gate, label):
        path = out / f"{label}.ys"
        path.write_text("\n".join([
            f"read_verilog -sv {gold}", "proc", "rename -hide w:_GEN*", f"rename {TOP} gold",
            f"read_verilog -sv {gate}", "proc", "rename -hide w:_GEN*", f"rename {TOP} gate",
            "equiv_make gold gate equiv", "hierarchy -check -top equiv", "equiv_simple",
            "equiv_induct -seq 1", "equiv_status -assert", ""]))
        log = run([yosys, "-Q", "-T", "-s", path], label)
        counts = re.search(r"Of those cells (\d+) are proven and 0 are unproven", log)
        if not counts or int(counts[1]) < 6233: raise RuntimeError("Incomplete state/output comparison")
        return int(counts[1])

    baseline_points = equivalence(out / "baseline.sv", out / "composed.sv", "legacy-equivalence")
    path = out / "synthesis.ys"
    path.write_text("\n".join([f"read_verilog -sv {out}/composed.sv", f"synth -top {TOP}",
        "check -assert", f"write_json {out}/gates.json", f"write_verilog -noattr {out}/gates.v", ""]))
    run([yosys, "-Q", "-T", "-s", path], "synthesis")
    gate_points = equivalence(out / "composed.sv", out / "gates.v", "gate-equivalence")
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/Loader.lean"], "loader-fixtures")
    run([sys.executable, "scripts/loader-vectors.py"], "loader-vectors")
    run([sys.executable, "scripts/measure-storage-variant.py", "small-dense-cached", "--ff", "6226",
         "--mlir", out / "composed.mlir", "--output", out / "measured"], "regression-and-mapping")
    if hashes != {str(p.resolve().relative_to(ROOT)): sha(p) for p in sources}:
        raise RuntimeError("Sources changed during verification")
    report = {"variant": variant, "source_sha256": hashes, "versions": versions, "commands": commands,
              "readback_receipt": bound_proof, "rtl_sha256": sha(out / "composed.sv"),
              "legacy_rtl_sha256": frozen, "same_rtl_as_previous_physical_run": sha(out / "composed.sv") == frozen,
              "legacy_equivalence_points": baseline_points, "generic_gate_equivalence_points": gate_points,
              "mapping": json.loads((out / "measured/report.json").read_text())["metrics"],
              "artifact_sha256": {str(p.relative_to(out)): sha(p) for p in out.rglob("*")
                                  if p.is_file() and p.suffix in (".json", ".log", ".sv", ".v", ".ys", ".mlir")},
              "elapsed_seconds": round(time.monotonic()-started, 3),
              "boundary": "The exact emitted RTL is bound to its Lean read-back proof. Yosys checks sequential "
                          "equivalence under corresponding states, including eliminated constant bits. "
                          "Independent uninitialized RTL tests and two technology mappings pass separately. "
                          "Generic-gate equivalence does not establish technology-mapped equivalence or routed timing."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Bank-selection checks passed: {out / 'report.json'}", flush=True)


if __name__ == "__main__": main()
