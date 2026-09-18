#!/usr/bin/env python3
"""Validate the emitted decoupled prefetch backend, alone and behind the pin pipeline.

Lean proves the netlist refines the atomic reference machine. This runner emits
it, exports RTL, proves RTL/generic-gate equivalence, runs the independent
atomic-loader oracle against both emissions (pins presented two edges early for
the sampled one), maps both corners, and records a receipt with the RTL identities.
"""
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--ff", type=int, default=6418, help="Expected mapped flip-flop count, inner emission")
    parser.add_argument("--sampled-ff", type=int, default=6422, help="Expected mapped flip-flop count, sampled")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.tag): parser.error("Invalid tag")
    out = ROOT / "build/prefetch" / args.tag
    if out.exists(): raise RuntimeError("Choose a fresh tag to retain earlier evidence")
    out.mkdir(parents=True)
    sources = [*sorted((ROOT / "Pinwheel").rglob("*.lean")), ROOT / "Pinwheel.lean", ROOT / "lakefile.toml",
               ROOT / "lean-toolchain", ROOT / "test/Prefetch.lean", ROOT / "test/Loader.lean",
               ROOT / "test/loader_tb.sv", Path(__file__).resolve(),
               ROOT / "scripts/measure-storage-variant.py", ROOT / "scripts/loader-vectors.py",
               ROOT / "scripts/reactive-core-vectors.py", ROOT / "tools/hardware-toolchain.json",
               ROOT / "tools/technology-library.json"]
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    commands, started = [], time.monotonic()

    def run(command, label, timeout=900, reject=None):
        command = list(map(str, command))
        then = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        text = result.stdout + result.stderr
        (out / f"{label}.log").write_text(text)
        commands.append({"argv": command, "exit_code": result.returncode, "expected_failure": bool(reject),
                         "seconds": round(time.monotonic() - then, 3)})
        if reject:
            if result.returncode == 0 or reject not in text:
                raise RuntimeError(f"{label}: expected rejection containing {reject!r}; see {out / (label + '.log')}")
            print(label + ": corruption rejected", flush=True)
        elif result.returncode:
            raise RuntimeError(f"{label}: {text[-3000:]}")
        else:
            print(label + ": passed", flush=True)
        return text

    run(["lake", "build", "Pinwheel", "prefetch_emit"], "build", timeout=3600)
    run(["lake", "env", "lean", "-DwarningAsError=true", "test/ProofAudit.lean"], "axioms", timeout=3600)
    run([ROOT / ".lake/build/bin/prefetch_emit", out], "emit")
    circt = ROOT / "build/tools/firtool-1.159.0/bin/circt-opt"
    yosys = ROOT / "build/tools/oss-cad-suite/bin/yosys"
    versions = {"circt": run([circt, "--version"], "circt-version").strip(),
                "yosys": run([yosys, "-V"], "yosys-version").strip()}
    for name in ("prefetch", "prefetch-sampled"):
        rtl = run([circt, out / f"{name}.mlir", "--canonicalize", "--lower-seq-to-sv", "--lower-hw-to-sv",
                   "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], name + "-export")
        (out / f"{name}.sv").write_text(rtl)

    def gates(name, minimum):
        script = out / f"{name}-synthesis.ys"
        script.write_text("\n".join([f"read_verilog -sv {out}/{name}.sv", f"synth -top {TOP}", "check -assert",
            f"write_verilog -noattr {out}/{name}-gates.v", ""]))
        run([yosys, "-Q", "-T", "-s", script], name + "-synthesis")
        path = out / f"{name}-gate-equivalence.ys"
        path.write_text("\n".join([f"read_verilog -sv {out}/{name}.sv", "proc", "rename -hide w:_GEN*",
            f"rename {TOP} gold", f"read_verilog -sv {out}/{name}-gates.v", "proc", "rename -hide w:_GEN*",
            f"rename {TOP} gate", "equiv_make gold gate equiv", "hierarchy -check -top equiv",
            # Synthesis drops the constant top bit of each fetched word (dense words expand
            # with a zero bit 63), so the induction must see one edge of the D inputs.
            "equiv_simple -seq 2", "equiv_induct -seq 2", "equiv_status -assert", ""]))
        log = run([yosys, "-Q", "-T", "-s", path], name + "-gate-equivalence")
        counts = re.search(r"Of those cells (\d+) are proven and 0 are unproven", log)
        if not counts or int(counts[1]) < minimum: raise RuntimeError(f"{name}: incomplete gate comparison")
        return int(counts[1])

    # Matched points are register bits plus outputs, less the constant bits synthesis
    # removes (the top bit of each fetched word and of the start word among them).
    points = {"prefetch": gates("prefetch", 6350), "prefetch-sampled": gates("prefetch-sampled", 6354)}

    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/Loader.lean"], "loader-fixtures")
    run([sys.executable, "scripts/loader-vectors.py"], "loader-vectors")
    measure = [sys.executable, "scripts/measure-storage-variant.py", "small-dense-cached"]
    run([*measure, "--ff", str(args.ff), "--mlir", out / "prefetch.mlir", "--output", out / "measured"],
        "regression-and-mapping", timeout=3600)
    run([*measure, "--ff", str(args.sampled_ff), "--pin-delay", "2", "--mlir", out / "prefetch-sampled.mlir",
         "--output", out / "measured-sampled"], "sampled-regression-and-mapping", timeout=3600)
    # The shifted traces must distinguish the pipeline depth.
    run([*measure, "--ff", str(args.sampled_ff), "--pin-delay", "0", "--mlir", out / "prefetch-sampled.mlir",
         "--output", out / "unshifted-rejected"], "unshifted-rejected", reject="LOADER edge")
    if hashes != {str(p.relative_to(ROOT)): sha(p) for p in sources}:
        raise RuntimeError("Sources changed during verification")
    measured = json.loads((out / "measured/report.json").read_text())
    sampled = json.loads((out / "measured-sampled/report.json").read_text())
    report = {"variant": "prefetch", "source_sha256": hashes, "versions": versions, "commands": commands,
              "inner": {"rtl_sha256": sha(out / "prefetch.sv"), "mlir_sha256": sha(out / "prefetch.mlir"),
                        "register_fields": 610, "register_bits": 6425,
                        "gate_equivalence_points": points["prefetch"],
                        "simulation": measured["simulation"], "mapping": measured["metrics"]},
              "sampled": {"rtl_sha256": sha(out / "prefetch-sampled.sv"),
                          "mlir_sha256": sha(out / "prefetch-sampled.mlir"),
                          "register_fields": 612, "register_bits": 6429,
                          "gate_equivalence_points": points["prefetch-sampled"],
                          "simulation": sampled["simulation"], "mapping": sampled["metrics"]},
              "artifact_sha256": {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*"))
                                  if p.is_file() and p.suffix in (".json", ".log", ".sv", ".v", ".ys", ".mlir", ".txt")},
              "elapsed_seconds": round(time.monotonic() - started, 3),
              "boundary": "Lean proves the emitted netlist's initialized, cycle-exact refinement of the atomic "
                          "reference, alone and behind the two-register pin pipeline. Yosys proves RTL/generic-gate "
                          "equivalence of both emissions (two-step induction: synthesis drops the constant top bit "
                          "of each fetched word). The independent oracle passes on both, with pins "
                          "presented two edges early for the sampled one, and fails otherwise. No Yosys "
                          "sequential equivalence to the composed RTL is claimed: the register sets differ. "
                          "No Lean read-back of this RTL, technology-mapped equivalence, metastability or "
                          "routed-timing claim is made."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Prefetch backend checks passed: {out / 'report.json'}", flush=True)


if __name__ == "__main__": main()
