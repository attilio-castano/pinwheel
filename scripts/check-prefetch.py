#!/usr/bin/env python3
"""Validate an emitted fetch-policy backend, alone and behind the pin pipeline.

Lean proves the netlist refines the atomic reference. This runner emits it,
exports RTL, proves RTL/generic-gate equivalence, runs the independent
atomic-loader oracle against both emissions (pins presented two edges early for
the sampled one), maps both corners, and records a receipt with the RTL
identities. Variants: `prefetch` (decoupled, three read ports) and `oneport`
(one read port, under the per-program readiness rule: the oracle's vectors are
then generated without the UART receiver exercise, and the unrestricted vectors
must be rejected).
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
VARIANTS = {
    "prefetch": dict(exe="prefetch_emit", stem="prefetch", test="test/Prefetch.lean", ready=False,
                     fields=(610, 6425), sampled_fields=(612, 6429), ff=(6415, 6419), points=(6350, 6354), induction=2,
                     lean="Decoupled (FetchPolicy) refinement, Backend.Prefetch.netlist_next/netlist_output/"
                          "completeRefinement, Prefetch.sampled_trace_correct"),
    "oneport": dict(exe="oneport_emit", stem="oneport", test="test/OnePort.lean", ready=True,
                    fields=(611, 6426), sampled_fields=(613, 6430), ff=(6416, 6420), points=(6350, 6354), induction=3,
                    lean="SinglePort (FetchPolicy) rule refinement, Backend.OnePort.netlist_next/netlist_output/"
                         "completeRefinement, OnePort.sampled_trace_correct, on ready programs"),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--variant", choices=sorted(VARIANTS), default="prefetch")
    parser.add_argument("--ff", type=int, help="Expected mapped flip-flop count, inner emission")
    parser.add_argument("--sampled-ff", type=int, help="Expected mapped flip-flop count, sampled")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.tag): parser.error("Invalid tag")
    v = VARIANTS[args.variant]
    stem = v["stem"]
    ff, sampled_ff = args.ff or v["ff"][0], args.sampled_ff or v["ff"][1]
    out = ROOT / "build" / stem / args.tag
    if out.exists(): raise RuntimeError("Choose a fresh tag to retain earlier evidence")
    out.mkdir(parents=True)
    sources = [*sorted((ROOT / "Pinwheel").rglob("*.lean")), ROOT / "Pinwheel.lean", ROOT / "lakefile.toml",
               ROOT / "lean-toolchain", ROOT / v["test"], ROOT / "test/Loader.lean",
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

    run(["lake", "build", "Pinwheel", v["exe"]], "build", timeout=3600)
    run(["lake", "env", "lean", "-DwarningAsError=true", "test/ProofAudit.lean"], "axioms", timeout=3600)
    run([ROOT / ".lake/build/bin" / v["exe"], out], "emit")
    circt = ROOT / "build/tools/firtool-1.159.0/bin/circt-opt"
    yosys = ROOT / "build/tools/oss-cad-suite/bin/yosys"
    versions = {"circt": run([circt, "--version"], "circt-version").strip(),
                "yosys": run([yosys, "-V"], "yosys-version").strip()}
    for name in (stem, stem + "-sampled"):
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
            # with a zero bit 63), so the induction must see one edge of the D inputs. The
            # one-port backend's untaken-word register can skip a load for one edge (never
            # two in a row), so it needs one step more; two steps leave 107 points unproven.
            f"equiv_simple -seq {v['induction']}", f"equiv_induct -seq {v['induction']}",
            "equiv_status -assert", ""]))
        log = run([yosys, "-Q", "-T", "-s", path], name + "-gate-equivalence")
        counts = re.search(r"Of those cells (\d+) are proven and 0 are unproven", log)
        if not counts or int(counts[1]) < minimum: raise RuntimeError(f"{name}: incomplete gate comparison")
        return int(counts[1])

    # Matched points are register bits plus outputs, less the constant bits synthesis
    # removes (the top bit of each fetched word and of the start word among them).
    points = {stem: gates(stem, v["points"][0]), stem + "-sampled": gates(stem + "-sampled", v["points"][1])}

    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/Loader.lean"], "loader-fixtures")
    run([sys.executable, "scripts/loader-vectors.py"], "loader-vectors")
    measure = [sys.executable, "scripts/measure-storage-variant.py", "small-dense-cached"]
    rule = ["--ready"] if v["ready"] else []
    run([*measure, *rule, "--ff", str(ff), "--mlir", out / f"{stem}.mlir", "--output", out / "measured"],
        "regression-and-mapping", timeout=3600)
    run([*measure, *rule, "--ff", str(sampled_ff), "--pin-delay", "2", "--mlir", out / f"{stem}-sampled.mlir",
         "--output", out / "measured-sampled"], "sampled-regression-and-mapping", timeout=3600)
    # The shifted traces must distinguish the pipeline depth.
    run([*measure, *rule, "--ff", str(sampled_ff), "--pin-delay", "0", "--mlir", out / f"{stem}-sampled.mlir",
         "--output", out / "unshifted-rejected"], "unshifted-rejected", reject="LOADER edge")
    rejected = ["sampled RTL with unshifted pins"]
    if v["ready"]:
        # The rule is not vacuous at the RTL level: on the unrestricted vectors, whose
        # programs include zero-duration branching records, this RTL leaves the reference.
        run([*measure, "--ff", str(ff), "--mlir", out / f"{stem}.mlir", "--output", out / "unready-rejected"],
            "unready-rejected", reject="LOADER edge")
        rejected.append("inner RTL on the unrestricted vectors (programs outside the readiness rule)")
    if hashes != {str(p.relative_to(ROOT)): sha(p) for p in sources}:
        raise RuntimeError("Sources changed during verification")
    measured = json.loads((out / "measured/report.json").read_text())
    sampled = json.loads((out / "measured-sampled/report.json").read_text())
    boundary = ("Lean proves the emitted netlist's initialized, cycle-exact refinement of the atomic reference, alone "
                "and behind the two-register pin pipeline. Yosys proves RTL/generic-gate equivalence of both "
                f"emissions ({v['induction']}-step induction: synthesis drops the constant top bit of each fetched word). The "
                "independent oracle passes on both, with pins presented two edges early for the sampled one, and "
                "fails otherwise. No Yosys sequential equivalence to the composed RTL is claimed: the register sets "
                "differ. No Lean read-back of this RTL, technology-mapped equivalence, metastability or "
                "routed-timing claim is made.")
    if v["ready"]:
        boundary += (" The refinement and the oracle runs are on programs satisfying the readiness rule: the oracle's "
                     "vectors omit the UART receiver exercise and give the terminal-capture branch record one cycle; "
                     "on the unrestricted vectors the RTL is rejected, as the rule predicts.")
    report = {"variant": args.variant, "source_sha256": hashes, "versions": versions, "commands": commands,
              "lean": v["lean"],
              "inner": {"rtl_sha256": sha(out / f"{stem}.sv"), "mlir_sha256": sha(out / f"{stem}.mlir"),
                        "register_fields": v["fields"][0], "register_bits": v["fields"][1],
                        "gate_equivalence_points": points[stem],
                        "simulation": measured["simulation"], "mapping": measured["metrics"]},
              "sampled": {"rtl_sha256": sha(out / f"{stem}-sampled.sv"),
                          "mlir_sha256": sha(out / f"{stem}-sampled.mlir"),
                          "register_fields": v["sampled_fields"][0], "register_bits": v["sampled_fields"][1],
                          "gate_equivalence_points": points[stem + "-sampled"],
                          "simulation": sampled["simulation"], "mapping": sampled["metrics"]},
              "rejected_traces": rejected,
              "artifact_sha256": {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*"))
                                  if p.is_file() and p.suffix in (".json", ".log", ".sv", ".v", ".ys", ".mlir", ".txt")},
              "elapsed_seconds": round(time.monotonic() - started, 3),
              "boundary": boundary}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{args.variant} backend checks passed: {out / 'report.json'}", flush=True)


if __name__ == "__main__": main()
