#!/usr/bin/env python3
"""Bind a pin-sampled backend to its proved inner RTL, equivalence and independent traces.

Lean proves the wrapped netlist against the reference machine on the delayed pin
history. This runner checks the emitted artifact: the inner emission must be the
byte-identical RTL whose Lean read-back is already recorded, and the sampled RTL
must equal that RTL behind an independently written two-register pipeline.
"""
import argparse
import json
from pathlib import Path
import re
import sys
import time

from validation_run import Commands, sha

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import backend_readback as rb

TOP = rb.TOP
PROVED = {
    "command-split": ("physical/experiments/bank-selection-results.json", "control"),
    "late-bank": ("physical/experiments/bank-selection-results.json", "candidate"),
    "enable-split": ("physical/experiments/cache-enable-results.json", "candidate"),
}
PIPELINE = {
    # The reference pipeline is written here by hand, not emitted from Lean.
    "two-stage": ("r_pin_second", True),
    "one-stage": ("r_pin_first", False),
    "bypass": ("incoming", False),
}


def ports(rtl):
    """Read the single generated module header: [(direction, width, name)]."""
    header = rtl.split(");", 1)[0].split("(\n", 1)[1]
    result, direction, width = [], None, 1
    for statement in header.split(","):
        match = re.fullmatch(r"\s*(?:(input|output)\s+(?:\[(\d+):0\]\s*)?)?(\w+)\s*", statement)
        if not match: raise RuntimeError(f"Unrecognized port declaration: {statement}")
        kind, bits, name = match.groups()
        if kind: direction, width = kind, int(bits) + 1 if bits else 1
        result.append((direction, width, name))
    return result


def wrapper(rtl, engine_input):
    declared = ports(rtl)
    expected = [("input", 1, "clk"), *[("input", w, n) for n, (w, _) in rb.INPUTS.items()]]
    if declared[:len(expected)] != expected or {n for d, _, n in declared if d == "output"} != set(rb.OUTPUTS):
        raise RuntimeError("Changed inner port contract")
    lines = ["module pinwheel_sampled_reference("]
    lines.append(",\n".join(f"  {d} {f'[{w-1}:0] ' if w > 1 else ''}{n}" for d, w, n in declared))
    lines += [");", "  reg [1:0] r_pin_first, r_pin_second;",
              "  always @(posedge clk) begin", "    r_pin_first <= incoming;",
              "    r_pin_second <= r_pin_first;", "  end"]
    connections = ", ".join(f".{n}({engine_input if n == 'incoming' else n})" for _, _, n in declared)
    lines += [f"  pinwheel_core core({connections});", "endmodule", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--variant", choices=sorted(PROVED), default="command-split")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.tag): parser.error("Invalid tag")
    out = ROOT / "build/sampled" / args.tag
    if out.exists(): raise RuntimeError("Choose a fresh tag to retain earlier evidence")
    out.mkdir(parents=True)
    manifest, role = PROVED[args.variant]
    proved = json.loads((ROOT / manifest).read_text())[role]
    if proved.get("variant") != args.variant: raise RuntimeError("Manifest names a different variant")
    sources = [*sorted((ROOT / "Pinwheel").rglob("*.lean")), ROOT / "Pinwheel.lean", ROOT / "lakefile.toml",
               ROOT / "lean-toolchain", ROOT / "test/Sampled.lean", ROOT / "test/Loader.lean",
               ROOT / "test/loader_tb.sv", Path(__file__).resolve(), ROOT / "scripts/backend_readback.py",
               ROOT / "scripts/process_group.py",
               ROOT / "scripts/measure-storage-variant.py", ROOT / "scripts/loader-vectors.py",
               ROOT / "scripts/reactive-core-vectors.py", ROOT / "scripts/execution-vectors.py",
               ROOT / "scripts/uart_rx_oracle.py",
               ROOT / "tools/hardware-toolchain.json", ROOT / "tools/technology-library.json", ROOT / manifest]
    sources += [ROOT / "scripts/validation_run.py", ROOT / "scripts/process_group.py"]
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    commands, started = [], time.monotonic()

    run = Commands(ROOT, out, commands, default_timeout=900)

    run(["lake", "build", "Pinwheel", "sampled_emit"], "build", timeout=3600)
    run([ROOT / ".lake/build/bin/sampled_emit", out, args.variant], "emit")
    circt = ROOT / "build/tools/firtool-1.159.0/bin/circt-opt"
    yosys = ROOT / "build/tools/oss-cad-suite/bin/yosys"
    versions = {"circt": run([circt, "--version"], "circt-version").strip(),
                "yosys": run([yosys, "-V"], "yosys-version").strip()}
    for name in ("inner", "sampled"):
        rtl = run([circt, out / f"{name}.mlir", "--canonicalize", "--lower-seq-to-sv", "--lower-hw-to-sv",
                   "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], name)
        (out / f"{name}.sv").write_text(rtl)
    if sha(out / "inner.sv") != proved["rtl_sha256"]:
        raise RuntimeError("Inner emission is not the RTL bound to the recorded Lean read-back")

    inner = (out / "inner.sv").read_text()
    renames = [f"rename core.{name} {name}" for name in rb.REGISTERS]

    def equivalence(label, gold_lines, gate, minimum, reject=False):
        path = out / f"{label}.ys"
        path.write_text("\n".join([*gold_lines, f"read_verilog -sv {gate}", "proc", "rename -hide w:_GEN*",
            f"rename {TOP} gate", "equiv_make gold gate equiv", "hierarchy -check -top equiv",
            "equiv_simple", "equiv_induct -seq 1", "equiv_status -assert", ""]))
        log = run([yosys, "-Q", "-T", "-s", path], label, reject="Found " if reject else None)
        if reject: return None
        counts = re.search(r"Of those cells (\d+) are proven and 0 are unproven", log)
        if not counts or int(counts[1]) < minimum: raise RuntimeError(f"{label}: incomplete comparison")
        return int(counts[1])

    def reference(kind):
        (out / f"reference-{kind}.sv").write_text(wrapper(inner, PIPELINE[kind][0]))
        return [f"read_verilog -sv {out}/inner.sv", "proc", "rename -hide w:_GEN*", f"rename {TOP} pinwheel_core",
                f"read_verilog -sv {out}/reference-{kind}.sv", "proc",
                "hierarchy -check -top pinwheel_sampled_reference", "flatten",
                "cd pinwheel_sampled_reference", *renames, "cd", "rename pinwheel_sampled_reference gold"]

    state_bits = sum(w for w, _ in rb.REGISTERS.values()) + 4
    points = {"reference": equivalence("reference-equivalence", reference("two-stage"), out / "sampled.sv", state_bits)}
    for kind in ("one-stage", "bypass"):
        equivalence(f"reference-{kind}-rejected", reference(kind), out / "sampled.sv", 0, reject=True)
    path = out / "synthesis.ys"
    path.write_text("\n".join([f"read_verilog -sv {out}/sampled.sv", f"synth -top {TOP}", "check -assert",
        f"write_json {out}/gates.json", f"write_verilog -noattr {out}/gates.v", ""]))
    run([yosys, "-Q", "-T", "-s", path], "synthesis")
    points["generic_gates"] = equivalence("gate-equivalence",
        [f"read_verilog -sv {out}/sampled.sv", "proc", "rename -hide w:_GEN*", f"rename {TOP} gold"],
        out / "gates.v", state_bits)

    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/Loader.lean"], "loader-fixtures")
    run([sys.executable, "scripts/loader-vectors.py"], "loader-vectors")
    measure = [sys.executable, "scripts/measure-storage-variant.py", "small-dense-cached"]
    # State grows by exactly the four pipeline bits. The mapped count grows by ten
    # with this recipe: cached-word bits 8:3 feed only a masked halt comparison,
    # which ABC removes in the inner mapping (6,226) and retains here.
    run([*measure, "--ff", "6236", "--pin-delay", "2", "--mlir", out / "sampled.mlir",
         "--output", out / "measured"], "regression-and-mapping", timeout=3600)
    # The shifted traces must distinguish the pipeline depth in both directions.
    run([*measure, "--ff", "6236", "--pin-delay", "0", "--mlir", out / "sampled.mlir",
         "--output", out / "unshifted-rejected"], "unshifted-rejected", reject="LOADER edge")
    run([*measure, "--ff", "6226", "--pin-delay", "2", "--mlir", out / "inner.mlir",
         "--output", out / "inner-shifted-rejected"], "inner-shifted-rejected", reject="LOADER edge")
    if hashes != {str(p.relative_to(ROOT)): sha(p) for p in sources}:
        raise RuntimeError("Sources changed during verification")
    measured = json.loads((out / "measured/report.json").read_text())
    report = {"variant": args.variant, "source_sha256": hashes, "versions": versions, "commands": commands,
              "proved_inner": {"manifest": manifest, "role": role, "rtl_sha256": proved["rtl_sha256"]},
              "rtl_sha256": sha(out / "sampled.sv"), "mlir_sha256": sha(out / "sampled.mlir"),
              "register_fields": len(rb.REGISTERS) + 2, "register_bits": state_bits,
              "equivalence_points": points, "simulation": measured["simulation"], "mapping": measured["metrics"],
              "artifact_sha256": {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*"))
                                  if p.is_file() and p.suffix in (".json", ".log", ".sv", ".v", ".ys", ".mlir", ".txt")},
              "elapsed_seconds": round(time.monotonic() - started, 3),
              "boundary": "The inner emission is byte-identical to RTL with a recorded Lean read-back. Yosys proves the "
                          "sampled RTL sequentially equivalent, under corresponding states, to that RTL behind a "
                          "hand-written two-register pipeline, and rejects one-stage and bypass pipelines. The "
                          "independent oracle passes with pins presented two edges early and fails otherwise. "
                          "No direct Lean read-back of the sampled RTL, technology-mapped equivalence, "
                          "metastability or routed-timing claim is made."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Sampled-backend checks passed: {out / 'report.json'}", flush=True)


if __name__ == "__main__": main()
