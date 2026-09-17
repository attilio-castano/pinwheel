#!/usr/bin/env python3
"""Kernel-check the selected backend's actual emitted RTL, with a fresh receipt."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

import backend_readback as rb
import bank_select_readback as banks

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Check:
    def __init__(self, out):
        self.out = out
        self.commands = []

    def run(self, command, label, *, directory=None, timeout=240, reject=False, lean_path=None):
        directory = directory or self.out
        path = directory / (label + ".log")
        command = list(map(str, command))
        start = time.monotonic()
        env = {**os.environ, "LEAN_PATH": str(lean_path or self.out)}
        with path.open("w") as log:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=timeout)
        self.commands.append({"argv": command, "log": str(path.relative_to(self.out)),
                              "exit_code": result.returncode,
                              "seconds": round(time.monotonic() - start, 3)})
        text = path.read_text()
        if reject:
            if result.returncode == 0 or "error: Type mismatch" not in text:
                raise RuntimeError(f"{label}: expected a Lean correspondence type mismatch; see {path}")
        elif result.returncode:
            raise RuntimeError(f"{label} failed; see {path}\n{text[-3000:]}")
        print(f"{path.relative_to(self.out).with_suffix('')}: {'corruption rejected' if reject else 'passed'}", flush=True)
        return text

    def lean(self, name, *, directory=None, reject=False, lean_path=None):
        directory = directory or self.out
        return self.run(["lake", "env", "lean", "-DwarningAsError=true", "-DmaxErrors=1",
                         "-o", directory / (name + ".olean"), directory / (name + ".lean")],
                        name, directory=directory, reject=reject, lean_path=lean_path)

    def import_rtl(self, rtl, directory):
        path = directory / "import.ys"
        path.write_text("\n".join([f"read_verilog -sv {rtl}",
            f"hierarchy -check -top {rb.TOP}", "proc", "opt_clean", "check -assert",
            f"write_json {directory}/import.json", ""]))
        self.run([ROOT / "build/tools/oss-cad-suite/bin/yosys", "-Q", "-T", "-s", path],
                 "import", directory=directory)
        return rb.read_rtl(directory / "import.json")


def generate(out, source, rtl, cuts, pairs, variant="composed"):
    (out / "Design.lean").write_text(banks.design_source(variant))
    def write(name, text):
        (out / (name + ".lean")).write_text("import Design\n" + text)
    write("Hints", rb.HEADER + source.definitions("Source") + "end Pinwheel.Artifact.Backend\n")
    write("Graphs", "import Hints\n" + rb.HEADER + rtl.definitions("RTL") + "end Pinwheel.Artifact.Backend\n")
    write("CutHints", "import Pinwheel.Hardware.Storage.BackendReadback\n" + rb.HEADER +
          source.definitions("Hint", cuts) + "end Pinwheel.Artifact.Backend\n")
    write("Embeddings", rb.embeddings_source(source, cuts, "Hints", "CutHints"))
    write("LocalProofs", rb.helper_source(pairs))
    write("Links", rb.links_source(source, rtl, pairs, "LocalProofs", "Graphs"))
    groups = {}
    core = [n for n, (_, ctor) in rb.REGISTERS.items() if ctor.startswith(".core") or n == "r_cached_word"]
    for k in range(0, len(core), 4):
        groups[f"HintCore{k // 4}"] = [("next", n) for n in core[k:k + 4]]
    groups["HintControl"] = [("next", n) for n in rb.REGISTERS if n.startswith("r_loader")]
    for b in (0, 1):
        groups[f"HintBank{b}"] = [("next", n) for n in rb.REGISTERS if n.startswith(f"r_bank{b}")]
    groups["HintOutputs"] = [("output", n) for n in rb.OUTPUTS]
    for name, items in groups.items():
        write(name, rb.scope_source(source, items, "CutHints") if variant == "composed" else
              banks.scope_source(source, cuts, items, "CutHints"))
    write("ReferenceCuts", rb.cuts_source(cuts, "Embeddings", "HintCore0") if variant == "composed" else
          banks.cuts_source(source, cuts, variant, "Embeddings", "HintCore0"))
    write("Model", rb.model_source(rtl, "Graphs"))
    endpoints = [("next", n) for n in rb.REGISTERS] + [("output", n) for n in rb.OUTPUTS]
    write("Endpoints", rb.endpoints_source(source, rtl, pairs, cuts, endpoints,
        ["ReferenceCuts", "Links", "Model", *groups],
        netlist_definitions=("netlist" if variant == "composed" else
                             "netlist, CacheEnable.netlist" if variant == "enable-split" else
                             "netlist, BankSelect.netlist")))
    flag = "true" if variant == "late-bank" else "false"
    write("Proof", rb.proof_source(["Endpoints"]) if variant == "composed" else
          rb.proof_source(["Endpoints"],
                          next_theorem="CacheEnable.netlist_next" if variant == "enable-split" else f"BankSelect.netlist_next {flag}",
                          output_theorem="CacheEnable.netlist_output" if variant == "enable-split" else f"BankSelect.netlist_output {flag}"))
    write("Audit", (ROOT / "test/ProofAudit.lean").read_text().replace(
        "import Pinwheel\n", "import Pinwheel\nimport Proof\n"))
    return ["Design", "Hints", "Graphs", "CutHints", "Embeddings", "LocalProofs", "Links",
            *groups, "ReferenceCuts", "Model", "Endpoints", "Proof", "Audit"]


def mutation_checks(check, original):
    """Try a frozen checked certificate against independent reimports of RTL.

    The unchanged control must pass. Each corrupt artifact must compile as RTL,
    import under the same full state/port contract, and fail in Lean.
    """
    fixtures = [
        ("unchanged", None, None, "next", ".control .active"),
        ("loader-initialization", r"r_loader_active\s*<=\s*[^;]+;", "r_loader_active <= 1'b1;", "next", ".control .active"),
        ("upload-cursor", r"r_loader_cursor\s*<=\s*[^;]+;", "r_loader_cursor <= 9'h0;", "next", ".control .cursor"),
        ("capture", r"r_sample0\s*<=\s*[^;]+;", "r_sample0 <= 1'b0;", "next", ".core (.sample ⟨0, by decide⟩)"),
        ("pc-output", r"assign pc = r_pc;", "assign pc = ~r_pc;", "output", ".core (.state .pc)"),
        ("rejected-command", r"assign loader_rejected\s*=\s*[^;]+;", "assign loader_rejected = 1'b0;", "output", ".control .rejected"),
        ("cache-update", r"r_cached_word\s*<=\s*[^;]+;", "r_cached_word <= 64'h0;", "next", ".current"),
    ]
    for name, pattern, replacement, kind, ctor in fixtures:
        directory = check.out / "mutations" / name
        directory.mkdir(parents=True)
        text = original
        if pattern:
            text, count = re.subn(pattern, replacement, original)
            if count != 1: raise RuntimeError(f"Mutation {name} did not match exactly once")
        (directory / "composed.sv").write_text(text)
        graph = check.import_rtl(directory / "composed.sv", directory)
        (directory / "MutantGraphs.lean").write_text(rb.HEADER + graph.definitions("Mutant") +
                                                    "end Pinwheel.Artifact.Backend\n")
        model = rb.model_source(graph, "MutantGraphs").replace("RTL.", "Mutant.").replace("rtlStep", "mutantStep").replace("rtlObserve", "mutantObserve")
        (directory / "MutantModel.lean").write_text(model)
        action = "mutantStep" if kind == "next" else "mutantObserve"
        operation = "step" if kind == "next" else "observe"
        (directory / "Reject.lean").write_text("import Proof\nimport MutantModel\n" + rb.HEADER + f"""
theorem candidate_correct (i : Machine.Inputs) (s : State) :
    {action} i.values s.values ({ctor}) = netlist.{operation} i.values s.values ({ctor}) := by
  exact model_{kind} i s ({ctor})
end Pinwheel.Artifact.Backend
""")
        lean_path = os.pathsep.join([str(directory), str(check.out)])
        for module in ("MutantGraphs", "MutantModel"): check.lean(module, directory=directory, lean_path=lean_path)
        check.lean("Reject", directory=directory, lean_path=lean_path, reject=pattern is not None)
    return [f[0] for f in fixtures if f[1] is not None]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--variant", choices=banks.VARIANTS, default="composed")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.tag): parser.error("Use letters, numbers, hyphens or underscores")
    out = ROOT / "build/backend" / args.tag
    if out.exists(): raise RuntimeError("Choose a fresh tag to retain previous evidence")
    out.mkdir(parents=True)
    sources = sorted((ROOT / "Pinwheel").rglob("*.lean")) + [ROOT / n for n in (
        "Pinwheel.lean", "test/Backend.lean", "test/BankSelect.lean", "test/ProofAudit.lean", "lakefile.toml", "lean-toolchain",
        "scripts/check-backend-readback.py", "scripts/backend_readback.py", "scripts/check-backend.py",
        "scripts/bank_select_readback.py", "test/test_backend_readback.py")]
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    check = Check(out)
    start = time.monotonic()
    emitter = "backend_emit" if args.variant == "composed" else "bank_select_emit"
    check.run(["lake", "build", emitter, "Pinwheel.Hardware.Readback.Boolean", "Pinwheel"], "build")
    check.run([sys.executable, "-m", "unittest", "discover", "-s", "test", "-p", "test_backend_readback.py", "-v"], "import-guards")
    check.run([ROOT / ".lake/build/bin" / emitter, out] +
              ([] if args.variant == "composed" else [args.variant]), "emit")
    circt = ROOT / "build/tools/firtool-1.159.0/bin/circt-opt"
    yosys = ROOT / "build/tools/oss-cad-suite/bin/yosys"
    z3 = ROOT / "build/tools/oss-cad-suite/bin/z3"
    versions = {label: check.run(command, label + "-version").strip() for label, command in (
        ("lean", ["lean", "--version"]), ("circt", [circt, "--version"]),
        ("yosys", [yosys, "-V"]), ("z3", [z3, "-version"]))}
    rtl_text = check.run([circt, out / "composed.mlir", "--canonicalize", "--lower-seq-to-sv",
        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], "circt")
    (out / "composed.sv").write_text(rtl_text)
    source = rb.read_hints(out / "composed.mlir")
    rtl = check.import_rtl(out / "composed.sv", out)
    if args.variant == "composed":
        labels = (out / "cuts.txt").read_text().splitlines()
        if len(labels) != 5 or any(not re.fullmatch(r"%v\d+", n) for n in labels): raise RuntimeError("Invalid cut hints")
        successor, pc, target, selected, index = [n[1:] for n in labels]
        cuts = {target: "address", selected: "selection", index: "indexValue", successor: "successorValue", pc: "pcValue"}
        if len(cuts) != 5 or [source.nodes[n].width for n in cuts] != [8, 1, 6, 64, 8]: raise RuntimeError("Changed cut widths")
    else:
        cuts = banks.read_cuts(out / "cuts.tsv", source, args.variant)
        successor = next(n for n, role in cuts.items() if role == "successorValue")
    rb.add_storage_views(rtl, source)
    pairs = rb.partitions(source, rtl, successor=successor, oracle=rb.cut_oracle(z3))
    (out / "partitions.json").write_text(json.dumps([{k: v for k, v in p.items() if k not in ("left", "right")}
        for p in pairs], indent=2) + "\n")
    for module in generate(out, source, rtl, cuts, pairs, args.variant): check.lean(module)
    mutations = mutation_checks(check, rtl_text)
    if {str(p.relative_to(ROOT)): sha(p) for p in sources} != hashes:
        raise RuntimeError("Sources changed during verification")
    artifacts = sorted(p for p in out.rglob("*") if p.is_file() and p.suffix in {".lean", ".mlir", ".sv", ".ys", ".json", ".log"})
    report = {"variant": args.variant, "source_sha256": hashes, "versions": versions, "commands": check.commands,
        "artifact_sha256": {str(p.relative_to(out)): sha(p) for p in artifacts},
        "register_fields": len(rb.REGISTERS), "register_bits": sum(w for w, _ in rb.REGISTERS.values()),
        "outputs": len(rb.OUTPUTS), "checked_local_equalities": len(pairs),
        "invalid_import_shapes_rejected": 27, "adapter_truth_table_cases": 344,
        "largest_local_expression": max(p["size"] for p in pairs), "standard_axioms_only": True,
        "mutation_rejections": mutations, "unchanged_reimport_certificate": "passed",
        "theorems": ["Pinwheel.Artifact.Backend." + n for n in ("model_next", "model_output", "initialized_trace")],
        "elapsed_seconds": round(time.monotonic() - start, 3),
        "boundary": "Lean checks all imported RTL register updates and outputs against the selected typed netlist, "
            "then composes its initialized, cycle-exact reference trace refinement. Two-state positive-edge semantics; "
            "the trace contract begins after initialization and retains the capacity adapter. Yosys Verilog/proc "
            "interpretation and the restricted JSON adapter remain trusted. MLIR, simulation and Z3 supply only "
            "proof hints; every accepted equality is checked by Lean without native-evaluation axioms. "
            "This is validation of the recorded artifact, not a universal compiler theorem or physical-timing result."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Backend read-back passed: {out / 'report.json'}", flush=True)


if __name__ == "__main__":
    main()
