#!/usr/bin/env python3
"""Reject corrupted memory RTL with Lean failures and kernel-checked witnesses."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import shutil
import time

import typed_circuit_readback as readback
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("memory_artifact", ROOT / "scripts/check-memory-command-artifact.py")
positive = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(positive)


def sources():
    return {**positive.sources(), "scripts/check-memory-command-artifact-negatives.py": sha(Path(__file__))}


def baseline(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != positive.sources() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed positive receipt matching current sources and tools")
    if not any(c.get("configuration") == [1, 1] for c in report.get("configurations", [])):
        raise ValueError("Receipt does not certify the negative-control configuration")
    hashes = report.get("artifact_sha256", {})
    for filename in ("memory.mlir", "memory.sv", "interface.json", "import.json", "Design.lean",
                     "Proof.lean", "MemoryTrace.lean", "Audit.lean", "Audit.log"):
        if "memory-1-1/" + filename not in hashes:
            raise ValueError("Receipt omits required positive evidence: " + filename)
    for name, digest in hashes.items():
        path = (receipt.parent / name).resolve()
        if not path.is_relative_to(receipt.parent.resolve()) or sha(path) != digest:
            raise ValueError("Positive artifact identity changed: " + name)
    return receipt.parent / "memory-1-1"


def witness(directory, descriptor, kind, endpoint, initial):
    reader = readback.importer(descriptor)
    source, actual = reader.read_hints(directory / "memory.mlir"), reader.read_rtl(directory / "import.json")

    def expression(graph, namespace):
        name = (graph.outputs if kind == "output" else graph.next)[endpoint]
        node = graph.nodes[name]
        if node.op in ("input", "reg", "lit"):
            return graph.expression(node, None).replace("i (", "witnessInputs (").replace("s (", "witnessState (")
        return f"{namespace}.{name} witnessInputs witnessState"

    return f"""import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
def witnessInputs : Values Input := fun {{w}} _ => BitVec.ofNat w 0
def witnessState : Values Register := fun {{w}} _ => BitVec.ofNat w {initial}
theorem memory_mutation :
    ({expression(source, 'Source')}) ≠ ({expression(actual, 'RTL')}) := by decide +kernel
#print axioms memory_mutation
end Pinwheel.TypedArtifact
"""


def control(run, tools, out, source, name):
    directory = out / name
    directory.mkdir()
    for filename in ("memory.mlir", "memory.sv", "interface.json"):
        shutil.copyfile(source / filename, directory / filename)
    descriptor = json.loads((directory / "interface.json").read_text())
    rtl = directory / "memory.sv"
    if name == "inverted-q":
        endpoint = descriptor["roles"]["q"]
        pattern = r"(\bassign\s+" + re.escape(endpoint) + r"\s*=\s*)([^;]+);"
        changed, count = re.subn(pattern, lambda m: m[1] + "~(" + m[2].strip() + ");", rtl.read_text())
        kind, initial = "output", 0
    else:
        endpoint = descriptor["register_roles"]["words"][0]
        pattern = r"(\b" + re.escape(endpoint) + r"\s*<=\s*)([^;]+);"
        changed, count = re.subn(pattern, lambda m: m[1] + "~(" + m[2].strip() + ");", rtl.read_text())
        kind, initial = "next", 0
    if count != 1 or changed == rtl.read_text():
        raise ValueError("RTL mutation no longer identifies exactly one assignment")
    rtl.write_text(changed)
    try:
        positive.certify(run, tools, directory, descriptor, 1, 1, rtl)
    except RuntimeError as error:
        match = re.match(r"(LocalProofs(?:[0-9]+)?) certificate failed:", str(error))
        if not match:
            raise
        stage = match[1]
        errors = re.findall(r"^.*?\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$",
                            (directory / (stage + ".log")).read_text(), re.M)
        allowed = ("`grind` failed", "unsolved goals", "Tactic `decide` proved that the proposition")
        if not errors or any(not any(marker in error for marker in allowed) for error in errors):
            raise RuntimeError("Rejection was not an expected semantic theorem failure")
        run.records[-1]["expected_failure"] = True
    else:
        raise AssertionError("Corrupted RTL received a memory certificate")
    (directory / "MutationWitness.lean").write_text(witness(directory, descriptor, kind, endpoint, initial))
    compile_modules(run, directory, ["MutationWitness"])
    return {"control": name, "stage": stage, "rejection": errors, "endpoint": endpoint,
            "inputs": 0, "all_registers": initial, "kernel_checked_counterexample": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-command-artifact-negatives", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "controls": [],
        "boundary": "Expected semantic Lean rejection plus kernel-checked concrete counterexamples. "
        "These controls do not prove the trusted RTL parser/JSON interpretation correct."}
    run, started = positive.rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = positive.rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, positive.rr.tool_hashes(paths)
        receipt = args.positive_report.resolve()
        source = baseline(receipt, report["tool_sha256"])
        report["positive_report"] = {"path": str(receipt), "sha256": sha(receipt)}
        for name in ("inverted-q", "flipped-word-d"):
            report["controls"].append(control(run, tools, out, source, name))
        if report["source_sha256"] != sources() or report["tool_sha256"] != positive.rr.tool_hashes(paths):
            raise RuntimeError("Owning sources/tools changed during negative controls")
        baseline(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_report"]["sha256"]:
            raise RuntimeError("Positive receipt changed during negative controls")
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
