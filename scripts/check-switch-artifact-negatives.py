#!/usr/bin/env python3
"""Reject semantic and interface corruptions of a checked switch RTL artifact.

A passed receipt binds the baseline source, tools, and complete artifact set.
Each negative uses an independent copy. Rejection alone is insufficient: the
runner additionally asks Lean's kernel to check a concrete mismatch witness.
This validates rejection controls, not arbitrary Verilog/JSON parser correctness.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import time

import process_group
import typed_circuit_readback as readback
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def helper(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


artifact = helper("switch_artifact_positive", "check-switch-artifact.py")
switch = helper("switch_artifact_mutations", "check-switch-circuit.py")


def sources():
    result = artifact.sources()
    for name in ("scripts/check-switch-artifact-negatives.py", "scripts/check-switch-circuit.py",
                 "scripts/check-switch-model.py", "scripts/switch_oracle.py"):
        result[name] = sha(ROOT / name)
    return result


def contained(base, name):
    path = (base / name).resolve()
    if not path.is_relative_to(base.resolve()):
        raise ValueError(f"Receipt path leaves its owning directory: {name}")
    return path


def verify_positive(receipt, config, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed":
        raise ValueError("A completed passed positive artifact receipt is required")
    if report.get("source_sha256") != artifact.sources():
        raise ValueError("Positive receipt does not match the current source profile/importer")
    if report.get("tool_sha256") != tools_hash:
        raise ValueError("Positive receipt does not match the selected tools")
    if not any(tuple(c["configuration"]) == config for c in report.get("configurations", [])):
        raise ValueError("Requested configuration was not certified by the positive receipt")
    hashes = report.get("artifact_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("Positive receipt has no artifact identities")
    for name, expected in hashes.items():
        if sha(contained(receipt.parent, name)) != expected:
            raise ValueError(f"Positive artifact changed: {name}")
    label = "switch-" + "-".join(map(str, config))
    for filename in ("switch.mlir", "switch.sv", "interface.json", "import.json",
                     "Design.lean", "Proof.lean", "Initialized.lean", "Audit.lean", "Audit.log"):
        if f"{label}/{filename}" not in hashes:
            raise ValueError(f"Positive receipt omits required evidence: {filename}")
    return receipt.parent / label


def compile_lean(run, directory, module):
    lean_path = str(directory) + os.pathsep + str(ROOT / ".lake/build/lib/lean")
    command = ["env", "LEAN_PATH=" + lean_path, "lake", "env", "lean", "-DwarningAsError=true",
               "-o", directory / f"{module}.olean", directory / f"{module}.lean"]
    record = {"label": directory.name + "-" + module, "argv": list(map(str, command)), "timeout_seconds": 300}
    run.records.append(record)
    started = time.monotonic()
    try:
        result = process_group.run_captured(record["argv"], cwd=ROOT, timeout=300,
                                            log_path=directory / f"{module}.log")
        record.update(exit_code=result.returncode, seconds=round(time.monotonic()-started, 3))
        return result
    except BaseException as error:
        record.update(error=type(error).__name__, seconds=round(time.monotonic()-started, 3))
        raise


def semantic_errors(log, stage):
    text = log.read_text()
    errors = re.findall(r"^.*?\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$", text, re.M)
    if not errors:
        raise RuntimeError(f"{stage} did not report a Lean theorem failure: {log}")
    allowed = ("`grind` failed", "unsolved goals", "Tactic `decide` proved that the proposition")
    if any(not any(marker in error for marker in allowed) for error in errors):
        raise RuntimeError(f"Unexpected failure is not a semantic negative-control result: {errors}")
    return errors


def check_witness(run, directory, text):
    (directory / "MutationWitness.lean").write_text(text)
    result = compile_lean(run, directory, "MutationWitness")
    if result.returncode:
        raise RuntimeError(f"Concrete mismatch witness failed: {directory / 'MutationWitness.log'}")
    print(directory.name + ": concrete mismatch kernel-checked", flush=True)


def graph_value(graph, name, namespace):
    node = graph.nodes[name]
    if node.op in ("input", "reg", "lit"):
        return graph.expression(node, None).replace("i (", "witnessInputs (").replace("s (", "witnessState (")
    return f"{namespace}.{name} witnessInputs witnessState"


def rtl_witness(directory, descriptor, kind, endpoint, reset_high):
    reader = readback.importer(descriptor)
    source = reader.read_hints(directory / "switch.mlir")
    actual = reader.read_rtl(directory / "import.json")
    reset_index = next(k for k, p in enumerate(descriptor["inputs"]) if p["name"] == descriptor["roles"]["reset"])
    left = (source.next if kind == "next" else source.outputs)[endpoint]
    right = (actual.next if kind == "next" else actual.outputs)[endpoint]
    input_value = f"if (inputs.position _p).val = {reset_index} then 1 else 0" if reset_high else "0"
    return f"""import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def witnessInputs : Values Input := fun {{w}} _p => BitVec.ofNat w ({input_value})
def witnessState : Values Register := fun {{w}} _ => BitVec.ofNat w 0
/-- The mutation changes this endpoint on concrete two-state input/state bits. -/
theorem semantic_mutation :
    ({graph_value(source, left, 'Source')}) ≠ ({graph_value(actual, right, 'RTL')}) := by decide +kernel
#print axioms semantic_mutation
end Pinwheel.TypedArtifact
"""


def flip_state_d(text, name):
    pattern = re.compile(r"(\b" + re.escape(name) + r"\s*<=\s*)(.*?);", re.DOTALL)
    changed, count = pattern.subn(lambda m: m[1] + "~(" + m[2].strip() + ");", text)
    if count != 1 or changed == text:
        raise ValueError(f"Expected exactly one state-D assignment for {name}, found {count}")
    return changed


def rtl_negative(run, tools, directory, config, descriptor, control):
    rtl = directory / "switch.sv"
    if control == "drop-ready":
        rtl.write_text(switch.mutate_rtl(rtl.read_text(), descriptor, "drop_ready"))
        kind, endpoint, reset_high = "output", descriptor["roles"]["in_ready"][0], False
    else:
        endpoint = descriptor["register_roles"]["fifo_valid"][0][0]
        rtl.write_text(flip_state_d(rtl.read_text(), endpoint))
        kind, reset_high = "next", True
    try:
        artifact.certify(run, tools, directory, config, descriptor, rtl)
    except RuntimeError as error:
        failure = re.match(r"(LocalProofs(?:[0-9]+)?) certificate failed:", str(error))
        if not failure:
            raise
        stage = failure[1]
        run.records[-1]["expected_failure"] = True
        errors = semantic_errors(directory / f"{stage}.log", stage)
    else:
        raise AssertionError(f"Corrupted RTL received a certificate: {control}")
    check_witness(run, directory, rtl_witness(directory, descriptor, kind, endpoint, reset_high))
    return {"control": control, "stage": stage, "rejection": errors,
            "endpoint_kind": kind, "endpoint": endpoint,
            "witness": {"reset_high": reset_high, "other_inputs": 0, "all_registers": 0},
            "kernel_checked_counterexample": True}


def omit_output(directory, descriptor):
    index = len(descriptor["outputs"]) - 1
    removed = descriptor["outputs"].pop()
    text = (directory / "switch.mlir").read_text()
    text, count = re.subn(r", out " + re.escape(removed["name"]) + r" : i" + str(removed["width"]) + r"(?=\))", "", text)
    if count != 1:
        raise ValueError("Cannot identify the final hint output declaration")
    pattern = re.compile(r"(\s*hw\.output\s+)([^\n]+?)(\s*:\s*)([^\n]+)")
    match = pattern.search(text)
    if not match:
        raise ValueError("Cannot identify hint output operands")
    values, widths = match[2].split(","), match[4].split(",")
    if len(values) != index + 1 or len(widths) != index + 1:
        raise ValueError("Hint output operand count differs from descriptor")
    text = text[:match.start()] + match[1] + ",".join(values[:index]) + match[3] + ",".join(widths[:index]) + text[match.end():]
    (directory / "switch.mlir").write_text(text)
    imported = json.loads((directory / "import.json").read_text())
    del imported["modules"][descriptor["module"]]["ports"][removed["name"]]
    (directory / "import.json").write_text(json.dumps(imported, indent=2) + "\n")
    return removed


def metadata_negative(run, tools, directory, config, descriptor, control):
    if control == "coordinated-output-omission":
        removed = omit_output(directory, descriptor)
        proposition = f"(outputs : Interface Output).size ≠ {len(descriptor['outputs'])}"
        expected_guard = f"(outputs : Interface Output).size = {len(descriptor['outputs'])}"
        detail = {"removed_output": removed["name"], "modified": ["interface.json", "switch.mlir", "import.json"]}
    else:
        a, b = next((a, b) for a in range(len(descriptor["inputs"]))
                    for b in range(a+1, len(descriptor["inputs"]))
                    if descriptor["inputs"][a]["width"] == descriptor["inputs"][b]["width"])
        descriptor["inputs"][a], descriptor["inputs"][b] = descriptor["inputs"][b], descriptor["inputs"][a]
        for k in (a, b):
            if "index" in descriptor["inputs"][k]: descriptor["inputs"][k]["index"] = k
        name = json.dumps(descriptor["inputs"][a]["name"])
        proposition = f"inputs.label (inputs.signal ⟨{a}, by decide +kernel⟩).2 ≠ {name}"
        expected_guard = f"inputs.label input_{a} = {name}"
        detail = {"swapped_input_ordinals": [a, b], "modified": ["interface.json"]}
    (directory / "interface.json").write_text(json.dumps(descriptor, indent=2) + "\n")
    readback.generate(directory, descriptor, directory / "switch.mlir", directory / "import.json", tools["z3"],
                      profile=artifact.profile(config, descriptor["destination_width"]))
    result = compile_lean(run, directory, "Design")
    if result.returncode == 0:
        raise AssertionError(f"Corrupted interface received a typed binding: {control}")
    run.records[-1]["expected_failure"] = True
    errors = semantic_errors(directory / "Design.log", "Design")
    source = (directory / "Design.lean").read_text().splitlines()
    locations = re.findall(r"Design\.lean:(\d+):\d+: error", (directory / "Design.log").read_text())
    if not any(expected_guard in source[int(line)-1] for line in locations):
        raise RuntimeError(f"Design failed outside the intended complete-interface guard: {control}")
    profile = artifact.profile(config, descriptor["destination_width"])
    imports = "\n".join(line for line in profile.splitlines() if line.startswith("import "))
    body = "\n".join(line for line in profile.splitlines() if not line.startswith("import "))
    witness = (imports + "\nopen Pinwheel.Hardware\nnamespace Pinwheel.TypedArtifact\n" + body +
               f"\ntheorem metadata_mutation : {proposition} := by decide +kernel\n" +
               "#print axioms metadata_mutation\nend Pinwheel.TypedArtifact\n")
    check_witness(run, directory, witness)
    return {"control": control, "stage": "Design", "rejection": errors, "kernel_checked_counterexample": True, **detail}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    parser.add_argument("--config", default="1,1,1,1", help="Certified INPUTS,OUTPUTS,DEPTH,WIDTH")
    args = parser.parse_args()
    config = tuple(map(int, args.config.split(",")))
    if len(config) != 4 or min(config) <= 0:
        parser.error("Configuration must contain four positive integers")
    out = fresh_directory(ROOT / "build/switch-artifact-negatives", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "controls": [],
              "boundary": "Expected Lean proof/binding rejection plus kernel-checked concrete mismatch witnesses. "
                          "The positive certificate remains conditional on the trusted RTL JSON interpretation."}
    run = artifact.rr.Commands(out, report["commands"])
    started = time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, tool_paths = artifact.rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        tool_paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, artifact.rr.tool_hashes(tool_paths)
        receipt = args.positive_report.resolve()
        baseline = verify_positive(receipt, config, report["tool_sha256"])
        report["positive_receipt"] = {"path": str(receipt), "sha256": sha(receipt), "configuration": config}
        shutil.copyfile(receipt, out / "positive-report.json")
        for control in ("drop-ready", "invert-state-d", "coordinated-output-omission", "same-width-input-permutation"):
            directory = out / control
            directory.mkdir()
            for filename in ("switch.sv", "switch.mlir", "interface.json", "import.json"):
                shutil.copyfile(baseline / filename, directory / filename)
            descriptor = json.loads((directory / "interface.json").read_text())
            before = {name: sha(directory / name) for name in ("switch.sv", "switch.mlir", "interface.json", "import.json")}
            if control in ("drop-ready", "invert-state-d"):
                evidence = rtl_negative(run, tools, directory, config, descriptor, control)
            else:
                evidence = metadata_negative(run, tools, directory, config, descriptor, control)
            evidence["before_sha256"] = before
            evidence["after_sha256"] = {name: sha(directory / name) for name in before}
            report["controls"].append(evidence)
            print(control + ": intended rejection confirmed", flush=True)
        verify_positive(receipt, config, report["tool_sha256"])
        if sha(receipt) != report["positive_receipt"]["sha256"] or sources() != report["source_sha256"] or \
                artifact.rr.tool_hashes(tool_paths) != report["tool_sha256"]:
            raise RuntimeError("Sources/tools/positive receipt changed during negative validation")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic()-started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
