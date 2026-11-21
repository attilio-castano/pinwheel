#!/usr/bin/env python3
"""Require semantic rejection and concrete witnesses for transfer RTL faults."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import shutil
import time

import typed_circuit_readback as readback
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
CONFIG = (2, 8, 8)


def helper(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


positive = helper("transfer_artifact_positive", "check-memory-transfer-artifact.py")
common = helper("transfer_artifact_negative_utilities", "check-switch-artifact-negatives.py")


def sources():
    result = positive.sources()
    result.update({name: sha(ROOT / name) for name in ("scripts/check-memory-transfer-artifact-negatives.py",
        "scripts/check-switch-artifact-negatives.py", "scripts/check-switch-artifact.py",
        "scripts/check-switch-circuit.py", "scripts/check-switch-model.py", "scripts/switch_oracle.py")})
    return dict(sorted(result.items()))


def verify_positive(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != positive.sources() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed transfer artifact receipt matching current sources/tools")
    entry = next((row for row in report.get("configurations", []) if tuple(row["configuration"]) == CONFIG), None)
    if entry is None or entry.get("initialized_trace_checked") is not True:
        raise ValueError("Receipt must certify a2/i8/o8 including its initialized trace")
    hashes = report.get("artifact_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("Missing artifact identities")
    for name, digest in hashes.items():
        if sha(common.contained(receipt.parent, name)) != digest:
            raise ValueError("Positive artifact changed: " + name)
    label = "transfer-" + "-".join(map(str, CONFIG))
    for filename in ("transfer.mlir", "transfer.sv", "interface.json", "import.json", "Design.lean",
                     "Proof.lean", "Initialized.lean", "Audit.lean", "Audit.log", "MemoryTransferSupport.olean"):
        if f"{label}/{filename}" not in hashes:
            raise ValueError("Positive receipt omits " + filename)
    return receipt.parent / label


def witness(directory, descriptor, kind, endpoint):
    reader = readback.importer(descriptor)
    source, actual = reader.read_hints(directory / "transfer.mlir"), reader.read_rtl(directory / "import.json")
    # A valid one-word transfer: source response 60 is accepted at destination2.
    inputs = [0, 0, 0, 0, 0, 1, 1, 60, 1]
    registers = [2, 1, 2, 1, 0, 0, 0]

    def expression(values, descriptor_name):
        result = "0"
        for k, value in reversed(list(enumerate(values))):
            if value:
                result = f"if ({descriptor_name}.position p).val = {k} then {value} else ({result})"
        return result

    source_name = (source.outputs if kind == "output" else source.next)[endpoint]
    actual_name = (actual.outputs if kind == "output" else actual.next)[endpoint]
    lhs = common.graph_value(source, source_name, "Source")
    rhs = common.graph_value(actual, actual_name, "RTL")
    valid = descriptor["roles"]["destination_valid"]
    original_valid = common.graph_value(source, source.outputs[valid], "Source")
    mutant_valid = common.graph_value(actual, actual.outputs[valid], "RTL")
    expected_value = 195 if kind == "output" else 1
    return f"""import Lean
import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact.MutationControl
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def witnessInputs : Values Input := fun {{w}} p => BitVec.ofNat w ({expression(inputs, 'inputs')})
def witnessState : Values Register := fun {{w}} p => BitVec.ofNat w ({expression(registers, 'registers')})
theorem active_write : ({original_valid}) = 1 ∧ ({mutant_valid}) = 1 := by decide +kernel
theorem correct_value : ({lhs}) = {expected_value} := by decide +kernel
theorem semantic_mutation : ({lhs}) ≠ ({rhs}) := by decide +kernel
end Pinwheel.TypedArtifact.MutationControl
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.TypedArtifact.MutationControl." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved witness axioms in {{name}}: {{bad}}"
  if count == 0 then throwError "Empty transfer mismatch audit"
  logInfo m!"Transfer mutation audit: {{count}} declarations, standard axioms only."
""", {"inputs": inputs, "registers": registers, "source_endpoint_value": expected_value,
        "active_condition": "source and mutant both offer a destination write; destination ready is asserted"}


def control(run, tools, out, baseline, name):
    directory = out / name
    directory.mkdir()
    for filename in ("transfer.mlir", "transfer.sv", "interface.json"):
        shutil.copyfile(baseline / filename, directory / filename)
    descriptor = json.loads((directory / "interface.json").read_text())
    positive.checks.validate_descriptor(descriptor, *CONFIG)
    rtl = directory / "transfer.sv"
    before = sha(rtl)
    changed = dict(positive.checks.mutations(rtl.read_text(), descriptor))[name]
    rtl.write_text(changed)
    if before == sha(rtl):
        raise AssertionError("Mutation changed no RTL")
    try:
        positive.certify(run, tools, directory, CONFIG, descriptor, rtl)
    except RuntimeError as error:
        match = re.match(r"(LocalProofs(?:[0-9]+)?) certificate failed:", str(error))
        if not match:
            raise
        stage = match[1]
        errors = common.semantic_errors(directory / (stage + ".log"), stage)
        run.records[-1]["expected_failure"] = True
    else:
        raise AssertionError("Corrupted transfer RTL received a certificate")
    if name == "invert-active-payload":
        kind, endpoint = "output", descriptor["roles"]["destination_data"]
    else:
        kind, endpoint = "next", descriptor["register_roles"]["index"]
    text, details = witness(directory, descriptor, kind, endpoint)
    common.check_witness(run, directory, text)
    if "standard axioms only" not in (directory / "MutationWitness.log").read_text():
        raise AssertionError("Missing transfer witness audit")
    return {"control": name, "stage": stage, "rejection": errors, "endpoint_kind": kind, "endpoint": endpoint,
            "witness": details, "kernel_checked_counterexample": True, "rtl_before_sha256": before, "rtl_after_sha256": sha(rtl)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer-artifact-negatives", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "controls": [],
        "boundary": "Two actual RTL corruptions must fail local semantic equalities, then prove exact concrete "
                    "source/imported-RTL mismatches during an active write. Parser errors/timeouts do not count."}
    run, started = positive.rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = positive.rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, positive.rr.tool_hashes(paths)
        receipt = args.positive_report.resolve()
        baseline = verify_positive(receipt, report["tool_sha256"])
        report["positive_receipt"] = {"path": str(receipt), "sha256": sha(receipt), "configuration": CONFIG}
        shutil.copyfile(receipt, out / "positive-report.json")
        for name in ("invert-active-payload", "erase-progress-index"):
            report["controls"].append(control(run, tools, out, baseline, name))
        if sources() != report["source_sha256"] or positive.rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during transfer negative validation")
        verify_positive(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_receipt"]["sha256"]:
            raise RuntimeError("Positive receipt changed during validation")
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
