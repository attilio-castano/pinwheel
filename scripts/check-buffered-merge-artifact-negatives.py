#!/usr/bin/env python3
"""Require semantic proof rejection and kernel witnesses for merge RTL faults."""
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
CONFIG = (2, 8)
CONTROLS = ("stalled_payload_corruption", "cursor_without_acceptance", "multiple_ready", "drop_replacement")


def helper(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


positive = helper("merge_positive_artifacts", "check-buffered-merge-artifact.py")
common = helper("merge_negative_utilities", "check-switch-artifact-negatives.py")


def sources():
    result = positive.sources()
    # These are executed imports of the reused containment, error filtering,
    # graph-expression, and private-module witness-compilation utilities.
    result.update({name: sha(ROOT / name) for name in (
        "scripts/check-buffered-merge-artifact-negatives.py",
        "scripts/check-switch-artifact-negatives.py", "scripts/check-switch-artifact.py",
        "scripts/check-switch-circuit.py", "scripts/check-switch-model.py", "scripts/switch_oracle.py")})
    return dict(sorted(result.items()))


def verify_positive(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != positive.sources() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed merge artifact receipt matching current sources/tools")
    entries = [row for row in report.get("configurations", []) if tuple(row.get("configuration", [])) == CONFIG]
    if len(entries) != 1 or entries[0].get("initialized_trace_checked") is not True:
        raise ValueError("Receipt must certify merge2/8 including arbitrary-state initialized traces")
    entry = entries[0]
    if entry.get("typed_registers") != 4 or entry.get("typed_outputs") != 4 or entry.get("endpoints") != 8:
        raise ValueError("Incomplete merge2/8 endpoint coverage")
    hashes = report.get("artifact_sha256")
    if type(hashes) is not dict or not hashes:
        raise ValueError("Missing positive artifact identities")
    for name, digest in hashes.items():
        if sha(common.contained(receipt.parent, name)) != digest:
            raise ValueError("Positive artifact changed: " + name)
    label = "merge-" + "-".join(map(str, CONFIG))
    for filename in ("merge.mlir", "merge.sv", "interface.json", "import.json", "Design.lean", "Graphs.lean",
                     "Proof.lean", "Initialized.lean", "Audit.lean", "Audit.log"):
        if f"{label}/{filename}" not in hashes:
            raise ValueError("Positive receipt omits " + filename)
    return receipt.parent / label


def witness(directory, descriptor, mutation):
    reader = readback.importer(descriptor)
    source = reader.read_hints(directory / "merge.mlir")
    actual = reader.read_rtl(directory / "import.json")
    roles, regs = descriptor["roles"], descriptor["register_roles"]
    pins = {roles["reset"]: 0, roles["out_ready"]: 0,
            roles["in_valid"][0]: 1, roles["in_valid"][1]: 1,
            roles["in_payload"][0]: 7, roles["in_payload"][1]: 9}
    bank = {regs["slot_valid"]: 1, regs["slot_payload"]: 90,
            regs["cursor"][0]: 1, regs["cursor"][1]: 0}

    def output(graph, name, namespace):
        return common.graph_value(graph, graph.outputs[name], namespace)

    def pin(name):
        index = next(k for k, port in enumerate(descriptor["inputs"]) if port["name"] == name)
        return f"witnessInputs input_{index}"

    def register(name):
        index = next(k for k, port in enumerate(descriptor["registers"]) if port["name"] == name)
        return f"witnessState register_{index}"

    conditions = [f"({pin(roles['reset'])}) = 0", f"({register(regs['cursor'][0])}) = 1",
                  f"({register(regs['cursor'][1])}) = 0"]
    conditions += [f"({pin(name)}) = 1" for name in roles["in_valid"]]
    if mutation in ("stalled_payload_corruption", "cursor_without_acceptance"):
        conditions += [f"({pin(roles['out_ready'])}) = 0", f"({register(regs['slot_valid'])}) = 1"]
        for graph, namespace in ((source, "Source"), (actual, "RTL")):
            conditions += [f"({output(graph, roles['out_valid'], namespace)}) = 1",
                           f"({output(graph, roles['out_payload'], namespace)}) = 90"]
            conditions += [f"({output(graph, name, namespace)}) = 0" for name in roles["in_ready"]]
        if mutation == "stalled_payload_corruption":
            kind, endpoint, expected, corrupted = "next", regs["slot_payload"], 90, 165
            description = "Both designs hold valid payload90 with downstream blocked and no input acceptance; mutant corrupts next payload to165"
        else:
            kind, endpoint, expected, corrupted = "next", regs["cursor"][0], 1, 0
            description = "Both designs hold valid payload90 with downstream blocked and no input acceptance; mutant rotates legal cursor0 to1"
    elif mutation == "multiple_ready":
        pins[roles["out_ready"]] = 1
        bank[regs["slot_valid"]] = bank[regs["slot_payload"]] = 0
        kind, endpoint, expected, corrupted = "output", roles["in_ready"][1], 0, 1
        conditions += [f"({register(regs['slot_valid'])}) = 0", f"({pin(roles['out_ready'])}) = 1"]
        for graph, namespace in ((source, "Source"), (actual, "RTL")):
            conditions += [f"({output(graph, roles['in_ready'][0], namespace)}) = 1"]
        description = "Both input offers are valid at an empty slot with legal cursor0; mutant additionally accepts source1 while accepting source0"
    elif mutation == "drop_replacement":
        pins[roles["out_ready"]] = 1
        kind, endpoint, expected, corrupted = "next", regs["slot_valid"], 1, 0
        conditions += [f"({pin(roles['out_ready'])}) = 1", f"({register(regs['slot_valid'])}) = 1",
                       f"({pin(roles['in_payload'][0])}) = 7"]
        for graph, namespace in ((source, "Source"), (actual, "RTL")):
            conditions += [f"({output(graph, roles['out_valid'], namespace)}) = 1",
                           f"({output(graph, roles['out_payload'], namespace)}) = 90",
                           f"({output(graph, roles['in_ready'][0], namespace)}) = 1",
                           f"({output(graph, roles['in_ready'][1], namespace)}) = 0"]
        description = "Both designs consume held payload90 and accept replacement7 from source0 on this edge; mutant drops the accepted replacement"
    else:
        raise ValueError("Unknown mutation " + mutation)

    input_values = [pins[p["name"]] for p in descriptor["inputs"]]
    state_values = [bank[p["name"]] for p in descriptor["registers"]]

    def expression(items, descriptor_name):
        result = "0"
        for k, value in reversed(list(enumerate(items))):
            if value:
                result = f"if ({descriptor_name}.position p).val = {k} then {value} else ({result})"
        return result

    left = (source.outputs if kind == "output" else source.next)[endpoint]
    right = (actual.outputs if kind == "output" else actual.next)[endpoint]
    lhs = common.graph_value(source, left, "Source")
    rhs = common.graph_value(actual, right, "RTL")
    text = f"""import Lean
import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact.MutationControl
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def witnessInputs : Values Input := fun {{w}} p => BitVec.ofNat w ({expression(input_values, 'inputs')})
def witnessState : Values Register := fun {{w}} p => BitVec.ofNat w ({expression(state_values, 'registers')})
theorem active_condition : {' ∧ '.join(conditions)} := by decide +kernel
theorem correct_value : ({lhs}) = {expected} := by decide +kernel
theorem corrupted_value : ({rhs}) = {corrupted} := by decide +kernel
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
      unless bad.isEmpty do throwError "Unapproved merge witness axioms in {{name}}: {{bad}}"
  if count == 0 then throwError "Empty merge mutation audit"
  logInfo m!"Merge mutation audit: {{count}} declarations, standard axioms only."
"""
    return text, {"inputs": pins, "registers": bank, "input_values": input_values, "register_values": state_values,
                  "source_endpoint_value": expected, "mutant_endpoint_value": corrupted,
                  "active_condition": description, "endpoint_kind": kind, "endpoint": endpoint}


def control(run, tools, out, baseline, mutation):
    directory = out / mutation
    directory.mkdir()
    for filename in ("merge.mlir", "merge.sv", "interface.json"):
        shutil.copyfile(baseline / filename, directory / filename)
    descriptor = json.loads((directory / "interface.json").read_text())
    positive.checks.validate_descriptor(descriptor, *CONFIG)
    rtl = directory / "merge.sv"
    before = sha(rtl)
    changed = positive.checks.mutate_rtl(rtl.read_text(), descriptor, mutation)
    # Every introduced logical operand is one bit. Its equivalent bitwise
    # spelling retains the raw binary truth table in the restricted importer.
    changed = changed.replace(" && ", " & ")
    for role in ("reset", "out_ready"):
        changed = re.sub(r"!" + re.escape(descriptor["roles"][role]) + r"\b",
                         "~" + descriptor["roles"][role], changed)
    rtl.write_text(changed)
    if sha(rtl) == before:
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
        raise AssertionError("Corrupted merge RTL received a certificate")
    text, details = witness(directory, descriptor, mutation)
    common.check_witness(run, directory, text)
    if "standard axioms only" not in (directory / "MutationWitness.log").read_text():
        raise AssertionError("Missing kernel witness axiom audit")
    return {"control": mutation, "stage": stage, "rejection": errors, "witness": details,
            "kernel_checked_counterexample": True, "rtl_before_sha256": before, "rtl_after_sha256": sha(rtl)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/buffered-merge-artifact-negatives", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "controls": [],
        "boundary": "Actual RTL payload-stability, cursor-acceptance, unique-ready and replacement faults must "
                    "fail local semantic equations and have kernel-checked exact mismatches with active conditions. "
                    "Parser failures, resource limits, unknown values and timeouts do not count."}
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
        for mutation in CONTROLS:
            report["controls"].append(control(run, tools, out, baseline, mutation))
        if sources() != report["source_sha256"] or positive.rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during merge negative validation")
        verify_positive(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_receipt"]["sha256"]:
            raise RuntimeError("Positive receipt changed during merge negative validation")
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
