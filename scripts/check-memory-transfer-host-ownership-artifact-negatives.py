#!/usr/bin/env python3
"""Require strict semantic rejection of ownership-candidate RTL faults."""
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
CONTROLS = ("clear-word-on-reset", "host-write-while-busy", "invert-active-readback")


def helper(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


positive = helper("ownership_artifact_positive", "check-memory-transfer-host-ownership-artifact.py")
common = helper("host_artifact_negative_utilities", "check-switch-artifact-negatives.py")


def sources():
    result = positive.sources()
    # The shared helper executes these local imports as well as defining the
    # semantic-error filter, receipt containment check, and witness compiler.
    result.update({name: sha(ROOT / name) for name in (
        "scripts/check-memory-transfer-host-ownership-artifact-negatives.py",
        "scripts/check-switch-artifact-negatives.py", "scripts/check-switch-artifact.py",
        "scripts/check-switch-circuit.py", "scripts/check-switch-model.py", "scripts/switch_oracle.py")})
    return dict(sorted(result.items()))


def verify_positive(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != positive.sources() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed ownership artifact receipt matching current sources/tools")
    entries = report.get("configurations", [])
    if [tuple(row["configuration"]) for row in entries] != positive.checks.MATRIX:
        raise ValueError("Receipt must certify the complete ordered ownership matrix")
    required = ("encoded_trace_checked", "encoded_final_state_checked", "state_preserving_reset_trace_checked",
                "reset_final_state_checked", "reserved_phase_recovery_trace_checked")
    hashes = report.get("artifact_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("Missing positive artifact identities")
    for name, digest in hashes.items():
        if sha(common.contained(receipt.parent, name)) != digest:
            raise ValueError("Positive artifact changed: " + name)
    for entry in entries:
        config = tuple(entry["configuration"])
        label = "host-" + "-".join(map(str, config))
        if any(entry.get(key) is not True for key in required):
            raise ValueError("Missing ownership trace/reset/recovery/final-state certificate: " + label)
        for filename in ("transfer-host.mlir", "transfer-host.sv", "interface.json", "before-pmuxtree.json",
                         "import.json", "Design.lean", "Graphs.lean", "Proof.lean", "HostTrace.lean",
                         "Audit.lean", "Audit.log", "MemoryTransferSupport.lean", "MemoryTransferSupport.olean"):
            if f"{label}/{filename}" not in hashes:
                raise ValueError("Positive receipt omits " + label + "/" + filename)
        descriptor = json.loads((receipt.parent / label / "interface.json").read_text())
        positive.checks.host.validate_descriptor(descriptor, *config)
        if entry.get("typed_registers") != len(descriptor["registers"]) or \
                entry.get("typed_outputs") != len(descriptor["outputs"]) or \
                entry.get("endpoints") != len(descriptor["registers"]) + len(descriptor["outputs"]):
            raise ValueError("Incomplete typed endpoint certificate: " + label)
    return receipt.parent / ("host-" + "-".join(map(str, CONFIG)))


def witness(directory, descriptor, name):
    reader = readback.importer(descriptor)
    source = reader.read_hints(directory / "transfer-host.mlir")
    actual = reader.read_rtl(directory / "import.json")
    inputs = dict.fromkeys(positive.checks.host.reference.INPUT_ROLES, 0)
    control = [0, 0, 0, 0, 0, 0, 0]
    source_memory = [10, 20, 30, 40, 55, 0]
    destination_memory = [165, 85, 3, 7, 60, 0]
    roles, regs = descriptor["roles"], descriptor["register_roles"]

    def output(graph, role, namespace):
        return common.graph_value(graph, graph.outputs[roles[role]], namespace)

    def pin(role):
        index = next(k for k, port in enumerate(descriptor["inputs"]) if port["name"] == roles[role])
        return f"witnessInputs input_{index}"

    if name == "clear-word-on-reset":
        inputs["reset"] = 1
        source_memory[-1] = destination_memory[-1] = 1
        kind, endpoint = "next", regs["destination_words"][0]
        expected, corrupted = 165, 0
        condition = (f"({pin('reset')}) = 1 ∧ "
                     f"({output(source, 'source_resp_valid', 'Source')}) = 0 ∧ "
                     f"({output(actual, 'destination_resp_valid', 'RTL')}) = 0")
        description = "Reset is asserted with both pending responses; stored destination word165 must be preserved"
    elif name == "host-write-while-busy":
        control = [1, 0, 0, 1, 0, 0, 0]
        inputs.update(source_req_valid=1, source_req_write=1, source_req_address=0, source_req_data=231)
        kind, endpoint = "next", regs["source_words"][0]
        expected, corrupted = 10, 231
        condition = (f"({pin('source_req_valid')}) = 1 ∧ ({pin('source_req_write')}) = 1 ∧ "
                     f"({output(source, 'busy', 'Source')}) = 1 ∧ ({output(actual, 'busy', 'RTL')}) = 1 ∧ "
                     f"({output(source, 'source_req_ready', 'Source')}) = 0 ∧ "
                     f"({output(actual, 'source_req_ready', 'RTL')}) = 0")
        description = "A valid busy transfer rejects the offered host write; source word10 must remain10, not231"
    elif name == "invert-active-readback":
        inputs["destination_resp_ready"] = 1
        destination_memory[0] = 60
        destination_memory[-1] = 1
        kind, endpoint = "output", roles["destination_resp_data"]
        expected, corrupted = 60, 195
        condition = (f"({pin('destination_resp_ready')}) = 1 ∧ "
                     f"({output(source, 'destination_resp_valid', 'Source')}) = 1 ∧ "
                     f"({output(actual, 'destination_resp_valid', 'RTL')}) = 1")
        description = "Both designs deliver an active host read response with ready asserted; snapshot60 is corrupted to195"
    else:
        raise ValueError("Unknown mutation " + name)
    bank = control + source_memory + destination_memory
    values = [inputs[role] for role in positive.checks.host.reference.INPUT_ROLES]

    def expression(items, descriptor_name):
        result = "0"
        for k, value in reversed(list(enumerate(items))):
            if value:
                result = f"if ({descriptor_name}.position p).val = {k} then {value} else ({result})"
        return result

    source_name = (source.outputs if kind == "output" else source.next)[endpoint]
    actual_name = (actual.outputs if kind == "output" else actual.next)[endpoint]
    lhs, rhs = common.graph_value(source, source_name, "Source"), common.graph_value(actual, actual_name, "RTL")
    text = f"""import Lean
import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact.MutationControl
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def witnessInputs : Values Input := fun {{w}} p => BitVec.ofNat w ({expression(values, 'inputs')})
def witnessState : Values Register := fun {{w}} p => BitVec.ofNat w ({expression(bank, 'registers')})
theorem active_condition : {condition} := by decide +kernel
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
      unless bad.isEmpty do throwError "Unapproved witness axioms in {{name}}: {{bad}}"
  if count == 0 then throwError "Empty host mismatch audit"
  logInfo m!"Host mutation audit: {{count}} declarations, standard axioms only."
"""
    return text, {"inputs": inputs, "registers": bank, "source_endpoint_value": expected,
                  "mutant_endpoint_value": corrupted, "active_condition": description,
                  "endpoint_kind": kind, "endpoint": endpoint}


def control(run, tools, out, baseline, name):
    directory = out / name
    directory.mkdir()
    for filename in ("transfer-host.mlir", "transfer-host.sv", "interface.json"):
        shutil.copyfile(baseline / filename, directory / filename)
    descriptor = json.loads((directory / "interface.json").read_text())
    positive.checks.host.validate_descriptor(descriptor, *CONFIG)
    rtl = directory / "transfer-host.sv"
    before = sha(rtl)
    changed = dict(positive.checks.host.mutations(rtl.read_text(), descriptor))[name]
    if name == "host-write-while-busy":
        # The reused simulation mutation uses logical AND. All three guard
        # signals are one bit, so bitwise AND has exactly the same binary
        # behavior and stays within the restricted importer's cell language.
        guard = " && ".join(descriptor["roles"][role] for role in
                            ("busy", "source_req_valid", "source_req_write"))
        if changed.count(guard) != 1:
            raise ValueError("Expected exactly the newly inserted busy host-write guard")
        changed = changed.replace(guard, guard.replace(" && ", " & "))
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
        errors = common.semantic_errors(directory / (stage+".log"), stage)
        run.records[-1]["expected_failure"] = True
    else:
        raise AssertionError("Corrupted host RTL received a certificate")
    text, details = witness(directory, descriptor, name)
    common.check_witness(run, directory, text)
    if "standard axioms only" not in (directory / "MutationWitness.log").read_text():
        raise AssertionError("Missing host witness axiom audit")
    return {"control": name, "stage": stage, "rejection": errors, "witness": details,
            "kernel_checked_counterexample": True, "rtl_before_sha256": before, "rtl_after_sha256": sha(rtl)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer-host-ownership-artifact-negatives", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "controls": [],
        "boundary": "Actual RTL reset-preservation, busy-isolation and active-readback faults must fail local "
                    "semantic equalities, followed by kernel-checked exact mismatches with active conditions. "
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
        for name in CONTROLS:
            report["controls"].append(control(run, tools, out, baseline, name))
        if sources() != report["source_sha256"] or positive.rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during ownership negative validation")
        verify_positive(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_receipt"]["sha256"]:
            raise RuntimeError("Positive receipt changed during validation")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic()-started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
