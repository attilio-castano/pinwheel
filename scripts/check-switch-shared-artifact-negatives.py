#!/usr/bin/env python3
"""Reject semantic corruptions of a fully certified shared-selector artifact.

Each control must fail a local Lean equality and independently prove an exact
source/imported-RTL mismatch on concrete active state. Parser failures and
timeouts are errors, not successful negative evidence.
"""
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
CONFIG = (2, 3, 2, 8)


def helper(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


positive = helper("shared_artifact_positive", "check-switch-shared-artifact.py")
common = helper("shared_artifact_negative_utilities", "check-switch-artifact-negatives.py")


def sources():
    result = positive.sources()
    for name in ("scripts/check-switch-shared-artifact-negatives.py", "scripts/check-switch-artifact-negatives.py",
                 "scripts/check-switch-artifact.py"):
        result[name] = sha(ROOT / name)
    return dict(sorted(result.items()))


def verify_positive(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != positive.sources() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed candidate artifact receipt matching current sources/tools")
    entry = next((c for c in report.get("configurations", []) if tuple(c["configuration"]) == CONFIG), None)
    if entry is None or entry.get("initialized_trace_checked") is not True:
        raise ValueError("Receipt must certify the 2x3/d2/w8 candidate and initialized trace")
    hashes = report.get("artifact_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("Positive receipt has no artifact identities")
    for name, digest in hashes.items():
        if sha(common.contained(receipt.parent, name)) != digest:
            raise ValueError("Positive artifact changed: " + name)
    label = "shared-" + "-".join(map(str, CONFIG))
    for filename in ("switch.mlir", "switch.sv", "interface.json", "import.json", "Design.lean",
                     "Proof.lean", "Initialized.lean", "Audit.lean", "Audit.log"):
        if f"{label}/{filename}" not in hashes:
            raise ValueError("Positive receipt omits required evidence: " + filename)
    return receipt.parent / label


def witness(directory, descriptor, kind, endpoint, control):
    reader = readback.importer(descriptor)
    source, actual = reader.read_hints(directory / "switch.mlir"), reader.read_rtl(directory / "import.json")
    state = {p["name"]: 0 for p in descriptor["registers"]}
    roles = descriptor["register_roles"]
    # Both witnesses use legal one-hot cursors and stalled occupied output
    # slots. A FIFO witness therefore holds an actual queued packet in place.
    for cursor in roles["cursor"]:
        state[cursor[0]] = 1
    for valid, data in zip(roles["slot_valid"], roles["slot_payload"], strict=True):
        state[valid], state[data] = 1, 0x55
    if control == "invert-active-payload":
        state[roles["slot_payload"][0]] = 0xA5
    else:
        state[roles["fifo_valid"][0][0]] = 1
        state[roles["fifo_data"][0][0]] = 0x3C  # destination zero, payload 60
    state_expression = "0"
    for k, port in reversed(list(enumerate(descriptor["registers"]))):
        if state[port["name"]]:
            state_expression = f"if (registers.position p).val = {k} then {state[port['name']]} else ({state_expression})"
    left = (source.outputs if kind == "output" else source.next)[endpoint]
    right = (actual.outputs if kind == "output" else actual.next)[endpoint]
    source_value = common.graph_value(source, left, "Source")
    actual_value = common.graph_value(actual, right, "RTL")
    active = ""
    if control == "invert-active-payload":
        valid_name = descriptor["roles"]["out_valid"][0]
        lhs = common.graph_value(source, source.outputs[valid_name], "Source")
        rhs = common.graph_value(actual, actual.outputs[valid_name], "RTL")
        active = f"theorem offered_response : ({lhs}) = 1 ∧ ({rhs}) = 1 := by decide +kernel\n"
        active += f"theorem source_payload : ({source_value}) = 165 := by decide +kernel\n"
    else:
        index = next(k for k, p in enumerate(descriptor["registers"]) if p["name"] == roles["fifo_valid"][0][0])
        active = f"theorem queued_packet : witnessState register_{index} = 1 := by decide +kernel\n"
        active += f"theorem retained_packet : ({source_value}) = 60 := by decide +kernel\n"
    text = f"""import Lean
import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact.MutationControl
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def witnessInputs : Values Input := fun {{w}} _ => BitVec.ofNat w 0
def witnessState : Values Register := fun {{w}} p => BitVec.ofNat w ({state_expression})
{active}
theorem semantic_mutation : ({source_value}) ≠ ({actual_value}) := by decide +kernel
end Pinwheel.TypedArtifact.MutationControl
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.TypedArtifact.MutationControl." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved witness axioms in {{name}}: {{bad}}"
  if count == 0 then throwError "Empty semantic witness audit"
  logInfo m!"Candidate mutation audit: {{count}} declarations, standard axioms only."
"""
    return text, {"all_inputs": 0, "registers": state,
                  "active_condition": "source and mutant both offer output0; source payload is165" if kind == "output" else
                                      "input0 has a queued destination0/payload60 packet retained under output stalls"}


def control(run, tools, out, baseline, name):
    directory = out / name
    directory.mkdir()
    for filename in ("switch.mlir", "switch.sv", "interface.json"):
        shutil.copyfile(baseline / filename, directory / filename)
    descriptor = positive.sw.descriptor(directory / "interface.json", CONFIG)
    before = {p: sha(directory / p) for p in ("switch.mlir", "switch.sv", "interface.json")}
    rtl = directory / "switch.sv"
    if name == "invert-active-payload":
        kind, endpoint = "output", descriptor["roles"]["out_payload"][0]
        pattern = r"(\bassign\s+" + re.escape(endpoint) + r"\s*=\s*)([^;]+);"
        changed, count = re.subn(pattern, lambda m: m[1] + "~(" + m[2].strip() + ");", rtl.read_text())
        if count != 1 or changed == rtl.read_text():
            raise ValueError("Expected exactly one active payload output assignment")
        rtl.write_text(changed)
    else:
        kind, endpoint = "next", descriptor["register_roles"]["fifo_data"][0][0]
        rtl.write_text(common.flip_state_d(rtl.read_text(), endpoint))
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
        raise AssertionError("Corrupted candidate RTL received a certificate")
    text, details = witness(directory, descriptor, kind, endpoint, name)
    common.check_witness(run, directory, text)
    if "standard axioms only" not in (directory / "MutationWitness.log").read_text():
        raise AssertionError("Missing semantic witness standard-axiom audit")
    return {"control": name, "stage": stage, "rejection": errors, "endpoint_kind": kind,
            "endpoint": endpoint, "witness": details, "kernel_checked_counterexample": True,
            "before_sha256": before, "after_sha256": {p: sha(directory / p) for p in before}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/switch-shared-artifact-negatives", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "controls": [],
              "boundary": "Semantic local-equality rejection plus exact kernel-checked active-state mismatch "
                          "witnesses for two corrupted shared-candidate RTL artifacts. Parser errors/timeouts "
                          "do not count as successful controls. This does not prove Verilog/JSON interpretation sound."}
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
        for name in ("invert-active-payload", "invert-queued-data-d"):
            report["controls"].append(control(run, tools, out, baseline, name))
        verify_positive(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_receipt"]["sha256"] or sources() != report["source_sha256"] or \
                positive.rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Sources/tools/positive receipt changed during negative validation")
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
