#!/usr/bin/env python3
"""Reject byte RAM RTL faults with semantic proof failures and active kernel witnesses."""
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
SPEC = importlib.util.spec_from_file_location("byte_artifact_positive", ROOT / "scripts/check-memory-byte-adapter-artifact.py")
positive = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(positive)
CONTROLS = ("clear-word-on-reset", "store-while-stalled", "zero-extend-signed-byte", "write-on-misalignment")
FLAGS = ("arbitrary_raw_state_trace_checked", "projected_final_state_checked",
         "state_preserving_reset_trace_checked", "reset_final_state_checked",
         "reset_preserves_memory_q_metadata_checked", "reset_clears_pending_checked",
         "reset_masks_outputs_checked", "reset_establishes_snapshot_checked",
         "actual_completion_event_replay_checked", "reset_event_replay_checked", "reset_emits_no_completion_checked")


def sources():
    return {**positive.sources(), "scripts/check-memory-byte-adapter-artifact-negatives.py": sha(Path(__file__))}


def contained(base, name):
    if type(name) is not str:
        raise ValueError("Artifact path must be a string")
    path = (base / name).resolve()
    if not path.is_relative_to(base.resolve()):
        raise ValueError("Artifact escapes its receipt bundle")
    return path


def verify_positive(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != positive.sources() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed source/tool-current positive artifact receipt")
    rows = report.get("configurations", [])
    if [r.get("configuration") for r in rows] != [[a, 32] for a in positive.checks.MATRIX]:
        raise ValueError("Require the full ordered byte adapter matrix exactly once")
    for a, row in zip(positive.checks.MATRIX, rows):
        if any(row.get(flag) is not True for flag in FLAGS) or row.get("typed_registers") != 2**a+8 or \
                row.get("typed_outputs") != 4 or row.get("endpoints") != 2**a+12:
            raise ValueError("Missing complete byte adapter endpoint/trace/reset evidence")
    hashes = report.get("artifact_sha256")
    if type(hashes) is not dict or not hashes:
        raise ValueError("Missing positive artifact identities")
    for name, digest in hashes.items():
        if sha(contained(receipt.parent, name)) != digest:
            raise ValueError("Positive artifact changed: " + name)
    for a in positive.checks.MATRIX:
        for name in ("byte-adapter.mlir", "byte-adapter.sv", "interface.json", "before-pmuxtree.json",
                     "import.json", "Design.lean", "Graphs.lean", "Proof.lean", "ByteTrace.lean", "Audit.lean", "Audit.log"):
            if f"byte-{a}/{name}" not in hashes:
                raise ValueError("Positive receipt omits required evidence: " + name)
    return receipt.parent / "byte-1"


def mutation(text, descriptor, name):
    p, r = descriptor["roles"], descriptor["register_roles"]
    endpoint = p["response_data"] if name == "zero-extend-signed-byte" else r["words"][0]
    assignment = r"(\bassign\s+" + re.escape(endpoint) + r"\s*=\s*)([^;]+);" if name == "zero-extend-signed-byte" else \
                 r"(\b" + re.escape(endpoint) + r"\s*<=\s*)([^;]+);"
    if name == "clear-word-on-reset":
        replace = lambda old: f"{p['reset']} ? 32'd0 : ({old})"
    elif name == "store-while-stalled":
        guard = f"(~{p['reset']}) & {r['pending']} & (~{p['response_ready']}) & {r['write']} & " + \
                f"({r['size']} == 2'd0) & ({r['offset']} == 2'd1) & ({r['address']} == 1'd0)"
        # A deliberately early byte store on a blocked acknowledgement.
        replace = lambda old: f"({guard}) ? {{{r['q']}[31:16], {r['data']}[7:0], {r['q']}[7:0]}} : ({old})"
    elif name == "zero-extend-signed-byte":
        guard = f"{r['signed']} & ({r['size']} == 2'd0)"
        replace = lambda old: f"({guard}) ? (({old}) & 32'h000000ff) : ({old})"
    elif name == "write-on-misalignment":
        guard = f"(~{p['reset']}) & {r['pending']} & {p['response_ready']} & {r['write']} & " + \
                f"({r['size']} == 2'd1) & ({r['offset']} == 2'd3) & ({r['address']} == 1'd0)"
        replace = lambda old: f"({guard}) ? 32'hfeedface : ({old})"
    else:
        raise ValueError("Unknown mutation")
    changed, count = re.subn(assignment, lambda m: m[1] + replace(m[2].strip()) + ";", text)
    if count != 1 or changed == text:
        raise ValueError("Mutation did not identify exactly one RTL assignment")
    return changed, endpoint, "output" if name == "zero-extend-signed-byte" else "next"


def graph_value(graph, name, namespace):
    node = graph.nodes[name]
    if node.op in ("input", "reg", "lit"):
        return graph.expression(node, None).replace("i (", "witnessInputs (").replace("s (", "witnessState (")
    return f"{namespace}.{name} witnessInputs witnessState"


def witness(directory, descriptor, name, endpoint, kind):
    reader = readback.importer(descriptor)
    source = reader.read_hints(directory / "byte-adapter.mlir")
    actual = reader.read_rtl(directory / "import.json")
    pins = dict.fromkeys(descriptor["roles"], 0)
    p, r = descriptor["roles"], descriptor["register_roles"]
    values = {r["words"][0]: 0x80ff7f01, r["words"][1]: 0x12345678, r["q"]: 0x80ff7f01,
              r["write"]: 1, r["signed"]: 0, r["size"]: 0, r["address"]: 0,
              r["offset"]: 1, r["data"]: 0xa5, r["pending"]: 1}
    if name == "clear-word-on-reset":
        pins["reset"] = 1
        expected, corrupted, code, valid = 0x80ff7f01, 0, 0, 0
        description = "Reset masks the pending store and preserves its old RAM word"
    elif name == "store-while-stalled":
        expected, corrupted, code, valid = 0x80ff7f01, 0x80ffa501, 1, 1
        description = "A valid stored acknowledgement is blocked; the pending byte store must not commit"
    elif name == "zero-extend-signed-byte":
        pins["response_ready"] = 1
        values.update({r["write"]: 0, r["signed"]: 1, r["offset"]: 3})
        expected, corrupted, code, valid = 0xffffff80, 0x80, 0, 1
        description = "An accepted signed byte read at lane3 must deliver negative128 sign-extended to32bits"
    else:
        pins["response_ready"] = 1
        values.update({r["size"]: 1, r["offset"]: 3})
        expected, corrupted, code, valid = 0x80ff7f01, 0xfeedface, 3, 1
        description = "An accepted misaligned halfword-store fault must preserve the RAM word"

    def encoded(items, family):
        result = "0"
        for k, value in reversed(list(enumerate(items))):
            if value:
                result = f"if ({family}.position _p).val = {k} then {value} else ({result})"
        return result

    def output(graph, namespace, role):
        return graph_value(graph, graph.outputs[p[role]], namespace)

    pin_values = {p[role]: value for role, value in pins.items()}
    ins = [pin_values[port["name"]] for port in descriptor["inputs"]]
    bank = [values[port["name"]] for port in descriptor["registers"]]
    lhs = graph_value(source, (source.outputs if kind == "output" else source.next)[endpoint], "Source")
    rhs = graph_value(actual, (actual.outputs if kind == "output" else actual.next)[endpoint], "RTL")
    conditions = [f"({output(graph, ns, role)}) = {value}" for graph, ns in ((source, "Source"), (actual, "RTL"))
                  for role, value in (("response_valid", valid), ("response_code", code))]
    for role in ("reset", "response_ready"):
        index = next(k for k, port in enumerate(descriptor["inputs"]) if port["name"] == p[role])
        conditions.append(f"witnessInputs input_{index} = {pins[role]}")
    for role in ("pending", "write", "signed", "size", "address", "offset"):
        index = next(k for k, port in enumerate(descriptor["registers"]) if port["name"] == r[role])
        conditions.append(f"witnessState register_{index} = {values[r[role]]}")
    text = f"""import Lean
import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact.MutationControl
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def witnessInputs : Values Input := fun {{w}} _p => BitVec.ofNat w ({encoded(ins, 'inputs')})
def witnessState : Values Register := fun {{w}} _p => BitVec.ofNat w ({encoded(bank, 'registers')})
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
      unless bad.isEmpty do throwError "Unapproved witness axioms in {{name}}: {{bad}}"
  if count == 0 then throwError "Empty byte mutation audit"
  logInfo m!"Byte mutation audit: {{count}} declarations, standard axioms only."
"""
    return text, {"inputs": ins, "registers": bank, "source_endpoint_value": expected,
                  "mutant_endpoint_value": corrupted, "active_condition": description}


def control(run, tools, out, baseline, name):
    directory = out / name
    directory.mkdir()
    for filename in ("byte-adapter.mlir", "byte-adapter.sv", "interface.json"):
        shutil.copyfile(baseline / filename, directory / filename)
    descriptor = json.loads((directory / "interface.json").read_text())
    positive.checks.validate_descriptor(descriptor, 1)
    rtl = directory / "byte-adapter.sv"
    before = sha(rtl)
    changed, endpoint, kind = mutation(rtl.read_text(), descriptor, name)
    rtl.write_text(changed)
    try:
        positive.certify(run, tools, directory, descriptor, 1, rtl)
    except RuntimeError as error:
        match = re.match(r"(LocalProofs(?:[0-9]+)?) certificate failed:", str(error))
        if not match:
            raise
        stage = match[1]
        errors = re.findall(r"^.*?\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$",
                            (directory / (stage + ".log")).read_text(), re.M)
        allowed = ("`grind` failed", "unsolved goals", "Tactic `decide` proved that the proposition")
        if not errors or any(not any(marker in error for marker in allowed) for error in errors):
            raise RuntimeError("Failure was not an expected semantic theorem rejection")
        run.records[-1]["expected_failure"] = True
    else:
        raise AssertionError("Corrupted byte RAM received an artifact certificate")
    text, details = witness(directory, descriptor, name, endpoint, kind)
    (directory / "MutationWitness.lean").write_text(text)
    compile_modules(run, directory, ["MutationWitness"])
    if "standard axioms only" not in (directory / "MutationWitness.log").read_text():
        raise AssertionError("Missing standard-only mutation witness audit")
    return {"control": name, "stage": stage, "rejection": errors, "endpoint": endpoint, "endpoint_kind": kind,
            "witness": details, "kernel_checked_counterexample": True,
            "rtl_before_sha256": before, "rtl_after_sha256": sha(rtl)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-byte-adapter-artifact-negatives", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "controls": [],
        "boundary": "Actual RTL faults must fail local semantic equalities and yield audited kernel witnesses "
            "under active handshake/fault conditions. Parser errors, timeouts and resource limits do not count."}
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
        report["positive_report"] = {"path": str(receipt), "sha256": sha(receipt)}
        shutil.copyfile(receipt, out / "positive-report.json")
        for name in CONTROLS:
            report["controls"].append(control(run, tools, out, baseline, name))
        if sources() != report["source_sha256"] or positive.rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Negative control sources/tools changed")
        verify_positive(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_report"]["sha256"] or \
                sha(out / "positive-report.json") != report["positive_report"]["sha256"]:
            raise RuntimeError("Positive receipt changed")
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
