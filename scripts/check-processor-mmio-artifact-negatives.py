#!/usr/bin/env python3
"""Reject actual MMIO RTL faults with local proof failures and active kernel witnesses."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import time

import typed_circuit_readback as readback
from typed_artifact_runner import compile_modules
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("mmio_artifact_positive", ROOT / "scripts/check-processor-mmio-artifact.py")
positive = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(positive)
CONTROLS = ("write-gpio-input", "overwrite-full-rx", "clear-new-framing-error", "read-post-tick-timer", "retain-gpio-on-reset")
FLAGS = ("arbitrary_raw_state_trace_checked", "projected_final_state_checked",
         "initialized_trace_checked", "initialized_final_state_checked",
         "reset_clears_registers_checked", "reset_masks_outputs_checked",
         "actual_response_checked", "admitted_actual_event_replay_checked",
         "reset_event_replay_checked", "reset_event_checked")


def sources():
    return dict(sorted({**positive.sources(),
        "scripts/check-processor-mmio-artifact-negatives.py": sha(Path(__file__))}.items()))


def contained(base, name):
    if type(name) is not str or not name or PurePosixPath(name).is_absolute() or \
            PurePosixPath(name).as_posix() != name or ".." in PurePosixPath(name).parts:
        raise ValueError("Artifact must have a canonical relative path")
    path = base / name
    if path.is_symlink() or not path.resolve().is_relative_to(base.resolve()):
        raise ValueError("Artifact escapes its receipt bundle")
    return path


def verify_positive(receipt, manifest, tools_hash):
    report = json.loads(receipt.read_text())
    if type(report.get("schema")) is not int or report["schema"] != 1 or \
            report.get("status") != "passed" or report.get("source_sha256") != positive.sources() or \
            report.get("tool_sha256") != tools_hash or report.get("tool_manifest") != manifest:
        raise ValueError("Require a passed source/tool-current positive MMIO artifact receipt")
    rows = report.get("configurations")
    if type(rows) is not list or len(rows) != 1 or rows[0].get("configuration") != [32]:
        raise ValueError("Require exactly the complete ordered MMIO configuration [32]")
    row = rows[0]
    if any(row.get(flag) is not True for flag in FLAGS) or any(
            type(row.get(key)) is not int or row[key] != expected
            for key, expected in (("typed_registers", 8), ("typed_outputs", 7), ("endpoints", 15))):
        raise ValueError("Missing complete MMIO endpoint/trace/reset/event evidence")
    commands = report.get("commands")
    if type(commands) is not list or not commands or any(
            type(command) is not dict or command.get("exit_code") != 0 or command.get("error") or
            command.get("expected_failure") for command in commands):
        raise ValueError("Positive certificate contains missing or failed command evidence")
    hashes = report.get("artifact_sha256")
    if type(hashes) is not dict or not hashes:
        raise ValueError("Missing positive artifact identities")
    inventory = {str(path.relative_to(receipt.parent)) for path in receipt.parent.rglob("*")
                 if path.is_file() and path.resolve() != receipt.resolve()}
    if inventory != set(hashes):
        raise ValueError("Positive artifact inventory differs from its receipt")
    for name, digest in hashes.items():
        if type(digest) is not str or not re.fullmatch(r"[0-9a-f]{64}", digest) or \
                sha(contained(receipt.parent, name)) != digest:
            raise ValueError("Positive artifact changed: " + name)
    required = ["mmio.mlir", "mmio.sv", "interface.json", "before-pmuxtree.json", "import.json", "import.ys"]
    for module in ("Design", "Graphs", "LocalProofs", "Links", "Proof", "MmioTrace", "Audit"):
        required.extend(module + suffix for suffix in (".lean", ".olean", ".log"))
    units = row.get("local_proof_units")
    if type(units) is not int or units < 1:
        raise ValueError("Missing positive local proof units")
    for number in range(units):
        required.extend(f"LocalProofs{number:03d}" + suffix for suffix in (".lean", ".olean", ".log"))
    for name in required:
        if "mmio/" + name not in hashes:
            raise ValueError("Positive receipt omits required evidence: " + name)
    if "standard axioms only" not in (receipt.parent / "mmio/Audit.log").read_text():
        raise ValueError("Positive certificate omits its standard-only axiom audit")
    positive.checks.validate_descriptor(json.loads((receipt.parent / "mmio/interface.json").read_text()))
    return receipt.parent / "mmio"


def mutation(text, descriptor, name):
    p, r = descriptor["roles"], descriptor["register_roles"]
    active = f"(~{p['reset']}) & {p['request_valid']}"
    if name == "write-gpio-input":
        endpoint, kind = r["gpio"], "next"
        guard = f"{active} & ({p['device']} == 2'd0) & {p['write']} & ({p['word']} == 6'd0)"
        replace = lambda old: f"({guard}) ? {p['data']} : ({old})"
    elif name == "overwrite-full-rx":
        endpoint, kind = r["rx_data"], "next"
        guard = f"(~{p['reset']}) & {p['rx_valid']} & {r['rx_valid']}"
        replace = lambda old: f"({guard}) ? {p['rx_data']} : ({old})"
    elif name == "clear-new-framing-error":
        endpoint, kind = r["framing"], "next"
        guard = f"{active} & ({p['device']} == 2'd2) & {p['write']} & ({p['word']} == 6'd3) & {p['data']}[3]"
        replace = lambda old: f"({guard}) ? 1'b0 : ({old})"
    elif name == "read-post-tick-timer":
        endpoint, kind = p["response_data"], "output"
        guard = f"{active} & ({p['device']} == 2'd1) & (~{p['write']}) & ({p['word']} == 6'd0)"
        replace = lambda old: f"({guard}) ? ({r['timer']} + 32'd1) : ({old})"
    elif name == "retain-gpio-on-reset":
        endpoint, kind = r["gpio"], "next"
        replace = lambda old: f"{p['reset']} ? {r['gpio']} : ({old})"
    else:
        raise ValueError("Unknown MMIO mutation")
    assignment = (r"(\bassign\s+" + re.escape(endpoint) + r"\s*=\s*)([^;]+);") if kind == "output" else \
                 (r"(\b" + re.escape(endpoint) + r"\s*<=\s*)([^;]+);")
    changed, count = re.subn(assignment, lambda match: match[1] + replace(match[2].strip()) + ";", text)
    if count != 1 or changed == text:
        raise ValueError("Mutation did not identify exactly one RTL assignment")
    return changed, endpoint, kind


def witness_case(name):
    reference = positive.checks.reference
    pins = dict.fromkeys(reference.INPUT_ROLES, 0)
    pins.update(request_valid=1, gpio_input=0xabcdef01)
    bank = dict(gpio=0x12345678, timer=0xffffffff, tx_active=1, tx_data=0x5a,
                rx_valid=1, rx_data=0x35, overrun=0, framing=1)
    if name == "write-gpio-input":
        pins.update(device=0, write=1, word=0, data=0xfeedface)
        expected, corrupted, valid, code = 0x12345678, 0xfeedface, 1, 3
        description = "Accepted GPIO INPUT write faults with direction code3 and must preserve GPIO OUT"
    elif name == "overwrite-full-rx":
        pins.update(device=2, word=0, rx_valid=1, rx_data=0xa6)
        bank.update(framing=0)
        expected, corrupted, valid, code = 0x35, 0xa6, 1, 0
        description = "UART STATUS read leaves RX full; a concurrent arrival sets overrun and preserves the held byte"
    elif name == "clear-new-framing-error":
        pins.update(device=2, write=1, word=3, data=8, framing_error=1)
        expected, corrupted, valid, code = 1, 0, 1, 1
        description = "Accepted UART CLEAR writes framing W1C while a new framing error arrives; the new error wins"
    elif name == "read-post-tick-timer":
        pins.update(device=1, word=0)
        expected, corrupted, valid, code = 0xffffffff, 0, 1, 0
        description = "Accepted TIMER read returns the pre-edge all-ones value even though the next timer wraps to zero"
    elif name == "retain-gpio-on-reset":
        pins.update(reset=1, device=0, write=1, word=1, data=0xfeedface)
        expected, corrupted, valid, code = 0, 0x12345678, 0, 0
        description = "Reset suppresses a concurrent GPIO OUT write and clears previously nonzero GPIO storage"
    else:
        raise ValueError("Unknown MMIO witness")
    return pins, bank, expected, corrupted, valid, code, description


def graph_value(graph, name, namespace):
    node = graph.nodes[name]
    if node.op in ("input", "reg", "lit"):
        return graph.expression(node, None).replace("i (", "witnessInputs (").replace("s (", "witnessState (")
    return f"{namespace}.{name} witnessInputs witnessState"


def witness(directory, descriptor, name, endpoint, kind):
    reader = readback.importer(descriptor)
    source = reader.read_hints(directory / "mmio.mlir")
    actual = reader.read_rtl(directory / "import.json")
    pins, bank, expected, corrupted, valid, code, description = witness_case(name)
    p, r = descriptor["roles"], descriptor["register_roles"]
    pin_values = {p[role]: value for role, value in pins.items()}
    bank_values = {r[role]: value for role, value in bank.items()}
    ins = [pin_values[port["name"]] for port in descriptor["inputs"]]
    state = [bank_values[port["name"]] for port in descriptor["registers"]]
    reference = positive.checks.reference
    raw = reference.row(**pins)
    reference.restore(state)
    reference_outputs = reference.observe(state, raw)
    reference_next = reference.step(state, raw)
    endpoint_index = next(k for k, port in enumerate(descriptor["outputs" if kind == "output" else "registers"])
                          if port["name"] == endpoint)
    if (reference_outputs if kind == "output" else reference_next)[endpoint_index] != expected or \
            reference_outputs[1:3] != [valid, code] or expected == corrupted:
        raise AssertionError("Inactive or incorrect independently checked MMIO witness")
    mutant_outputs = reference_outputs.copy()
    if kind == "output":
        mutant_outputs[endpoint_index] = corrupted

    def encoded(items, family):
        result = "0"
        for index, value in reversed(list(enumerate(items))):
            if value:
                result = f"if ({family}.position _p).val = {index} then {value} else ({result})"
        return result

    lhs = graph_value(source, (source.outputs if kind == "output" else source.next)[endpoint], "Source")
    rhs = graph_value(actual, (actual.outputs if kind == "output" else actual.next)[endpoint], "RTL")
    # Every raw input/register value is a kernel-checked condition, as are all
    # seven outputs on both graphs (especially ready, valid and response code).
    conditions = [f"witnessInputs input_{k} = {value}" for k, value in enumerate(ins)]
    conditions += [f"witnessState register_{k} = {value}" for k, value in enumerate(state)]
    for graph, namespace, values in ((source, "Source", reference_outputs), (actual, "RTL", mutant_outputs)):
        for port, value in zip(descriptor["outputs"], values, strict=True):
            conditions.append(f"({graph_value(graph, graph.outputs[port['name']], namespace)}) = {value}")
    text = f"""import Lean
import Graphs
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact.MutationControl
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def witnessInputs : Values Input := fun {{w}} _p => BitVec.ofNat w ({encoded(ins, 'inputs')})
def witnessState : Values Register := fun {{w}} _p => BitVec.ofNat w ({encoded(state, 'registers')})
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
      unless bad.isEmpty do throwError "Unapproved MMIO witness axioms in {{name}}: {{bad}}"
  if count < 6 then throwError "Incomplete MMIO mutation audit"
  logInfo m!"MMIO mutation audit: {{count}} declarations, standard axioms only."
"""
    return text, {"inputs": ins, "registers": state, "input_roles": pins, "register_roles": bank,
        "source_outputs": reference_outputs, "mutant_outputs": mutant_outputs,
        "source_next_state_oracle": reference_next, "source_endpoint_value": expected,
        "mutant_endpoint_value": corrupted, "active_condition": description,
        "kernel_checked_input_register_conditions": len(ins)+len(state),
        "kernel_checked_output_conditions": 2*len(reference_outputs),
        "independent_oracle_checked": True}


def control(run, tools, out, baseline, name):
    directory = out / name
    directory.mkdir()
    for filename in ("mmio.mlir", "mmio.sv", "interface.json"):
        shutil.copyfile(baseline / filename, directory / filename)
    descriptor = positive.checks.validate_descriptor(json.loads((directory / "interface.json").read_text()))
    rtl = directory / "mmio.sv"
    before = sha(rtl)
    changed, endpoint, kind = mutation(rtl.read_text(), descriptor, name)
    rtl.write_text(changed)
    try:
        positive.certify(run, tools, directory, descriptor, rtl)
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
        if run.records[-1].get("exit_code") != 1 or run.records[-1].get("error"):
            raise RuntimeError("Missing ordinary Lean semantic-failure exit evidence")
        run.records[-1]["expected_failure"] = True
    else:
        raise AssertionError("Corrupted MMIO RTL received an artifact certificate")
    text, details = witness(directory, descriptor, name, endpoint, kind)
    (directory / "MutationWitness.lean").write_text(text)
    compile_modules(run, directory, ["MutationWitness"])
    audit = re.search(r"MMIO mutation audit: (\d+) declarations, standard axioms only\.",
                      (directory / "MutationWitness.log").read_text())
    if not audit:
        raise AssertionError("Missing standard-only MMIO mutation witness audit")
    return {"control": name, "stage": stage, "rejection": errors, "endpoint": endpoint,
        "endpoint_kind": kind, "witness": details, "kernel_checked_counterexample": True,
        "audited_witness_declarations": int(audit[1]), "rtl_before_sha256": before, "rtl_after_sha256": sha(rtl)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/processor-mmio-artifact-negatives", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "controls": [],
        "boundary": "Five single-assignment RTL faults must fail local semantic equalities and yield standard-only "
            "kernel witnesses for exact graph endpoints. Every input/register bit value and all outputs are checked "
            "under explicit active request/reset/frontend conditions. Parser failures, timeouts and resource limits "
            "do not count. No serial-wire, CPU retirement, synthesis-preservation or physical timing claim."}
    run, started = positive.rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = positive.rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, positive.rr.tool_hashes(paths)
        receipt = args.positive_report.resolve()
        baseline = verify_positive(receipt, manifest, report["tool_sha256"])
        report["positive_report"] = {"path": str(receipt), "sha256": sha(receipt)}
        shutil.copyfile(receipt, out / "positive-report.json")
        for name in CONTROLS:
            report["controls"].append(control(run, tools, out, baseline, name))
        if sources() != report["source_sha256"] or positive.rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Negative control sources/tools changed")
        verify_positive(receipt, manifest, report["tool_sha256"])
        if sha(receipt) != report["positive_report"]["sha256"] or \
                sha(out / "positive-report.json") != report["positive_report"]["sha256"]:
            raise RuntimeError("Positive receipt changed")
        if [row["control"] for row in report["controls"]] != list(CONTROLS):
            raise AssertionError("Incomplete MMIO semantic controls")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic()-started, 3)
        report["artifact_sha256"] = {str(path.relative_to(out)): sha(path) for path in sorted(out.rglob("*")) if path.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
