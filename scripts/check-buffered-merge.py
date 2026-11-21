#!/usr/bin/env python3
"""Fresh-source BufferedMerge RTL/oracle replay and generic synthesis evidence.

Every emitted register and both edge observations are compared before synthesis;
external observations are compared after synthesis. Artifact interpretation and
physical qualification are separate gates, not claims of this finite campaign.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import random
import re
import sys
import time

import buffered_merge_oracle as oracle

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("merge_cad_helpers", ROOT / "scripts/check-round-robin-circuit.py")
rr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rr)
MATRIX = tuple((n, w) for n in (1, 2, 3, 5, 8) for w in (1, 8, 17))
LEAN_ROOTS = ("test/BufferedMergeEmit.lean", "test/BufferedMergeReplay.lean",
              "test/BufferedMergeCircuit.lean", "test/BufferedMergeModel.lean")


def source_hashes():
    pending, paths = [ROOT / name for name in LEAN_ROOTS], set()
    while pending:
        path = pending.pop()
        if path in paths:
            continue
        paths.add(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for module in match[1].split("--", 1)[0].split():
                    if module == "Pinwheel" or module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    paths.update(ROOT / name for name in (
        "lakefile.toml", "lake-manifest.json", "lean-toolchain", "tools/hardware-toolchain.json",
        "scripts/check-buffered-merge.py", "scripts/buffered_merge_oracle.py",
        "scripts/check-round-robin-circuit.py", "scripts/validation_run.py", "scripts/process_group.py",
        "test/test_buffered_merge_oracle.py"))
    return {str(path.relative_to(ROOT)): rr.sha(path) for path in sorted(paths)}


def validate_descriptor(data, inputs, width):
    oracle.dimensions(inputs, width)
    for key, value in {"schema": 1, "input_count": inputs, "output_count": 1,
                       "payload_width": width, "cursor_encoding": "one_hot",
                       "reset_synchronous": True}.items():
        if not oracle.same_json(data.get(key), value):
            raise ValueError(f"Descriptor {key} mismatch")
    for key in ("module", "clock"):
        if type(data.get(key)) is not str or not rr.IDENTIFIER.fullmatch(data[key]):
            raise ValueError(f"Invalid descriptor {key}")
    all_names = []
    for group in ("inputs", "outputs", "registers"):
        if type(data.get(group)) is not list:
            raise ValueError(f"Missing descriptor {group}")
        for port in data[group]:
            if type(port) is not dict or type(port.get("name")) is not str or \
                    not rr.IDENTIFIER.fullmatch(port["name"]) or type(port.get("width")) is not int or port["width"] <= 0:
                raise ValueError(f"Invalid {group} descriptor")
            all_names.append(port["name"])
            if group == "registers":
                if port.get("reference") != port["name"] or any(
                        type(port.get(k)) is not int or not 0 <= port[k] < 1 << port["width"] for k in ("initial", "reset")):
                    raise ValueError("Invalid register reference/reset metadata")
    if len(set(all_names)) != len(all_names) or data["clock"] in all_names:
        raise ValueError("Duplicated typed signal names")
    roles, regs = data.get("roles"), data.get("register_roles")
    if type(roles) is not dict or set(roles) != {"reset", "out_ready", "in_valid", "in_payload", "in_ready", "out_valid", "out_payload"}:
        raise ValueError("Incomplete port roles")
    if type(regs) is not dict or set(regs) != {"slot_valid", "slot_payload", "cursor"}:
        raise ValueError("Incomplete register roles")
    for names in (roles["in_valid"], roles["in_payload"], roles["in_ready"], regs["cursor"]):
        if type(names) is not list or len(names) != inputs or any(type(x) is not str for x in names):
            raise ValueError("Incorrect indexed role cardinality")
    expected = {
        "inputs": list(zip([roles["reset"], roles["out_ready"]] + roles["in_valid"] + roles["in_payload"],
                           [1, 1] + [1] * inputs + [width] * inputs, strict=True)),
        "outputs": list(zip(roles["in_ready"] + [roles["out_valid"], roles["out_payload"]],
                            [1] * inputs + [1, width], strict=True)),
        "registers": list(zip([regs["slot_valid"], regs["slot_payload"]] + regs["cursor"],
                              [1, width] + [1] * inputs, strict=True))}
    for group, entries in expected.items():
        if [(p["name"], p["width"]) for p in data[group]] != entries:
            raise ValueError(f"Typed {group} enumeration/role mismatch")
    initial = [0, 0, 1] + [0] * (inputs - 1)
    if [r["initial"] for r in data["registers"]] != initial or [r["reset"] for r in data["registers"]] != initial:
        raise ValueError("Reset metadata does not encode an empty slot and cursor zero")
    if data.get("startup") != "encoded_initial; hardware requires a reset edge before use":
        raise ValueError("Missing explicit hardware startup boundary")
    return data


def physical(observation):
    slot = observation["offered"]
    return {"in_ready": observation["ready"], "out_valid": slot is not None,
            "out_payload": slot["payload"] if slot else 0}


def output_values(data, observation):
    roles = data["roles"]
    values = dict(zip(roles["in_ready"], map(int, observation["in_ready"]), strict=True))
    values.update({roles["out_valid"]: int(observation["out_valid"]), roles["out_payload"]: observation["out_payload"]})
    return [values[p["name"]] for p in data["outputs"]]


def encoded_state(data, state):
    slot, roles = state["slot"], data["register_roles"]
    values = {roles["slot_valid"]: int(slot is not None), roles["slot_payload"]: slot["payload"] if slot else 0}
    values.update({name: int(k == state["cursor"]) for k, name in enumerate(roles["cursor"])})
    return [values[r["name"]] for r in data["registers"]]


def expected_frames(data, rows, config):
    logical = oracle.simulate(rows, *config)
    frames = []
    for row, frame in zip(rows, logical, strict=True):
        pre, post = physical(frame["pre"]), physical(frame["post"])
        frames.append({"cycle": frame["cycle"], "input": row, "pre": pre, "post": post,
                       "pre_values": output_values(data, pre), "post_values": output_values(data, post),
                       "post_registers": encoded_state(data, frame["state"]),
                       "logical": {k: frame[k] for k in ("pre", "post", "grant", "state")}})
    return logical, frames


def traffic(config, random_edges=192):
    inputs, width = config
    mask = (1 << width) - 1
    rng = random.Random(0x4D455247 + inputs * 257 + width)
    rows, phases = [], []

    def add(phase, valid, ready, reset=False, payload=None):
        values = [(len(rows) * 29 + k * 13) & mask for k in range(inputs)] if payload is None else [payload] * inputs
        rows.append({"reset": reset, "valid": list(valid), "payload": values, "ready": ready})
        phases.append(phase)

    all_valid, idle = [True] * inputs, [False] * inputs
    add("dirty-startup-reset", all_valid, False, True, mask)
    for _ in range(3):
        add("idle-garbage", idle, True, payload=mask)
    add("fill-slot", [k == inputs - 1 for k in range(inputs)], False, payload=mask)
    for k in range(19):
        add("long-stall", [((j + k) % 3 != 0) for j in range(inputs)], False)
    for _ in range(4 * inputs + 9):
        add("same-payload-contention", all_valid, True, payload=0)
    for _ in range(3):
        add("drain-gap", idle, True)
    add("replacement-setup", all_valid, False, payload=mask)
    for _ in range(inputs + 6):
        add("consume-refill", all_valid, True, payload=0)
    add("loaded-reset", all_valid, True, True, mask)
    for k in range(5 * inputs + 15):
        add("persistent-contention-stalls", all_valid, k % 5 == 4, payload=1 & mask)
    for bits in range(1 << inputs):
        add("request-mask-sweep", [bool(bits & (1 << k)) for k in range(inputs)], True)
    for _ in range(random_edges):
        add("random-raw", [rng.randrange(4) != 0 for _ in range(inputs)], bool(rng.randrange(2)),
            rng.randrange(97) == 0, rng.choice((0, 0, mask, rng.randrange(1 << width))))
    for _ in range(3):
        add("final-drain", idle, True)
    return rows, phases


def coverage(rows, logical, phases, inputs):
    result = Counter(phases)
    previous = None
    for row, frame in zip(rows, logical, strict=True):
        offered, grant = frame["pre"]["offered"], frame["grant"]
        result["stalled_held_cycles"] += int(offered is not None and not row["ready"] and not row["reset"])
        result["full_replacements"] += int(offered is not None and row["ready"] and grant is not None)
        result["idle_nonzero_payloads"] += sum(not v and p != 0 for v, p in zip(row["valid"], row["payload"], strict=True))
        result["request_set_changes"] += int(previous is not None and previous != row["valid"])
        if grant is not None:
            result[f"source_{grant}_acceptances"] += 1
        previous = row["valid"]
    required = ("stalled_held_cycles", "full_replacements", "idle_nonzero_payloads", "request_set_changes")
    if any(not result[k] for k in required) or any(not result[f"source_{k}_acceptances"] for k in range(inputs)):
        raise AssertionError("Required acceptance/stall/replacement/garbage coverage missing")
    return dict(sorted(result.items()))


def testbench(data, rows, registers):
    declarations = ["reg clk = 0;"]
    for group, kind in (("inputs", "reg"), ("outputs", "wire")):
        declarations += [f"{kind} [{p['width']-1}:0] {p['name']};" for p in data[group]]
    names = [p["name"] for p in data["inputs"] + data["outputs"]]
    connections = [f".{data['clock']}(clk)"] + [f".{name}({name})" for name in names]
    body = [f"{p['name']} = 0;" for p in data["inputs"]]
    if registers:
        body += [f"force dut.{r['reference']} = {r['width']}'h{(1 << r['width'])-1:x};" for r in data["registers"]]
        body += ["#1;"] + [f"release dut.{r['reference']};" for r in data["registers"]]
    body += ["#1;"]
    output_args = ", ".join(p["name"] for p in data["outputs"])
    register_args = ", ".join("dut." + r["reference"] for r in data["registers"])
    for cycle, row in enumerate(rows):
        roles = data["roles"]
        values = {roles["reset"]: int(row["reset"]), roles["out_ready"]: int(row["ready"])}
        for role, field in (("in_valid", "valid"), ("in_payload", "payload")):
            values.update(zip(roles[role], map(int, row[field]), strict=True))
        body += [f"{p['name']} = {p['width']}'h{values[p['name']]:x};" for p in data["inputs"]]
        body += ["#5;", f'$display("MERGE,{cycle},pre{",%0d" * len(data["outputs"])}", {output_args});',
                 "clk = 1;", "#5;", f'$display("MERGE,{cycle},post{",%0d" * len(data["outputs"])}", {output_args});']
        if registers:
            body += [f'$display("REG,{cycle}{",%0d" * len(data["registers"])}", {register_args});']
        body += ["clk = 0;", "#5;"]
    body += ['$display("MERGE_DONE");', "$finish;"]
    return "`timescale 1ns/1ps\nmodule tb;\n" + "\n".join(declarations) + \
        f"\n{data['module']} dut({', '.join(connections)});\ninitial begin\n  " + "\n  ".join(body) + "\nend\nendmodule\n"


class ConcreteMismatch(AssertionError):
    pass


def check_rtl_trace(text, frames, registers):
    observations, done = [], 0
    for line in text.splitlines():
        if line == "MERGE_DONE":
            done += 1
        elif line.startswith(("MERGE,", "REG,")):
            if done:
                raise AssertionError("Observation follows completion marker")
            parts = line.split(",")
            start = 3 if parts[0] == "MERGE" else 2
            if len(parts) <= start or not parts[1].isdecimal() or any(not p.isdecimal() for p in parts[start:]):
                raise AssertionError("Malformed or unknown-valued RTL observation")
            observations.append((parts[0], int(parts[1]), parts[2] if start == 3 else "registers", list(map(int, parts[start:]))))
        elif line.strip() and not re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)", line):
            raise AssertionError(f"Unexpected simulator output: {line}")
    expected = []
    for frame in frames:
        expected += [("MERGE", frame["cycle"], phase, frame[phase + "_values"]) for phase in ("pre", "post")]
        if registers:
            expected.append(("REG", frame["cycle"], "registers", frame["post_registers"]))
    if done != 1 or len(observations) != len(expected):
        raise AssertionError("Incomplete trace or wrong completion-marker count")
    # Validate every row's structure before allowing a negative control to
    # count a concrete mismatch; truncated/unknown/error output never passes.
    for actual, want in zip(observations, expected, strict=True):
        if actual[:3] != want[:3] or len(actual[3]) != len(want[3]):
            raise AssertionError("Incorrect trace order, phase, cycle or port count")
    for index, (actual, want) in enumerate(zip(observations, expected, strict=True)):
        if actual[3] != want[3]:
            raise ConcreteMismatch(f"RTL value mismatch at observation {index}: expected {want}, got {actual}")
    return len(frames)


def checker_self_test():
    frames = [{"cycle": 0, "pre_values": [0, 0], "post_values": [1, 0], "post_registers": [0, 1]}]
    good = "MERGE,0,pre,0,0\nMERGE,0,post,1,0\nREG,0,0,1\nMERGE_DONE\n"
    check_rtl_trace(good, frames, True)
    variants = {"wrong_value": good.replace("post,1,0", "post,0,0"),
                "unknown": good.replace("REG,0,0,1", "REG,0,x,1"),
                "missing_row": good.replace("REG,0,0,1\n", ""),
                "wrong_phase": good.replace("0,pre", "0,post"),
                "wrong_count": good.replace("REG,0,0,1", "REG,0,0"),
                "missing_done": good.replace("MERGE_DONE\n", ""),
                "double_done": good + "MERGE_DONE\n", "trailing_error": good + "ERROR\n"}
    for name, altered in variants.items():
        try:
            check_rtl_trace(altered, frames, True)
        except AssertionError as error:
            if isinstance(error, ConcreteMismatch) != (name == "wrong_value"):
                raise AssertionError("Malformed trace incorrectly qualified as a semantic negative control")
        else:
            raise AssertionError(f"Comparator accepted {name}")
    return list(variants)


def mutate_rtl(source, data, mutation):
    text, roles, regs = source, data["roles"], data["register_roles"]

    def replace(name, operator, change):
        nonlocal text
        pattern = re.compile(r"(\b" + ("assign\\s+" if operator == "=" else "") + re.escape(name) +
                             r"\s*" + re.escape(operator) + r"\s*)(.*?);", re.DOTALL)
        text, count = pattern.subn(lambda m: m[1] + change(m[2]) + ";", text)
        if count != 1:
            raise AssertionError(f"Expected one driver for {name}, found {count}")

    reset, ready, valid, payload = roles["reset"], roles["out_ready"], regs["slot_valid"], regs["slot_payload"]
    if mutation == "cursor_without_acceptance":
        if len(regs["cursor"]) < 2:
            raise ValueError("Cursor rotation is identity for N=1")
        for k, name in enumerate(regs["cursor"]):
            predecessor = regs["cursor"][(k-1) % len(regs["cursor"])]
            initial = int(k == 0)
            replace(name, "<=", lambda rhs, previous=predecessor, initial=initial:
                    f"{reset} ? 1'b{initial} : ({valid} && !{ready}) ? {previous} : ({rhs})")
    elif mutation == "multiple_ready":
        if len(roles["in_ready"]) < 2:
            raise ValueError("Multiple source acceptance requires N>=2")
        replace(roles["in_ready"][1], "=", lambda rhs:
                f"{reset} ? 1'b0 : ({roles['in_ready'][0]} | ({rhs}))")
    elif mutation == "drop_replacement":
        accepted = "(" + " | ".join(roles["in_ready"]) + ")"
        condition = f"!{reset} && {valid} && {ready} && {accepted}"
        replace(valid, "<=", lambda rhs: f"({condition}) ? 1'b0 : ({rhs})")
        replace(payload, "<=", lambda rhs: f"({condition}) ? {data['payload_width']}'h0 : ({rhs})")
    elif mutation == "stalled_payload_corruption":
        replace(payload, "<=", lambda rhs: f"(!{reset} && {valid} && !{ready}) ? ~{payload} : ({rhs})")
    else:
        raise ValueError(mutation)
    if text == source:
        raise AssertionError("Mutation did not change RTL")
    return text


def json_lines(path, rows):
    path.write_text("".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows))


def configuration(run, out, tools, config, random_edges):
    inputs, width = config
    label = f"merge-{inputs}-{width}"
    directory = out / label
    directory.mkdir()
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/BufferedMergeEmit.lean", *config, directory], label + "-emit")
    data = validate_descriptor(json.loads((directory / "interface.json").read_text()), *config)
    rows, phases = traffic(config, random_edges)
    logical, frames = expected_frames(data, rows, config)
    stimulus, startup, trace = (directory / name for name in ("stimulus.jsonl", "startup.json", "lean-trace.jsonl"))
    json_lines(stimulus, rows)
    startup.write_text(json.dumps([(1 << r["width"]) - 1 for r in data["registers"]]) + "\n")
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/BufferedMergeReplay.lean", *config,
         stimulus, trace, startup], label + "-replay", timeout=300)
    actual = [json.loads(line) for line in trace.read_text().splitlines()]
    if not oracle.same_json(actual, frames):
        differing = next((k for k, (a, b) in enumerate(zip(actual, frames)) if not oracle.same_json(a, b)), None)
        raise AssertionError(f"Lean/independent oracle mismatch at cycle {differing}; lengths {len(actual)}/{len(frames)}")
    accounting = oracle.check_trace(rows, [{"cycle": f["cycle"], **f["logical"]} for f in actual], *config, require_drained=True)
    observed_coverage = coverage(rows, logical, phases, inputs)
    json_lines(directory / "oracle-trace.jsonl", frames)
    rtl = directory / "merge.sv"
    rtl.write_text(run([tools["circt"], directory / "merge.mlir", "--canonicalize", "--lower-seq-to-sv",
                        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label + "-export"))

    def simulate(source, stage, registers, negative=False):
        tb, executable = directory / (stage + "-tb.sv"), directory / (stage + ".vvp")
        tb.write_text(testbench(data, rows, registers))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], label + "-" + stage + "-compile")
        output = run([tools["vvp"], executable], label + "-" + stage + "-simulate")
        (directory / (stage + "-trace.txt")).write_text(output)
        try:
            count = check_rtl_trace(output, frames, registers)
        except ConcreteMismatch as error:
            if negative:
                return {"detected": True, "reason": str(error), "source_sha256": rr.sha(source)}
            raise
        if negative:
            raise AssertionError(f"Actual RTL mutation {stage} escaped validation")
        return count

    rtl_edges = simulate(rtl, "rtl", True)
    stats, netlist, gates = (directory / name for name in ("stats.json", "netlist.json", "gates.sv"))
    script = directory / "synth.ys"
    script.write_text("\n".join(("read_verilog -sv " + rr.yosys_quote(rtl), "hierarchy -check -top " + data["module"],
        "synth -top " + data["module"], "check -assert", "tee -o " + rr.yosys_quote(stats) + " stat -json",
        "write_json " + rr.yosys_quote(netlist), "write_verilog -noattr " + rr.yosys_quote(gates), "")))
    run([tools["yosys"], "-Q", "-s", script], label + "-synth")
    modules = json.loads(netlist.read_text())["modules"]
    if set(modules) != {data["module"]} or modules[data["module"]].get("memories"):
        raise AssertionError("Unexpected synthesized hierarchy or memory")
    cells = Counter(c["type"] for c in modules[data["module"]].get("cells", {}).values())
    if any(not re.fullmatch(r"\$_(?:NOT|BUF|AND|NAND|OR|NOR|XOR|XNOR|ANDNOT|ORNOT|MUX|NMUX|AOI[34]|OAI[34]|(?:DFF|DFFE|SDFF|SDFFE|SDFFCE)_[PN01]+)_", k) for k in cells):
        raise AssertionError(f"Unexpected generic cells: {dict(cells)}")
    reported = json.loads(stats.read_text())["modules"]["\\" + data["module"]]
    if reported["num_cells"] != sum(cells.values()) or reported["num_cells_by_type"] != dict(cells):
        raise AssertionError("Synthesis statistics differ from saved netlist")
    gate_edges = simulate(gates, "gates", False)
    negatives = {}
    applicable = ["drop_replacement", "stalled_payload_corruption"]
    if inputs > 1:
        applicable += ["cursor_without_acceptance", "multiple_ready"]
    for mutation in applicable:
        altered = directory / (mutation + ".sv")
        altered.write_text(mutate_rtl(rtl.read_text(), data, mutation))
        negatives[mutation] = simulate(altered, mutation, True, negative=True)
    evidence = {"configuration": config, "edges": len(rows), "rtl_edges": rtl_edges, "synthesized_edges": gate_edges,
        "accounting": accounting, "coverage": observed_coverage, "generic_cells": sum(cells.values()),
        "generic_cells_by_type": dict(sorted(cells.items())), "generic_wire_bits": reported["num_wire_bits"],
        "register_bits": sum(r["width"] for r in data["registers"]), "typed_register_count": len(data["registers"]),
        "typed_output_count": len(data["outputs"]), "rtl_negative_controls": negatives,
        "inapplicable_controls": [] if inputs > 1 else ["cursor rotation is identity at N=1", "multiple ready sources require N>=2"],
        "startup": "Emitted registers forced to all ones and released before initial reset; synthesized state unconstrained until reset. Reset-visible outputs checked before and after edge.",
        "artifact_certificate": {"status": "not_run", "reason": "Separate typed artifact/kernel certificate campaign"}}
    (directory / "result.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"PASS merge {config}: {len(rows)} edges/form; {sum(cells.values())} generic cells; {len(negatives)} semantic RTL mutations rejected", flush=True)
    return evidence


def parse_config(value):
    if not re.fullmatch(r"[1-9][0-9]*,[1-9][0-9]*", value):
        raise argparse.ArgumentTypeError("Use positive INPUTS,WIDTH")
    return tuple(map(int, value.split(",")))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag")
    parser.add_argument("--config", action="append", type=parse_config)
    parser.add_argument("--random-edges", type=int, default=192)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        print("Rejected malformed/value trace controls: " + ", ".join(checker_self_test()))
        return
    if not args.tag or args.random_edges < 0:
        parser.error("--tag required; random edges must be nonnegative")
    configs = args.config or MATRIX
    if len(configs) != len(set(configs)):
        parser.error("Duplicate configurations")
    out = rr.fresh_directory(ROOT / "build/buffered-merge", args.tag)
    started, records = time.monotonic(), []
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
        "boundary": "Finite RTL simulation and generic synthesis, separate from universal Lean proofs and artifact interpretation. Integer modulo/origin-occurrence oracle; every emitted post-register and pre/post output checked. Synthesized external observations checked after reset; logical provenance is erased in hardware. No physical timing/fabrication claim.",
        "artifact_certificate": {"status": "not_run"},
        "tool_hash_scope": "Selected launchers, underlying executables, ABC and Icarus backend; not full dynamic-library closure."}
    run = rr.Commands(out, records)
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        report["trace_mutations_rejected"] = checker_self_test()
        run(["lake", "env", "lean", "--version"], "lean-version")
        for tool, option in (("circt", "--version"), ("iverilog", "-V"), ("yosys", "-V")):
            run([tools[tool], option], tool + "-version")
        run(["lake", "build", "Pinwheel.Hardware.Stream.BufferedMerge.Proofs", "Pinwheel.Hardware.Emit"], "build", timeout=900)
        audited = run(["lake", "env", "lean", "-DwarningAsError=true", "test/BufferedMergeCircuit.lean"], "proof-audit")
        if "standard axioms only" not in audited:
            raise AssertionError("Missing structural proof audit")
        run([sys.executable, "-B", "-m", "unittest", "discover", "-s", "test", "-p", "test_buffered_merge_oracle.py", "-v"], "oracle-tests")
        for config in configs:
            report["configurations"].append(configuration(run, out, tools, config, args.random_edges))
        if source_hashes() != report["source_sha256"]:
            raise RuntimeError("Owning source closure changed; use a fresh validation tag")
        if rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Selected tools changed during validation")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["artifact_sha256"] = {str(p.relative_to(out)): rr.sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        report["seconds"] = round(time.monotonic() - started, 3)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
