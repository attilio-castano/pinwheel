#!/usr/bin/env python3
"""Fresh-source buffered-switch RTL simulation and generic synthesis campaign.

An independent deque oracle checks physical outputs, encoded register state and
logical occurrence accounting. This finite campaign is separate from the Lean
universal circuit proofs and from kernel-certified RTL artifact interpretation.
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

import switch_oracle as oracle

ROOT = Path(__file__).resolve().parents[1]


def load_helper(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


rr = load_helper("switch_cad_helpers", "check-round-robin-circuit.py")
model_checks = load_helper("switch_model_helpers", "check-switch-model.py")
MATRIX = ((1, 1, 1, 1), (2, 3, 2, 8), (3, 1, 1, 8), (3, 5, 3, 17), (5, 3, 2, 8))
LEAN_ROOTS = ("test/SwitchCircuitEmit.lean", "test/SwitchCircuitReplay.lean", "test/SwitchCircuit.lean")


def source_hashes():
    pending = [ROOT / name for name in LEAN_ROOTS]
    sources = set()
    while pending:
        path = pending.pop()
        if path in sources:
            continue
        sources.add(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for module in match[1].split("--", 1)[0].split():
                    if module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    sources.update(ROOT / name for name in (
        "lakefile.toml", "lean-toolchain", "lake-manifest.json", "tools/hardware-toolchain.json",
        "scripts/check-switch-circuit.py", "scripts/check-switch-model.py", "scripts/switch_oracle.py",
        "scripts/check-round-robin-circuit.py", "scripts/validation_run.py", "scripts/process_group.py",
        "test/test_switch_oracle.py"))
    return {str(path.relative_to(ROOT)): rr.sha(path) for path in sorted(sources)}


def descriptor(path, config):
    data = json.loads(path.read_text())
    ni, no, depth, width = config
    dw = max(1, (no - 1).bit_length())
    for key, expected in {"schema": 1, "input_count": ni, "output_count": no,
                          "depth": depth, "payload_width": width, "destination_width": dw,
                          "reset_synchronous": True}.items():
        if data.get(key) != expected:
            raise ValueError(f"Descriptor {key} mismatch")
    for key in ("module", "clock"):
        if not isinstance(data.get(key), str) or not rr.IDENTIFIER.fullmatch(data[key]):
            raise ValueError(f"Invalid {key} identifier")
    names = []
    for group in ("inputs", "outputs", "registers"):
        for port in data[group]:
            name, bits = port["name"], port["width"]
            if not isinstance(name, str) or not rr.IDENTIFIER.fullmatch(name) or type(bits) is not int or bits <= 0:
                raise ValueError(f"Invalid {group} entry")
            names.append(name)
            if group == "registers":
                if port["reference"] != name or any(type(port[k]) is not int or not 0 <= port[k] < 1 << bits
                                                    for k in ("initial", "reset")):
                    raise ValueError("Invalid register reference or initialization")
    if len(names) != len(set(names)) or data["clock"] in names:
        raise ValueError("Duplicated signal names")
    roles = data["roles"]
    expected_inputs = {roles["reset"]: 1}
    expected_outputs = {}
    for role, size, bits, target in (
        ("in_valid", ni, 1, expected_inputs), ("in_destination", ni, dw, expected_inputs),
        ("in_payload", ni, width, expected_inputs), ("out_ready", no, 1, expected_inputs),
        ("in_ready", ni, 1, expected_outputs), ("out_valid", no, 1, expected_outputs),
        ("out_payload", no, width, expected_outputs)):
        if len(roles[role]) != size:
            raise ValueError(f"Wrong {role} cardinality")
        for name in roles[role]:
            if name in target:
                raise ValueError("Duplicated port role")
            target[name] = bits
    for group, expected in (("inputs", expected_inputs), ("outputs", expected_outputs)):
        if {p["name"]: p["width"] for p in data[group]} != expected:
            raise ValueError(f"Incomplete typed {group} role map")
    reg_roles, expected_regs = data["register_roles"], {}
    for role, outer, inner, bits in (("fifo_valid", ni, depth, 1), ("fifo_data", ni, depth, dw + width),
                                     ("cursor", no, ni, 1)):
        if len(reg_roles[role]) != outer or any(len(row) != inner for row in reg_roles[role]):
            raise ValueError(f"Wrong {role} register dimensions")
        for row in reg_roles[role]:
            for name in row:
                if name in expected_regs:
                    raise ValueError("Duplicated register role")
                expected_regs[name] = bits
    for role, bits in (("slot_valid", 1), ("slot_payload", width)):
        if len(reg_roles[role]) != no:
            raise ValueError(f"Wrong {role} cardinality")
        for name in reg_roles[role]:
            if name in expected_regs:
                raise ValueError("Duplicated register role")
            expected_regs[name] = bits
    if {p["name"]: p["width"] for p in data["registers"]} != expected_regs:
        raise ValueError("Incomplete typed register role map")
    initial = encoded_state(data, {"queues": [[] for _ in range(ni)], "slots": [None] * no, "cursor": [0] * no})
    if initial != [r["initial"] for r in data["registers"]] or initial != [r["reset"] for r in data["registers"]]:
        raise ValueError("Declared reset values do not encode the empty switch with cursor zero")
    return data


def decode_raw(row, config):
    ni, no, _, width = config
    dw = max(1, (no - 1).bit_length())
    if set(row) != {"reset", "valid", "destination", "payload", "ready"} or type(row["reset"]) is not bool:
        raise ValueError("Malformed physical stimulus")
    for key, size in (("valid", ni), ("destination", ni), ("payload", ni), ("ready", no)):
        if not isinstance(row[key], list) or len(row[key]) != size:
            raise ValueError("Wrong physical stimulus shape")
    if any(type(v) is not bool for v in row["valid"] + row["ready"]):
        raise ValueError("Physical control values must be Boolean")
    for key, bits in (("destination", dw), ("payload", width)):
        if any(type(v) is not int or not 0 <= v < 1 << bits for v in row[key]):
            raise ValueError("Physical data exceeds its declared wire width")
    return {"reset": row["reset"], "ready": row["ready"], "offered": [
        {"destination": d, "payload": p} if valid and d < no else None
        for valid, d, p in zip(row["valid"], row["destination"], row["payload"], strict=True)]}


def physical_output(raw, observation, outputs):
    return {"in_ready": [r and (not valid or d < outputs) for r, valid, d in
                          zip(observation["ready"], raw["valid"], raw["destination"], strict=True)],
            "out_valid": [p is not None for p in observation["offered"]],
            "out_payload": [p["payload"] if p else 0 for p in observation["offered"]]}


def output_values(data, observation):
    named = {}
    for role in ("in_ready", "out_valid", "out_payload"):
        named.update(zip(data["roles"][role], map(int, observation[role]), strict=True))
    return [named[p["name"]] for p in data["outputs"]]


def encoded_state(data, state):
    roles, values = data["register_roles"], {}
    width = data["payload_width"]
    for k, queue in enumerate(state["queues"]):
        for cell in range(data["depth"]):
            p = queue[cell] if cell < len(queue) else None
            values[roles["fifo_valid"][k][cell]] = int(p is not None)
            values[roles["fifo_data"][k][cell]] = (p["destination"] << width) | p["payload"] if p else 0
    for o, slot in enumerate(state["slots"]):
        values[roles["slot_valid"][o]] = int(slot is not None)
        values[roles["slot_payload"][o]] = slot["payload"] if slot else 0
        for k, name in enumerate(roles["cursor"][o]):
            values[name] = int(k == state["cursor"][o])
    return [values[r["name"]] for r in data["registers"]]


def expected_frames(data, rows, config):
    ni, no, depth, _ = config
    logical_rows = [decode_raw(row, config) for row in rows]
    logical = oracle.simulate(logical_rows, ni, no, depth)
    frames = []
    for raw, frame in zip(rows, logical, strict=True):
        pre, post = (physical_output(raw, frame[phase], no) for phase in ("pre", "post"))
        frames.append({"cycle": frame["cycle"], "input": raw, "pre": pre, "post": post,
                       "pre_values": output_values(data, pre), "post_values": output_values(data, post),
                       "post_registers": encoded_state(data, frame["state"]),
                       "logical": {key: frame[key] for key in ("pre", "post", "grants", "state")}})
    return logical_rows, logical, frames


def check_lean_trace(actual, expected):
    if len(actual) != len(expected):
        raise AssertionError("Lean replay frame count mismatch")
    for cycle, (got, want) in enumerate(zip(actual, expected, strict=True)):
        if got != want:
            fields = [key for key in want if got.get(key) != want[key]]
            raise AssertionError(f"Lean/independent oracle mismatch at edge {cycle}: {fields}")


def traffic(config, random_edges=384):
    ni, no, depth, width = config
    dw, mask = max(1, (no - 1).bit_length()), (1 << width) - 1
    rng = random.Random(0x53574349 + ni * 257 + no)
    rows, phases = [], []

    def add(phase, destinations, ready, reset=False, payload=None):
        cycle = len(rows)
        rows.append({"reset": reset, "valid": [d is not None for d in destinations],
                     "destination": [(1 << dw) - 1 if d is None else d for d in destinations],
                     "payload": [((cycle + k) & mask) if payload is None else payload for k in range(ni)],
                     "ready": list(ready)})
        phases.append(phase)

    drain = ni * depth + no + 4
    add("arbitrary-startup-reset", [(1 << dw) - 1] * ni, [False] * no, True, mask)
    for _ in range(3):
        add("idle-invalid-code", [None] * ni, [True] * no)
    for code in range(no, 1 << dw):
        for _ in range(3):
            add("invalid-asserted", [code] * ni, [True] * no)
    for destination in range(no):
        for _ in range(ni + depth + 4):
            add("destination-sweep", [destination] * ni, [True] * no)
    for _ in range(4 * ni + depth + 16):
        add("repeated-payload-contention", [0] * ni, [True] * no, payload=0)
    for _ in range(ni * depth + 4):
        add("fill-stalled", [0] * ni, [False] * no, payload=mask)
    for _ in range(ni * depth + 16):
        add("full-replacement", [0] * ni, [True] * no, payload=0)
    add("loaded-reset", [0] * ni, [False] * no, True)
    if no > 1 and depth > 1:
        ready = [False] + [True] * (no - 1)
        for destination in (0, 0, 1):
            add("head-of-line-setup", [destination] + [None] * (ni - 1), ready)
        for _ in range(8):
            add("head-of-line-stall", [None] + ([1] + [None] * (ni - 2) if ni > 1 else []), ready)
    for edge in range(3 * depth + 4 * ni + 24):
        blocked = (edge // (depth + ni + 3)) % no
        add("independent-stalls", [(edge + k) % no for k in range(ni)], [o != blocked for o in range(no)])
    for _ in range(random_edges):
        destinations = [None if rng.randrange(4) == 0 else rng.randrange(1 << dw) for _ in range(ni)]
        add("random-raw", destinations, [bool(rng.randrange(2)) for _ in range(no)], rng.randrange(97) == 0,
            rng.choice((0, 0, mask, rng.randrange(1 << width))))
    for _ in range(drain):
        add("final-drain", [None] * ni, [True] * no)
    return rows, phases


def physical_coverage(rows, logical_rows, logical_frames, phases, config):
    ni, no, depth, _ = config
    result = model_checks.coverage(logical_rows, logical_frames, phases, ni, no, depth)
    result["invalid_asserted_offers"] = sum(valid and d >= no for row in rows
                                            for valid, d in zip(row["valid"], row["destination"], strict=True))
    result["invalid_idle_codes"] = sum(not valid and d >= no for row in rows
                                       for valid, d in zip(row["valid"], row["destination"], strict=True))
    if no < 1 << max(1, (no - 1).bit_length()) and not all(
            result[key] for key in ("invalid_asserted_offers", "invalid_idle_codes")):
        raise AssertionError("Missing invalid destination admission/idle coverage")
    if ni > 1 and no > 1 and not result["independent_output_progress"]:
        raise AssertionError("Missing independent output progress under stall")
    if no > 1 and depth > 1 and not result["head_of_line_blocked_cycles"]:
        raise AssertionError("Missing head-of-line blocking coverage")
    return result


def testbench(data, rows, registers):
    declarations = ["reg clk = 0;"]
    for group, kind in (("inputs", "reg"), ("outputs", "wire")):
        declarations.extend(f"{kind} [{p['width']-1}:0] {p['name']};" for p in data[group])
    names = [p["name"] for p in data["inputs"] + data["outputs"]]
    connections = [f".{data['clock']}(clk)"] + [f".{name}({name})" for name in names]
    body = [f"{p['name']} = 0;" for p in data["inputs"]]
    if registers:
        body.extend(f"force dut.{r['reference']} = {r['width']}'h{(1 << r['width']) - 1:x};" for r in data["registers"])
        body.append("#1;")
        body.extend(f"release dut.{r['reference']};" for r in data["registers"])
    body.append("#1;")
    output_args = ", ".join(p["name"] for p in data["outputs"])
    output_format = ",%0d" * len(data["outputs"])
    register_args = ", ".join("dut." + r["reference"] for r in data["registers"])
    for cycle, row in enumerate(rows):
        values = {data["roles"]["reset"]: int(row["reset"])}
        for role, field in (("in_valid", "valid"), ("in_destination", "destination"),
                            ("in_payload", "payload"), ("out_ready", "ready")):
            values.update(zip(data["roles"][role], map(int, row[field]), strict=True))
        body.extend(f"{p['name']} = {p['width']}'h{values[p['name']]:x};" for p in data["inputs"])
        body.extend(("#5;", f'$display("SW,{cycle},pre{output_format}", {output_args});', "clk = 1;", "#5;",
                     f'$display("SW,{cycle},post{output_format}", {output_args});'))
        if registers:
            body.append(f'$display("REG,{cycle}{",%0d" * len(data["registers"])}", {register_args});')
        body.extend(("clk = 0;", "#5;"))
    body.extend(('$display("SW_DONE");', "$finish;"))
    return "`timescale 1ns/1ps\nmodule tb;\n" + "\n".join(declarations) + \
        f"\n{data['module']} dut({', '.join(connections)});\ninitial begin\n  " + \
        "\n  ".join(body) + "\nend\nendmodule\n"


def check_rtl_trace(text, frames, registers):
    observations, done = [], 0
    for line in text.splitlines():
        if line == "SW_DONE":
            done += 1
        elif line.startswith(("SW,", "REG,")):
            if done:
                raise AssertionError("RTL observations follow completion")
            parts = line.split(",")
            start = 3 if parts[0] == "SW" else 2
            if not parts[1].isdecimal() or any(not p.isdecimal() for p in parts[start:]):
                raise AssertionError("Malformed or unknown-valued RTL observation")
            observations.append((parts[0], int(parts[1]), parts[2] if start == 3 else "registers",
                                 list(map(int, parts[start:]))))
        elif line.strip() and not re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)", line):
            raise AssertionError(f"Unexpected simulator output: {line}")
    expected = []
    for frame in frames:
        cycle = frame["cycle"]
        expected.extend(("SW", cycle, phase, frame[phase + "_values"]) for phase in ("pre", "post"))
        if registers:
            expected.append(("REG", cycle, "registers", frame["post_registers"]))
    if done != 1 or len(observations) != len(expected):
        raise AssertionError("Incomplete RTL trace or completion marker")
    for index, (actual, want) in enumerate(zip(observations, expected, strict=True)):
        if actual != want:
            raise AssertionError(f"RTL mismatch at observation {index}: expected {want}, got {actual}")
    return len(frames)


def checker_self_test():
    frames = [{"cycle": 0, "pre_values": [0, 0], "post_values": [1, 0], "post_registers": [0, 1]},
              {"cycle": 1, "pre_values": [1, 0], "post_values": [1, 1], "post_registers": [1, 0]}]
    good = "SW,0,pre,0,0\nSW,0,post,1,0\nREG,0,0,1\nSW,1,pre,1,0\nSW,1,post,1,1\nREG,1,1,0\nSW_DONE\n"
    check_rtl_trace(good, frames, True)
    variants = {"wrong_output": good.replace("SW,0,post,1,0", "SW,0,post,0,0"),
                "wrong_register": good.replace("REG,0,0,1", "REG,0,1,1"),
                "missing_edge": good.replace("SW,1,pre,1,0\n", ""),
                "unknown_value": good.replace("REG,0,0,1", "REG,0,x,1"),
                "wrong_phase": good.replace("SW,1,pre", "SW,1,post"),
                "missing_completion": good.replace("SW_DONE\n", "")}
    for name, trace in variants.items():
        try:
            check_rtl_trace(trace, frames, True)
        except AssertionError:
            continue
        raise AssertionError(f"Trace comparator accepted mutation {name}")
    return list(variants)


def audit_source():
    return '''import Lean
import Pinwheel.Hardware.Switch.CircuitProofs
open Lean Elab Command
elab "#audit_switch_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Switch." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty switch circuit audit"
  logInfo m!"Switch circuit audit: {count} declarations, standard axioms only."
#audit_switch_circuit
'''


def mutate_rtl(source, data, mutation):
    text = source

    def change_assignment(name, rhs):
        nonlocal text
        pattern = re.compile(r"(\bassign\s+" + re.escape(name) + r"\s*=).*?;", re.DOTALL)
        text, count = pattern.subn(lambda match: match[1] + " " + rhs + ";", text)
        if count != 1:
            raise AssertionError(f"Mutation requires exactly one assignment to {name}, found {count}")

    if mutation == "drop_ready":
        change_assignment(data["roles"]["in_ready"][0], "1'b0")
    elif mutation == "ignore_reset":
        header, body = text.split(");", 1)
        body, count = re.subn(r"\b" + re.escape(data["roles"]["reset"]) + r"\b", "1'b0", body)
        if count == 0:
            raise AssertionError("No reset uses to mutate")
        text = header + ");" + body
    elif mutation == "wrong_route":
        if data["output_count"] < 2:
            raise ValueError("Route swap requires at least two outputs")
        for role in ("out_valid", "out_payload"):
            a, b = data["roles"][role][:2]
            rhs = []
            for name in (a, b):
                matches = re.findall(r"\bassign\s+" + re.escape(name) + r"\s*=\s*(.*?);", text, re.DOTALL)
                if len(matches) != 1:
                    raise AssertionError("Route mutation cannot identify output driver")
                rhs.append(matches[0])
            change_assignment(a, rhs[1])
            change_assignment(b, rhs[0])
    else:
        raise ValueError(mutation)
    if text == source:
        raise AssertionError("Mutation did not change RTL")
    return text


def configuration(run, out, tools, config, random_edges):
    ni, no, depth, width = config
    label = f"i{ni}-o{no}-d{depth}-w{width}"
    directory = out / label
    directory.mkdir()
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/SwitchCircuitEmit.lean", *config, directory],
        label + "-emit")
    data = descriptor(directory / "interface.json", config)
    rows, phases = traffic(config, random_edges)
    stimulus, startup, trace = (directory / name for name in ("stimulus.jsonl", "startup.json", "lean-trace.jsonl"))
    model_checks.json_lines(stimulus, rows)
    startup.write_text(json.dumps([(1 << r["width"]) - 1 for r in data["registers"]]) + "\n")
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/SwitchCircuitReplay.lean", *config,
         stimulus, trace, startup], label + "-replay", timeout=300)
    actual = [json.loads(line) for line in trace.read_text().splitlines()]
    logical_rows, logical, frames = expected_frames(data, rows, config)
    check_lean_trace(actual, frames)
    accounting = oracle.check_trace(logical_rows, [{"cycle": f["cycle"], **f["logical"]} for f in actual],
                                    ni, no, depth, require_drained=True)
    coverage = physical_coverage(rows, logical_rows, logical, phases, config)
    model_checks.json_lines(directory / "oracle-trace.jsonl", frames)
    rtl = directory / "switch.sv"
    rtl.write_text(run([tools["circt"], directory / "switch.mlir", "--canonicalize", "--lower-seq-to-sv",
                        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label + "-export"))

    def simulate(source, stage, registers, negative=False):
        tb, executable = directory / (stage + "-tb.sv"), directory / (stage + ".vvp")
        tb.write_text(testbench(data, rows, registers))
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], label + "-" + stage + "-compile")
        result = run([tools["vvp"], executable], label + "-" + stage + "-simulate")
        (directory / (stage + "-trace.txt")).write_text(result)
        try:
            edges = check_rtl_trace(result, frames, registers)
        except AssertionError as error:
            if negative and str(error).startswith("RTL mismatch"):
                return {"detected": True, "reason": str(error), "source_sha256": rr.sha(source)}
            raise
        if negative:
            raise AssertionError(f"Intentional RTL mutation {stage} escaped validation")
        return edges

    rtl_edges = simulate(rtl, "rtl", True)
    stats, netlist, gates = (directory / name for name in ("stats.json", "netlist.json", "gates.sv"))
    script = directory / "synth.ys"
    script.write_text("\n".join(("read_verilog -sv " + rr.yosys_quote(rtl),
        "hierarchy -check -top " + data["module"], "synth -top " + data["module"], "check -assert",
        "tee -o " + rr.yosys_quote(stats) + " stat -json", "write_json " + rr.yosys_quote(netlist),
        "write_verilog -noattr " + rr.yosys_quote(gates), "")))
    run([tools["yosys"], "-Q", "-s", script], label + "-synth", timeout=300)
    modules = json.loads(netlist.read_text())["modules"]
    if set(modules) != {data["module"]} or modules[data["module"]].get("memories"):
        raise AssertionError("Unexpected synthesized module hierarchy or memory")
    cells = Counter(cell["type"] for cell in modules[data["module"]].get("cells", {}).values())
    if any(not re.fullmatch(r"\$_(?:NOT|BUF|AND|NAND|OR|NOR|XOR|XNOR|ANDNOT|ORNOT|MUX|NMUX|AOI[34]|OAI[34]|(?:DFF|DFFE|SDFF|SDFFE|SDFFCE)_[PN01]+)_", kind)
           for kind in cells):
        raise AssertionError(f"Unexpected generic cell types: {dict(cells)}")
    reported = json.loads(stats.read_text())["modules"]["\\" + data["module"]]
    if reported["num_cells"] != sum(cells.values()) or reported["num_cells_by_type"] != dict(cells):
        raise AssertionError("Synthesis statistics differ from saved netlist")
    gate_edges = simulate(gates, "gates", False)
    negatives = {}
    for mutation in ("drop_ready", "ignore_reset") + (("wrong_route",) if no > 1 else ()):
        altered = directory / (mutation + ".sv")
        altered.write_text(mutate_rtl(rtl.read_text(), data, mutation))
        negatives[mutation] = simulate(altered, mutation, True, negative=True)
    evidence = {"configuration": config, "edges": len(rows), "rtl_edges": rtl_edges, "synthesized_edges": gate_edges,
                "accounting": accounting, "coverage": coverage, "typed_output_count": len(data["outputs"]),
                "typed_register_count": len(data["registers"]), "register_bits": sum(r["width"] for r in data["registers"]),
                "generic_cells": sum(cells.values()), "generic_cells_by_type": dict(sorted(cells.items())),
                "generic_wire_bits": reported["num_wire_bits"], "rtl_negative_controls": negatives,
                "startup": "All unsynthesized RTL registers forced to ones, then released before first reset edge; "
                           "synthesized registers uninitialized before first reset edge. All visible reset outputs checked.",
                "artifact_certificate": {"status": "not_run", "reason": "Separate typed readback/kernel artifact campaign"}}
    (directory / "result.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"PASS switch {config}: {len(rows)} edges in each RTL form; {sum(cells.values())} generic cells", flush=True)
    return evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", help="Fresh evidence tag; existing directories are never overwritten")
    parser.add_argument("--config", action="append", type=model_checks.parse_config)
    parser.add_argument("--random-edges", type=int, default=384)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        print("Rejected trace mutations: " + ", ".join(checker_self_test()))
        return
    if not args.tag or args.random_edges < 0:
        parser.error("--tag is required and --random-edges must be nonnegative")
    configs = args.config or MATRIX
    if len(configs) != len(set(configs)):
        parser.error("Duplicate configurations")
    out = rr.fresh_directory(ROOT / "build/switch-circuit", args.tag)
    started, records = time.monotonic(), []
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "boundary": "Universal Lean expression refinement audited separately from finite RTL simulation. "
                          "Independent deque oracle and occurrence scoreboard; every typed output pre/post and every "
                          "post-edge register checked in unsynthesized RTL; outputs checked after generic synthesis. "
                          "No physical area/timing or fabrication claim. Kernel-certified artifact interpretation not run here.",
              "artifact_certificate": {"status": "not_run"},
              "tool_hash_scope": "Selected launchers, underlying executables, ABC and Icarus backend; not complete dynamic-library closure."}
    run = rr.Commands(out, records)
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        report["trace_mutations_rejected"] = checker_self_test()
        run(["lake", "env", "lean", "--version"], "lean-version")
        for tool, option in (("circt", "--version"), ("iverilog", "-V"), ("yosys", "-V")):
            run([tools[tool], option], tool + "-version")
        run(["lake", "build", "Pinwheel.Hardware.Switch.CircuitProofs", "Pinwheel.Hardware.Emit"], "build", timeout=900)
        run(["lake", "env", "lean", "-DwarningAsError=true", "test/SwitchCircuit.lean"], "switch-proof-examples")
        audit_file = out / "ProofAudit.lean"
        audit_file.write_text(audit_source())
        audit = run(["lake", "env", "lean", "-DwarningAsError=true", audit_file], "switch-proof-audit")
        if "standard axioms only" not in audit:
            raise AssertionError("Missing switch structural proof audit")
        run([sys.executable, "-B", "-m", "unittest", "discover", "-s", "test", "-p", "test_switch_oracle.py", "-v"], "oracle-tests")
        for config in configs:
            report["configurations"].append(configuration(run, out, tools, config, args.random_edges))
        if source_hashes() != report["source_sha256"]:
            raise RuntimeError("Owning sources changed during validation; use a fresh tag")
        if rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Selected tools changed during validation; use a fresh tag")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["artifact_sha256"] = {str(path.relative_to(out)): rr.sha(path) for path in sorted(out.rglob("*")) if path.is_file()}
        report["seconds"] = round(time.monotonic() - started, 3)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
