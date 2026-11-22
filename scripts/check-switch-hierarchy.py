#!/usr/bin/env python3
"""Compare freshly emitted flat and hierarchical switches on arbitrary raw state.

The default 1x1/depth1/width1 fixture exhausts every binary input/state bit pattern.
The 2x3/depth2/width8 fixture samples 512 patterns, including zero/multiple-hot
cursors. Every case compares settled pre/post outputs and all post-edge state.
This simulation receipt is separate from kernel-certified artifact readback.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import random
import re
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("hierarchy_cad_helpers", ROOT / "scripts/check-round-robin-circuit.py")
cad = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cad)
CONFIGURATIONS = ((1, 1, 1, 1), (2, 3, 2, 8))
PATH_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


def source_hashes():
    pending = [ROOT / "test/SwitchHierarchyEmit.lean"]
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
        "scripts/check-switch-hierarchy.py", "scripts/check-round-robin-circuit.py",
        "scripts/process_group.py", "scripts/validation_run.py"))
    return {str(path.relative_to(ROOT)): cad.sha(path) for path in sorted(sources)}


def read_descriptor(path, config):
    data = json.loads(path.read_text())
    ni, no, depth, width = config
    for key, expected in {"schema": 1, "input_count": ni, "output_count": no,
                          "depth": depth, "payload_width": width,
                          "destination_width": max(1, (no - 1).bit_length()),
                          "clock": "clk", "latency_added": 0, "reset_synchronous": True}.items():
        if data.get(key) != expected:
            raise ValueError(f"Hierarchy descriptor {key} mismatch")
    for name in [data["module"], data["flat_module"], *data["leaves"]]:
        if not isinstance(name, str) or not cad.IDENTIFIER.fullmatch(name):
            raise ValueError("Invalid HDL module identifier")
    if len(data["leaves"]) != 3 or len(set(data["leaves"])) != 3:
        raise ValueError("Expected distinct FIFO, slot and control modules")
    for group in ("inputs", "outputs", "registers"):
        for p in data[group]:
            if not cad.IDENTIFIER.fullmatch(p["name"]) or type(p["width"]) is not int or p["width"] <= 0:
                raise ValueError(f"Invalid {group} name or width")
        names = [p["name"] for p in data[group]]
        if len(names) != len(set(names)):
            raise ValueError(f"Duplicated {group} names")
    if set(p["name"] for p in data["inputs"]) & set(p["name"] for p in data["outputs"]):
        raise ValueError("Input/output names overlap")
    regs = data["registers"]
    expected_count = ni * (2 * depth) + no * 2 + ni * no
    if len(regs) != expected_count:
        raise ValueError("Hierarchy added or omitted state registers")
    if any(not PATH_IDENTIFIER.fullmatch(r["reference"]) or r["flat_reference"] != r["name"] for r in regs):
        raise ValueError("Invalid hierarchy register reference")
    refs = [r["reference"] for r in regs]
    if len(refs) != len(set(refs)) or refs != data["hierarchical_registers"]:
        raise ValueError("Hierarchy register paths must be bijective and retain typed order")
    if data["register_map"] != {r["name"]: r["reference"] for r in regs}:
        raise ValueError("Hierarchy register map disagrees with typed enumeration")
    cursor_names = [name for row in data["register_roles"]["cursor"] for name in row]
    if len(cursor_names) != ni * no or len(set(cursor_names)) != len(cursor_names):
        raise ValueError("Wrong cursor register role map")
    widths = {r["name"]: r["width"] for r in regs}
    if any(widths.get(name) != 1 for name in cursor_names):
        raise ValueError("Cursor bits must be one-bit registers")
    for leaf in data["leaf_interfaces"]:
        for register in leaf["registers"]:
            if register["reference"] != register["name"]:
                raise ValueError("Leaf register references must match emitted names")
    if "requires a reset edge" not in data.get("startup", ""):
        raise ValueError("Missing explicit hardware startup contract")
    return data


def raw_cases(data, exhaustive, samples, seed):
    widths = [p["width"] for p in data["inputs"] + data["registers"]]
    bits = sum(widths)
    count = (1 << bits) if exhaustive else samples
    rng = random.Random(seed)
    register_index = {r["name"]: k for k, r in enumerate(data["registers"])}
    cursor = data["register_roles"]["cursor"]
    ni = data["input_count"]
    rows, coverage = [], [Counter() for _ in cursor]
    for case in range(count):
        number = case if exhaustive else (0 if case == 0 else (1 << bits) - 1 if case == 1 else rng.getrandbits(bits))
        values = []
        for width in widths:
            values.append(number & ((1 << width) - 1))
            number >>= width
        inputs, registers = values[:len(data["inputs"])], values[len(data["inputs"]):]
        # Guarantee every raw cursor encoding for each output in the sampled
        # fixture, independently of the seeded remaining state and input bits.
        if not exhaustive and case >= 2:
            for output, names in enumerate(cursor):
                mask = (case - 2 + output) % (1 << ni)
                for k, name in enumerate(names):
                    registers[register_index[name]] = (mask >> k) & 1
        for output, names in enumerate(cursor):
            mask = sum(registers[register_index[name]] << k for k, name in enumerate(names))
            coverage[output][mask] += 1
        rows.append({"case": case, "inputs": inputs, "registers": registers})
    if exhaustive and count != 2048:
        raise AssertionError("The exhaustive smallest fixture changed its input/state bit count")
    if any(set(counts) != set(range(1 << ni)) for counts in coverage):
        raise AssertionError("Not every raw cursor encoding is exercised")
    return rows, {"input_bits": sum(widths[:len(data["inputs"])]),
                  "register_bits": sum(widths[len(data["inputs"]):]),
                  "exhaustive_binary_input_state": exhaustive,
                  "cursor_encoding_counts_by_output": [dict(sorted(c.items())) for c in coverage]}


def testbench(data, rows):
    lines = ["`timescale 1ns/1ps", "module tb;", "reg clk = 0;"]
    lines.extend(f"reg [{p['width']-1}:0] {p['name']};" for p in data["inputs"])
    for stem in ("h", "f"):
        lines.extend(f"wire [{p['width']-1}:0] {stem}_{p['name']};" for p in data["outputs"])

    def instance(module, name, stem):
        ports = [".clk(clk)"] + [f".{p['name']}({p['name']})" for p in data["inputs"]]
        ports.extend(f".{p['name']}({stem}_{p['name']})" for p in data["outputs"])
        return f"{module} {name}({', '.join(ports)});"

    lines.extend((instance(data["module"], "hier", "h"), instance(data["flat_module"], "flat", "f"), "initial begin"))

    def compare(a, b, message):
        # Case inequality alone would accept x===x; explicitly reject unknown
        # bits before testing the two-state equality of either implementation.
        lines.append(f"if ((^{a}) === 1'bx || (^{b}) === 1'bx) $fatal(1, \"unknown {message}\");")
        lines.append(f'if ({a} !== {b}) $fatal(1, "mismatch {message}");')

    for row in rows:
        case = row["case"]
        for port, value in zip(data["inputs"], row["inputs"], strict=True):
            lines.append(f"{port['name']} = {port['width']}'h{value:x};")
        for reg, value in zip(data["registers"], row["registers"], strict=True):
            for name in ("hier." + reg["reference"], "flat." + reg["flat_reference"]):
                lines.append(f"force {name} = {reg['width']}'h{value:x};")
        lines.append("#1;")
        for port in data["outputs"]:
            compare("h_" + port["name"], "f_" + port["name"], f"pre case {case} {port['name']}")
        for reg in data["registers"]:
            lines.extend(("release hier." + reg["reference"] + ";", "release flat." + reg["flat_reference"] + ";"))
        lines.extend(("#1;", "clk=1;", "#1;"))
        for port in data["outputs"]:
            compare("h_" + port["name"], "f_" + port["name"], f"post case {case} {port['name']}")
        for reg in data["registers"]:
            compare("hier." + reg["reference"], "flat." + reg["flat_reference"], f"state case {case} {reg['name']}")
        lines.extend(("clk=0;", "#1;"))
    lines.extend((f'$display("HIERARCHY_PASS {len(rows)}");', "$finish;", "end", "endmodule"))
    return "\n".join(lines) + "\n"


def configuration(run, out, tools, config, samples):
    ni, no, depth, width = config
    label = f"i{ni}-o{no}-d{depth}-w{width}"
    directory = out / label
    directory.mkdir()
    exported = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/SwitchHierarchyEmit.lean", *config, directory],
                   label + "-emit")
    if "standard axioms only" not in exported:
        raise AssertionError("Missing hierarchy control proof audit")
    data = read_descriptor(directory / "interface.json", config)
    sources = [directory / data["top_verilog"]]
    for name in data["leaves"] + ["flat"]:
        target = directory / (name + ".sv")
        target.write_text(run([tools["circt"], directory / (name + ".mlir"), "--canonicalize", "--lower-seq-to-sv",
                               "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"],
                              label + "-lower-" + name))
        sources.append(target)
    rows, coverage = raw_cases(data, config == (1, 1, 1, 1), samples, 904)
    (directory / "raw-cases.jsonl").write_text("".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows))
    tb, binary = directory / "equivalence_tb.sv", directory / "equivalence.vvp"
    tb.write_text(testbench(data, rows))
    run([tools["iverilog"], "-g2012", "-s", "tb", "-o", binary, *sources, tb], label + "-compile")
    result = run([tools["vvp"], binary], label + "-simulate")
    (directory / "simulation.txt").write_text(result)
    markers = [line for line in result.splitlines() if line.startswith("HIERARCHY_PASS")]
    if markers != [f"HIERARCHY_PASS {len(rows)}"]:
        raise AssertionError("Missing or incorrect complete hierarchy comparison result")
    evidence = {"configuration": config, "raw_cases": len(rows), "coverage": coverage,
                "outputs_checked_before_and_after": len(data["outputs"]),
                "post_registers_checked": len(data["registers"]), "unknown_bits_rejected": True,
                "state_precondition": "None: every raw register is forced to the same chosen binary value in both forms, "
                                      "then released before the tested clock edge. Reset is a varied input, not a prerequisite.",
                "artifact_certificate": {"status": "not_run", "reason": "Separate typed alias/kernel readback campaign"}}
    (directory / "result.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(f"PASS hierarchy {config}: {len(rows)} arbitrary raw input/state cases", flush=True)
    return evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True, help="Fresh evidence tag; never overwrites prior receipts")
    parser.add_argument("--samples", type=int, default=512, help="Raw samples for 2x3; 1x1 remains exhaustive")
    args = parser.parse_args()
    if args.samples < 6:
        parser.error("At least six samples are needed to exercise all raw cursor encodings")
    out = cad.fresh_directory(ROOT / "build/switch-hierarchy", args.tag)
    started, records = time.monotonic(), []
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "boundary": "Fresh flat-versus-hierarchical RTL comparison on arbitrary binary input and register values; "
                          "no reachable-state or one-hot-cursor assumption. Finite simulation, not an HDL emitter proof, "
                          "synthesis assessment or physical timing claim. Kernel artifact certification is a separate campaign.",
              "artifact_certificate": {"status": "not_run"},
              "tool_hash_scope": "Selected launchers, underlying executables, ABC and Icarus backend; not complete dynamic-library closure."}
    run = cad.Commands(out, records)
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = cad.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, cad.tool_hashes(paths)
        run(["lake", "env", "lean", "--version"], "lean-version")
        run([tools["circt"], "--version"], "circt-version")
        run([tools["iverilog"], "-V"], "iverilog-version")
        run(["lake", "build", "Pinwheel.Hardware.Switch.Export"], "build", timeout=900)
        for config in CONFIGURATIONS:
            report["configurations"].append(configuration(run, out, tools, config, args.samples))
        if source_hashes() != report["source_sha256"]:
            raise RuntimeError("Owning sources changed during validation; use a fresh tag")
        if cad.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Selected tools changed during validation; use a fresh tag")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["artifact_sha256"] = {str(path.relative_to(out)): cad.sha(path) for path in sorted(out.rglob("*")) if path.is_file()}
        report["seconds"] = round(time.monotonic() - started, 3)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
