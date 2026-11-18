"""Lower, replay and certify flat synchronous modules emitted by TypedModule."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import re

import typed_circuit_readback as readback
from typed_artifact_runner import compile_modules
from validation_run import Commands

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "typed_module_cad", ROOT / "scripts/check-round-robin-circuit.py"
)
cad = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cad)


def tool_config():
    manifest, tools, paths = cad.selected_tools()
    suite = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
    tools["z3"] = suite / "bin/z3"
    paths += [tools["z3"], suite / "libexec/z3"]
    return manifest, tools, paths


def source_paths():
    return (*readback.source_paths(), Path(__file__).resolve(),
            ROOT / "scripts/check-round-robin-circuit.py",
            ROOT / "scripts/validation_run.py",
            ROOT / "tools/hardware-toolchain.json")


def profile(import_module, design, *, bindings=""):
    """Point readback at the same typed declaration the client exported."""
    return f"""import {import_module}
{bindings}abbrev exported := {design}
abbrev Input := exported.Input
abbrev Register := exported.Register
abbrev Output := exported.Output
abbrev circuit := exported.circuit
abbrev inputs := exported.inputs
abbrev registers := exported.registers
abbrev outputs := exported.outputs
"""


def testbench(descriptor, traffic, expected):
    ins, outs = descriptor["inputs"], descriptor["outputs"]

    def assignments(ports, values):
        for p, value in zip(ports, values, strict=True):
            if type(value) is not int or not 0 <= value < 1 << p["width"]:
                raise ValueError(f"Invalid replay value for {p['name']}: {value}")
            yield p["name"], f"{p['width']}'d{value}"

    if not traffic:
        raise ValueError("Replay needs at least one edge")
    lines = ["`timescale 1ns/1ps", "module tb;", "reg clk = 0;"]
    for kind, ports in (("reg", ins), ("wire", outs)):
        lines.extend(f"{kind} [{p['width'] - 1}:0] {p['name']};" for p in ports)
    connections = ", ".join(f".{p['name']}({p['name']})" for p in ins + outs)
    lines.extend([f"{descriptor['module']} dut(.clk(clk), {connections});", "initial begin"])
    for cycle, (row, (before, after)) in enumerate(zip(traffic, expected, strict=True)):
        lines.extend(f"  {name} = {literal};" for name, literal in assignments(ins, row))
        lines.append("  #1;")
        for phase, values in (("before", before), ("after", after)):
            if phase == "after":
                lines.append("  clk = 1; #1;")
            elif values is None and cycle == 0:
                continue
            for name, literal in assignments(outs, values):
                lines.append(
                    f"  if ({name} !== {literal}) "
                    f'$fatal(1, "ARTIFACT_MISMATCH cycle {cycle} {phase} {name}: expected %0h, got %0h", '
                    f"{literal}, {name});"
                )
        lines.append("  clk = 0; #1;")
    lines.extend(['  $display("Artifact replay passed");', "end", "endmodule"])
    return "\n".join(lines) + "\n"


def import_rtl(run, tools, directory, rtl, top, label, *, mapped=None):
    script = directory / ("compare.ys" if mapped is not None else "import.ys")
    imported = directory / "import.json"
    front = f"read_verilog -sv {cad.yosys_quote(rtl)}\nhierarchy -check -top {top}\n"
    commands = front + "proc\npmuxtree\nopt_clean\ncheck -assert\n"
    commands += f"write_json {cad.yosys_quote(imported)}\n"
    if mapped is not None:
        # Preserve the existing switch comparison's Yosys session. Restarting
        # Yosys before synthesis changes its internal numbering and ABC result.
        commands += "design -reset\n" + front
        commands += f"synth -top {top}\ncheck -assert\nwrite_json {cad.yosys_quote(mapped)}\n"
    script.write_text(commands)
    run([tools["yosys"], "-Q", "-T", "-s", script], label + "-import")
    return imported


def swap_output_drivers(text, first, second):
    """Keep the public port declarations and swap the two right-hand sides."""
    if first["width"] != second["width"] or first["name"] == second["name"]:
        raise ValueError("Choose distinct outputs of the same width")
    names = [p["name"] for p in (first, second)]
    matches = []
    for name in names:
        drivers = list(re.finditer(r"\bassign\s+" + re.escape(name) + r"\s*=\s*(.*?);", text, re.S))
        if len(drivers) != 1:
            raise ValueError(f"Expected exactly one continuous driver for output {name}")
        matches.extend(drivers)
    if matches[0][1] == matches[1][1]:
        raise ValueError("Outputs already have the same driver")
    edits = [(*a.span(1), b[1]) for a, b in zip(matches, reversed(matches), strict=True)]
    for start, end, rhs in sorted(edits, reverse=True):
        text = text[:start] + rhs + text[end:]
    return text


def check_output_swap(run, tools, directory, rtl, tb, descriptor, mlir, design, outputs, extra_lean_paths):
    first, second = (descriptor["outputs"][index] for index in outputs)
    negative = directory / "output-swap"
    negative.mkdir()
    mutated = negative / rtl.name
    mutated.write_text(swap_output_drivers(rtl.read_text(), first, second))
    label = directory.name + "-output-swap"
    executable = negative / "replay.vvp"
    run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, mutated, tb], label + "-compile")
    result = Commands(ROOT, negative, run.records)(
        [tools["vvp"], executable], label + "-replay", reject="ARTIFACT_MISMATCH"
    )
    diagnostic = next(line for line in result.splitlines() if "ARTIFACT_MISMATCH" in line)
    if not any(f" {p['name']}:" in diagnostic for p in (first, second)):
        raise RuntimeError(f"Swap failed at an unrelated port: {diagnostic}")

    imported = import_rtl(run, tools, negative, mutated, descriptor["module"], label)
    modules, _ = readback.generate(negative, descriptor, mlir, imported, tools["z3"], profile=design)
    try:
        compile_modules(run, negative, modules, extra_lean_paths=extra_lean_paths)
    except RuntimeError as error:
        failure = re.match(r"(LocalProofs[0-9]*) certificate failed:", str(error))
        if failure is None:
            raise
        log = (negative / f"{failure[1]}.log").read_text()
        errors = re.findall(r"\.lean:\d+:\d+: error(?:\s*\([^)]*\))?: (.*)", log)
        allowed = ("unsolved goals", "`grind` failed", "Tactic `decide` proved that the proposition")
        if not errors or any(not any(marker in e for marker in allowed) for e in errors):
            raise
        run.records[-1]["expected_failure"] = True
    else:
        raise RuntimeError("The swapped RTL received a certificate")
    return {"outputs": [first["name"], second["name"]], "width": first["width"],
            "replay_rejected": diagnostic, "kernel_rejection_module": failure[1]}


def verify(run, tools, directory, stem, design, initialized, traffic, expected, *,
           extra_lean_paths=(), swap_outputs=None, mapped=None):
    """Return a receipt only after complete replay, endpoint proofs and trace audit."""
    label = directory.name
    descriptor = json.loads((directory / "interface.json").read_text())
    readback.validate_descriptor(descriptor)
    if descriptor.get("clock") != "clk":
        raise ValueError("Expected a single synchronous clock named clk")
    mlir, rtl = directory / (stem + ".mlir"), directory / (stem + ".sv")
    rtl.write_text(run([tools["circt"], mlir, "--lower-seq-to-sv", "--lower-hw-to-sv",
                        "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"], label + "-lower"))
    tb, executable = directory / "tb.sv", directory / "replay.vvp"
    tb.write_text(testbench(descriptor, traffic, expected))
    run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, rtl, tb], label + "-compile-replay")
    if run([tools["vvp"], executable], label + "-replay").strip() != "Artifact replay passed":
        raise ValueError(f"{label}: missing completed replay marker")
    imported = import_rtl(run, tools, directory, rtl, descriptor["module"], label, mapped=mapped)
    modules, evidence = readback.generate(directory, descriptor, mlir, imported, tools["z3"], profile=design)
    (directory / "Initialized.lean").write_text(initialized)
    audit = directory / "Audit.lean"
    audit.write_text(audit.read_text().replace("import Proof", "import Initialized"))
    modules.insert(-1, "Initialized")
    compile_modules(run, directory, modules, extra_lean_paths=extra_lean_paths)
    if "standard axioms only" not in (directory / "Audit.log").read_text():
        raise RuntimeError(f"{label}: missing Lean axiom audit")
    report = {
        **evidence,
        "registers": len(descriptor["registers"]),
        "outputs": len(descriptor["outputs"]),
        "initialized_trace_checked": True,
        "replay_cycles": len(traffic),
        "replay_output_values": sum(len(row) for edge in expected for row in edge if row is not None),
    }
    if swap_outputs is not None:
        report["output_swap"] = check_output_swap(
            run, tools, directory, rtl, tb, descriptor, mlir, design, swap_outputs, extra_lean_paths
        )
    return report
