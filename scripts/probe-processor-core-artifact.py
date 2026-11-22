#!/usr/bin/env python3
"""Check the exact tapped processor core retained by a passing cold-boot run.

Solver scope checks both graphs and audits directly reducible typed endpoints.
Kernel scope additionally requires the complete Lean correspondence theorem.
The exact tapped core leaf has 37 next-state and 67 output endpoints.
"""

from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import time
import typed_circuit_readback as readback
import readback_miter
from typed_artifact_runner import compile_modules
from readback_control_proofs import split_two_bit_controls
from readback_slice_proofs import prove_slice_bounds
from readback_mux_proofs import add_mux_algebra

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "cold_boot", ROOT / "scripts/check-processor-loadable-system-boot.py"
)
cold = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cold)
rr = cold.rr


def sources():
    result = cold.source_hashes()
    pending = [ROOT / "Pinwheel/Hardware/Processor/CoreCertified.lean"]
    seen = set()
    while pending:
        p = pending.pop()
        if p in seen:
            continue
        seen.add(p)
        result[str(p.relative_to(ROOT))] = rr.sha(p)
        for line in p.read_text().splitlines():
            if m := re.match(r"^import\s+(.+)$", line):
                pending.extend(
                    ROOT / (name.replace(".", "/") + ".lean")
                    for name in m[1].split("--")[0].split()
                    if name.startswith("Pinwheel.")
                )
    for p in (
        *readback.source_paths(),
        Path(__file__),
        ROOT / "scripts/readback_guard_proofs.py",
        ROOT / "Pinwheel/Hardware/Readback/Guard.lean",
        ROOT / "Pinwheel/Hardware/Readback/SourceBinding.lean",
        ROOT / "scripts/readback_control_proofs.py",
        ROOT / "scripts/readback_slice_proofs.py",
        ROOT / "scripts/readback_mux_proofs.py",
        ROOT / "scripts/readback_miter.py",
        ROOT / "Pinwheel/Hardware/Readback/Mux.lean",
        ROOT / "test/HardwareReadbackMux.lean",
        ROOT / "test/test_readback_mux_proofs.py",
        ROOT / "test/test_typed_circuit_readback.py",
    ):
        result[str(p.relative_to(ROOT))] = rr.sha(p)
    return dict(sorted(result.items()))


def verify_cold(receipt, manifest, tool_hashes):
    data = json.loads(receipt.read_text())
    if (
        data.get("status") != "passed"
        or data.get("source_sha256") != cold.source_hashes()
        or data.get("tool_sha256") != tool_hashes
        or data.get("tool_manifest") != manifest
    ):
        raise ValueError("Cold boot source/tool receipt is stale or incomplete")
    for name, digest in data.get("artifact_sha256", {}).items():
        p = receipt.parent / name
        if (
            not p.resolve().is_relative_to(receipt.parent.resolve())
            or p.is_symlink()
            or rr.sha(p) != digest
        ):
            raise ValueError("Changed cold artifact " + name)
    inventory = {
        str(p.relative_to(receipt.parent))
        for p in receipt.parent.rglob("*")
        if p.is_file() and p.resolve() != receipt.resolve()
    }
    if not data.get("artifact_sha256") or set(data["artifact_sha256"]) != inventory:
        raise ValueError("Incomplete cold artifact inventory")
    if not data.get("commands") or any(
        x.get("exit_code") != 0 or x.get("error") for x in data["commands"]
    ):
        raise ValueError("Failed cold command")
    system = receipt.parent / "system"
    descriptor = cold.validate_descriptor(
        json.loads((system / "interface.json").read_text())
    )
    cold.validate_topology(descriptor, (system / "top.sv").read_text())
    return system, descriptor


def profile():
    return """import Pinwheel.Hardware.Processor.CoreCertified
import Pinwheel.Hardware.Processor.SystemExport
abbrev Input := Processor.CoreInterface.Input
abbrev Register := Processor.CoreCircuit.Register
abbrev Output := Stream.Joint Processor.CoreInterface.Output Register
abbrev circuit := Processor.SystemExport.tapped Processor.CoreCircuit.circuit
abbrev inputs := Processor.CoreInterface.inputs
abbrev registers := Processor.CoreCircuit.registers
abbrev outputs := Processor.SystemExport.tapInterface Processor.CoreInterface.outputs registers
"""


def generate(directory, solver, cadical, scope):
    data = json.loads((directory / "interface.json").read_text())
    modules, evidence = readback.generate(
        directory,
        data,
        directory / "core.mlir",
        directory / "import.json",
        solver,
        profile=profile(),
        compact=True,
        guard_solver=cadical if scope != "solver" else None,
        guard_outputs=("out_state_15", "out_state_16"),
        focused=scope == "writeback",
    )
    evidence["finite_control_proof_search"] = split_two_bit_controls(directory, modules)
    evidence["slice_bound_proof_search"] = prove_slice_bounds(directory, modules)
    evidence["mux_algebra_proof_search"] = add_mux_algebra(directory, modules)
    if evidence["endpoints"] != (2 if scope == "writeback" else 104):
        raise AssertionError("Incomplete core next/output/tap coverage")
    (directory / "generation.json").write_text(
        json.dumps(dict(modules=modules, evidence=evidence), indent=2) + "\n"
    )


def graph_keys(graph, intern):
    """Syntactic matches only schedule cheap proofs. Lean checks each equation."""
    keys, sizes = {}, {}
    for name, node in graph.nodes.items():
        children = tuple(keys[child] for child in node.args)
        key = (node.width, node.op, node.value, children)
        keys[name] = intern.setdefault(key, len(intern))
        sizes[name] = 1 + sum(sizes[child] for child in node.args)
    return keys, sizes


def check_direct(run, directory, descriptor, rb, source, actual):
    registers = {p["reference"] for p in descriptor["registers"]}
    taps = descriptor["state_taps"]
    if taps.keys() != registers or len(set(taps.values())) != len(taps):
        raise ValueError("Incomplete or duplicate core state taps")
    if any(actual.outputs[port] != ref for ref, port in taps.items()):
        raise ValueError("Incorrect state tap in imported core")

    def endpoint(graph, node, namespace):
        item = graph.nodes[node]
        if item.op in ("input", "reg", "lit"):
            return graph.expression(item, None)
        return f"{namespace}.{node} i s"

    intern = {}
    left, sizes = graph_keys(source, intern)
    right, _ = graph_keys(actual, intern)
    lines = ["import Graphs", readback.HEADER]
    checked = {"next": [], "output": []}
    hints = {"next": [], "output": []}
    for kind, ports, lhs, rhs, operation in (
        ("next", rb.REGISTERS, source.next, actual.next, "step"),
        ("output", rb.OUTPUTS, source.outputs, actual.outputs, "observe"),
    ):
        for name, (_, ctor) in ports.items():
            sn, rn = lhs[name], rhs[name]
            if sizes[sn] > 64:
                continue
            common = f"circuit.{operation} i s {ctor}"
            params = "(i : Values Input) (s : Values Register)"
            lines.append(
                f"theorem direct_hint_{ctor} {params} : {endpoint(source, sn, 'Source')} = {common} := by rfl"
            )
            hints[kind].append(name)
            if left[sn] == right[rn]:
                lines.append(
                    f"theorem direct_rtl_{ctor} {params} : {endpoint(actual, rn, 'RTL')} = {common} := by rfl"
                )
                checked[kind].append(name)
    if not set(taps.values()).issubset(checked["output"]):
        raise ValueError("Missing typed state tap theorem")
    (directory / "DirectEndpoints.lean").write_text(
        "\n".join(lines + ["end Pinwheel.TypedArtifact", ""])
    )
    audit = (
        (directory / "Audit.lean")
        .read_text()
        .replace("import Proof", "import DirectEndpoints")
    )
    (directory / "DirectAudit.lean").write_text(audit)
    compile_modules(
        run, directory, ["Design", "Graphs", "DirectEndpoints", "DirectAudit"]
    )
    if "standard axioms only" not in (directory / "DirectAudit.log").read_text():
        raise AssertionError("Missing direct endpoint axiom audit")
    return {"rtl_to_typed": checked, "source_to_typed": hints}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag")
    parser.add_argument("--cold-report", type=Path)
    parser.add_argument("--scope", choices=("kernel", "solver", "writeback"), default="kernel")
    parser.add_argument("--generate", type=Path)
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--cadical", type=Path)
    args = parser.parse_args()
    if args.generate:
        if not args.solver:
            parser.error("--generate requires --solver")
        generate(args.generate, args.solver, args.cadical, args.scope)
        return
    if not args.tag or not args.cold_report:
        parser.error("--tag and --cold-report required")
    out = rr.fresh_directory(ROOT / "build/processor-core-artifact", args.tag)
    directory = out / "core"
    directory.mkdir()
    report = dict(
        schema=1,
        status="running",
        commands=[],
        scope=args.scope,
        kernel_correspondence=False,
    )
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"] = manifest
        baseline, descriptor = verify_cold(
            args.cold_report.resolve(), manifest, rr.tool_hashes(paths)
        )
        report["cold_report"] = dict(
            path=str(args.cold_report.resolve()), sha256=rr.sha(args.cold_report)
        )
        shutil.copyfile(args.cold_report, out / "cold-report.json")
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_sha256"] = rr.tool_hashes(paths)
        cadical = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin/cadical"
        report["cadical_sha256"] = rr.sha(cadical)
        run(
            ["lake", "build", "Pinwheel.Hardware.Readback.Mux", "Pinwheel.Hardware.Readback.Guard",
             "Pinwheel.Hardware.Readback.SourceBinding"],
            "mux-helper-build",
            timeout=120,
        )
        run(
            [
                "lake",
                "env",
                "lean",
                "-DwarningAsError=true",
                "test/HardwareReadbackMux.lean",
            ],
            "mux-helper-audit",
            timeout=120,
        )
        run(
            ["python3", "test/test_readback_mux_proofs.py"],
            "mux-helper-tests",
            timeout=120,
        )
        run(
            ["python3", "test/test_typed_circuit_readback.py"],
            "typed-import-tests",
            timeout=120,
        )
        leaf = descriptor["leaf_interfaces"][0]
        readback.validate_descriptor(leaf)
        if len(leaf["registers"]) != 37 or len(leaf["outputs"]) != 67:
            raise ValueError("Incomplete tapped core leaf")
        (directory / "interface.json").write_text(json.dumps(leaf, indent=2) + "\n")
        for name in ("core.mlir", "core.sv"):
            shutil.copyfile(baseline / name, directory / name)
        script = directory / "import.ys"
        script.write_text(
            f"read_verilog -sv {rr.yosys_quote(directory / 'core.sv')}\nhierarchy -check -top {leaf['module']}\nflatten -noscopeinfo\nproc\nwrite_json {rr.yosys_quote(directory / 'before-pmuxtree.json')}\npmuxtree\nopt_clean\ncheck -assert\nwrite_json {rr.yosys_quote(directory / 'import.json')}\n"
        )
        run([tools["yosys"], "-Q", "-T", "-s", script], "core-import", timeout=120)
        rb = readback.importer(leaf)
        source = rb.read_hints(directory / "core.mlir")
        actual = rb.read_rtl(directory / "import.json")
        report["solver_check"] = readback_miter.check(
            run, tools, rb, source, actual, directory
        )
        run(
            [
                "python3",
                Path(__file__),
                "--generate",
                directory,
                "--solver",
                tools["z3"],
                "--scope", args.scope, "--cadical", cadical,
            ],
            "core-generate",
            timeout=180,
        )
        generation = json.loads((directory / "generation.json").read_text())
        report["evidence"] = generation["evidence"]
        report["direct_kernel"] = check_direct(run, directory, leaf, rb, source, actual)
        if args.scope in ("kernel", "writeback"):
            remaining = [
                m for m in generation["modules"] if m not in ("Design", "Graphs")
            ]
            compile_modules(run, directory, remaining, timeout=120)
            if "standard axioms only" not in (directory / "Audit.log").read_text():
                raise AssertionError("Missing complete core audit")
            report["kernel_correspondence"] = args.scope == "kernel"
            report["checked_writeback"] = True
        if rr.sha(cadical) != report["cadical_sha256"]:
            raise RuntimeError("SAT tool changed")
        if report["source_sha256"] != sources() or report[
            "tool_sha256"
        ] != rr.tool_hashes(paths):
            raise RuntimeError("Source/tool drift")
        report["status"] = "passed"
    except BaseException as e:
        report["status"], report["error"] = "failed", f"{type(e).__name__}: {e}"
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 3)
        report["artifact_sha256"] = {
            str(p.relative_to(out)): rr.sha(p)
            for p in sorted(out.rglob("*"))
            if p.is_file()
        }
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
