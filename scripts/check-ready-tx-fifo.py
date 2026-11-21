#!/usr/bin/env python3
"""Verify the Ready depth-two TX FIFO substitution from source to public pins."""

import argparse
import json
from pathlib import Path

from buffered_rtl_session_full import SectionRun
import ready_tx_fifo_replay as replay
import streaming_ready_artifacts as artifacts
import streaming_ready_composition as composition
import streaming_ready_wrapper_readback as wrappers
import typed_module_checks as checks
from streaming_ready_wrapper import bridge_source, package_source, tt_source
from typed_ready_engine import legacy_assembly
from validation_run import Commands, fresh_directory


ROOT = Path(__file__).resolve().parents[1]
READY = "Pinwheel.Hardware.StreamingReady"
POINTERS = {"r_tx_head", "r_tx_tail"}
FIXTURE = "StreamingReadyTxShiftProof"


def emit(run, tools, out):
    ring, shift = out / "ring-emitted", out / "shift-emitted"
    for target, arguments, label in (("StreamingReadyTypedEmit", [ring, "1"], "ring"),
                                     ("StreamingReadyShiftEmit", [shift], "shift")):
        run([tools["lake"], "env", "lean", "-DwarningAsError=true", "--run",
             f"test/{target}.lean", *arguments], f"emit-{label}")
    inventories = dict(
        ring=legacy_assembly(ring / "core-interface.json", addr_bits=1),
        shift=legacy_assembly(shift / "core-interface.json", addr_bits=1),
        frontend=legacy_assembly(ring / "frontend-interface.json"),
    )
    baseline = inventories["ring"]
    expected = [entry for entry in baseline["registers"] if entry["name"] not in POINTERS]
    if len(baseline["registers"]) - len(expected) != 2:
        raise RuntimeError("The ring emitter omitted the two TX pointers")
    if inventories["shift"] != dict(baseline, registers=expected):
        raise RuntimeError("Shift must preserve the core ABI and omit exactly the TX pointers")
    if (ring / "core.mlir").read_bytes() == (shift / "core.mlir").read_bytes():
        raise RuntimeError("Expected different hardware implementations")
    for stem, name, entry in ((ring, "assembly.json", "ring"), (shift, "assembly.json", "shift"),
                              (ring, "frontend-assembly.json", "frontend")):
        (stem / name).write_text(json.dumps(inventories[entry], indent=2) + "\n")
    return inventories, ring, shift


def certify_composition(run, tools, gate, out, report):
    wrapper = report["wrapper_certificate"]
    proof_dirs = [out / key / "proof" for key in ("ring", "shift", "frontend")]
    proof_dirs.append(Path(wrapper["proof_directory"]))
    generated = [name for component in report["components"].values()
                 for name in component["compiled_modules"]]
    generated.append(wrapper["module"])
    directory = out / "composition"
    directory.mkdir()
    ((module, source),) = composition.generate(1).items()
    path = directory / f"{module}.lean"
    path.write_text(source)
    fixture = ROOT / "test" / f"{FIXTURE}.lean"
    imports = [line.removeprefix("import ") for text in (source, fixture.read_text())
               for line in text.splitlines() if line.startswith("import Pinwheel.")]
    run([tools["lake"], "--no-cache", "build", *imports], "build-composition-dependencies", timeout=1800)
    gate.compile_lean(run, tools, directory, module, paths=proof_dirs)
    (directory / fixture.name).write_bytes(fixture.read_bytes())
    gate.compile_lean(run, tools, directory, FIXTURE, paths=proof_dirs)
    audit = gate.audit_source((ROOT / "test/ProofAudit.lean").read_text(),
                             [*generated, module, FIXTURE], root_module=FIXTURE)
    (directory / "ReadyTxFifoAudit.lean").write_text(audit)
    report["axiom_audit"] = gate.compile_lean(run, tools, directory, "ReadyTxFifoAudit", paths=proof_dirs).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    out = fresh_directory(ROOT / "build/ready-tx-fifo", parser.parse_args().tag)
    logs = out / "logs"
    logs.mkdir()
    report = dict(schema="pinwheel.ready-tx-fifo.v1", passed=False, commands=[], components={}, replays={})
    run = Commands(ROOT, logs, report["commands"])

    try:
        manifest, tools, paths = checks.tool_config()
        tools["solver"] = tools["z3"]
        report["toolchain"] = manifest
        report["tool_sha256"] = checks.cad.tool_hashes(paths)
        prefix = Path(run(["lake", "env", "lean", "--print-prefix"], "lean-toolchain").strip())
        tools["lake"] = prefix / "bin/lake"
        modules = ("TypedExportShift", "TxShiftPackage", "Readback", "TinyWiring")
        run([tools["lake"], "--no-cache", "build", *(f"{READY}.{module}" for module in modules)],
            "build-ready-source", timeout=1800)
        inventories, ring, shift = emit(run, tools, out)
        report["removed_registers"] = sorted(POINTERS)
        gate = artifacts.load_gate()
        for name, kind, emitted, options in (
            ("frontend", "frontend", ring, {}),
            ("ring", "core", ring, {}),
            ("shift", "core", shift, {"tx_layout": "shift"}),
        ):
            report["components"][name] = artifacts.component(
                kind, 1, emitted, out / name, tools, SectionRun(run, name), gate=gate, **options
            )

        shell = out / "shell"
        shell.mkdir()
        package, tt, bridge = [shell / f"{name}.sv" for name in ("package", "tt", "bridge")]
        package.write_text(package_source(inventories["ring"], inventories["frontend"]))
        tt.write_text(tt_source(2))
        bridge.write_text(bridge_source(2))
        report["wrapper_certificate"] = wrappers.certify(1, package, tt, out / "wrappers", tools, run, gate=gate)
        frontend = out / "frontend/frontend.sv"
        replay_dirs = {}
        sources = [out / "ring/core.sv", out / "shift/core.sv", frontend, package, tt, bridge]
        report["rtl_sha256"] = {str(path.relative_to(out)): gate.digest(path) for path in sources}
        certify_composition(run, tools, gate, out, report)
        for name in ("ring", "shift"):
            replay_dirs[name] = out / f"{name}-replay"
            report["replays"][name] = replay.replay(
                SectionRun(run, name), tools, replay_dirs[name], inventories[name],
                [out / name / "core.sv", frontend, package, tt, bridge]
            )
        report["identical_public_traces"] = replay.compare(replay_dirs["ring"], replay_dirs["shift"])
        gate.assert_hashes(out, report["rtl_sha256"])
        report["passed"] = True
    except BaseException as error:
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified Ready TX FIFO substitution. Report at {out / 'report.json'}")


if __name__ == "__main__":
    main()
