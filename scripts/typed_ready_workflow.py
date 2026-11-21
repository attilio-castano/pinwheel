#!/usr/bin/env python3
"""Certify sampled-ready hardware once per configuration and verify its protocol clients."""

import argparse
import json
from pathlib import Path

import spi_typed_replay
import streaming_ready_artifacts as artifacts
import streaming_ready_composition as composition
import streaming_ready_wrapper_readback as wrappers
import typed_module_checks as checks
import typed_ready_engine
from buffered_rtl_session_full import SectionRun
from streaming_ready_compile import i2c_image, lean_certificate
from streaming_ready_wire_cases import check_i2c_cases, run_i2c_cases
from streaming_ready_wire_controls import check_controls, prepare_controls, run_ready_controls
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
READY = "Pinwheel.Hardware.StreamingReady"
ENGINE_MODULE = "StreamingReadyTypedEngine"
SPI_PROOF = "StreamingReadyTypedSPIProof"
I2C_PROOF = "StreamingReadyTypedI2CProof"
ETHERNET_PROOF = "StreamingReadyTypedEthernetProof"


def typed_engine_source(module, addr_bits):
    return f"""import {module}
import {READY}.TypedExport

namespace Pinwheel.Artifact.StreamingReadyTypedEngine
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady

abbrev addrBits : Nat := {addr_bits}
export {module} (physicalStep physicalObserve physicalRun physical_step_correct
  physical_observe_correct physical_run_correct embedded_engine_pins publicDrive
  publicDrive_correct publicDriveTrace publicDriveTrace_correct concrete_i2c_custody
  i2cBootPins PhysicalCustody)

theorem components_eq_export : {module}.components =
    ⟨.ofCircuit TypedExport.frontend.circuit,
     .ofCircuit (TypedExport.core addrBits (by decide)).circuit⟩ :=
  {module}.components_correct.eq_typed

end Pinwheel.Artifact.StreamingReadyTypedEngine
"""


def match_certified_rtl(path, engine, kind):
    if path.read_bytes() != engine.typed.rtl[kind].read_bytes():
        raise RuntimeError(f"Certified {kind} RTL differs from depth-{engine.depth} pin replay RTL")


def certify(run, tools, gate, out, typed, engine, frontend, frontend_report, clients, report, *, target_checks=""):
    addr_bits = engine.addr_bits
    core_dir = out / "core"
    report["core_certificate"] = artifacts.component(
        "core", addr_bits, typed, core_dir, tools, SectionRun(run, "core"), gate=gate
    )
    match_certified_rtl(core_dir / "core.sv", engine, "core")
    match_certified_rtl(frontend / "frontend.sv", engine, "frontend")

    wrapper = wrappers.certify(addr_bits, engine.package, engine.tt, out / "wrappers", tools, run, gate=gate)
    report["wrapper_certificate"] = wrapper
    proof_dirs = [core_dir / "proof", frontend / "proof", Path(wrapper["proof_directory"])]
    proof_modules = [*report["core_certificate"]["compiled_modules"],
                     *frontend_report["compiled_modules"], wrapper["module"]]

    directory = out / "composition"
    directory.mkdir()
    ((module, source),) = composition.generate(addr_bits).items()
    (directory / f"{module}.lean").write_text(source)
    imports = [line.removeprefix("import ") for line in source.splitlines() if line.startswith("import Pinwheel.")]
    run([tools["lake"], "--no-cache", "build", *imports], "build-composition-dependencies", timeout=1800)
    gate.compile_lean(run, tools, directory, module, paths=proof_dirs)

    (directory / f"{ENGINE_MODULE}.lean").write_text(typed_engine_source(module, addr_bits))
    gate.compile_lean(run, tools, directory, ENGINE_MODULE, paths=proof_dirs)
    for client in clients:
        name = f"{client}.lean"
        (directory / name).write_bytes((ROOT / "test" / name).read_bytes())
        gate.compile_lean(run, tools, directory, client, paths=proof_dirs)
    report["proof_modules"] = [module, ENGINE_MODULE, *clients]

    targets = "StreamingReadyTypedProofTargets"
    imports = "".join(f"import {client}\n" for client in clients)
    (directory / f"{targets}.lean").write_text(imports + target_checks)
    gate.compile_lean(run, tools, directory, targets, paths=proof_dirs)
    audit = gate.audit_source((ROOT / "test/ProofAudit.lean").read_text(),
                             [*proof_modules, *report["proof_modules"], targets], root_module=targets)
    audit_module = "StreamingReadyTypedAudit"
    (directory / f"{audit_module}.lean").write_text(audit)
    report["axiom_audit"] = gate.compile_lean(run, tools, directory, audit_module, paths=proof_dirs).strip()


def replay_i2c(run, tools, engine, directory):
    directory.mkdir()
    cases = run_i2c_cases(tools["vvp"], engine.typed.executable, directory / "cases", depth=engine.depth)
    check_i2c_cases(cases)
    inputs = [engine.typed.rtl["core"], engine.typed.rtl["frontend"],
              engine.package, engine.tt, engine.bridge]
    mutants = prepare_controls(inputs, directory / "mutants", tools, run)
    controls = run_ready_controls(tools["vvp"], engine.typed.executable, mutants, directory / "controls",
                                  depth=engine.depth)
    check_controls(controls)
    print(f"I²C depth {engine.depth} pin replay passed {len(cases['cases'])} cases and "
          f"{len(controls['controls'])} controls", flush=True)
    return dict(cases=cases, controls=controls)


def replay_ethernet(tools, engine, directory):
    from streaming_8x4_ethernet import replay_schedules

    directory.mkdir()
    traces = {name: directory / f"{name}.bin" for name in ("legacy", "typed")}
    legacy = replay_schedules(tools["vvp"], engine.legacy.executable, traces["legacy"])
    typed = replay_schedules(tools["vvp"], engine.typed.executable, traces["typed"])
    if legacy != typed or traces["legacy"].read_bytes() != traces["typed"].read_bytes():
        raise RuntimeError("Legacy and typed Ethernet schedule traces differ")
    print("Ethernet pin replay passed both refill policies and the missed-deadline control", flush=True)
    return dict(backends=dict(legacy=legacy, typed=typed), public_traces_identical=True)


def ethernet_target_checks(replay):
    """Bind the runtime peer evidence to the exact admitted Lean schedules."""
    typed = replay["backends"]["typed"]
    source = f"""
open Pinwheel.Program
open StreamingEthernetSchedule

set_option maxRecDepth 30000

example : (StreamingEthernetCore.image.words, StreamingEthernetCore.idlePins) =
  ({typed["words"]}, ⟨{typed["idle_levels"]}, {typed["idle_enabled"]}⟩) := by decide +kernel
"""
    for policy in ("uniform", "staggered"):
        cases = [case for case in typed["cases"] if case["name"] == policy]
        if not cases:
            raise RuntimeError(f"Ethernet replay omitted {policy} policy")
        for case in cases:
            first_sample = case["phy"]["first_rise"]
            launches = [burst["start"] - first_sample for burst in case["bursts"][1:]]
            payload = [f"{byte}#8" for byte in bytes.fromhex(case["phy"]["sampled_hex"])]
            # Replay records the pre-request cycle, one tick before Lean's launch cut.
            source += f"""
example : (List.finRange 8).map (fun i =>
    StreamingEthernetRefill.launch StreamingEthernetRefill.{policy} i - (firstSample + 1)) =
    {launches} := by decide +kernel

example : StreamingEthernetFrame.frameBytes = [{", ".join(payload)}] := by decide +kernel
"""
    (late,) = (case for case in typed["cases"] if case["name"] == "late")
    source += f"""
private def latePolicy : StreamingEthernetRefill.Policy :=
  fun i => ({late["refill_delays"]} : List Nat)[i.val]?.getD 0

example :
    let cut := firstSample - 2 + 6 * 64
    let body := StreamingEthernetRefill.bodyPins latePolicy {late["phy"]["high_ticks"]}
    let core := (preloaded.run StreamingEthernetCore.program false (body.take cut)).core
    core.phase = .boundary ∧ core.txConsumed = 64 ∧ core.canReserve = false := by
  decide +kernel
"""
    return source


def main(*, spi_only=False):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    if not spi_only:
        parser.add_argument("--ethernet-only", action="store_true",
                            help="check Ethernet refill policies at FIFO depth two")
    args = parser.parse_args()
    ethernet_only = not spi_only and args.ethernet_only
    matrix = not spi_only and not ethernet_only
    workflow = "typed-ethernet" if ethernet_only else ("typed-spi" if spi_only else "typed-ready")
    out = fresh_directory(ROOT / "build" / workflow, args.tag)
    logs = out / "logs"
    logs.mkdir()
    report = dict(schema="pinwheel.typed-ready-protocols.v1", passed=False, commands=[], configurations={})
    run = Commands(ROOT, logs, report["commands"])

    try:
        manifest, tools, paths = checks.tool_config()
        tools["solver"] = tools["z3"]
        report["toolchain"] = manifest
        report["tool_sha256"] = checks.cad.tool_hashes(paths)
        prefix = Path(run(["lake", "env", "lean", "--print-prefix"], "lean-toolchain").strip())
        tools["lake"] = prefix / "bin/lake"
        modules = ["TypedExport", "CoreEmit", "Readback", "TinyWiring"]
        if ethernet_only:
            modules.append("EthernetRefill")
            clients = [ETHERNET_PROOF]
        else:
            modules.append("SPISession")
            clients = [SPI_PROOF]
        if matrix:
            modules.append("I2CReadSession")
            clients.append(I2C_PROOF)
        run([tools["lake"], "--no-cache", "build", *(f"{READY}.{mod}" for mod in modules)],
            "build-ready-source", timeout=1800)
        if matrix:
            image_path = out / "i2c-image.lean"
            image_path.write_text(lean_certificate(i2c_image()))
            run([tools["lake"], "env", "lean", "-DwarningAsError=true", image_path], "check-i2c-image")

        gate = artifacts.load_gate()
        frontend = out / "shared-frontend"
        for addr_bits in ((1, 2) if matrix else (1,)):
            config_name = f"d{1 << addr_bits}"
            config = out / config_name
            result = dict(addr_bits=addr_bits)
            report["configurations"][config_name] = result

            scoped = SectionRun(run, config_name)
            legacy, typed = config / "legacy-emitted", config / "typed-emitted"
            for label, directory, entry in (("legacy", legacy, "StreamingReadyArtifactEmit"),
                                            ("typed", typed, "StreamingReadyTypedEmit")):
                scoped([tools["lake"], "env", "lean", "-DwarningAsError=true", "--run",
                        f"test/{entry}.lean", directory, str(addr_bits)], f"emit-{label}")
            engine = typed_ready_engine.prepare(run, tools, config / "engine", addr_bits, legacy, typed)
            evidence = [*typed.iterdir(), *legacy.iterdir(), *engine.out.rglob("*")]
            evidence = [path for path in evidence if path.is_file()]
            result["engine_sha256"] = {str(path.relative_to(out)): sha(path) for path in sorted(evidence)}

            target_checks = ""
            if ethernet_only:
                result["ethernet"] = replay_ethernet(tools, engine, config / "ethernet")
                target_checks = ethernet_target_checks(result["ethernet"])
            else:
                result["spi"] = spi_typed_replay.replay(tools, config / "spi", engine)
            if matrix:
                result["i2c"] = replay_i2c(scoped, tools, engine, config / "i2c")
            if addr_bits == 1:
                report["frontend_certificate"] = artifacts.component(
                    "frontend", addr_bits, typed, frontend, tools, SectionRun(run, "shared-frontend"), gate=gate
                )
            certify(scoped, tools, gate, config, typed, engine, frontend,
                    report["frontend_certificate"], clients, result, target_checks=target_checks)
            gate.assert_hashes(out, result["engine_sha256"])
        report["passed"] = True
    except BaseException as error:
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified sampled-ready protocol artifacts. Report at {out / 'report.json'}")


if __name__ == "__main__":
    main()
