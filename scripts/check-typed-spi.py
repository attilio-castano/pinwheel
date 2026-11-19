#!/usr/bin/env python3
"""Certify the typed depth-two SPI engine and replay its public pins."""

import argparse
import json
from pathlib import Path

import spi_typed_replay
import streaming_ready_artifacts as artifacts
import streaming_ready_composition as composition
import streaming_ready_wrapper_readback as wrappers
import typed_module_checks as checks
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
ADDR_BITS = 1
SOURCE_PROOF = "Pinwheel.Hardware.StreamingReady.SPISession"
TYPED_MODULE = "Pinwheel.Hardware.StreamingReady.TypedExport"


def certify(run, tools, out, emitted, replay, report):
    gate = artifacts.load_gate()
    proof_dirs, proof_modules = [], []
    report["components"] = {}
    for kind in ("core", "frontend"):
        directory = out / kind

        def scope(command, name, **options):
            return run(command, f"{kind}-{name}", **options)

        result = artifacts.component(kind, ADDR_BITS, emitted, directory, tools, scope, gate=gate)
        if (directory / f"{kind}.sv").read_bytes() != (replay / "typed" / f"{kind}.sv").read_bytes():
            raise RuntimeError(f"Certified {kind} RTL differs from the RTL used in pin replay")
        report["components"][kind] = result
        proof_dirs.append(directory / "proof")
        proof_modules.extend(result["compiled_modules"])

    report["wrappers"] = wrappers.certify(
        ADDR_BITS, replay / "package.sv", replay / "tt.sv", out / "wrappers", tools, run, gate=gate
    )
    proof_dirs.append(Path(report["wrappers"]["proof_directory"]))
    proof_modules.append(report["wrappers"]["module"])

    directory = out / "composition"
    directory.mkdir()
    ((module, source),) = composition.generate(ADDR_BITS).items()
    (directory / f"{module}.lean").write_text(source)
    imports = [line.removeprefix("import ") for line in source.splitlines() if line.startswith("import Pinwheel.")]
    run([tools["lake"], "--no-cache", "build", *imports], "build-spi-composition-dependencies", timeout=1800)
    gate.compile_lean(run, tools, directory, module, paths=proof_dirs)

    join = "StreamingReadyTypedSPIProof"
    (directory / f"{join}.lean").write_bytes((ROOT / f"test/{join}.lean").read_bytes())
    gate.compile_lean(run, tools, directory, join, paths=proof_dirs)
    audit = gate.audit_source((ROOT / "test/ProofAudit.lean").read_text(),
                             [*proof_modules, module, join], root_module=join)
    audit_module = "TypedSPIAudit"
    (directory / f"{audit_module}.lean").write_text(audit)
    report["axiom_audit"] = gate.compile_lean(run, tools, directory, audit_module, paths=proof_dirs).strip()
    report["spi_proofs"] = dict(source=f"{SOURCE_PROOF}.completed_release",
                               artifact="Pinwheel.Artifact.StreamingReadyTypedSPI.completed_release")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    out = fresh_directory(ROOT / "build/typed-spi", parser.parse_args().tag)
    logs = out / "logs"
    logs.mkdir()
    report = dict(passed=False, addr_bits=ADDR_BITS, commands=[])
    run = Commands(ROOT, logs, report["commands"])

    try:
        manifest, tools, paths = checks.tool_config()
        tools["solver"] = tools["z3"]
        report["toolchain"] = manifest
        report["tool_sha256"] = checks.cad.tool_hashes(paths)
        prefix = Path(run(["lake", "env", "lean", "--print-prefix"], "lean-toolchain").strip())
        tools["lake"] = prefix / "bin/lake"
        run([tools["lake"], "--no-cache", "build", TYPED_MODULE, SOURCE_PROOF,
             "Pinwheel.Hardware.StreamingReady.CoreEmit", "Pinwheel.Hardware.Streaming.FrontendEmit",
             "Pinwheel.Hardware.StreamingReady.Readback", "Pinwheel.Hardware.StreamingReady.TinyWiring"],
            "build-spi-source", timeout=1800)

        legacy, typed = out / "legacy-emitted", out / "typed-emitted"
        for label, directory, entry in (("legacy", legacy, "StreamingReadyArtifactEmit"),
                                        ("typed", typed, "StreamingReadyTypedEmit")):
            run([tools["lake"], "env", "lean", "-DwarningAsError=true", "--run",
                 f"test/{entry}.lean", directory, str(ADDR_BITS)], f"emit-{label}")

        replay = out / "pin-replay"
        report["replay"] = spi_typed_replay.replay(run, tools, replay, legacy, typed)
        for stem, name, options in (("core", "assembly.json", {"addr_bits": ADDR_BITS}),
                                    ("frontend", "frontend-assembly.json", {})):
            descriptor = spi_typed_replay.legacy_assembly(typed / f"{stem}-interface.json", **options)
            (typed / name).write_text(json.dumps(descriptor, indent=2) + "\n")

        certify(run, tools, out, typed, replay, report)
        evidence = [*typed.iterdir(), *legacy.iterdir(), *replay.glob("*.sv"),
                    *replay.glob("*/*.sv"), *replay.glob("*/wire.bin")]
        report["sha256"] = {str(path.relative_to(out)): sha(path) for path in sorted(evidence)}
        report["passed"] = True
    except BaseException as error:
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified typed SPI source artifacts and pin replay. Report at {out / 'report.json'}")


if __name__ == "__main__":
    main()
