#!/usr/bin/env python3
"""Prove the fetch boundary and replay the emitted combined I2C read."""

import argparse
import json
from pathlib import Path
import subprocess

from reactive_fetch_replay import replay
from typed_module_checks import tool_config
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
REPLAY_FILES = ("scripts/reactive_fetch_replay.py", "scripts/i2c_read_peers.py", "scripts/pad_io.py",
                "scripts/pinwheel_sim.py", "scripts/pinwheel_host.py", "scripts/protocol_results.py",
                "scripts/validation_run.py", "scripts/process_group.py", "scripts/typed_module_checks.py",
                "test/reactive_fetch_bridge.sv", "test/ReactiveRegisteredFetch.lean")


def timing_examples(cases):
    examples = ["import Pinwheel.I2C.RegisterReadFetch", "open Pinwheel.I2C.RegisterReadFetch"]
    timings = {}
    for name, case in sorted(cases.items()):
        aperture = case["ack_aperture"]
        timing = ", ".join(str(aperture["timing"][key]) for key in ("rise", "sample", "fall", "nextRise"))
        window = ", ".join(str(aperture["window"][key]) for key in ("earliestSample", "latestSample", "lowLimit"))
        timings[name] = timing
        sign = "¬ " if name == "read-late" else ""
        examples.append(f"example : {sign}(⟨{timing}⟩ : AckTiming).Fits ⟨{window}⟩ := by\n"
                        "  decide +kernel")
    for name, case in sorted(timings.items()):
        scenario, variant = name.rsplit("-", 1)
        if variant == "baseline":
            continue
        baseline = timings[f"{scenario}-baseline"]
        hold = "holdLow" if variant == "low" else "holdHigh"
        examples.append(f"example : (⟨{baseline}⟩ : AckTiming).{hold} 1 = ⟨{case}⟩ := by decide +kernel")
    return "\n\n".join(examples) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    out = fresh_directory(ROOT / "build/i2c-fetch-retiming", parser.parse_args().tag)
    logs = out / "logs"
    logs.mkdir()
    report = dict(passed=False, commands=[], source_commit=subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(), source_sha256={})
    sources = sorted((ROOT / "Pinwheel").rglob("*.lean"))
    sources.extend(ROOT / name for name in (*REPLAY_FILES, "Pinwheel.lean", "test/ProofAudit.lean",
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "tools/hardware-toolchain.json"))
    sources.append(Path(__file__).resolve())

    def source_hashes():
        return {str(path.relative_to(ROOT)): sha(path) for path in sources}

    report["source_sha256"] = source_hashes()
    run = Commands(ROOT, logs, report["commands"])
    try:
        manifest, tools, _ = tool_config()
        report["toolchain"] = manifest
        lean = ["lake", "env", "lean", "-DwarningAsError=true"]
        run(["lake", "--no-cache", "build"], "build-library", timeout=1800)
        run([*lean, "test/ProofAudit.lean"], "audit-library")
        emitted = out / "emitted"
        run([*lean, "--run", "test/ReactiveRegisteredFetch.lean", emitted], "emit-fetch-variants")
        emitted_hashes = {path.name: sha(path) for path in emitted.iterdir()}
        report["replay"] = replay(run, tools, emitted, out / "replay")
        examples = out / "MeasuredAckTiming.lean"
        examples.write_text(timing_examples(report["replay"]["cases"]))
        run([*lean, examples], "check-measured-ack-windows")
        current = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        if current != report["source_commit"] or source_hashes() != report["source_sha256"]:
            raise RuntimeError("Source inputs changed during verification")
        if emitted_hashes != {path.name: sha(path) for path in emitted.iterdir()}:
            raise RuntimeError("Emitted inputs changed during replay")
        report["artifact_sha256"] = {str(path.relative_to(out)): sha(path)
                                     for path in sorted(out.rglob("*")) if path.is_file()}
        report["passed"] = True
    except BaseException as error:
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified I2C fetch retiming. Report at {out / 'report.json'}")


if __name__ == "__main__":
    main()
