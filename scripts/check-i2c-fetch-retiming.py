#!/usr/bin/env python3
"""Prove the fetch boundary and replay the emitted combined I2C read."""

import argparse
import json
from pathlib import Path
import subprocess

from pad_io import PadObservation
from reactive_fetch_replay import ACK_HIGH_PC, ACK_LOW_PC, ACK_SLOT, Edge, replay
from typed_module_checks import tool_config
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
REPLAY_FILES = ("scripts/reactive_fetch_replay.py", "scripts/i2c_read_peers.py", "scripts/pad_io.py",
                "scripts/pinwheel_sim.py", "scripts/pinwheel_host.py", "scripts/protocol_results.py",
                "scripts/validation_run.py", "scripts/process_group.py", "scripts/typed_module_checks.py",
                "test/reactive_fetch_bridge.sv", "test/ReactiveRegisteredFetch.lean")


def observed_ack(trace, expected_hash, timing):
    if sha(trace) != expected_hash:
        raise RuntimeError(f"ACK witness source changed: {trace}")
    rows = (json.loads(line) for line in trace.read_text().splitlines())
    edges = [Edge(row["cycle"], PadObservation(**row["pads"])) for row in rows]
    base = timing["rise"] - 1
    end = timing["nextRise"]
    window = [edge for edge in edges if base <= edge.cycle <= end]
    if [edge.cycle for edge in window] != list(range(base, end + 1)):
        raise RuntimeError(f"Missing or out-of-order ACK witness edges: {trace}")

    captures = [current for prior, current in zip(window, window[1:])
                if (prior.mode, prior.pc, prior.remaining, current.pc) == (3, ACK_HIGH_PC, 0, ACK_LOW_PC)]
    if len(captures) != 1 or captures[0].cycle != timing["sample"]:
        raise RuntimeError(f"ACK witness capture does not match the recorded hardware transition: {trace}")
    sampled = captures[0].sampled_raw
    value = bool(sampled & 2)
    observations = []
    for edge in window:
        raw = edge.pads.wires & 3
        logical = edge.pads.logical
        if edge.pads.known & 3 != 3 or logical.levels or logical.enabled & ~3:
            raise RuntimeError(f"ACK witness needs defined, open-drain pads: {trace}")
        drive = ", ".join(".low" if logical.enabled & bit else ".release" for bit in (1, 2))
        bus = ", ".join(str(bool(raw & bit)).lower() for bit in (1, 2))
        capture = "none"
        if edge.cycle + 1 == timing["sample"]:
            if raw != sampled or not raw & 1 or bool(captures[0].samples >> ACK_SLOT & 1) != value:
                raise RuntimeError(f"ACK witness does not have the captured value on the pre-edge bus: {trace}")
            capture = f"some ({ACK_SLOT}, {str(value).lower()})"
        observations.append(f"⟨⟨⟨{drive}⟩, ⟨{bus}⟩⟩, {capture}⟩")
    return base, str(value).lower(), "[" + ",\n    ".join(observations) + "]"


def timing_examples(cases, traces):
    examples = ["import Pinwheel.I2C.RegisterReadFetch", "open Pinwheel.I2C Pinwheel.I2C.RegisterReadFetch"]
    timings = {}
    for name, case in sorted(cases.items()):
        aperture = case["ack_aperture"]
        coords = aperture["timing"]
        keys = ("rise", "sample", "fall", "nextRise")
        timing = ", ".join(str(coords[key]) for key in keys)
        window = ", ".join(str(aperture["window"][key]) for key in ("earliestSample", "latestSample", "lowLimit"))
        timings[name] = timing
        sign = "¬ " if name == "read-late" else ""
        base, value, observations = observed_ack(traces / f"{name}.jsonl", case["trace_sha256"], coords)
        local_timing = ", ".join(str(coords[key] - base) for key in keys)
        examples.append(f"example : (⟨{local_timing}⟩ : AckTiming).Observed\n"
                        f"    {observations} {ACK_SLOT} {value} := by decide +kernel\n"
                        f"example : {sign}(⟨{local_timing}⟩ : AckTiming).Fits ⟨{window}⟩ := by decide +kernel")
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
        examples.write_text(timing_examples(report["replay"]["cases"], out / "replay"))
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
