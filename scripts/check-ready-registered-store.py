#!/usr/bin/env python3
"""Compare the Ready instruction stores through deadline and warm-reload sessions."""

import argparse
import json
from pathlib import Path
import subprocess

from ready_tx_fifo_replay import LATE_SLOT, SHORT_BUDGET, replay_late, replay_protocol_reload
from streaming_ready_artifacts import LOWERING_PASSES, lowering_copy
from streaming_ready_compile import i2c_image
from streaming_ready_wire_cases import check_deadline_alignment, require, run_i2c_case
from streaming_ready_wrapper import bridge_source, package_source, tt_source
from typed_module_checks import tool_config
from typed_ready_engine import legacy_assembly
from validation_run import Commands, fresh_directory, sha


ROOT = Path(__file__).resolve().parents[1]
EMITTERS = {
    "combinational": "StreamingReadyTypedEmit",
    "registered": "StreamingReadyRegisteredStoreEmit",
}
BUDGET_PROFILES = {31: "I2cProfile.standard", SHORT_BUDGET: "I2CReadSession.shortDeadlineProfile"}
RELOAD = "i2c-to-spi.bin"


def emit(run, lean, out):
    emitted = {}
    for store, emitter in EMITTERS.items():
        directory = out / (store + "-emitted")
        run([*lean, "--run", f"test/{emitter}.lean", directory, "1"], f"emit-{store}")
        emitted[store] = directory

    baseline, registered = emitted.values()
    for filename in ("frontend.mlir", "frontend-interface.json"):
        require((baseline / filename).read_bytes() == (registered / filename).read_bytes(),
                f"Instruction-store replacement changed shared {filename}")
    direct = legacy_assembly(baseline / "core-interface.json", addr_bits=1)
    cached = legacy_assembly(registered / "core-interface.json", addr_bits=1)
    added = [row for row in cached["registers"] if row not in direct["registers"]]
    remaining = [row for row in cached["registers"] if row not in added]
    require(dict(cached, registers=remaining) == direct, "Registered store changed the existing core interface")
    require(len(added) == 1 and added[0]["width"] == 64, "Expected one 64-bit instruction read register")
    require((baseline / "core.mlir").read_bytes() != (registered / "core.mlir").read_bytes(),
            "Expected distinct instruction stores")
    frontend = legacy_assembly(baseline / "frontend-interface.json")
    return emitted, direct, frontend, added


def lower(run, circt, source, directory, label):
    directory.mkdir(parents=True, exist_ok=True)
    prepared = directory / f"{source.stem}-lowering.mlir"
    lowering_copy(source, prepared)
    rtl = directory / f"{source.stem}.sv"
    rtl.write_text(run([circt, prepared, *LOWERING_PASSES], label, timeout=180))
    return rtl


def build_rtl(run, tools, out, emitted, core, frontend):
    shell = out / "shell"
    frontend_rtl = lower(run, tools["circt"], emitted["combinational"] / "frontend.mlir", shell,
                         "lower-frontend")
    package, tt, bridge = (shell / f"{name}.sv" for name in ("package", "tt", "bridge"))
    package.write_text(package_source(core, frontend))
    tt.write_text(tt_source(2))
    bridge.write_text(bridge_source(2))
    builds = {}
    for store, directory in emitted.items():
        rtl = lower(run, tools["circt"], directory / "core.mlir", out / store, f"lower-{store}")
        executable = rtl.parent / "bridge.vvp"
        run([tools["iverilog"], "-g2012", "-s", "streaming_quad_host_bridge", "-o", executable,
             rtl, frontend_rtl, package, tt, bridge], f"compile-{store}")
        builds[store] = executable
    require((out / "combinational/core.sv").read_bytes() != (out / "registered/core.sv").read_bytes(),
            "Lowering erased the instruction store distinction")
    return builds


def replay(vvp, executable, directory):
    directory.mkdir()
    reloaded = replay_protocol_reload(vvp, executable, directory / RELOAD)
    require(reloaded["exit_code"] == 0, "Warm reload failed to exit native RTL cleanly")
    cases = {}
    for budget in BUDGET_PROFILES:
        path = directory / f"budget-{budget}"
        image = i2c_image(wait_budget=budget, stretch_bound=budget - 3)
        last = run_i2c_case(vvp, executable, path / "last-poll", depth=2, direction="read",
                            profile="lastpoll", image=image)
        require(last["passed"], f"Last-poll read with budget {budget} failed: {last.get('error')}")
        peer = last["peer"]
        check_deadline_alignment(peer["deadline_alignment"], peer["deadline_trace"], budget=budget)
        require(last["image_words"] == list(image.words), "Last-poll image differs from the late-poll image")
        late = replay_late(vvp, executable, path / "late-poll", image, budget=budget)
        later = replay_late(vvp, executable, path / "late-poll-after-word", image,
                            budget=budget, deadline_slot=LATE_SLOT)
        terminal = later["observation"]["terminal_reply"]
        require((terminal["rx_start"], terminal["rx_valid"]) == (32, LATE_SLOT - 32),
                "Late poll did not retain one full RX word and the exact partial word")
        cases[budget] = dict(image_words=last["image_words"], last_poll=last, late_poll=late,
                             late_poll_after_word=later)
    return dict(warm_reload=reloaded, deadline_cases=cases)


def compare(out, replays):
    direct, registered = replays.values()
    require(direct["warm_reload"] == registered["warm_reload"], "Instruction store changed the warm reload receipt")
    require(direct["warm_reload"]["i2c"]["image_words"] == direct["deadline_cases"][31]["image_words"],
            "Warm reload did not use the validated standard I2C image")
    traces = [Path(RELOAD)]
    for budget in BUDGET_PROFILES:
        require(direct["deadline_cases"][budget]["image_words"] == registered["deadline_cases"][budget]["image_words"],
                f"Different instruction images at poll budget {budget}")
        traces.extend(Path(f"budget-{budget}") / case / "wire.bin"
                      for case in ("last-poll", "late-poll", "late-poll-after-word"))
    return {str(path): identical_trace(out, path) for path in traces}


def identical_trace(out, path):
    baseline = (out / "combinational-replay" / path).read_bytes()
    require(baseline == (out / "registered-replay" / path).read_bytes(),
            f"Registered store changed public pin trace {path}")
    require(baseline and len(baseline) % 20 == 0, f"Incomplete public pin trace {path}")
    return dict(edges=len(baseline) // 20, sha256=sha(out / "combinational-replay" / path))


def check_images(run, lean, out, data):
    path = out / "ReadyStoreReplayImages.lean"
    spi = data["warm_reload"]["spi"]["image_words"]
    cases = data["deadline_cases"]
    path.write_text(
        "import Pinwheel.Hardware.StreamingReady.ProtocolSwitch\n"
        "open Pinwheel.Hardware.StreamingReady Pinwheel.Program.StreamingReady\n\n"
        f"example : (Pinwheel.Program.StreamingSPI.image .mode0 3).words = {spi} := by decide +kernel\n"
        + "".join(
            f"example : (i2cImage {profile}).words = {cases[budget]['image_words']} := by decide +kernel\n"
            f"example : {profile}.budgetMinusOne.val + 1 = {budget} := by decide +kernel\n"
            for budget, profile in BUDGET_PROFILES.items()
        )
    )
    run([*lean, path], "check-replay-images")


def reactive_late_control(run, tag, commit):
    """Retain the isolated Reactive experiment's actual late-fetch timing control."""
    reactive_tag = f"ready-store-{tag}"
    run(["python3", "-B", "scripts/check-i2c-fetch-retiming.py", "--tag", reactive_tag],
        "reactive-late-fetch-control", timeout=1800)
    path = ROOT / "build/i2c-fetch-retiming" / reactive_tag / "report.json"
    report = json.loads(path.read_text())
    require(report["passed"] and report["source_commit"] == commit, "Late control used a different source revision")
    cases = report["replay"]["cases"]
    baseline, late = cases["read-baseline"], cases["read-late"]
    aperture = late["ack_aperture"]
    timing, window = aperture["timing"], aperture["window"]
    require(not aperture["sample_within_aperture"] and
            timing["sample"] > timing["rise"] + window["latestSample"],
            "Late fetch control did not cross its declared aperture")
    require((late["outcome"], late["samples"]) == (baseline["outcome"], baseline["samples"]),
            "Late fetch control changed the terminal result before timing was checked")
    return dict(engine="reactive", report=str(path.relative_to(ROOT)), report_sha256=sha(path),
                aperture=aperture, payload_bytes=late["wire"]["payload_bytes"],
                same_result=True)


def source_hashes():
    paths = [*ROOT.glob("Pinwheel/**/*.lean"), *ROOT.glob("test/*.lean"), *ROOT.glob("test/*.sv"),
             *ROOT.glob("scripts/*.py"), *(ROOT / name for name in (
                 "Pinwheel.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
                 "tools/hardware-toolchain.json"))]
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(paths)}


def source_commit():
    return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/ready-registered-store", args.tag)
    logs = out / "logs"
    logs.mkdir()
    report = dict(schema="pinwheel.ready-registered-store.v1", passed=False,
                  commands=[], replays={}, source_commit=source_commit(), source_sha256=source_hashes())
    run = Commands(ROOT, logs, report["commands"])
    try:
        report["toolchain"], tools, _ = tool_config()
        lean = ["lake", "env", "lean", "-DwarningAsError=true"]
        run(["lake", "--no-cache", "build"], "build-library", timeout=1800)
        run([*lean, "test/ProofAudit.lean"], "audit-library")
        emitted, core, frontend, report["added_registers"] = emit(run, lean, out)
        executables = build_rtl(run, tools, out, emitted, core, frontend)
        frozen = {path: sha(path) for path in out.rglob("*") if path.is_file() and path.parent != logs}
        for store, executable in executables.items():
            report["replays"][store] = replay(tools["vvp"], executable, out / (store + "-replay"))
        report["identical_public_traces"] = compare(out, report["replays"])
        check_images(run, lean, out, report["replays"]["combinational"])
        report["late_fetch_control"] = reactive_late_control(run, args.tag, report["source_commit"])
        require(source_commit() == report["source_commit"] and source_hashes() == report["source_sha256"],
                "Source inputs changed during verification")
        require(all(sha(path) == expected for path, expected in frozen.items()),
                "Generated hardware inputs changed during replay")
        report["artifact_sha256"] = {str(path.relative_to(out)): sha(path)
                                     for path in sorted(out.rglob("*")) if path.is_file()}
        report["passed"] = True
    except BaseException as error:
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified Ready instruction store substitution. Report at {out / 'report.json'}")


if __name__ == "__main__":
    main()
