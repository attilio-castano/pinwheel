"""Regenerate the four byte-bound RTL files for the frozen 8x4 entry."""

import argparse
import hashlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tarfile

from streaming_8x4_e982_native import read, require, sha, write
from streaming_8x4_hold_cap_physical import ROOT, TARGET, TRIAL


SOURCE = "a305a4b339767e80719c9720a12ced7345b0e814"
BUNDLE = TRIAL / "rehearsal-01/bundle"
BUNDLE_MANIFEST = "0533dfb6c6ddf203a43f8b2a5cd67a399e6deb1a3afa2911a1d0b00646b4158f"
SCHEMA = "pinwheel.streaming-8x4-jane-street-source.v1"
TOP = "tt_um_pinwheel_streaming_ready_d2"
# Source files consumed by the October physical parent, before the layout ECOs.
RTL = {
    "core.sv": "c3ae379437eac2d1ae60c23ec244099aae070037ad1b884cbe40243f7b558db6",
    "frontend.sv": "5d7f6261335f647b94b0ad21ff1a3f292f5d83a5bd27a1937e6ca203708f9e6c",
    "package.sv": "369f4594953ddf44e073587556121c31efcdcb743d48f5612a9982f54753fc12",
    "tt.sv": "a6d52749a2e6797d21a9704834be14436127f637bc220989b834593c29a0e21e",
}
RTL_PREPARE = """
import json
from pathlib import Path
import sys
from streaming_ready_artifacts import lowering_copy, LOWERING_PASSES
from streaming_ready_wrapper import bridge_source, package_source, tt_source

out = Path(sys.argv[1])
emitted = out / 'emitted'
for name in ('core', 'frontend'):
    lowering_copy(emitted / (name + '.mlir'), emitted / (name + '-lowering.mlir'))
core = json.loads((emitted / 'assembly.json').read_bytes())
frontend = json.loads((emitted / 'frontend-assembly.json').read_bytes())
(out / 'src/package.sv').write_text(package_source(core, frontend))
(out / 'src/tt.sv').write_text(tt_source(2))
(out / 'bridge.sv').write_text(bridge_source(2))
(out / 'lowering-passes.json').write_text(json.dumps(LOWERING_PASSES) + '\\n')
"""


def record(path):
    return dict(sha256=sha(path), bytes=path.stat().st_size)


def extract_source(snapshot, expected):
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_NO_LAZY_FETCH="1", GIT_NO_REPLACE_OBJECTS="1", GIT_OPTIONAL_LOCKS="0")
    archive = subprocess.check_output(["git", "archive", SOURCE], cwd=ROOT, env=env, timeout=60)
    with tarfile.open(fileobj=io.BytesIO(archive)) as stream:
        files = [member.name for member in stream.getmembers() if member.isfile()]
        require(len(files) == len(set(files)) and set(expected) <= set(files) and
                all(member.isfile() or member.isdir() for member in stream.getmembers()),
                "Frozen Git archive omits bundle sources or has unsupported members")
        stream.extractall(snapshot, filter="data")
        inventory = {member.name: hashlib.file_digest(stream.extractfile(member), "sha256").hexdigest()
                     for member in stream.getmembers() if member.isfile()}
    require(all(inventory.get(name) == digest for name, digest in expected.items()) and
            all(sha(snapshot / name) == digest for name, digest in inventory.items()),
            "Frozen Git archive and extracted source differ")
    return hashlib.sha256(archive).hexdigest(), inventory


def run(out, lean_bin, circt, iverilog, vvp, jobs):
    require(out.is_relative_to(ROOT / "build") and not out.exists(), "Use a fresh output below build/")
    manifest_path = BUNDLE / "manifest.json"
    require(sha(manifest_path) == BUNDLE_MANIFEST, "Wrong frozen rehearsal manifest")
    manifest = read(manifest_path)
    require(manifest["source_commit"] == SOURCE and manifest["gds_sha256"] == TARGET["gds_sha256"],
            "Wrong frozen design or source checkpoint")
    tools = dict(lean=lean_bin / "lean", lake=lean_bin / "lake", circt=circt, iverilog=iverilog, vvp=vvp)
    tool_receipt = {name: record(path) for name, path in tools.items()}
    snapshot = out / "snapshot"
    src = out / "src"
    src.mkdir(parents=True)
    archive_sha, snapshot_hashes = extract_source(snapshot, manifest["source_sha256"])
    env = {name: value for name, value in os.environ.items()
           if not name.startswith(("LEAN_", "LAKE_", "CIRCT_", "IVERILOG_", "VVP_", "PYTHON"))}
    env.update(PATH=str(lean_bin) + os.pathsep + env.get("PATH", os.defpath), LEAN_NUM_THREADS=str(jobs))
    commands = []

    def capture(label, argv, output=None, timeout=1800):
        argv = [str(arg) for arg in argv]
        log = out / (label + ".log")
        output = output or log
        commands.append(dict(label=label, argv=argv, output=output.relative_to(out).as_posix()))
        with log.open("xb") as err:
            if output == log:
                subprocess.run(argv, cwd=snapshot, env=env, stdout=err, stderr=subprocess.STDOUT,
                               check=True, timeout=timeout)
            else:
                with output.open("xb") as std:
                    subprocess.run(argv, cwd=snapshot, env=env, stdout=std, stderr=err, check=True, timeout=timeout)

    capture("lean-version", [tools["lean"], "--version"], timeout=60)
    capture("circt-version", [circt, "--version"], timeout=60)
    capture("iverilog-version", [iverilog, "-V"], timeout=60)
    require("version 4.33.1" in (out / "lean-version.log").read_text() and
            "firtool-1.159.0" in (out / "circt-version.log").read_text(), "Unexpected Lean or CIRCT release")
    capture("lean-build", [tools["lake"], "--no-cache", "build", "Pinwheel.Hardware.StreamingReady.CoreEmit",
                           "Pinwheel.Hardware.Streaming.FrontendEmit"])
    capture("lean-emit", [tools["lake"], "env", tools["lean"], "-DwarningAsError=true", "--run",
                          "test/StreamingReadyArtifactEmit.lean", out / "emitted", "1"])
    prepare = "import sys; sys.path.insert(0, 'scripts')\n" + RTL_PREPARE
    capture("prepare-rtl", [sys.executable, "-B", "-c", prepare, out])
    for name in ("core", "frontend"):
        capture(name + "-lower", [circt, out / "emitted" / (name + "-lowering.mlir"),
                                  *read(out / "lowering-passes.json")], src / (name + ".sv"))
    files = {"src/" + name: record(src / name) for name in RTL}
    require({Path(name).name: row["sha256"] for name, row in files.items()} == RTL,
            "Generated RTL differs from the byte-bound physical parent")
    ordered = [src / name for name in RTL]
    capture("top-compile", [iverilog, "-g2012", "-s", TOP, "-o", out / "design.vvp", *ordered])
    bridge = out / "bridge.vvp"
    capture("bridge-compile", [iverilog, "-g2012", "-s", "streaming_quad_host_bridge", "-o", bridge,
                               *ordered, out / "bridge.sv"])
    dry_path = out / "bringup.json"
    capture("bringup", [sys.executable, "-B", "scripts/streaming_8x4_bringup.py", "simulate", "--vvp", vvp,
                        "--executable", bridge, "--executable-sha256", sha(bridge)], dry_path)
    reference = manifest["payload"]["bringup_dry_run"]
    reference_path = BUNDLE / reference["path"]
    require(sha(reference_path) == reference["sha256"], "Frozen bring-up receipt changed")
    dry = read(dry_path)
    frozen_dry = read(reference_path)
    # The RTL and placed-cell models have different executable digests. Their public trace results agree.
    require(dry.pop("model_sha256") == sha(bridge) and frozen_dry.pop("model_sha256") and dry == frozen_dry,
            "Generated RTL bring-up observations differ from frozen implementation")
    require(sha(manifest_path) == BUNDLE_MANIFEST and
            all(sha(snapshot / name) == digest for name, digest in snapshot_hashes.items()) and
            files == {name: record(out / name) for name in files} and
            tool_receipt == {name: record(path) for name, path in tools.items()}, "Source or tool bytes changed")
    write(out / "receipt.json", dict(schema=SCHEMA, passed=True, source_commit=SOURCE,
          target_gds_sha256=TARGET["gds_sha256"], target_odb_sha256=TARGET["odb_sha256"], top=TOP,
          bundle_manifest_sha256=BUNDLE_MANIFEST, source_archive_sha256=archive_sha,
          source_files=len(snapshot_hashes), files=files, tools=tool_receipt, commands=commands,
          producer=record(Path(__file__)), compiled_top=record(out / "design.vvp"),
          bringup=record(dry_path), bringup_cases=sorted(dry["cases"]), board_exercised=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("out", "lean-bin", "circt", "iverilog", "vvp"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--jobs", type=int, choices=range(1, 5), default=3)
    args = parser.parse_args()
    run(args.out.resolve(), args.lean_bin.resolve(strict=True), args.circt.resolve(strict=True),
        args.iverilog.resolve(strict=True), args.vvp.resolve(strict=True), args.jobs)


if __name__ == "__main__":
    main()
