"""Build the frozen release RTL through the stock Tiny Tapeout CMOS5L flow."""

import argparse
import fcntl
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tarfile
import tempfile
import time
import uuid

from streaming_8x4_bringup import DEPTH, simulate
from streaming_8x4_e982_native import ROOT, TOP, read, sha, write
from streaming_8x4_jane_street_behavior import PDK_MODELS, compile_model, succession
from streaming_8x4_jane_street_release import (
    ACTION, ASSETS, BUILD, GDS, PDK, PDK_REVISION, SUPPORT, TEMPLATE, TEMPLATE_DEF, TEMPLATE_SHA, record, run_precheck,
)
from streaming_8x4_jane_street_source import RTL, SOURCE
from streaming_8x4_tt_rehearsal import file_spec, require
from streaming_ready_wrapper import bridge_source
from streaming_tt_signoff import cleanup, python_environment


ENTRY = ROOT / "build/8x4-jane-street-entry-20261114"
HANDOFF = ENTRY / "release-01"
HANDOFF_SHA = "c0eff2d9fbdd395bf120c3eba742a4784021c74e9fbf760f8936bd45a3e010ba"
LL = "3.1.0.dev4"
IMAGE = "ghcr.io/librelane/librelane:" + LL
BASELINE = ("info.yaml", "LICENSE", "docs/info.md", *(f"src/{name}" for name in RTL))


def capture(argv, **kwargs):
    return subprocess.check_output(argv, text=True, timeout=30, **kwargs).strip()


def git_archive(repo, revision, destination, paths=()):
    with tempfile.TemporaryFile() as archive:
        subprocess.run(["git", "-C", str(repo), "archive", revision, *paths],
                       stdout=archive, check=True, timeout=60)
        archive.seek(0)
        with tarfile.open(fileobj=archive) as tar:
            tar.extractall(destination, filter="data")


def bindings(root, paths):
    return {path: sha(root / path) for path in sorted(paths)}


def stage(out, template, support, python):
    require(sha(HANDOFF / "handoff.json") == HANDOFF_SHA, "Wrong reviewed release handoff")
    handoff = read(HANDOFF / "handoff.json")
    files = {item["path"]: item for item in handoff["files"]}
    for name in BASELINE:
        file_spec(HANDOFF, files[name])
    require({name: files[f"src/{name}"]["sha256"] for name in RTL} == RTL, "Wrong generated RTL bytes")
    project = out / "project"
    project.mkdir(parents=True)
    git_archive(template, TEMPLATE, project, ("src/config.json",))
    git_archive(support, SUPPORT, project / "tt")
    require(sha(project / "tt" / TEMPLATE_DEF) == TEMPLATE_SHA, "Tiny Tapeout 8x4 DEF differs")
    for name in BASELINE:
        dest = project / name
        dest.parent.mkdir(exist_ok=True, parents=True)
        shutil.copyfile(HANDOFF / name, dest)
        file_spec(project, files[name])
    original = bindings(project, [*BASELINE, "src/config.json", *(
        item.relative_to(project).as_posix() for item in (project / "tt").rglob("*") if item.is_file())])
    env = python_environment(os.environ)
    env.update(PATH=str(python.parent) + os.pathsep + env["PATH"], XDG_CACHE_HOME=str(out / "cache"),
               YOWASP_CACHE_DIR=str(out / "cache/yowasp"), MPLCONFIGDIR=str(out / "matplotlib"))
    command = [str(python), "-B", "tt/tt_tool.py", "--create-user-config", "--pdk", PDK]
    with (out / "config.log").open("x") as log:
        subprocess.run(command, cwd=project, env=env, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=120)
    config_file = "src/config_merged.json"
    config = read(project / config_file)
    require(config["DESIGN_NAME"] == TOP and config["VERILOG_FILES"] == [f"dir::{name}" for name in RTL]
            and config["FP_DEF_TEMPLATE"] == f"dir::../tt/{TEMPLATE_DEF}" and config["RT_MAX_LAYER"] == "Metal4"
            and config["VDD_PIN"] == "VPWR" and config["GND_PIN"] == "VGND"
            and list(map(float, config["DIE_AREA"].split())) == [0, 0, 1724.16, 710.64],
            "Generated Tiny Tapeout build does not match the exact release sources and outline")
    require(bindings(project, original) == original and not (project / "runs").exists(),
            "Stock config generation changed inputs or found an existing run")
    write(out / "stage.json", dict(schema="pinwheel.streaming-8x4-tt-clean-stage.v1", handoff_sha256=HANDOFF_SHA,
        source_commit=SOURCE, template_commit=TEMPLATE, support_commit=SUPPORT, action_commit=ACTION,
        exact_rtl=RTL, config_command=command, pdk_revision=PDK_REVISION,
        inputs=bindings(project, [*original, config_file, "src/user_config.json"])))


def run(out, pdk, lease, timeout, jobs, memory):
    project = out / "project"
    staged = read(out / "stage.json")
    require(staged["schema"] == "pinwheel.streaming-8x4-tt-clean-stage.v1"
            and staged["handoff_sha256"] == HANDOFF_SHA and bindings(project, staged["inputs"]) == staged["inputs"],
            "Clean hardening inputs changed")
    require(not (project / "runs").exists(), "Select an unused staged directory for a clean build")
    pdk_source = pdk / PDK / "SOURCES"
    require(pdk_source.read_text().split() == ["IHP-Open-PDK", PDK_REVISION], "Wrong Ciel PDK revision")
    pdk_input = sha(pdk_source)
    image = capture(["docker", "image", "inspect", IMAGE, "--format", "{{.Id}}"])
    label = "pinwheel-tt-clean-" + out.name
    owner = str(uuid.uuid4())
    mount = ["--mount", f"type=bind,source={project},target=/work/project",
             "--mount", f"type=bind,source={pdk},target=/work/pdk,readonly"]
    docker = ["docker", "run", "--rm", "--pull", "never", "--network", "none", "--cpus", str(jobs),
              "--memory", memory, "--memory-swap", memory, "--label", f"org.pinwheel.signoff_owner={owner}",
              "--name", label, *mount, "--workdir", "/work/project", "--entrypoint", "python3", image]
    command = [*docker, "-m", "librelane", "--pdk-root", "/work/pdk", "--pdk", PDK,
               "--run-tag", "wokwi", "--force-run-dir", "runs/wokwi", "--hide-progress-bar",
               "--jobs", str(jobs), "src/config_merged.json"]
    started = time.monotonic()
    receipt = dict(schema="pinwheel.streaming-8x4-tt-clean-run.v1", status="running", candidate_promoted=False,
                   github_action_run=False, stage_sha256=sha(out / "stage.json"), pdk_source_sha256=pdk_input,
                   command=command, image=image, owner=owner, timeout_seconds=timeout)
    with lease.open("rb") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        require(not (lease.parent / "cleanup-unconfirmed.json").exists(), "Prior native cleanup is unconfirmed")
        (project / "runs/wokwi").mkdir(parents=True)
        write(out / "execution.json", receipt)
        def interrupt(_signal, _frame):
            raise KeyboardInterrupt

        handler = signal.signal(signal.SIGTERM, interrupt)
        try:
            with (out / "harden.log").open("x") as log:
                process = subprocess.run(command, timeout=timeout, stdout=log, stderr=subprocess.STDOUT)
            receipt["exit_code"] = process.returncode
            receipt["status"] = "pass" if process.returncode == 0 else "fail"
        except subprocess.TimeoutExpired:
            receipt["status"] = "timeout"
            raise
        except KeyboardInterrupt:
            receipt["status"] = "interrupted"
            raise
        finally:
            signal.signal(signal.SIGTERM, handler)
            receipt["elapsed_seconds"] = time.monotonic() - started
            receipt["cleanup"] = cleanup(owner)
            receipt["inputs_unchanged"] = bindings(project, staged["inputs"]) == staged["inputs"] and sha(pdk_source) == pdk_input
            write(out / "execution.json", receipt)
    require(receipt["status"] == "pass" and receipt["inputs_unchanged"], "Stock hardening did not complete with intact inputs")


def stock_candidate(out):
    execution = read(out / "execution.json")
    require(execution["status"] == "pass" and execution["exit_code"] == 0
            and execution["inputs_unchanged"] is True and execution["cleanup"]["status"] == "absent"
            and execution["stage_sha256"] == sha(out / "stage.json"), "Stock hardening has no successful terminal run")
    project = out / "project"
    stage = read(out / "stage.json")
    require(bindings(project, stage["inputs"]) == stage["inputs"], "Stock project inputs changed since routing")
    run_root = project / "runs/wokwi"
    final = run_root / "final"
    resolved = read(run_root / "resolved.json")
    require(resolved["meta"]["librelane_version"] == LL and resolved["DESIGN_NAME"] == TOP
            and resolved["PDK"] == PDK and resolved["RT_MAX_LAYER"] == "Metal4", "Wrong final stock flow configuration")
    assets = {role: final / kind / name for role, kind, name in (
        ("gds", "gds", f"{TOP}.gds"), ("lef", "lef", f"{TOP}.lef"), ("nl", "nl", f"{TOP}.nl.v"),
        ("pnl", "pnl", f"{TOP}.pnl.v"), ("odb", "odb", f"{TOP}.odb"), ("def", "def", f"{TOP}.def"),
    )}
    require(all(path.is_file() and path.stat().st_size for path in assets.values()), "Stock flow is missing a final view")
    require(sha(assets["gds"]) != GDS, "Treat the frozen GDS through its existing release path")
    trace = [run_root / "resolved.json", out / "execution.json", out / "harden.log"]
    trace.extend(sorted(path for path in final.rglob("*") if path.is_file()))
    return assets, dict(schema="pinwheel.streaming-8x4-tt-clean-candidate.v1",
        source_stage_sha256=execution["stage_sha256"], files=[record(out, path) for path in trace],
        views={role: record(out, path) for role, path in assets.items()}, candidate_promoted=False,
        qualified_timing=False, qualified_power=False)


def check_stock(out, support, action, pdk, python, lease, timeout):
    assets, candidate = stock_candidate(out)
    check = out / "stock-precheck"
    check.mkdir(exist_ok=False)
    project = out / "project"
    sources = {**assets, "info_yaml": project / "info.yaml", "docs_info_md": project / "docs/info.md",
               "license": project / "LICENSE"}
    files = []
    for role, name in ASSETS.items():
        dest = check / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(sources[role], dest)
        files.append(dict(path=name, sha256=sha(sources[role]), bytes=sources[role].stat().st_size))
    write(check / "candidate.json", candidate)

    def verify_inputs():
        return [file_spec(check, item) for item in files]

    run_precheck(check, support, action, pdk, python, lease, timeout, verify_inputs, candidate["views"]["gds"]["sha256"])


def exercise_stock(out, view, models, compiler, vvp):
    project = out / "project"
    stage = read(out / "stage.json")
    require(bindings(project, stage["inputs"]) == stage["inputs"], "Stock project inputs changed before simulation")
    if view == "final":
        netlist = stock_candidate(out)[0]["nl"]
    else:
        netlist = project / "runs/wokwi/06-yosys-synthesis" / f"{TOP}.nl.v"
        require((netlist.parent / "state_out.json").is_file(), "Synthesis has no terminal state")
    rtl = [project / "src" / name for name in RTL]
    vendor = [models / name for name in PDK_MODELS]
    inputs = {netlist: sha(netlist), compiler: sha(compiler), vvp: sha(vvp),
              **{path: RTL[path.name] for path in rtl}, **{path: PDK_MODELS[path.name] for path in vendor}}
    require(all(sha(path) == digest for path, digest in inputs.items()), "Stock wire-test input hashes differ")
    run_dir = out / f"wire-{view}"
    run_dir.mkdir(exist_ok=False)
    bridge = run_dir / "bridge.sv"
    bridge.write_text(bridge_source(DEPTH))
    receipt = dict(schema="pinwheel.streaming-8x4-tt-clean-wire.v1", passed=False, view=view,
                   inputs={str(path): digest for path, digest in inputs.items()},
                   target_netlist_sha256=inputs[netlist], compiles={}, fixtures={}, successions={})
    try:
        for name, sources in (("stock", [*vendor, netlist]), ("rtl", rtl)):
            model, receipt["compiles"][name] = compile_model(compiler, run_dir, name, [*sources, bridge])
            observed = simulate(vvp, model, sha(model))
            require(observed.pop("model_sha256") == sha(model), f"Wrong loaded model for {name}")
            receipt["fixtures"][name] = observed
            receipt["successions"][name] = succession(vvp, model, run_dir / f"{name}-succession.bin")
        for check in ("fixtures", "successions"):
            require(receipt[check]["stock"] == receipt[check]["rtl"], f"Stock {view} {check} differ from released RTL")
        require(all(sha(path) == digest for path, digest in inputs.items()), "Stock wire-test inputs changed")
        receipt["passed"] = True
    finally:
        write(run_dir / "receipt.json", receipt)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("stage", "run", "review", "precheck", "simulate"))
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--template", type=Path, default=BUILD / "verification-template-4b1204a")
    parser.add_argument("--support", type=Path, default=BUILD / "verification-support-9d13ff3")
    parser.add_argument("--action", type=Path, default=BUILD / "verification-action-e7a50f8")
    parser.add_argument("--python", type=Path, default=ENTRY / "clean-hardening-python/bin/python")
    parser.add_argument("--precheck-python", type=Path, default=BUILD / "verification-precheck-venv/bin/python")
    parser.add_argument("--pdk", type=Path, default=BUILD / "verification-ciel")
    parser.add_argument("--lease", type=Path)
    parser.add_argument("--timeout", type=int, default=21600)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--memory", default="6g")
    parser.add_argument("--view", choices=("synthesis", "final"), default="final")
    parser.add_argument("--iverilog", type=Path)
    parser.add_argument("--vvp", type=Path)
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.parent == ENTRY, "Use a dedicated ignored output directory in the current worktree")
    if args.phase == "stage":
        require(not out.exists(), "Use a fresh project staging directory")
        stage(out, args.template.resolve(), args.support.resolve(), args.python.absolute())
    elif args.phase == "review":
        write(out / "candidate.json", stock_candidate(out)[1])
    elif args.phase == "run":
        require(args.lease and args.timeout > 0 and args.jobs > 0, "Supply the shared native lease and positive budgets")
        run(out, args.pdk.resolve(), args.lease.resolve(), args.timeout, args.jobs, args.memory)
    elif args.phase == "simulate":
        require(args.iverilog and args.vvp, "Supply the Icarus compiler and runtime")
        models = args.pdk / PDK / "libs.ref/sg13cmos5l_stdcell/verilog"
        exercise_stock(out, args.view, models.resolve(strict=True), args.iverilog.resolve(strict=True),
                       args.vvp.resolve(strict=True))
    else:
        require(args.lease and args.timeout > 0, "Supply the shared native lease and positive budget")
        check_stock(out, args.support.resolve(), args.action.resolve(), args.pdk.resolve(),
                    args.precheck_python.absolute(), args.lease.resolve(), args.timeout)


if __name__ == "__main__":
    main()
