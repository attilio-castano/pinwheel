"""Build the frozen release RTL through the Tiny Tapeout CMOS5L flow."""

import argparse
import fcntl
import json
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
CONTINUATION = "route-capacity-continuation"
CONTINUATION_FILE = "route-continuation.json"
CONTINUATION_SEED = "route-continuation-seed.json"


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


def flow_directory(run):
    return run / "project/runs/wokwi"


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


def global_route_trial(project, baseline, staged, reserve):
    stock_project = baseline / "project"
    stock_stage = read(baseline / "stage.json")
    require(stock_stage["inputs"] == staged["inputs"]
            and bindings(stock_project, stock_stage["inputs"]) == stock_stage["inputs"],
            "Route trial changed the staged inputs")
    stock_run = stock_project / "runs/wokwi"
    stock_config_path = stock_run / "resolved.json"
    stock_route_state = stock_run / "39-openroad-globalrouting/state_out.json"
    stock_config = read(stock_config_path)
    require(stock_config["GRT_ADJUSTMENT"] == 0.30 and stock_config["CTS_APPLY_NDR"] == "half"
            and stock_route_state.is_file(),
            "Route trial requires the completed stock global-route comparator")
    stock_state = stock_run / "38-openroad-stamidpnr-2/state_out.json"
    state = read(stock_state)
    sources = {path.relative_to(stock_project).as_posix() for path in (stock_config_path, stock_route_state, stock_state)}

    def remap(value):
        if isinstance(value, dict):
            return {name: remap(path) for name, path in value.items()}
        relative = Path(value).relative_to("/work/project")
        require(".." not in relative.parts and (stock_project / relative).is_file(), "Invalid checked seed view")
        sources.add(relative.as_posix())
        return f"/work/stock/{relative.as_posix()}"

    for view in state.keys() - {"metrics"}:
        state[view] = remap(state[view])
    require(state["odb"].startswith("/work/stock/runs/wokwi/37-openroad-resizertimingpostcts/"),
            "Route trial must use the stock pre-global-route checkpoint")
    seed = project / "route-trial-seed.json"
    # LibreLane serializes non-finite timing metrics in its native state JSON.
    seed.write_text(json.dumps(state, indent=2, allow_nan=True) + "\n")
    checked = bindings(stock_project, sources)
    return (["--mount", f"type=bind,source={stock_project},target=/work/stock,readonly"],
            ["--with-initial-state", "/work/project/route-trial-seed.json", "--only", "OpenROAD.GlobalRouting",
             "--override-config", f"GRT_ADJUSTMENT={reserve}"],
            {**checked, seed.name: sha(seed)})


def stage_continuation(out, stock, trial):
    require(stock.parent == trial.parent == ENTRY and len({stock, trial, out}) == 3,
            "Choose separate stock, reserve trial, and continuation directories in this worktree")
    staged = read(out / "stage.json")
    execution = read(trial / "execution.json")
    require(execution["schema"] == "pinwheel.streaming-8x4-tt-clean-run.v1"
            and execution["mode"] == "route-capacity-trial" and execution["status"] == "pass"
            and execution["exit_code"] == 0 and execution["inputs_unchanged"] is True
            and execution["cleanup"]["status"] == "absent" and execution["route_trial_config_matches"] is True
            and execution["stage_sha256"] == sha(trial / "stage.json"),
            "Continuation requires a completed, checked global-route trial")
    stock_project, trial_project = stock / "project", trial / "project"
    require(f"type=bind,source={stock_project},target=/work/stock,readonly" in execution["command"]
            and f"type=bind,source={trial_project},target=/work/project" in execution["command"],
            "The supplied stock and trial must match the executed route trial mounts")
    sources = {stock / "stage.json", trial / "stage.json", trial / "execution.json"}
    for root in (stock, trial):
        inputs = read(root / "stage.json")["inputs"]
        require(inputs == staged["inputs"] and bindings(root / "project", inputs) == inputs,
                "Continuation changed the staged inputs")
        sources.update(root / "project" / path for path in inputs)
    original = dict(execution["route_trial_inputs"])
    original_seed = trial_project / "route-trial-seed.json"
    require(sha(original_seed) == original.pop(original_seed.name)
            and bindings(stock_project, original) == original, "Retained route trial inputs changed")
    sources.add(original_seed)
    sources.update(stock_project / path for path in original)
    trial_root = flow_directory(trial)
    trial_config = trial_root / "resolved.json"
    config = read(trial_config)
    reserve = config["GRT_ADJUSTMENT"]
    stock_config = read(flow_directory(stock) / "resolved.json")
    require(0 <= reserve < 0.30 and stock_config["GRT_ADJUSTMENT"] == 0.30
            and config == {**stock_config, "GRT_ADJUSTMENT": reserve}, "Wrong reserve trial configuration")
    grt = trial_root / "01-openroad-globalrouting"
    checkpoint = grt / "state_out.json"
    state = read(checkpoint)
    for view, suffix in (("odb", ".odb"), ("def", ".def")):
        asset = grt / (TOP + suffix)
        snapshot = trial_root / "final" / view / asset.name
        require(state[view] == f"/work/project/{asset.relative_to(trial_project).as_posix()}"
                and sha(asset) == sha(snapshot), f"Trial state does not match its final {view} snapshot")
        sources.add(snapshot)
    sources.update((trial_config, checkpoint, grt / "after_grt.guide", grt / "openroad-globalrouting.log"))

    def remap(value):
        if isinstance(value, dict):
            return {name: remap(path) for name, path in value.items()}
        path = Path(value)
        if path.is_relative_to("/work/stock"):
            require(path.relative_to("/work/stock").as_posix() in original, "Unbound stock continuation view")
            return value
        relative = path.relative_to("/work/project")
        require(".." not in relative.parts and (trial_project / relative).is_file(), "Invalid trial continuation view")
        sources.add(trial_project / relative)
        return f"/work/trial/{relative.as_posix()}"

    for view in state.keys() - {"metrics"}:
        state[view] = remap(state[view])
    seed = out / "project" / CONTINUATION_SEED
    seed.write_text(json.dumps(state, indent=2, allow_nan=True) + "\n")
    write(out / CONTINUATION_FILE, dict(schema="pinwheel.streaming-8x4-tt-route-continuation.v1",
        reserve=reserve, image=execution["image"], pdk_source_sha256=execution["pdk_source_sha256"],
        stock=stock.name, trial=trial.name, stage_sha256=sha(out / "stage.json"), seed_sha256=sha(seed),
        inputs=bindings(ENTRY, (path.relative_to(ENTRY).as_posix() for path in sources))))


def continuation_inputs_match(out, continuation):
    return (sha(out / "stage.json") == continuation["stage_sha256"]
            and sha(out / "project" / CONTINUATION_SEED) == continuation["seed_sha256"]
            and bindings(ENTRY, continuation["inputs"]) == continuation["inputs"])


def run(out, pdk, lease, timeout, jobs, memory, baseline=None, reserve=0.19):
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
    extra = []
    trial_inputs = {}
    continuation_receipt = out / CONTINUATION_FILE
    continuation = read(continuation_receipt) if continuation_receipt.is_file() else None
    mode = "stock"
    if baseline:
        require(continuation is None, "A staged continuation already selects the route to run")
        require(0 <= reserve < 0.30, "Use a routing reserve below the stock 30 percent")
        mounts, extra, trial_inputs = global_route_trial(project, baseline, staged, reserve)
        mount.extend(mounts)
        mode = "route-capacity-trial"
    elif continuation:
        require(continuation["schema"] == "pinwheel.streaming-8x4-tt-route-continuation.v1"
                and continuation_inputs_match(out, continuation)
                and continuation["image"] == image and continuation["pdk_source_sha256"] == pdk_input,
                "Route continuation inputs or pinned tool identities changed")
        for origin in ("stock", "trial"):
            source = ENTRY / continuation[origin] / "project"
            mount.extend(["--mount", f"type=bind,source={source},target=/work/{origin},readonly"])
        extra = ["--with-initial-state", f"/work/project/{CONTINUATION_SEED}",
                 "--from", "OpenROAD.CheckAntennas", "--override-config", f"GRT_ADJUSTMENT={continuation['reserve']}"]
        mode = CONTINUATION
    docker = ["docker", "run", "--rm", "--pull", "never", "--network", "none", "--cpus", str(jobs),
              "--memory", memory, "--memory-swap", memory, "--label", f"org.pinwheel.signoff_owner={owner}",
              "--name", label, *mount, "--workdir", "/work/project", "--entrypoint", "python3", image]
    command = [*docker, "-m", "librelane", "--pdk-root", "/work/pdk", "--pdk", PDK,
               "--run-tag", "wokwi", "--force-run-dir", "runs/wokwi", "--hide-progress-bar",
               "--jobs", str(jobs), *extra, "src/config_merged.json"]
    started = time.monotonic()
    receipt = dict(schema="pinwheel.streaming-8x4-tt-clean-run.v1", status="running", candidate_promoted=False,
                   github_action_run=False, stage_sha256=sha(out / "stage.json"), pdk_source_sha256=pdk_input,
                   command=command, image=image, owner=owner, timeout_seconds=timeout,
                   mode=mode, route_trial_inputs=trial_inputs)
    if continuation:
        receipt["route_continuation_sha256"] = sha(continuation_receipt)
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
            if baseline and process.returncode == 0:
                after = read(project / "runs/wokwi/resolved.json")
                before = read(baseline / "project/runs/wokwi/resolved.json")
                receipt["route_trial_config_matches"] = after == {**before, "GRT_ADJUSTMENT": reserve}
                if not receipt["route_trial_config_matches"]:
                    receipt["status"] = "fail"
            if continuation and process.returncode == 0:
                expected = read(flow_directory(ENTRY / continuation["trial"]) / "resolved.json")
                receipt["route_continuation_config_matches"] = read(flow_directory(out) / "resolved.json") == expected
                if not receipt["route_continuation_config_matches"]:
                    receipt["status"] = "fail"
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
            if baseline:
                seed = project / "route-trial-seed.json"
                retained = bindings(baseline / "project", trial_inputs.keys() - {seed.name})
                receipt["inputs_unchanged"] &= {**retained, seed.name: sha(seed)} == trial_inputs
            if continuation:
                receipt["inputs_unchanged"] &= (sha(continuation_receipt) == receipt["route_continuation_sha256"]
                                                 and continuation_inputs_match(out, continuation))
            write(out / "execution.json", receipt)
    require(receipt["status"] == "pass" and receipt["inputs_unchanged"], "Hardening did not complete with intact inputs")


def review_candidate(out):
    execution = read(out / "execution.json")
    mode = execution.get("mode", "stock")
    require(mode in ("stock", CONTINUATION) and execution["status"] == "pass" and execution["exit_code"] == 0
            and execution["inputs_unchanged"] is True and execution["cleanup"]["status"] == "absent"
            and execution["stage_sha256"] == sha(out / "stage.json"), "Hardening has no successful terminal full flow")
    project = out / "project"
    stage = read(out / "stage.json")
    require(bindings(project, stage["inputs"]) == stage["inputs"], "Project inputs changed since routing")
    run_root = flow_directory(out)
    final = run_root / "final"
    resolved = read(run_root / "resolved.json")
    require(resolved["meta"]["librelane_version"] == LL and resolved["DESIGN_NAME"] == TOP
            and resolved["PDK"] == PDK and resolved["RT_MAX_LAYER"] == "Metal4", "Wrong final flow configuration")
    assets = {role: final / kind / name for role, kind, name in (
        ("gds", "gds", f"{TOP}.gds"), ("lef", "lef", f"{TOP}.lef"), ("nl", "nl", f"{TOP}.nl.v"),
        ("pnl", "pnl", f"{TOP}.pnl.v"), ("odb", "odb", f"{TOP}.odb"), ("def", "def", f"{TOP}.def"),
    )}
    require(all(path.is_file() and path.stat().st_size for path in assets.values()), "Flow is missing a final view")
    require(sha(assets["gds"]) != GDS, "Treat the frozen GDS through its existing release path")
    trace = [run_root / "resolved.json", out / "execution.json", out / "harden.log"]
    trace.extend(sorted(path for path in final.rglob("*") if path.is_file()))
    schema = "pinwheel.streaming-8x4-tt-clean-candidate.v1"
    route = {}
    if mode == CONTINUATION:
        manifest = out / CONTINUATION_FILE
        continuation = read(manifest)
        require(execution["route_continuation_config_matches"] is True
                and sha(manifest) == execution["route_continuation_sha256"]
                and continuation_inputs_match(out, continuation)
                and resolved == read(flow_directory(ENTRY / continuation["trial"]) / "resolved.json"),
                "Final flow is no longer bound to the reserve trial")
        trace.extend((manifest, project / CONTINUATION_SEED))
        for step in ("openroad-repairantennas", "openroad-detailedrouting", "checker-trdrc",
                     "klayout-streamout", "netgen-lvs", "misc-reportmanufacturability"):
            states = list(run_root.glob(f"*-{step}/state_out.json"))
            require(len(states) == 1, f"Continuation is missing completed {step}")
            trace.extend(states)
        schema = "pinwheel.streaming-8x4-tt-reserve-candidate.v1"
        route = dict(mode=mode, route_reserve=continuation["reserve"], route_continuation=record(out, manifest))
    return assets, dict(schema=schema, **route,
        source_stage_sha256=execution["stage_sha256"], files=[record(out, path) for path in trace],
        views={role: record(out, path) for role, path in assets.items()}, candidate_promoted=False,
        qualified_timing=False, qualified_power=False)


def check_candidate(out, support, action, pdk, python, lease, timeout):
    assets, candidate = review_candidate(out)
    check = out / ("reserve-precheck" if candidate.get("mode") == CONTINUATION else "stock-precheck")
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


def exercise_candidate(out, view, models, compiler, vvp):
    project = out / "project"
    stage = read(out / "stage.json")
    require(bindings(project, stage["inputs"]) == stage["inputs"], "Project inputs changed before simulation")
    target = "stock"
    if view == "final":
        assets, candidate = review_candidate(out)
        netlist = assets["nl"]
        if candidate.get("mode") == CONTINUATION:
            target = "reserve"
    else:
        netlist = project / "runs/wokwi/06-yosys-synthesis" / f"{TOP}.nl.v"
        require((netlist.parent / "state_out.json").is_file(), "Synthesis has no terminal state")
    rtl = [project / "src" / name for name in RTL]
    vendor = [models / name for name in PDK_MODELS]
    inputs = {netlist: sha(netlist), compiler: sha(compiler), vvp: sha(vvp),
              **{path: RTL[path.name] for path in rtl}, **{path: PDK_MODELS[path.name] for path in vendor}}
    require(all(sha(path) == digest for path, digest in inputs.items()), "Wire-test input hashes differ")
    run_dir = out / f"wire-{view}"
    run_dir.mkdir(exist_ok=False)
    bridge = run_dir / "bridge.sv"
    bridge.write_text(bridge_source(DEPTH))
    receipt = dict(schema="pinwheel.streaming-8x4-tt-clean-wire.v1", passed=False, view=view,
                   inputs={str(path): digest for path, digest in inputs.items()},
                   target_netlist_sha256=inputs[netlist], compiles={}, fixtures={}, successions={})
    try:
        for name, sources in ((target, [*vendor, netlist]), ("rtl", rtl)):
            model, receipt["compiles"][name] = compile_model(compiler, run_dir, name, [*sources, bridge])
            observed = simulate(vvp, model, sha(model))
            require(observed.pop("model_sha256") == sha(model), f"Wrong loaded model for {name}")
            receipt["fixtures"][name] = observed
            receipt["successions"][name] = succession(vvp, model, run_dir / f"{name}-succession.bin")
        for check in ("fixtures", "successions"):
            require(receipt[check][target] == receipt[check]["rtl"], f"{target} {view} {check} differ from released RTL")
        require(all(sha(path) == digest for path, digest in inputs.items()), "Wire-test inputs changed")
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
    parser.add_argument("--route-trial-from", type=Path,
                        help="Replay only global routing from a stock run")
    parser.add_argument("--route-reserve", type=float, default=0.19,
                        help="Modeled reserve as a fraction for --route-trial-from (default 0.19)")
    parser.add_argument("--continue-from", type=Path, help="Stage a continuation from a completed reserve trial")
    parser.add_argument("--stock-from", type=Path, help="Original stock run required with --continue-from")
    args = parser.parse_args()
    require((args.continue_from is None) == (args.stock_from is None)
            and (args.continue_from is None or args.phase == "stage"),
            "Use --continue-from and --stock-from together with stage")
    require(args.route_trial_from is None or args.phase == "run", "Use --route-trial-from with run")
    out = args.out.resolve()
    require(out.parent == ENTRY, "Use a dedicated ignored output directory in the current worktree")
    if args.phase == "stage":
        require(not out.exists(), "Use a fresh project staging directory")
        stage(out, args.template.resolve(), args.support.resolve(), args.python.absolute())
        if args.continue_from:
            stage_continuation(out, args.stock_from.resolve(strict=True), args.continue_from.resolve(strict=True))
    elif args.phase == "review":
        write(out / "candidate.json", review_candidate(out)[1])
    elif args.phase == "run":
        require(args.lease and args.timeout > 0 and args.jobs > 0, "Supply the shared native lease and positive budgets")
        baseline = args.route_trial_from.resolve(strict=True) if args.route_trial_from else None
        run(out, args.pdk.resolve(), args.lease.resolve(), args.timeout, args.jobs, args.memory, baseline, args.route_reserve)
    elif args.phase == "simulate":
        require(args.iverilog and args.vvp, "Supply the Icarus compiler and runtime")
        models = args.pdk / PDK / "libs.ref/sg13cmos5l_stdcell/verilog"
        exercise_candidate(out, args.view, models.resolve(strict=True), args.iverilog.resolve(strict=True),
                           args.vvp.resolve(strict=True))
    else:
        require(args.lease and args.timeout > 0, "Supply the shared native lease and positive budget")
        check_candidate(out, args.support.resolve(), args.action.resolve(), args.pdk.resolve(),
                        args.precheck_python.absolute(), args.lease.resolve(), args.timeout)


if __name__ == "__main__":
    main()
