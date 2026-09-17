#!/usr/bin/env python3
"""Run the pinned physical core experiment locally; preserve failure evidence."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

import physical_checkpoint

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "build/physical"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write_receipt(path, receipt):
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(receipt, indent=2) + "\n")
    temporary.replace(path)


def stop_container(name, log):
    """Keep cleanup failure separate from the already-recorded timeout."""
    termination = {"status": "unconfirmed"}
    try:
        result = subprocess.run(["docker", "stop", "--time", "10", name],
                                stdout=log, stderr=subprocess.STDOUT, timeout=30)
        termination["stop_exit_code"] = result.returncode
        if result.returncode == 0:
            termination["status"] = "stopped"
            return termination
    except (subprocess.TimeoutExpired, OSError) as error:
        termination["stop_error"] = f"{type(error).__name__}: {error}"

    # --rm can remove the container before stop reaches it. A failed stop alone
    # does not prove absence: require a successful query of the Docker daemon.
    try:
        result = subprocess.run(
            ["docker", "container", "ls", "--all", "--filter", f"name={name}",
             "--format", "{{json .}}"], capture_output=True, text=True, timeout=10)
        termination["query_exit_code"] = result.returncode
        if result.returncode != 0:
            termination["query_error"] = result.stderr
            return termination
        states = []
        for line in result.stdout.splitlines():
            row = json.loads(line)
            if not isinstance(row, dict) or not all(
                    isinstance(row.get(key), str) for key in ("Names", "State")):
                raise ValueError("Malformed Docker container listing")
            # Docker's name filter also matches substrings.
            if name in row["Names"].split(","):
                states.append(row["State"])
        termination["observed_states"] = states
        if not states:
            termination["status"] = "absent"
        elif states == ["exited"]:
            termination["status"] = "stopped"
    except (subprocess.TimeoutExpired, OSError, ValueError) as error:
        termination["query_error"] = f"{type(error).__name__}: {error}"
    return termination


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tag", default="initial")
    parser.add_argument("--design", default="core",
                        help="Prepared design under build/physical; each holds one frozen RTL identity")
    parser.add_argument("--to", help="Optional LibreLane stopping step; partial runs never establish final fit")
    parser.add_argument("--from-step", help="Resume at a named LibreLane step")
    parser.add_argument("--state", type=Path, help="Completed checkpoint state under build/physical/core")
    parser.add_argument("--checkpoint-manifest", type=Path, help="Previously captured checkpoint artifact manifest; required for resume")
    parser.add_argument("--overrides", type=Path, help="JSON implementation-flow controls; preserves RTL, timing boundary and floorplan")
    parser.add_argument("--timeout-seconds", type=int, default=3600,
                        help="Wall-time limit for this attempt; timeout stops only this run's named container")
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    if bool(args.from_step) != bool(args.state):
        parser.error("--from-step and --state must be supplied together")
    if bool(args.state) != bool(args.checkpoint_manifest):
        parser.error("--state and --checkpoint-manifest must be supplied together")
    if not args.tag.replace("-", "").replace("_", "").isalnum():
        parser.error("tag must contain only letters, numbers, hyphens, or underscores")
    if not args.design.replace("-", "").replace("_", "").isalnum() or args.design == "pdk":
        parser.error("design must contain only letters, numbers, hyphens, or underscores")
    design = BASE / args.design
    receipt_path = BASE / (args.tag + "-invocation.json")
    snapshot = design / "experiments" / args.tag
    if receipt_path.exists() or snapshot.exists() or (design / "runs" / args.tag).exists():
        raise RuntimeError("Choose a new tag to preserve earlier run evidence")
    # Reject changed checkpoints before Docker inspection or run-directory creation.
    if args.state:
        physical_checkpoint.verify(args.state, args.checkpoint_manifest, design)
    lock = json.loads((ROOT / "tools/physical-toolchain.json").read_text())
    inputs = json.loads((design / "inputs.json").read_text())
    for name in ["core.json", "core.sdc"]:
        if sha(design / name) != sha(ROOT / "physical" / name):
            raise RuntimeError("Physical inputs are stale; rerun prepare-physical.py")
    if sha(design / "design.sv") != inputs["rtl_sha256"]:
        raise RuntimeError("Prepared RTL changed")
    config = json.loads((design / "core.json").read_text())
    overrides = json.loads(args.overrides.read_text()) if args.overrides else {}
    # Estimation controls change what the optimizer believes about wires; final
    # timing still comes from extraction of the routed layout.
    allowed = {"MAX_FANOUT_CONSTRAINT", "CTS_SINK_CLUSTERING_SIZE",
               "RUN_POST_GRT_DESIGN_REPAIR", "RUN_POST_GRT_RESIZER_TIMING",
               "LAYERS_RC", "SIGNAL_WIRE_RC_LAYERS",
               "SYNTH_CLOCKGATE_MIN_WIDTH", "SYNTH_CLOCKGATE_POSEDGE_ICG",
               "PL_TARGET_DENSITY_PCT", "GRT_ALLOW_CONGESTION"}
    if not isinstance(overrides, dict) or set(overrides) - allowed:
        raise RuntimeError("Overrides must contain only the documented implementation-flow controls")
    config.update(overrides)
    image = lock["container_tag"]
    image_info = json.loads(subprocess.check_output(["docker", "image", "inspect", image], text=True))[0]
    image_id = image_info["Id"]
    # Docker's containerd image store may assign a new manifest ID on archive
    # import. Verify the original uncompressed layer identities and runtime
    # configuration instead of mistaking a manifest digest for a config digest.
    runtime = {k: v for k, v in image_info["Config"].items() if v is not None}
    runtime_hash = hashlib.sha256(json.dumps(runtime, sort_keys=True).encode()).hexdigest()
    if (image_info["Architecture"] != "arm64" or image_info["Os"] != "linux"
            or image_info["RootFS"]["Layers"] != lock["container_rootfs_diff_ids"]
            or runtime_hash != lock["container_runtime_config_sha256"]):
        raise RuntimeError("Local container filesystem/config differs from the pinned ARM64 image")
    pdk_receipt = json.loads((BASE / "pdk/installed.json").read_text())
    if pdk_receipt["tree_sha256"] != lock["pdk_tree_sha256"] or pdk_receipt["revision"] != lock["pdk_revision"]:
        raise RuntimeError("Wrong PDK source identity")
    # Detect edits after installation to all regular files in the selected process.
    for path, expected in pdk_receipt["files_sha256"].items():
        if sha(BASE / "pdk" / path) != expected:
            raise RuntimeError(f"Modified installed PDK file: {path}")
    for path, target in pdk_receipt["symlinks"].items():
        actual = BASE / "pdk" / path
        if not actual.is_symlink() or os.readlink(actual) != target:
            raise RuntimeError(f"Modified PDK symlink: {path}")
    snapshot.mkdir(parents=True)
    (design / "runs" / args.tag).mkdir(parents=True)
    for name in ["design.sv", "core.json", "core.sdc", "inputs.json"]:
        shutil.copyfile(design / name, snapshot / name)
    (snapshot / "core.json").write_text(json.dumps(config, indent=2) + "\n")
    (snapshot / "overrides.json").write_text(json.dumps(overrides, indent=2) + "\n")
    checkpoint_receipt = None
    checkpoint_mount = []
    if args.state:
        checkpoint_receipt = physical_checkpoint.snapshot(
            args.state, args.checkpoint_manifest, snapshot / "checkpoint", design)
        checkpoint_mount = ["--mount", f"type=bind,source={snapshot / 'checkpoint'},target={checkpoint_receipt['mount_path']},readonly"]
    container_name = "pinwheel-" + args.tag
    command = [
        "docker", "run", "--rm", "--name", container_name, "--network", "none", "--cpus", "4", "--memory", "6g",
        "--mount", f"type=bind,source={design},target=/work/core",
        "--mount", f"type=bind,source={BASE / 'pdk'},target=/work/pdk,readonly",
        *checkpoint_mount,
        "--workdir", "/work/core", image_id,
        "python3", "-m", "librelane", "--manual-pdk", "--pdk-root", "/work/pdk",
        "--pdk", "ihp-sg13cmos5l", "--jobs", "4", "--run-tag", args.tag,
        "--force-run-dir", "/work/core/runs/" + args.tag,
    ]
    if args.to:
        command += ["--to", args.to]
    if args.state:
        command += ["--from", args.from_step, "--with-initial-state", checkpoint_receipt["state_path"]]
    command += [f"/work/core/experiments/{args.tag}/core.json"]
    receipt = {
        "command": command, "image_id": image_id, "stop_step": args.to,
        "resume_step": args.from_step,
        "checkpoint_sha256": checkpoint_receipt["source_state_sha256"] if checkpoint_receipt else None,
        "checkpoint": checkpoint_receipt,
        "inputs_sha256": sha(design / "inputs.json"),
        "config_sha256": sha(snapshot / "core.json"),
        "base_config_sha256": sha(design / "core.json"),
        "overrides": overrides,
        "runner_sha256": sha(Path(__file__).resolve()),
        "checkpoint_helper_sha256": sha(Path(physical_checkpoint.__file__).resolve()),
        "sdc_sha256": sha(design / "core.sdc"),
        "pdk_receipt_sha256": sha(BASE / "pdk/installed.json"),
        "boundary": inputs["boundary"],
        "variant": inputs.get("variant", "small-dense-cached"),
        "design": args.design,
        "timeout_seconds": args.timeout_seconds,
    }
    write_receipt(receipt_path, receipt)
    with (BASE / (args.tag + ".log")).open("w") as log:
        try:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout_seconds)
            exit_code = result.returncode
        except subprocess.TimeoutExpired:
            exit_code = 124
            receipt["exit_code"] = exit_code
            receipt["stop_reason"] = "wall_time_limit"
            receipt["container_termination"] = {"status": "unconfirmed"}
            write_receipt(receipt_path, receipt)
            try:
                receipt["container_termination"] = stop_container(container_name, log)
            finally:
                write_receipt(receipt_path, receipt)
            if receipt["container_termination"]["status"] == "unconfirmed":
                print(f"Container {container_name} termination is unconfirmed; "
                      "inspect the invocation receipt before collecting evidence.")
    receipt["exit_code"] = exit_code
    write_receipt(receipt_path, receipt)
    print(f"Physical run {args.tag}: exit {exit_code}; inspect build/physical/{args.tag}.log")
    raise SystemExit(exit_code)


if __name__ == "__main__":
    main()
