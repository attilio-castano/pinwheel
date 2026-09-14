#!/usr/bin/env python3
"""Run the pinned physical core experiment locally; preserve failure evidence."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "build/physical"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tag", default="initial")
    parser.add_argument("--to", help="Optional LibreLane stopping step; partial runs never establish final fit")
    args = parser.parse_args()
    if not args.tag.replace("-", "").replace("_", "").isalnum():
        parser.error("tag must contain only letters, numbers, hyphens, or underscores")
    receipt_path = BASE / (args.tag + "-invocation.json")
    snapshot = BASE / "core/experiments" / args.tag
    if receipt_path.exists() or snapshot.exists() or (BASE / "core/runs" / args.tag).exists():
        raise RuntimeError("Choose a new tag to preserve earlier run evidence")
    lock = json.loads((ROOT / "tools/physical-toolchain.json").read_text())
    inputs = json.loads((BASE / "core/inputs.json").read_text())
    for name in ["core.json", "core.sdc"]:
        if sha(BASE / "core" / name) != sha(ROOT / "physical" / name):
            raise RuntimeError("Physical inputs are stale; rerun prepare-physical.py")
    if sha(BASE / "core/design.sv") != inputs["rtl_sha256"]:
        raise RuntimeError("Prepared RTL changed")
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
    for name in ["design.sv", "core.json", "core.sdc", "inputs.json"]:
        shutil.copyfile(BASE / "core" / name, snapshot / name)
    command = [
        "docker", "run", "--rm", "--network", "none", "--cpus", "4", "--memory", "6g",
        "--mount", f"type=bind,source={BASE / 'core'},target=/work/core",
        "--mount", f"type=bind,source={BASE / 'pdk'},target=/work/pdk,readonly",
        "--workdir", "/work/core", image_id,
        "python3", "-m", "librelane", "--manual-pdk", "--pdk-root", "/work/pdk",
        "--pdk", "ihp-sg13cmos5l", "--jobs", "4", "--run-tag", args.tag,
        "--force-run-dir", "/work/core/runs/" + args.tag,
    ]
    if args.to:
        command += ["--to", args.to]
    command += [f"/work/core/experiments/{args.tag}/core.json"]
    receipt = {
        "command": command, "image_id": image_id, "stop_step": args.to,
        "inputs_sha256": sha(BASE / "core/inputs.json"),
        "config_sha256": sha(BASE / "core/core.json"),
        "sdc_sha256": sha(BASE / "core/core.sdc"),
        "pdk_receipt_sha256": sha(BASE / "pdk/installed.json"),
        "boundary": inputs["boundary"],
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    with (BASE / (args.tag + ".log")).open("w") as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
    receipt["exit_code"] = result.returncode
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Physical run {args.tag}: exit {result.returncode}; inspect build/physical/{args.tag}.log")
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
