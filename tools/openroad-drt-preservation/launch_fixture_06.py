"""Versioned isolated build/fixture jobs under the authorized campaign lock."""
import json
from pathlib import Path
import shutil
import sys

ROOT = Path.cwd().resolve()
CAMPAIGN = ROOT / "build/physical/tt-overnight-campaign-20261015"
TOOLS = ROOT / "tools/openroad-drt-preservation"
BUNDLE = ROOT / "build/physical/tt-overnight-taper-tools-01"
DEPS = Path("/Users/attiliocastano/.codex/worktrees/c6eb/pinwheel/build/validation/hold-repair-01/headers")
sys.path.insert(0, str(ROOT / "tools/pinwheel-physical-campaign"))
from runner import JobSpec, run_owned_job, sha256_file

mode = sys.argv[1]
assert mode == "regression-06"
manifest = json.loads((CAMPAIGN / "manifest.json").read_text())
prior = json.loads((BUNDLE / "jobs/build-02/report.json").read_text())
assert prior["container_termination"]["status"] == "absent" and prior["inputs_unchanged"]
assert not (CAMPAIGN / "heavy.lock").exists(), "Another campaign job owns the heavy slot"
out = BUNDLE / "jobs" / mode
out.mkdir(parents=True, exist_ok=False)
(out / "build-support").mkdir()
if mode == "build-04":
    for name in ["source", "source-extra-01", "source-extra-02", "generated-02"]:
        shutil.copytree(BUNDLE / name, out / name)
    for name in ["source-fetch.json", "source-extra-01-fetch.json", "source-extra-02-fetch.json", "preparation-qualification-02.json"]:
        shutil.copyfile(BUNDLE / name, out / name)
    for name in ["build-04.py", "extension-02.cc"]:
        shutil.copyfile(TOOLS / name, out / "build-support" / name)
    command = ["python3", "-B", "/support/build-04.py", "/work/diagnostic"]
    native, total, minimum = 540, 600, 480
else:
    build = BUNDLE / "jobs/build-05"
    receipt = json.loads((build / "report.json").read_text())
    assert receipt["status"] == "passed" and receipt["inputs_unchanged"] and receipt["container_termination"]["status"] == "absent"
    assert json.loads((build / "native-05/build.json").read_text())["status"] == "passed"
    shutil.copytree(build / "native-05", out / "native-05")
    shutil.copytree(BUNDLE / "fixtures", out / "fixtures")
    shutil.copyfile(BUNDLE / "fixture-source-fetch.json", out / "fixture-source-fetch.json")
    shutil.copyfile(TOOLS / "regression-06.py", out / "build-support/regression-06.py")
    command = ["python3", "-B", "/support/regression-06.py", "/work/diagnostic", "/work/diagnostic/results"]
    native, total, minimum = 300, 360, 240
inputs = dict(manifest["protected_sources_sha256"])
inputs.update(manifest["reference_files_sha256"])
for top in [out, DEPS]:
    for path in top.rglob("*"):
        if path.is_file():
            inputs[str(path)] = sha256_file(path)
for path in [Path(__file__), CAMPAIGN / "manifest.json", ROOT / "tools/pinwheel-physical-campaign/runner.py"]:
    inputs[str(path)] = sha256_file(path)
spec = JobSpec(output_dir=out, heavy_lock_path=CAMPAIGN / "heavy.lock", image_id=manifest["image_id"], command=command,
    campaign_id="tt-overnight-20261015-000717", hard_end_epoch=manifest["hard_stop_epoch"] - 3600,
    input_sha256=inputs, native_seconds=native, max_job_seconds=total, closeout_reserve_seconds=45,
    minimum_native_seconds=minimum, cpus=4, memory="6g", readonly_mounts=[(out / "build-support", "/support"), (DEPS, "/deps")],
    scope="Pinned pre-GC TAPER/native width preservation " + mode + "; original source, physical design, RTL/ABI and earlier receipts unchanged.")
result = run_owned_job(spec)
print(json.dumps({k: result.get(k) for k in ["status", "exit_code", "inputs_unchanged", "container_termination", "elapsed_all_in_seconds"]}, indent=2))
