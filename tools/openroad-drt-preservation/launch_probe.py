"""One read-only capability job under the campaign's shared owned-job lock."""
import json
from pathlib import Path
import shutil
import sys
import time

root = Path.cwd().resolve()
campaign = root / "build/physical/tt-overnight-campaign-20261015"
manifest = json.loads((campaign / "manifest.json").read_text())
sys.path.insert(0, str(root / "tools/pinwheel-physical-campaign"))
from runner import JobSpec, run_owned_job, sha256_file
output = root / "build/physical/tt-overnight-taper-tools-01/jobs/capability-openmp-01"
output.mkdir(parents=True, exist_ok=False)
shutil.copyfile(Path(__file__).with_name("probe_openmp.py"), output / "probe.py")
inputs = dict(manifest["protected_sources_sha256"])
inputs.update(manifest["reference_files_sha256"])
for p in [Path(__file__), output / "probe.py", campaign / "manifest.json", root / "tools/pinwheel-physical-campaign/runner.py"]:
    inputs[str(p)] = sha256_file(p)
spec = JobSpec(output_dir=output, heavy_lock_path=campaign / "heavy.lock", image_id=manifest["image_id"],
    command=["python3", "-B", "/work/diagnostic/probe.py"], campaign_id="tt-overnight-20261015-000717",
    hard_end_epoch=min(manifest["hard_stop_epoch"] - 3600, time.time() + 90), input_sha256=inputs,
    native_seconds=30, max_job_seconds=90, closeout_reserve_seconds=30, minimum_native_seconds=10,
    cpus=1, memory="1g", scope="Read-only pinned image OpenMP header/library discovery; no CAD or mutation.")
result = run_owned_job(spec)
print(json.dumps({k: result.get(k) for k in ["status", "exit_code", "inputs_unchanged", "container_termination", "elapsed_all_in_seconds"]}, indent=2))
