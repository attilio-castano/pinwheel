#!/usr/bin/env python3
"""Re-emit the measured general core and freeze its physical-run inputs."""
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "build/physical/core"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    subprocess.run(["lake", "build", "Pinwheel.Hardware.Storage.DenseEmit"], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/Storage.lean"], cwd=ROOT, check=True)
    circt = ROOT / "build/tools/firtool-1.159.0/bin/circt-opt"
    result = subprocess.run([
        str(circt), "build/storage/small-dense-cached.mlir", "--canonicalize",
        "--lower-seq-to-sv", "--lower-hw-to-sv", "--hw-legalize-modules",
        "--export-verilog", "-o", "/dev/null",
    ], cwd=ROOT, check=True, capture_output=True)
    (OUT / "design.sv").write_bytes(result.stdout)
    receipt = json.loads((ROOT / "build/storage/small-dense-cached/report.json").read_text())
    if sha(OUT / "design.sv") != receipt["rtl_sha256"]:
        raise RuntimeError("Emitted RTL differs from measured storage candidate; validate the new artifact first")
    for name in ["core.json", "core.sdc"]:
        shutil.copyfile(ROOT / "physical" / name, OUT / name)
    sources = list((ROOT / "Pinwheel").rglob("*.lean")) + [ROOT / "test/Storage.lean", Path(__file__).resolve(), ROOT / "physical/core.json", ROOT / "physical/core.sdc"]
    report = {
        "rtl_sha256": sha(OUT / "design.sv"),
        "storage_receipt_sha256": sha(ROOT / "build/storage/small-dense-cached/report.json"),
        "source_sha256": {str(p.relative_to(ROOT)): sha(p) for p in sorted(sources)},
        "boundary": "Full observable core with synchronous internal word-loader ports. 6x4-sized core rectangle; no Tiny Tapeout pin wrapper, external serial loader, or 8x4 submission-fit claim.",
    }
    (OUT / "inputs.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Prepared physical inputs; fresh RTL matches measured candidate:", report["rtl_sha256"])


if __name__ == "__main__":
    main()
