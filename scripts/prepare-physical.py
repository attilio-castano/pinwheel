#!/usr/bin/env python3
"""Re-emit the measured general core and freeze its physical-run inputs."""
import argparse
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
    parser = argparse.ArgumentParser()
    parser.add_argument("--validated-command-split", type=Path,
                        help="Freeze the exact RTL identified by the committed command-split result")
    args = parser.parse_args()
    manifest = ROOT / "physical/experiments/command-split-results.json"
    candidate = json.loads(manifest.read_text()) if args.validated_command_split else None
    if candidate and sha(args.validated_command_split) != candidate["rtl_sha256"]:
        raise RuntimeError("Candidate RTL differs from the committed validated artifact")
    if candidate and (OUT / "inputs.json").exists():
        raise RuntimeError("Preserve the existing prepared design; use a separate checkout for this candidate")
    OUT.mkdir(parents=True, exist_ok=True)
    if candidate:
        shutil.copyfile(args.validated_command_split, OUT / "design.sv")
        receipt_path = manifest
        receipt = candidate
    else:
        subprocess.run(["lake", "build", "Pinwheel.Hardware.Storage.DenseEmit"], cwd=ROOT, check=True)
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/Storage.lean"], cwd=ROOT, check=True)
        circt = ROOT / "build/tools/firtool-1.159.0/bin/circt-opt"
        result = subprocess.run([
            str(circt), "build/storage/small-dense-cached.mlir", "--canonicalize",
            "--lower-seq-to-sv", "--lower-hw-to-sv", "--hw-legalize-modules",
            "--export-verilog", "-o", "/dev/null",
        ], cwd=ROOT, check=True, capture_output=True)
        (OUT / "design.sv").write_bytes(result.stdout)
        receipt_path = ROOT / "build/storage/small-dense-cached/report.json"
        receipt = json.loads(receipt_path.read_text())
    if sha(OUT / "design.sv") != receipt["rtl_sha256"]:
        raise RuntimeError("Prepared RTL differs from the validated artifact")
    for name in ["core.json", "core.sdc"]:
        shutil.copyfile(ROOT / "physical" / name, OUT / name)
    sources = list((ROOT / "Pinwheel").rglob("*.lean")) + [ROOT / "test/Storage.lean", Path(__file__).resolve(), ROOT / "physical/core.json", ROOT / "physical/core.sdc"]
    report = {
        "rtl_sha256": sha(OUT / "design.sv"),
        "storage_receipt_sha256": sha(receipt_path),
        "variant": "command-split" if candidate else "small-dense-cached",
        "generation": "Frozen artifact from committed command-split evidence" if candidate else "Current source emission",
        "validation_receipt": str(receipt_path.relative_to(ROOT)),
        "source_sha256": {str(p.relative_to(ROOT)): sha(p) for p in sorted(sources)},
        "boundary": "Full observable core with synchronous internal word-loader ports. 6x4-sized core rectangle; no Tiny Tapeout pin wrapper, external serial loader, or 8x4 submission-fit claim.",
    }
    (OUT / "inputs.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Prepared physical inputs; RTL matches validated artifact:", report["rtl_sha256"])


if __name__ == "__main__":
    main()
