#!/usr/bin/env python3
"""Install pinned official archives under build/tools; no global environment changes."""
import hashlib
import json
import platform
import sys
import tarfile
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    if sys.version_info < (3, 12):
        raise SystemExit("Python 3.12+ is required for safe archive extraction")
    manifest = json.loads((ROOT / "tools/hardware-toolchain.json").read_text())
    host = f"{platform.system().lower()}-{platform.machine()}"
    if host != manifest["platform"]:
        raise SystemExit(f"Pinned archives target {manifest['platform']}, not {host}")
    target = ROOT / "build/tools"
    target.mkdir(parents=True, exist_ok=True)
    for name, package in manifest["packages"].items():
        archive = target / package["archive"]
        if not archive.exists():
            print(f"Downloading {name} {package['release']}", flush=True)
            partial = archive.with_name(archive.name + ".part")
            urllib.request.urlretrieve(package["url"], partial)
            if digest(partial) != package["sha256"]:
                raise SystemExit(f"Checksum mismatch: {partial}")
            partial.replace(archive)
        if digest(archive) != package["sha256"]:
            raise SystemExit(f"Checksum mismatch: {archive}")
        print(f"Verified {name}; extracting {package['directory']}", flush=True)
        with tarfile.open(archive) as bundle:
            members = bundle.getmembers()
            directory = package["directory"]
            if any(m.name.rstrip("/") != directory and not m.name.startswith(directory + "/")
                   for m in members):
                raise SystemExit(f"Unexpected archive layout: {archive}")
            bundle.extractall(target, members=members, filter="data")
    (target / "installed.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("Installed verified tools under build/tools (ignored by Git).")


if __name__ == "__main__":
    main()
