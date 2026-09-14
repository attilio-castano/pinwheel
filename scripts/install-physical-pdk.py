#!/usr/bin/env python3
"""Install the pinned digital-flow PDK subset and its symlink dependencies."""
import concurrent.futures
import hashlib
import json
import os
import posixpath
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "build/physical"
OUT = BASE / "pdk"
PREFIXES = [
    "ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/",
    "ihp-sg13cmos5l/libs.ref/sg13cmos5l_io/",
    "ihp-sg13cmos5l/libs.tech/librelane/",
    "ihp-sg13cmos5l/libs.tech/klayout/tech/",
    "ihp-sg13cmos5l/libs.tech/magic/",
    "ihp-sg13cmos5l/libs.tech/netgen/",
]


def blob_hash(data):
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()


def main():
    lock = json.loads((ROOT / "tools/physical-toolchain.json").read_text())
    revision = lock["pdk_revision"]
    tree_path = BASE / "upstream/pdk-tree.json"
    tree_path.parent.mkdir(parents=True, exist_ok=True)
    if not tree_path.exists():
        with urllib.request.urlopen(f"https://api.github.com/repos/IHP-GmbH/IHP-Open-PDK/git/trees/{revision}?recursive=1", timeout=90) as response:
            tree_path.write_bytes(response.read())
    raw = tree_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != lock["pdk_tree_sha256"]:
        raise RuntimeError("Pinned PDK tree inventory changed")
    tree = json.loads(raw)
    if tree["truncated"]:
        raise RuntimeError("Incomplete PDK tree inventory")
    entries = {x["path"]: x for x in tree["tree"]}
    selected = {p for p, e in entries.items() if e["type"] == "blob" and any(p.startswith(v) for v in PREFIXES)}
    contents = {}

    def fetch(path):
        entry = entries[path]
        target = OUT / path
        if target.is_symlink():
            data = os.readlink(target).encode()
        elif target.is_file():
            data = target.read_bytes()
        else:
            data = b""
        if blob_hash(data) != entry["sha"]:
            url = f"https://raw.githubusercontent.com/IHP-GmbH/IHP-Open-PDK/{revision}/{path}"
            try:
                with urllib.request.urlopen(url, timeout=120) as response:
                    data = response.read()
            except Exception as error:
                raise RuntimeError(f"Cannot fetch pinned PDK file {path}: {error}") from error
            if blob_hash(data) != entry["sha"]:
                raise RuntimeError(f"Upstream blob mismatch: {path}")
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.is_symlink():
                target.unlink()
            if entry["mode"] == "120000":
                if target.exists():
                    target.unlink()
                target.symlink_to(data.decode())
            else:
                target.write_bytes(data)
        return path, data

    while pending := selected - contents.keys():
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
            contents.update(pool.map(fetch, sorted(pending)))
        for path, data in list(contents.items()):
            if entries[path]["mode"] != "120000":
                continue
            destination = posixpath.normpath(posixpath.join(posixpath.dirname(path), data.decode()))
            if destination.startswith("../") or destination.startswith("/") or destination not in entries:
                raise RuntimeError(f"Unresolved PDK symlink: {path} -> {destination}")
            if entries[destination]["type"] == "tree":
                selected.update(p for p, e in entries.items() if e["type"] == "blob" and p.startswith(destination + "/"))
            elif entries[destination]["type"] == "blob":
                selected.add(destination)
            else:
                raise RuntimeError(f"Uninstalled submodule dependency: {destination}")
    receipt = {
        "revision": revision, "tree_sha256": lock["pdk_tree_sha256"],
        "files_sha256": {p: hashlib.sha256(data).hexdigest() for p, data in sorted(contents.items()) if entries[p]["mode"] != "120000"},
        "symlinks": {p: data.decode() for p, data in sorted(contents.items()) if entries[p]["mode"] == "120000"},
        "scope": "Digital-flow views and transitive symlink dependencies; not the full analog PDK or unused SRAM library",
    }
    (OUT / "installed.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Verified {len(contents)} pinned PDK files/links")


if __name__ == "__main__":
    main()
