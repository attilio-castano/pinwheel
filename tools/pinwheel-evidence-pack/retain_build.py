#!/usr/bin/env python3
"""Retain a whole ignored build without following links or editing receipts.

This is independent of the receipt-bound pack.py collector. Collection requires
macOS clone-copy support; verification is host-only and needs no original tree.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import stat
import subprocess
import sys
import time
from datetime import datetime, timezone


SCHEMA = "pinwheel-whole-build-retention-v1"


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def exclusive_json(path: Path, value: object) -> str:
    data = json_bytes(value)
    with path.open("xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    return digest(data)


def identity(info: os.stat_result) -> dict:
    return {
        "device": info.st_dev,
        "inode": info.st_ino,
        "mtime_ns": info.st_mtime_ns,
        "ctime_ns": info.st_ctime_ns,
    }


def file_sha(path: Path, before: os.stat_result) -> str:
    checksum = hashlib.sha256()
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    with os.fdopen(fd, "rb") as stream:
        opened = os.fstat(stream.fileno())
        if identity(opened) != identity(before) or opened.st_size != before.st_size:
            raise ValueError(f"File changed before hashing: {path}")
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            checksum.update(block)
        after = os.fstat(stream.fileno())
        if (identity(after), after.st_size, stat.S_IMODE(after.st_mode)) != (
            identity(before), before.st_size, stat.S_IMODE(before.st_mode)
        ):
            raise ValueError(f"File changed while hashing: {path}")
    return checksum.hexdigest()


def inventory(root: Path, *, progress: bool = False) -> dict[str, dict]:
    """Inventory each directory, regular file and link exactly once; never follow links."""
    if root.is_symlink():
        raise ValueError(f"Inventory root must be a real directory: {root}")
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError(f"Inventory root must be a directory: {root}")
    result: dict[str, dict] = {}
    pending = [root]
    last_progress = time.monotonic()
    while pending:
        path = pending.pop()
        rel = str(path.relative_to(root))
        info = path.lstat()
        entry = {"mode": stat.S_IMODE(info.st_mode), "identity": identity(info)}
        if stat.S_ISLNK(info.st_mode):
            target = os.readlink(path)
            if os.path.isabs(target):
                raise ValueError(f"Absolute symlink is not portable: {path}")
            resolved = path.resolve(strict=True)
            if not resolved.is_relative_to(root):
                raise ValueError(f"Symlink leaves retained tree: {path}")
            entry.update(kind="symlink", target=target,
                         resolved_relative=str(resolved.relative_to(root)),
                         target_kind="directory" if resolved.is_dir() else "file")
        elif stat.S_ISDIR(info.st_mode):
            entry["kind"] = "directory"
            pending.extend(sorted(path.iterdir(), reverse=True))
        elif stat.S_ISREG(info.st_mode):
            entry.update(kind="file", size=info.st_size, sha256=file_sha(path, info))
        else:
            raise ValueError(f"Unsupported special filesystem object: {path}")
        result[rel] = entry
        if progress and time.monotonic() - last_progress >= 30:
            print(json.dumps({"UTC": utc(), "event": "inventory_progress",
                              "root": str(root), "entries": len(result)}), flush=True)
            last_progress = time.monotonic()
    return dict(sorted(result.items()))


def payload(entries: dict[str, dict]) -> dict[str, dict]:
    return {name: {k: v for k, v in item.items() if k != "identity"}
            for name, item in entries.items()}


def compare(expected: dict[str, dict], actual: dict[str, dict], label: str) -> None:
    if expected != actual:
        differing = sorted(set(expected) ^ set(actual))
        differing += [name for name in sorted(set(expected) & set(actual))
                      if expected[name] != actual[name]]
        raise ValueError(f"{label} mismatch ({len(differing)} paths): {differing[:12]}")


def independent_inodes(source: dict[str, dict], destination: dict[str, dict]) -> None:
    origins = {(v["identity"]["device"], v["identity"]["inode"])
               for v in source.values() if v["kind"] == "file"}
    reused = [name for name, item in destination.items()
              if item["kind"] == "file" and
              (item["identity"]["device"], item["identity"]["inode"]) in origins]
    if reused:
        raise ValueError(f"Destination shares source file inodes: {reused[:12]}")


def clone_copy(source: Path, destination: Path, log: Path) -> None:
    if sys.platform != "darwin":
        raise ValueError("Collection requires macOS /bin/cp clone-copy support")
    with log.open("xb") as stream:
        subprocess.run(["/bin/cp", "-cRpP", str(source), str(destination)],
                       stdout=stream, stderr=subprocess.STDOUT, check=True)


def collect(source: Path, archive: Path) -> dict:
    if source.is_symlink():
        raise ValueError("Source root must be a real directory")
    source = source.resolve(strict=True)
    if not source.is_dir():
        raise ValueError("Source must be a directory")
    archive = archive.parent.resolve(strict=True) / archive.name
    if archive == source or archive.is_relative_to(source) or source.is_relative_to(archive):
        raise ValueError("Source and archive must be disjoint")
    # Exclusive creation precedes all writes. Existing destinations are never reused.
    archive.mkdir(mode=0o700)
    started = utc()
    destination = archive / "build"
    try:
        print(json.dumps({"UTC": started, "event": "hash_source_before"}), flush=True)
        before = inventory(source, progress=True)
        before_sha = exclusive_json(archive / "source-before.json", before)
        print(json.dumps({"UTC": utc(), "event": "clone_copy"}), flush=True)
        clone_copy(source, destination, archive / "copy.log")
        print(json.dumps({"UTC": utc(), "event": "hash_destination"}), flush=True)
        copied = inventory(destination, progress=True)
        compare(payload(before), payload(copied), "Destination content/mode/link")
        independent_inodes(before, copied)
        print(json.dumps({"UTC": utc(), "event": "rehash_source_after"}), flush=True)
        after = inventory(source, progress=True)
        compare(before, after, "Source stability including identity and timestamps")
        manifest = {
            "schema": SCHEMA,
            "source_root": str(source),
            "destination_root_at_collection": str(destination),
            "source_before_sha256": before_sha,
            "entries": payload(before),
            "source_identities": {k: v["identity"] for k, v in before.items()},
            "destination_identities": {k: v["identity"] for k, v in copied.items()},
            "physical_acceptance_claim": False,
            "external_runtime_packed": False,
            "original_absolute_receipt_paths_rewritten": False,
        }
        manifest_sha = exclusive_json(archive / "manifest.json", manifest)
        kinds = {kind: sum(v["kind"] == kind for v in before.values())
                 for kind in ("file", "directory", "symlink")}
        report = {
            "schema": SCHEMA,
            "status": "copied_and_fully_verified",
            "started_UTC": started,
            "finished_UTC": utc(),
            "source_root": str(source),
            "archive_root": str(archive),
            "copy_argv": ["/bin/cp", "-cRpP", str(source), str(destination)],
            "entry_counts": kinds,
            "regular_file_bytes": sum(v.get("size", 0) for v in before.values()),
            "all_regular_file_SHA256_and_modes_match": True,
            "all_directory_modes_match": True,
            "all_relative_symlinks_and_resolved_targets_match": True,
            "source_inventory_and_all_file_hashes_unchanged": True,
            "destination_file_inodes_independent_from_all_source_files": True,
            "source_before_sha256": before_sha,
            "manifest_sha256": manifest_sha,
            "helper_sha256": digest(Path(__file__).read_bytes()),
            "host_platform": platform.platform(),
            "python": sys.version,
            "physical_acceptance_claim": False,
            "external_runtime_packed": False,
            "archive_is_a_local_copy_not_an_offsite_backup": True,
        }
        exclusive_json(archive / "retention-report.json", report)
        return report
    except BaseException as exc:
        exclusive_json(archive / "retention-failed.json", {
            "schema": SCHEMA, "status": "failed_not_accepted", "UTC": utc(),
            "error_type": type(exc).__name__, "error": str(exc),
            "source_root": str(source), "archive_root": str(archive),
            "partial_outputs_preserved": True,
        })
        raise


def verify(archive: Path, manifest_sha256: str) -> dict:
    """Read-only offline destination verification against an externally pinned manifest."""
    archive = archive.resolve(strict=True)
    raw = (archive / "manifest.json").read_bytes()
    if digest(raw) != manifest_sha256:
        raise ValueError("Manifest digest differs from external pin")
    manifest = json.loads(raw)
    if manifest.get("schema") != SCHEMA:
        raise ValueError("Unsupported retention manifest schema")
    current = inventory(archive / "build", progress=True)
    compare(manifest["entries"], payload(current), "Retained destination")
    return {"schema": SCHEMA, "status": "verified_retained_build",
            "archive_root": str(archive), "manifest_sha256": manifest_sha256,
            "entries": len(current), "source_available_or_unchanged_claim": False,
            "physical_acceptance_claim": False, "external_runtime_packed": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("collect")
    create.add_argument("--source", type=Path, required=True)
    create.add_argument("--archive-root", type=Path, required=True)
    check = commands.add_parser("verify")
    check.add_argument("--archive-root", type=Path, required=True)
    check.add_argument("--manifest-sha256", required=True)
    args = parser.parse_args()
    result = collect(args.source, args.archive_root) if args.command == "collect" else verify(
        args.archive_root, args.manifest_sha256)
    print(json.dumps(result, sort_keys=True, indent=2), flush=True)


if __name__ == "__main__":
    main()
