#!/usr/bin/env python3
"""Verify historical source mirrors without importing or executing them."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


HERE = Path(__file__).resolve().parent


def strict_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("Duplicate JSON key: " + key)
        result[key] = value
    return result


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bound_file(root: Path, relative: str) -> Path:
    require(isinstance(relative, str) and relative, "Expected relative path")
    parts = PurePosixPath(relative)
    require(not parts.is_absolute() and all(p not in (".", "..") for p in parts.parts),
            "Unsafe relative path: " + relative)
    require(str(parts) == relative and "\\" not in relative,
            "Noncanonical relative path: " + relative)
    path = root
    for part in parts.parts:
        path = path / part
        require(not path.is_symlink(), "Symlink is not an archived regular file: " + str(path))
    require(path.is_file() and path.resolve().is_relative_to(root.resolve()),
            "Missing or escaping file: " + str(path))
    return path


def verify(archive: Path, origin_root: Path | None = None) -> dict:
    archive = archive.resolve()
    manifest_path = archive / "SOURCE-MANIFEST.json"
    require(not manifest_path.is_symlink(), "Manifest must be a regular file")
    raw = manifest_path.read_bytes()
    manifest = json.loads(raw, object_pairs_hook=strict_object)
    require(manifest.get("schema") == "pinwheel-historical-physical-source-archive-v1",
            "Unexpected source manifest schema")
    require(manifest.get("native_or_physical_acceptance_claim") is False,
            "Source archive cannot assert native acceptance")
    entries = manifest.get("files")
    require(isinstance(entries, list) and entries, "Expected nonempty source file list")
    seen_original, seen_archived, groups = set(), set(), set()
    total_bytes = total_lines = 0
    for entry in entries:
        require(isinstance(entry, dict) and set(entry) == {
            "original_relative_path", "archived_relative_path", "sha256", "bytes"},
            "Unexpected source record fields")
        original = entry["original_relative_path"]
        archived = entry["archived_relative_path"]
        digest = entry["sha256"]
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) is not None,
                "Malformed SHA256")
        require(type(entry["bytes"]) is int and entry["bytes"] >= 0, "Invalid file size")
        require(original not in seen_original and archived not in seen_archived,
                "Duplicate original or archived file identity")
        seen_original.add(original)
        seen_archived.add(archived)
        original_parts = PurePosixPath(original)
        archived_parts = PurePosixPath(archived)
        require(len(original_parts.parts) == 4 and original_parts.parts[:2] == ("build", "physical"),
                "Unexpected original source location: " + original)
        require(archived_parts == PurePosixPath("snapshots") / original_parts.parent.name / original_parts.name,
                "Archive mirror changed source directory or filename")
        groups.add(original_parts.parent.name)
        path = bound_file(archive, archived)
        data = path.read_bytes()
        require(len(data) == entry["bytes"] and hashlib.sha256(data).hexdigest() == digest,
                "Archived source mismatch: " + archived)
        if origin_root is not None:
            source = bound_file(origin_root, original)
            source_data = source.read_bytes()
            require(len(source_data) == entry["bytes"] and hashlib.sha256(source_data).hexdigest() == digest,
                    "Original source mismatch: " + original)
        total_bytes += len(data)
        total_lines += len(data.splitlines())
    snapshot_root = archive / "snapshots"
    require(snapshot_root.is_dir() and not snapshot_root.is_symlink(), "Missing regular snapshots directory")
    actual = set()
    for path in snapshot_root.rglob("*"):
        require(not path.is_symlink(), "Unexpected archived symlink: " + str(path))
        if path.is_file():
            actual.add(str(path.relative_to(archive)))
        else:
            require(path.is_dir(), "Unexpected nonregular archive entry: " + str(path))
    require(actual == seen_archived, "Archive file inventory differs from manifest")
    for key, value in {"file_count": len(entries), "directory_count": len(groups),
                       "source_bytes": total_bytes, "source_lines": total_lines}.items():
        require(type(manifest.get(key)) is int and manifest[key] == value,
                "Manifest aggregate mismatch: " + key)
    return {"schema": "pinwheel-historical-physical-source-verification-v1",
            "status": "source_bytes_verified", "file_count": len(entries),
            "directory_count": len(groups), "source_bytes": total_bytes,
            "source_lines": total_lines, "originals_checked": origin_root is not None,
            "manifest_sha256": hashlib.sha256(raw).hexdigest(),
            "native_or_physical_acceptance_claim": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=HERE)
    parser.add_argument("--origins", action="store_true",
                        help="Also compare each retained original source file")
    parser.add_argument("--origin-root", type=Path, default=HERE.parents[1],
                        help="Original checkout root; used only with --origins")
    args = parser.parse_args()
    try:
        result = verify(args.archive, args.origin_root.resolve() if args.origins else None)
    except (ValueError, OSError, TypeError, KeyError) as exc:
        print("Source archive verification failed: " + str(exc), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
