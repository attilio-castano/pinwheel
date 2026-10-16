"""Load bounded, SHA-bound host fixtures without reading ignored build inputs."""
from __future__ import annotations

import gzip
import hashlib
import io
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
FIXTURES = HERE / "fixtures"
REPOSITORY = HERE.parents[2]
MAX_FIXTURE_BYTES = 3_000_000
FILES = {
    "p2-onepass-native": ("p2-onepass-native.log.txt", "utf-8", "passed", 0),
    "p2-control-native": ("p2-control-native.log.txt", "utf-8", "failed", 1),
    "p2-partial-native": ("p2-partial-native.log.txt", "utf-8", "timed_out", 124),
    "p2-onepass-report": ("p2-onepass-violations.rpt.gz", "gzip", "passed", 0),
}
NATIVE_SOURCE = "tools/pinwheel-physical-history/snapshots/tt-p2-drt-onepass-route-01/native.py"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def strict_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate fixture manifest key: " + key)
        result[key] = value
    return result


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load_manifest(fixture_root=FIXTURES):
    path = Path(fixture_root) / "manifest.json"
    require(path.is_file() and not path.is_symlink(), "Missing regular fixture manifest")
    manifest = json.loads(path.read_text(), object_pairs_hook=strict_object)
    require(manifest["schema"] == "pinwheel-campaign-host-fixtures-v1", "Unexpected fixture schema")
    require(manifest["native_or_physical_acceptance_claim"] is False,
            "Host fixtures cannot establish physical acceptance")
    require(set(manifest["files"]) == set(FILES), "Unexpected fixture inventory")
    for name, (filename, encoding, status, exit_code) in FILES.items():
        entry = manifest["files"][name]
        require((entry["stored_path"], entry["encoding"]) == (filename, encoding),
                "Unexpected fixture path or encoding: " + name)
        for key in ("stored_bytes", "raw_bytes"):
            require(type(entry[key]) is int and 0 < entry[key] <= MAX_FIXTURE_BYTES,
                    "Unbounded fixture size: " + name)
        for key in ("stored_sha256", "raw_sha256"):
            require(isinstance(entry[key], str) and re.fullmatch(r"[0-9a-f]{64}", entry[key]),
                    "Malformed fixture digest: " + name)
        require((entry["producer_receipt"]["status"], entry["producer_receipt"]["exit_code"])
                == (status, exit_code), "Historical producer outcome changed: " + name)
    require(manifest["native_program"]["repository_relative_path"] == NATIVE_SOURCE,
            "Unexpected native source fixture path")
    return manifest


def checked_bytes(path, size, digest, label):
    require(path.is_file() and not path.is_symlink(), "Missing regular fixture: " + label)
    require(path.stat().st_size == size, "Stored fixture size mismatch: " + label)
    data = path.read_bytes()
    require(sha(data) == digest, "Stored fixture digest mismatch: " + label)
    return data


def load_text(name, fixture_root=FIXTURES):
    require(name in FILES, "Unknown fixture: " + str(name))
    entry = load_manifest(fixture_root)["files"][name]
    stored = checked_bytes(Path(fixture_root) / entry["stored_path"],
                           entry["stored_bytes"], entry["stored_sha256"], name)
    if entry["encoding"] == "gzip":
        require(stored[:3] == b"\x1f\x8b\x08" and stored[4:8] == b"\0" * 4,
                "Expected gzip fixture with mtime=0: " + name)
        with gzip.GzipFile(fileobj=io.BytesIO(stored), mode="rb") as compressed:
            raw = compressed.read(entry["raw_bytes"] + 1)
    else:
        raw = stored
    require(len(raw) == entry["raw_bytes"] and sha(raw) == entry["raw_sha256"],
            "Raw fixture digest or size mismatch: " + name)
    return raw.decode("utf-8")


def native_program_bytes():
    entry = load_manifest()["native_program"]
    return checked_bytes(REPOSITORY / NATIVE_SOURCE, entry["bytes"], entry["sha256"],
                         "tracked native source")
