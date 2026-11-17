#!/usr/bin/env python3
"""Fetch or verify the pinned official ISA PDF in the ignored build cache."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def verify(data, manifest):
    if not data.startswith(b"%PDF-") or len(data) != manifest["bytes"] or \
            hashlib.sha256(data).hexdigest() != manifest["sha256"]:
        raise ValueError("ISA PDF identity mismatch; refusing to use or replace it")


def main():
    manifest = json.loads((ROOT / "tools/riscv-isa.json").read_text())
    filename = manifest["filename"]
    if manifest.get("schema") != 1 or not isinstance(filename, str) or Path(filename).name != filename or \
            not filename.endswith(".pdf") or type(manifest["bytes"]) is not int or not 0 < manifest["bytes"] <= 8_000_000 or \
            not re.fullmatch(r"[0-9a-f]{64}", manifest["sha256"]) or \
            not manifest["url"].startswith("https://docs.riscv.org/reference/isa/"):
        raise ValueError("Malformed ISA source manifest")
    destination = ROOT / "build/specifications" / filename
    if destination.exists():
        data = destination.read_bytes()
        verify(data, manifest)
    else:
        with urllib.request.urlopen(manifest["url"], timeout=30) as response:
            data = response.read(manifest["bytes"] + 1)
        verify(data, manifest)
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("xb") as output:
            output.write(data)
    print(f"Verified {destination}: {manifest['bytes']} bytes, SHA-256 {manifest['sha256']}")


if __name__ == "__main__":
    main()
