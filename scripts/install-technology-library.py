#!/usr/bin/env python3
"""Fetch only pinned IHP CMOS5L Liberty corners/license into ignored build/tools."""
import hashlib
import json
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'build/tools/ihp-cmos5l'


def main():
    manifest = json.loads((ROOT/'tools/technology-library.json').read_text())
    OUT.mkdir(parents=True, exist_ok=True)
    for item in manifest['files']:
        destination = OUT/item['name']
        if destination.exists():
            data = destination.read_bytes()
        else:
            repository = manifest['repository'].removeprefix('https://github.com/')
            url = f"https://raw.githubusercontent.com/{repository}/{manifest['commit']}/{item['path']}"
            with urllib.request.urlopen(url, timeout=60) as response:
                data = response.read()
        if hashlib.sha256(data).hexdigest() != item['sha256']:
            raise RuntimeError(f"Hash mismatch: {item['name']}; refusing to use/replace it")
        if not destination.exists(): destination.write_bytes(data)
        print(f"Verified {item['name']}")


if __name__ == '__main__': main()
