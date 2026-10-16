"""Fetch a bounded, Git-object-verified pinned header/source subset; never builds."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
import time
import urllib.request

REV = "dcf36133a369abc8f3c5e5738cd4d82e4903c0e0"
REPO = "https://api.github.com/repos/The-OpenROAD-Project/OpenROAD"
RAW = f"https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD/{REV}/"
MAX_BYTES = 30_000_000

def get(url, maximum=15_000_000):
    request = urllib.request.Request(url, headers={"User-Agent": "Pinwheel-source-preservation"})
    with urllib.request.urlopen(request, timeout=30) as response:
        data = response.read(maximum + 1)
    assert len(data) <= maximum, (url, len(data))
    return data

def main():
    output = Path(sys.argv[1]).resolve()
    assert output.name == "source" and output.parent.name == "tt-overnight-taper-tools-01"
    output.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    commit = json.loads(get(f"{REPO}/git/commits/{REV}"))
    assert commit["sha"] == REV
    metadata = get(f"{REPO}/git/trees/{commit['tree']['sha']}?recursive=1")
    tree = json.loads(metadata)
    assert tree["truncated"] is False and tree["sha"] == commit["tree"]["sha"]
    explicit = {"src/drt/src/TritonRoute.cpp", "src/drt/src/TritonRoute.i",
                "src/drt/src/io/io.cpp", "src/drt/src/io/io_post_process.cpp",
                "src/drt/src/drt.tcl", "src/drt/src/TritonRoute.tcl", "LICENSE"}
    entries = []
    for item in tree["tree"]:
        path = item["path"]
        header = path.endswith((".h", ".hh", ".hpp")) and (
            path.startswith("include/") or path.startswith("src/drt/") or "/include/" in path)
        if item["type"] == "blob" and (header or path in explicit):
            entries.append(item)
    assert 10 <= len(entries) <= 2000 and sum(i.get("size", 0) for i in entries) <= MAX_BYTES
    def fetch(item):
        data = get(RAW + item["path"], 4_000_000)
        assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == item["sha"]
        target = output / item["path"]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        return item["path"], {"git_blob_sha1": item["sha"], "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    with ThreadPoolExecutor(max_workers=12) as pool:
        files = dict(pool.map(fetch, entries))
    assert sum(i["bytes"] for i in files.values()) <= MAX_BYTES
    (output.parent / "source-fetch.json").write_text(json.dumps({
        "revision": REV, "status": "passed", "file_count": len(files),
        "total_bytes": sum(i["bytes"] for i in files.values()),
        "tree_sha256": hashlib.sha256(metadata).hexdigest(), "files": files,
        "seconds": round(time.monotonic() - start, 3)}, indent=2) + "\n")
    print(len(files), sum(i["bytes"] for i in files.values()), "bytes", flush=True)

if __name__ == "__main__":
    main()
