"""Read-only header/library discovery; caller owns the bounded Docker job."""
import glob
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

patterns = ["/nix/store/*/include/omp.h", "/nix/store/*/lib/clang/*/include/omp.h",
            "/nix/store/*/lib/gcc/*/*/include/omp.h", "/nix/store/*/lib/libomp*", "/nix/store/*/lib/libgomp*"]
found = {}
for pattern in patterns:
    for name in glob.glob(pattern):
        path = Path(name)
        if path.is_file():
            found[name] = {"resolved": str(path.resolve()), "bytes": path.stat().st_size,
                           "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
elf = "/nix/store/c60x0zn4vxd3h2mybmg8i7q55y95i3a6-openroad-2026-02-17/bin/.openroad-wrapped"
ldd = shutil.which("ldd")
libraries = subprocess.run([ldd, elf], capture_output=True, text=True, timeout=10) if ldd else None
Path("/work/diagnostic/probe.json").write_text(json.dumps({"files": found, "native_elf": elf,
    "ldd": libraries.stdout + libraries.stderr if libraries else None}, indent=2) + "\n")
print(json.dumps({"files": found, "ldd": libraries.stdout if libraries else None}, indent=2))
