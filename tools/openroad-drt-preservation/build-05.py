"""Compile inside the pinned offline image; caller owns Docker/resource limits."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

root = Path(sys.argv[1]).resolve()
support = Path(__file__).resolve().parent
source = root / "source"
generated = root / "generated-03"
out = root / "native-05"
out.mkdir(exist_ok=False)
compiler = "/nix/store/h6vk77gc3300z162ywhcz8asjckrgmr3-clang-wrapper-21.1.8/bin/clang++"
sta = Path("/nix/store/dl4s2h66da8piq4wq9p0ylhc3mmn6wab-opensta-dev/include")
include = [generated / "include", root / "source-extra-01/src/odb/include", source / "include", source / "src/drt/src", *sorted((source / "src").glob("*/include"))]
system = [root / "source-extra-02", sta, Path("/deps/boost/include"), Path("/deps/fmt/include"), Path("/deps/spdlog/include"), Path("/nix/store/xrhg1bl0nlhvz4aipvack0r4ch3q85k1-tcl-8.6.16/include")]
flags = [compiler, "-std=c++20", "-O2", "-DNDEBUG", "-fPIC", "-shared", "-fopenmp", "-Wl,-Bsymbolic", "-L/nix/store/j2flxsr6nxmvrfna9fbql99j8pf4w11n-openmp-21.1.8/lib", "-Wl,-rpath,/nix/store/j2flxsr6nxmvrfna9fbql99j8pf4w11n-openmp-21.1.8/lib", "-DSPDLOG_COMPILED_LIB", "-DSPDLOG_FMT_EXTERNAL", "-DFMT_SHARED", "-DBOOST_STACKTRACE_GNU_SOURCE_NOT_REQUIRED=1"]
flags += ["-I" + str(p) for p in include] + [v for p in system for v in ["-isystem", str(p)]]
assert hashlib.sha256((root / "source-extra-02/omp.h").read_bytes()).hexdigest() == json.loads((root / "source-extra-02-fetch.json").read_text())["configured_header_sha256"]
assert hashlib.sha256(Path("/nix/store/j2flxsr6nxmvrfna9fbql99j8pf4w11n-openmp-21.1.8/lib/libomp.so").read_bytes()).hexdigest() == "b3ff345bd25740266ae5725c038e12ad72057cea104ce9be431a6c44a9083d4e"
records = []
start = time.monotonic()
for label, importer in [("original", source / "src/drt/src/io/io.cpp"), ("patched", generated / "io-patched.cpp")]:
    folder = out / label
    folder.mkdir()
    command = flags + ["-DPW_IMPORTER_PATCHED=" + str(int(label == "patched")), str(importer), str(generated / "entrypoints.cpp"), str(support / "extension-02.cc"), "-o", str(folder / "libpinwheel_drt_preservation.so")]
    t = time.monotonic()
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=240)
    (folder / "compile.log").write_text(result.stdout)
    record = {"variant": label, "command": command, "returncode": result.returncode, "seconds": round(time.monotonic() - t, 3)}
    if result.returncode == 0:
        record["binary_sha256"] = hashlib.sha256((folder / "libpinwheel_drt_preservation.so").read_bytes()).hexdigest()
    records.append(record)
    (out / "build.json").write_text(json.dumps({"status": "running" if result.returncode == 0 else "failed", "commands": records}, indent=2) + "\n")
    if result.returncode:
        raise RuntimeError(result.stdout[-6000:])
(out / "build.json").write_text(json.dumps({"status": "passed", "seconds": round(time.monotonic() - start, 3), "commands": records}, indent=2) + "\n")
print("Built original and patched adapters", round(time.monotonic() - start, 3), flush=True)
