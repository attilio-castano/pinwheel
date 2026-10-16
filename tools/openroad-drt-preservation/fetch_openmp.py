"""Configure the official matching OpenMP header using its source CMake values."""
import hashlib
import json
from pathlib import Path
import re
import sys
import urllib.request

root = Path(sys.argv[1]).resolve()
out = root / "source-extra-02"
out.mkdir(exist_ok=False)
repository = "https://api.github.com/repos/llvm/llvm-project"
def read(url):
    with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "Pinwheel-native-preservation"}), timeout=25) as response:
        data = response.read(2_000_001)
    assert len(data) <= 2_000_000
    return data
commit = json.loads(read(repository + "/commits/llvmorg-21.1.8"))["sha"]
assert re.fullmatch("[0-9a-f]{40}", commit)
paths = ["openmp/runtime/src/include/omp.h.var", "openmp/runtime/CMakeLists.txt",
         "openmp/runtime/src/kmp_version.cpp", "openmp/runtime/cmake/LibompUtils.cmake", "LICENSE.TXT"]
files = {}
contents = {}
for path in paths:
    data = read(f"https://raw.githubusercontent.com/llvm/llvm-project/{commit}/{path}")
    entry = json.loads(read(f"{repository}/contents/{path}?ref={commit}"))
    git_sha = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    assert git_sha == entry["sha"]
    target = out / "upstream" / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    contents[path] = data.decode()
    files[path] = {"git_blob_sha1": git_sha, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
cmake = contents["openmp/runtime/CMakeLists.txt"]
build_source = contents["openmp/runtime/src/kmp_version.cpp"]
variables = {key: re.search(r"set\(" + key + r" ([^)]+)\)", cmake)[1].strip('"')
             for key in ["LIBOMP_VERSION_MAJOR", "LIBOMP_VERSION_MINOR", "LIBOMP_BUILD_DATE"]}
variables["LIBOMP_VERSION_BUILD"] = re.search(r"^#define KMP_VERSION_BUILD (\d+)$", build_source, re.M)[1]
assert variables == {"LIBOMP_VERSION_MAJOR": "5", "LIBOMP_VERSION_MINOR": "0", "LIBOMP_BUILD_DATE": "No_Timestamp", "LIBOMP_VERSION_BUILD": "20140926"}
header = contents["openmp/runtime/src/include/omp.h.var"]
assert set(re.findall(r"@([^@\n]+)@", header)) == set(variables)
for key, value in variables.items():
    header = header.replace("@" + key + "@", value)
(out / "omp.h").write_text(header)
(root / "source-extra-02-fetch.json").write_text(json.dumps({"schema": "pinwheel-matching-llvm-openmp-header-v1", "status": "passed",
    "upstream_release": "llvmorg-21.1.8", "resolved_commit": commit, "files": files, "cmake_substitutions": variables,
    "configured_header_sha256": hashlib.sha256(header.encode()).hexdigest(),
    "native_library": "/nix/store/j2flxsr6nxmvrfna9fbql99j8pf4w11n-openmp-21.1.8/lib/libomp.so",
    "native_library_sha256": "b3ff345bd25740266ae5725c038e12ad72057cea104ce9be431a6c44a9083d4e"}, indent=2) + "\n")
print(commit, hashlib.sha256(header.encode()).hexdigest(), flush=True)
