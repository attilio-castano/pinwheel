#!/usr/bin/env python3
"""Record native/interpreted FastEmit compatibility with explicit build provenance.

This is finite exporter evidence, not a proof of the unsafe replacement, Lean's
native compiler, generated RTL, or the operating system. Currently the native
receipt supports the installed macOS Lean toolchain (bundled clang/ld64.lld).
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import shlex
import shutil
import sys
import time

import process_group

ROOT = Path(__file__).resolve().parents[1]
TEST = Path("test/HardwareFastEmit.lean")
MODULE = "Pinwheel.Hardware.FastEmit"
SIDECARS = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".ilean")


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def hashes(paths):
    return {str(path): sha(path) for path in sorted(set(map(Path, paths)))}


def imports(path):
    return [module for line in Path(path).read_text().splitlines()
            if (match := re.fullmatch(r"import\s+(.+)", line))
            for module in match[1].split("--", 1)[0].split()]


def source_paths():
    pending, seen = [ROOT / TEST], set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for module in imports(path):
            candidate = ROOT / (module.replace(".", "/") + ".lean")
            if candidate.is_file():
                pending.append(candidate)
    seen.update(ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "scripts/check-fast-emit.py", "scripts/process_group.py"))
    return seen


def source_hashes():
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(source_paths())}


class Commands:
    def __init__(self, out, records, environment):
        self.out, self.records, self.environment = out, records, environment

    def __call__(self, command, label, timeout=300, environment=None):
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", label):
            raise ValueError("Invalid command label")
        log = self.out / (label + ".log")
        if log.exists():
            raise FileExistsError(log)
        env = self.environment | (environment or {})
        argv = ["/usr/bin/env", "-i", *[key + "=" + value for key, value in sorted(env.items())],
                *map(str, command)]
        record = {"label": label, "argv": argv, "timeout_seconds": timeout}
        self.records.append(record)
        start = time.monotonic()
        try:
            result = process_group.run_captured(argv, cwd=ROOT, timeout=timeout, log_path=log)
            record["exit_code"] = result.returncode
            if result.returncode:
                raise RuntimeError(f"{label} failed: {result.stderr[-2000:]}; see {log}")
        except BaseException as error:
            record["error"] = type(error).__name__
            raise
        finally:
            record["seconds"] = round(time.monotonic() - start, 3)
        print(label + ": passed", flush=True)
        return result.stdout, result.stderr


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def parse_results(text, audit):
    pattern = r"FastEmit: (\d+) complete byte comparisons, (\d+) zero-width errors, (\d+) shared operations\."
    matches = re.findall(pattern, text)
    require(matches == [("29", "10", "1280")], "Missing or malformed complete FastEmit results")
    stress = re.findall(r"Shared DAG: 5 widths × 256 levels, 40 outputs, 1280 operations, (\d+)ms", text)
    require(len(stress) == 1 and int(stress[0]) <= 30000, "Missing or over-budget DAG result")
    if audit:
        require(text.count("FastEmit logical API: 2 declarations, standard axioms only; native exporter remains untrusted.") == 1,
                "Missing standard-only logical API audit")
    return {"byte_comparisons": 29, "zero_width_cases": 10, "stress_operations": 1280,
            "stress_milliseconds": int(stress[0]), "logical_declarations_audited": 2 if audit else 0}


def parse_plan(stderr, compiler, linker):
    """Accept only the expected compiler and linker in clang's dry-run output."""
    commands = [shlex.split(line) for line in stderr.splitlines() if line.startswith(' "')]
    require(len(commands) == 2, "Expected one native compilation and one link in the dry-run")
    require(Path(commands[0][0]).resolve() == compiler and "-cc1" in commands[0],
            "Native compilation selected a different compiler")
    require(Path(commands[1][0]).resolve() == linker, "Native compilation selected a different linker")
    return commands


def header_paths(path):
    content = path.read_text().replace("\\\n", " ")
    target, separator, body = content.partition(":")
    require(separator and target.strip(), "Malformed compiler header dependencies")
    paths = {Path(item).resolve() for item in shlex.split(body)}
    require(paths and all(path.is_file() for path in paths), "Missing compiler header input")
    return paths


def linked_files(text):
    """ld64.lld -t reports actual input files, including archive(member) rows."""
    paths = set()
    for line in text.splitlines():
        require(line.startswith("/"), "Unexpected native linker trace row: " + line)
        value = line.split("(", 1)[0]
        path = Path(value)
        require(path.is_file(), "Missing input named by linker trace: " + value)
        paths.add(path.resolve())
    require(paths, "No native linker inputs were reported")
    return paths


def dynamic_closure(run, roots, prefix, label):
    """Hash file-backed dylibs; explicitly expose Apple's dyld-cache boundary."""
    pending = [(Path(root).resolve(), Path(root).resolve().parent, []) for root in roots]
    seen, records, files = set(), [], set()
    while pending:
        path, executable_dir, inherited = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        text, _ = run(["/usr/bin/otool", "-L", path], f"{label}-dylibs-{len(seen):03}")
        loads, _ = run(["/usr/bin/otool", "-l", path], f"{label}-load-commands-{len(seen):03}")
        rpaths = re.findall(r"cmd LC_RPATH\s+cmdsize \d+\s+path (.*?) \(offset \d+\)", loads)
        def expand(value):
            return Path(value.replace("@loader_path", str(path.parent)).replace("@executable_path", str(executable_dir))).resolve()
        search = [expand(value) for value in rpaths] + inherited
        for line in text.splitlines()[1:]:
            match = re.fullmatch(r"\s*(\S+) \(compatibility version ([^,]+), current version ([^)]+)\)", line)
            require(match is not None, "Malformed otool dependency row: " + line)
            name = match[1]
            if name.startswith("@rpath/"):
                relative = name[len("@rpath/"):]
                candidates = [directory / relative for directory in search]
                candidates = [p.resolve() for p in candidates if p.is_file()]
                require(len(set(candidates)) == 1, "Ambiguous/unresolved runtime dependency: " + name)
                resolved = candidates[0]
            elif name.startswith("@loader_path/"):
                resolved = (path.parent / name[len("@loader_path/"):]).resolve()
            elif name.startswith("@executable_path/"):
                resolved = (executable_dir / name[len("@executable_path/"):]).resolve()
            else:
                require(name.startswith("/"), "Unknown runtime dependency: " + name)
                resolved = Path(name)
            row = {"consumer": str(path), "install_name": name, "resolved": str(resolved),
                   "compatibility_version": match[2], "current_version": match[3],
                   "rpath_search": list(map(str, search))}
            if resolved.is_file():
                files.add(resolved)
                pending.append((resolved, executable_dir, search))
                row["custody"] = "file_sha256"
            else:
                require(str(resolved).startswith(("/usr/lib/", "/System/Library/")),
                        "Missing non-system runtime library: " + str(resolved))
                row["custody"] = "macOS dyld shared cache; install name/version only, not hashed or qualified"
            records.append(row)
    return records, files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    require(re.fullmatch(r"[A-Za-z0-9_-]+", args.tag), "Invalid receipt tag")
    require(sys.platform == "darwin", "This receipt currently supports macOS bundled Lean tools only")
    out = ROOT / "build/fast-emit" / args.tag
    out.mkdir(parents=True, exist_ok=False)
    (out / "tmp").mkdir()
    # Resolve the installed pinned toolchain directly; no elan auto-install/network action.
    pin = (ROOT / "lean-toolchain").read_text().strip()
    require(re.fullmatch(r"leanprover/lean4:v[0-9.]+", pin), "Unsupported toolchain pin")
    prefix = (Path.home() / ".elan/toolchains" / pin.replace("/", "--").replace(":", "---")).resolve()
    tools = {name: (prefix / "bin" / name).resolve() for name in ("lean", "lake", "leanc", "clang", "ld64.lld")}
    require(all(path.is_file() for path in tools.values()), "Pinned local toolchain is incomplete; no installation attempted")
    environment = {"PATH": str(prefix / "bin") + ":/usr/bin:/bin", "HOME": str(Path.home()),
                   "TMPDIR": str(out / "tmp") + "/", "LANG": "C", "LC_ALL": "C",
                   "LEAN_SYSROOT": str(prefix), "MACOSX_DEPLOYMENT_TARGET": "99.0"}
    report = {"passed": False, "schema": 1, "toolchain_pin": pin, "toolchain_prefix": str(prefix),
              "invocation": [sys.executable, *sys.argv],
              "source_sha256": source_hashes(), "commands": [], "environment": environment,
              "host": {"platform": platform.platform(), "machine": platform.machine()},
              "boundary": "Finite native/interpreted compatibility and DAG stress only. Logical rfl does not certify unsafe native code or exported RTL. Existing imported modules are built by Lake and their exact build inputs are hashed; this is not a clean compiler rebuild. macOS dyld-cache system libraries/OS are recorded, not hash-qualified."}
    run = Commands(out, report["commands"], environment)
    before_inputs, before_tools = {}, {}
    try:
        tool_files = set(tools.values()) | {Path(sys.executable).resolve(), Path("/usr/bin/env"),
                     Path("/usr/bin/otool"), Path("/usr/bin/sw_vers"),
                     prefix / "src/lean/Leanc.lean", prefix / "src/lean/Lean/Compiler/FFI.lean"}
        before_tools = hashes(tool_files)
        for name in ("lean", "lake", "clang", "ld64.lld"):
            report[name + "_version"] = "".join(run([tools[name], "--version"], name + "-version")).strip()
        report["os_version"] = "".join(run(["/usr/bin/sw_vers"], "os-version")).strip()
        report["leanc_cflags"] = run([tools["leanc"], "--print-cflags"], "leanc-cflags")[0].strip()
        report["leanc_ldflags"] = run([tools["leanc"], "--print-ldflags"], "leanc-ldflags")[0].strip()
        runtime, dynlibs = dynamic_closure(run, tools.values(), prefix, "tool")
        require(hashes(tool_files) == before_tools, "Tool identity changed during discovery")
        tool_files |= dynlibs
        before_tools = hashes(tool_files)
        report["tool_sha256"] = before_tools
        report["tool_runtime_dependencies"] = runtime
        # Lake uses the unchanged bundled tool configuration for module objects.
        run([tools["lake"], "build", MODULE + ":dynlib"], "native-modules")
        deps = run([tools["lake"], "env", tools["lean"], "--deps", TEST], "lean-deps")[0]
        direct = sorted({Path(line).resolve() for line in deps.splitlines() if line})
        require(direct and all(path.suffix == ".olean" and path.is_file() for path in direct),
                "Malformed Lean dependency output")
        report["lean_direct_dependencies"] = list(map(str, direct))
        manifest = out / "ImportManifest.lean"
        manifest.write_text("\n".join("import " + module for module in imports(ROOT / TEST)) + '''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for moduleName in env.header.moduleNames do
    let path ← findOLean moduleName
    rows := rows.push (Json.mkObj [("module", toJson moduleName.toString), ("olean", toJson path.toString)])
  liftIO (IO.println ("FAST_EMIT_IMPORTS=" ++ (toJson rows).compress))
''')
        output = run([tools["lake"], "env", tools["lean"], "-DwarningAsError=true", manifest], "lean-import-manifest")[0]
        lines = [line.removeprefix("FAST_EMIT_IMPORTS=") for line in output.splitlines()
                 if line.startswith("FAST_EMIT_IMPORTS=")]
        require(len(lines) == 1, "Missing transitive Lean import manifest")
        modules = json.loads(lines[0])
        require(modules and len({row["module"] for row in modules}) == len(modules), "Invalid import manifest")
        (out / "imports.json").write_text(json.dumps(modules, indent=2) + "\n")
        imported = set()
        for row in modules:
            olean = Path(row["olean"]).resolve()
            require(olean.is_file() and olean.suffix == ".olean", "Missing imported olean")
            require(olean.is_relative_to(prefix) or olean.is_relative_to(ROOT / ".lake/build/lib/lean"),
                    "Import resolved outside the pinned toolchain/project build")
            for suffix in SIDECARS:
                path = olean.with_suffix(suffix)
                if path.is_file():
                    imported.add(path)
        require(set(direct) <= imported, "Direct dependencies absent from transitive manifest")
        local = sorted(path for path in source_paths() if path.is_relative_to(ROOT / "Pinwheel"))
        objects, build_files = [], set(imported)
        for source in local:
            relative = source.relative_to(ROOT).with_suffix("")
            stem = ROOT / ".lake/build/ir" / relative
            obj = Path(str(stem) + ".c.o.export")
            require(obj.is_file(), "Missing exported module object: " + str(obj))
            target = out / "linked-objects" / relative.with_suffix(".c.o.export")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(obj, target)
            require(sha(obj) == sha(target), "Object changed while copied")
            objects.append(target)
            build_files.update(path for path in stem.parent.glob(stem.name + ".*") if path.is_file())
            libstem = ROOT / ".lake/build/lib/lean" / relative
            build_files.update(path for path in libstem.parent.glob(libstem.name + ".*") if path.is_file())
            dylibstem = "pinwheel_" + "_".join(relative.parts) + ".dylib"
            dylibs = list((ROOT / ".lake/build/lib/lean").glob(dylibstem + "*"))
            require(any(path.name == dylibstem for path in dylibs), "Missing Lake module dynlib")
            build_files.update(path for path in dylibs if path.is_file())
        require(len(objects) == 13, "FastEmit local native closure changed; review the object set")
        report["linked_object_sha256"] = hashes(objects)
        report["import_manifest_modules"] = len(modules)
        report["imported_artifact_scope"] = "Compiler-resolved transitive modules plus every present olean/private/server/IR/signature/ilean sidecar; conservative superset, not a claim every sidecar is loaded"
        before_inputs = hashes(build_files)
        report["build_input_sha256"] = before_inputs
        # Pin native compilation explicitly. LEAN_CC drops internal wrapper flags;
        # restore the installed bundled sysroot/header/lib policy explicitly.
        native_env = {"LEAN_CC": str(tools["clang"])}
        native_flags = ["--sysroot", prefix, "-nostdinc", "-isystem", prefix / "include/clang",
                        "-L", prefix / "lib", "-L", prefix / "lib/libc",
                        "-fuse-ld=" + str(tools["ld64.lld"])]
        report["native_compiler_policy"] = {"LEAN_CC": str(tools["clang"]),
                                             "explicit_bundled_flags": list(map(str, native_flags))}
        interpreted = "".join(run([tools["lake"], "env", tools["lean"], "-DwarningAsError=true", "--run", TEST], "interpreted-tests"))
        report["interpreted"] = parse_results(interpreted, audit=True)
        generated = out / "test.c"
        run([tools["lake"], "env", tools["lean"], "-DwarningAsError=true", "-c", generated, TEST], "compile-tests")
        executable = out / "test"
        command = [tools["leanc"], *native_flags, "-O3", "-o", executable, generated, *objects]
        _, plan = run([*command, "-v", "-###"], "native-plan", environment=native_env)
        report["native_plan"] = parse_plan(plan, tools["clang"], tools["ld64.lld"])
        # The input/header census is captured before compilation, then rechecked.
        header_file = out / "native-headers.d"
        run([tools["leanc"], *native_flags, "-M", "-MF", header_file, generated], "native-headers", environment=native_env)
        native_inputs = header_paths(header_file)
        # Toolchain libraries are candidate linker inputs; -t below identifies
        # the actual subset. Hash before link, so mid-run replacement is caught.
        compiler_plan = report["native_plan"][0]
        resource = Path(compiler_plan[compiler_plan.index("-resource-dir") + 1])
        require(resource.is_relative_to(prefix), "Compiler selected a foreign resource directory")
        candidate_libs = {path.resolve() for directory in [prefix / "lib", prefix / "lib/lean", prefix / "lib/libc",
                                                           resource / "lib/darwin"]
                          for path in directory.glob("*") if path.is_file() and path.suffix in {".a", ".tbd", ".dylib"}}
        native_before = hashes(native_inputs | candidate_libs)
        native_object = out / "test.o"
        _, compile_stderr = run([tools["leanc"], *native_flags, "-O3", "-c", generated, "-o", native_object, "-v"],
                                "native-compile", environment=native_env)
        link = [tools["leanc"], *native_flags, "-O3", "-o", executable, native_object, *objects]
        stdout, stderr = run([*link, "-v", "-Wl,-t", "-Wl,-map," + str(out / "native-link.map")],
                             "link-tests", environment=native_env)
        require(str(tools["clang"]) in stderr.splitlines()[0], "leanc did not report the pinned compiler")
        report["native_actual_commands"] = parse_plan(compile_stderr + stderr, tools["clang"], tools["ld64.lld"])
        actual = linked_files(stdout)
        retained_objects = set(map(Path.resolve, [native_object, *objects]))
        require(retained_objects <= actual, "Link trace omitted a retained module object")
        libraries = {path for path in actual if path.suffix in {".a", ".tbd", ".dylib"}}
        require(libraries and libraries <= candidate_libs, "Link selected an unrecorded native library")
        require(any(path.name == "libleanrt.a" for path in libraries), "Lean runtime archive absent from link trace")
        # Temporary compiler-produced objects are deliberately separate from
        # durable imported objects and runtime archive custody.
        report["native_link_files"] = list(map(str, sorted(actual)))
        report["native_header_sha256"] = hashes(native_inputs)
        report["native_library_sha256"] = hashes(libraries)
        require(hashes(native_inputs | candidate_libs) == native_before, "Native headers/libraries changed during compilation")
        runtime, dylibs = dynamic_closure(run, [executable], prefix, "native")
        report["native_runtime_dependencies"] = runtime
        report["native_runtime_file_sha256"] = hashes(dylibs)
        native = "".join(run([executable], "native-tests"))
        report["native"] = parse_results(native, audit=False)
        require(source_hashes() == report["source_sha256"], "Source closure changed during validation")
        require(hashes(build_files) == before_inputs, "Imported build inputs changed during validation")
        require(hashes(tool_files) == before_tools, "Tool/runtime identity changed during validation")
        require(hashes(objects) == report["linked_object_sha256"], "Retained native object changed")
        require(hashes(dylibs) == report["native_runtime_file_sha256"], "Native runtime library changed")
        require(hashes(native_inputs | libraries) == {str(path): native_before[str(path)] for path in native_inputs | libraries},
                "Native input/header/library changed during execution")
        report["passed"] = True
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        report["artifact_sha256"] = {str(path.relative_to(ROOT)): sha(path) for path in sorted(out.rglob("*"))
                                      if path.is_file() and path.name != "report.json"}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("FastEmit provenance gate passed: " + str(out / "report.json"), flush=True)


if __name__ == "__main__":
    main()
