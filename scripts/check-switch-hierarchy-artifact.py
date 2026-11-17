#!/usr/bin/env python3
"""Certify all flattened hierarchy endpoints and reset-initialized switch traces."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import time

import typed_circuit_hierarchy as hierarchy
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("switch_artifact", ROOT / "scripts/check-switch-artifact.py")
base = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(base)


def sources():
    found = base.sources()
    pending = [ROOT / "test/SwitchHierarchyEmit.lean"]
    while pending:
        path = pending.pop()
        key = str(path.relative_to(ROOT))
        if key in found:
            continue
        found[key] = sha(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for module in match[1].split("--", 1)[0].split():
                    if module == "Pinwheel" or module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    for name in ("scripts/check-switch-hierarchy-artifact.py", "scripts/typed_circuit_hierarchy.py"):
        found[name] = sha(ROOT / name)
    return dict(sorted(found.items()))


def configuration(run, tools, out, config):
    directory = out / ("hierarchy-" + "-".join(map(str, config)))
    directory.mkdir()
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/SwitchHierarchyEmit.lean",
         *config, directory], directory.name + "-emit")
    descriptor = json.loads((directory / "interface.json").read_text())
    hierarchy.normalize_descriptor(descriptor)
    # One source reference circuit; lower the actual instantiated leaf modules.
    (directory / "switch.mlir").write_text((directory / "flat.mlir").read_text())
    leaves = descriptor.get("leaves")
    if not isinstance(leaves, list) or len(leaves) != 3 or len(set(leaves)) != 3 or any(
            not isinstance(name, str) or not base.rr.IDENTIFIER.fullmatch(name) for name in leaves):
        raise ValueError("Expected three distinct shared leaf/control modules")
    sources_sv = []
    for index, leaf in enumerate(leaves):
        target = directory / (leaf + ".sv")
        target.write_text(run([tools["circt"], directory / (leaf + ".mlir"), "--canonicalize", "--lower-seq-to-sv",
                               "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"],
                              directory.name + f"-lower-{index}"))
        sources_sv.append(target)
    sources_sv.append(directory / "hierarchy_top.sv")
    actual = directory / "hierarchical.sv"
    actual.write_text("\n".join(p.read_text() for p in sources_sv))
    raw = directory / "raw.json"
    script = directory / "import.ys"
    script.write_text(f"read_verilog -sv {base.rr.yosys_quote(actual)}\n"
                      f"hierarchy -check -top {descriptor['module']}\n"
                      "flatten -noscopeinfo\nproc\nopt_clean\ncheck -assert\n"
                      f"write_json {base.rr.yosys_quote(raw)}\n")
    run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-import")
    flat = hierarchy.prepare_json(raw, directory / "import.json", descriptor)
    (directory / "canonical-interface.json").write_text(json.dumps(flat, indent=2) + "\n")
    profile_text = base.profile(config, descriptor["destination_width"]) + "\nimport Pinwheel.Hardware.Switch.Export\n"
    checks = "\n".join(f'example : Switch.Export.hierarchyReference register_{k} = "{r["reference"]}" := by decide +kernel'
                       for k, r in enumerate(descriptor["registers"]))
    evidence = base.prove_imported(run, tools, directory, config, flat,
                                   profile_text=profile_text, interface_checks=checks)
    return {"configuration": config, "state_aliases": len(flat["registers"]), **evidence}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", help="INPUTS,OUTPUTS,DEPTH,WIDTH")
    args = parser.parse_args()
    configs = [tuple(map(int, c.split(","))) for c in args.config] if args.config else [(1, 1, 1, 1), (2, 3, 2, 8)]
    if any(len(c) != 4 or min(c) <= 0 for c in configs):
        parser.error("Configurations must contain four positive integers")
    out = fresh_directory(ROOT / "build/switch-hierarchy-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
              "boundary": "Kernel-checked complete imported hierarchy state/output equations and "
                          "reset-initialized traces; Yosys, restricted JSON interpretation and explicit "
                          "hierarchical state-name binding are trusted; no physical timing claim."}
    run = base.rr.Commands(out, report["commands"])
    started = time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, tool_paths = base.rr.selected_tools()
        cad = ROOT / "build/tools" / manifest["packages"]["oss-cad-suite"]["directory"]
        tools["z3"] = cad / "bin/z3"
        tool_paths += [cad / "bin/z3", cad / "libexec/z3"]
        report["tool_manifest"], report["tool_sha256"] = manifest, base.rr.tool_hashes(tool_paths)
        run(["lake", "build", "Pinwheel.Hardware.Switch.Certified", "Pinwheel.Hardware.Switch.Export",
             "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        for config in configs:
            report["configurations"].append(configuration(run, tools, out, config))
        if sources() != report["source_sha256"] or base.rr.tool_hashes(tool_paths) != report["tool_sha256"]:
            raise RuntimeError("Sources/tools changed during certification; rerun under a fresh tag")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
