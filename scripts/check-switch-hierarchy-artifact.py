#!/usr/bin/env python3
"""Certify all flattened hierarchy endpoints and reset-initialized switch traces."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import time

import typed_circuit_hierarchy as hierarchy
import typed_module_checks as module_checks
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("switch_artifact", ROOT / "scripts/check-switch-artifact.py")
base = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(base)


def sources():
    found = base.sources(("test/SwitchHierarchyEmit.lean", "Pinwheel/Hardware/Switch/Certified.lean"))
    for path in (Path(__file__).resolve(), *hierarchy.source_paths(), *module_checks.source_paths()):
        found[str(path.relative_to(ROOT))] = sha(path)
    return dict(sorted(found.items()))


def configuration(run, tools, out, config, *, miswire=False):
    directory = out / ("hierarchy-" + "-".join(map(str, config)))
    directory.mkdir()
    run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/SwitchHierarchyEmit.lean",
         *config, directory], directory.name + "-emit")
    descriptor = json.loads((directory / "interface.json").read_text())
    hierarchy.normalize_descriptor(descriptor)
    # Prove the assembled leaves against the existing flat structural circuit.
    mlir = directory / "switch.mlir"
    mlir.write_text((directory / "flat.mlir").read_text())
    leaves = hierarchy.lower_leaves(run, tools, directory, descriptor)
    flat = hierarchy.import_assembly(run, tools, directory, descriptor, leaves)
    n, _, depth, width = config
    top = json.dumps(descriptor["module"])
    profile_text = (base.profile(config, descriptor["destination_width"])
                    + "import Pinwheel.Hardware.Switch.Export\n"
                    + f"abbrev assembly := Switch.Export.hierarchy encoding {n-1} {width} {depth} {top}\n")
    checks = hierarchy.path_checks(descriptor, "assembly")
    evidence = base.prove_imported(run, tools, directory, config, flat,
                                   profile_text=profile_text, interface_checks=checks)
    if miswire and n >= 2:
        evidence["miswire"] = hierarchy.check_miswire(run, tools, directory, descriptor, leaves, mlir,
                                                     profile_text, checks, ("fifo_0", "fifo_1"), "in_data")
    return {"configuration": config, "state_aliases": len(flat["registers"]), **evidence}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", help="INPUTS,OUTPUTS,DEPTH,WIDTH")
    parser.add_argument("--miswire", action="store_true", help="Swap input payloads on two FIFO instances")
    args = parser.parse_args()
    configs = [tuple(map(int, c.split(","))) for c in args.config] if args.config else [(1, 1, 1, 1), (2, 3, 2, 8)]
    if any(len(c) != 4 or min(c) <= 0 for c in configs):
        parser.error("Configurations must contain four positive integers")
    if args.miswire and not any(c[0] >= 2 for c in configs):
        parser.error("--miswire needs a configuration with at least two inputs")
    out = fresh_directory(ROOT / "build/switch-hierarchy-artifact", args.tag)
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
              "boundary": "Kernel-checked complete imported hierarchy state/output equations and "
                          "reset-initialized traces; Yosys, restricted JSON interpretation and explicit "
                          "hierarchical state-name binding are trusted; no physical timing claim."}
    run = base.rr.Commands(out, report["commands"])
    started = time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, tool_paths = module_checks.tool_config()
        report["tool_manifest"], report["tool_sha256"] = manifest, base.rr.tool_hashes(tool_paths)
        run(["lake", "build", "Pinwheel.Hardware.Switch.Certified", "Pinwheel.Hardware.Switch.Export",
             "Pinwheel.Hardware.Readback.Boolean"], "build", timeout=900)
        for config in configs:
            report["configurations"].append(configuration(run, tools, out, config, miswire=args.miswire))
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
