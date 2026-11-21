#!/usr/bin/env python3
"""Matched technology mapping and mapped-cell replay of checked switch variants.

Cell area sums and ABC combinational estimates are an early mapping screen.
They exclude routed wires, clock trees and sequential setup/clock-to-Q timing.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import shutil
import time

from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("shared_switch", ROOT / "scripts/check-switch-shared-selection.py")
candidate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(candidate)
rr, sw = candidate.rr, candidate.sw


def sources():
    return {**candidate.source_hashes(),
        "scripts/check-switch-technology.py": sha(Path(__file__)),
        "tools/technology-library.json": sha(ROOT / "tools/technology-library.json")}


def verified_libraries():
    manifest = json.loads((ROOT / "tools/technology-library.json").read_text())
    libraries = {}
    for item in manifest["files"]:
        path = ROOT / "build/tools/ihp-cmos5l" / item["name"]
        if sha(path) != item["sha256"]:
            raise ValueError("Pinned technology library mismatch: " + str(path))
        if path.suffix == ".lib":
            corner = "typical" if "_typ_" in path.name else "slow"
            if corner in libraries:
                raise ValueError("Ambiguous technology corner")
            libraries[corner] = path
    if set(libraries) != {"typical", "slow"}:
        raise ValueError("Require both pinned technology corners")
    return manifest, libraries


def verify_receipt(receipt, tool_hashes, configs):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != candidate.source_hashes() or \
            report.get("tool_sha256") != tool_hashes:
        raise ValueError("Require a passed shared-switch replay receipt matching current sources/tools")
    covered = {tuple(entry["configuration"]) for entry in report.get("configurations", [])}
    if not set(configs) <= covered:
        raise ValueError("A requested configuration has no checked source RTL")
    hashes = report.get("artifact_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("Missing positive artifact identities")
    for name, digest in hashes.items():
        path = (receipt.parent / name).resolve()
        if not path.is_relative_to(receipt.parent.resolve()) or sha(path) != digest:
            raise ValueError("Changed or escaping positive artifact: " + name)
    for n, m, d, w in configs:
        label = f"i{n}-o{m}-d{d}-w{w}"
        required = [label + "/stimulus.jsonl", label + "/oracle-trace.jsonl"]
        required += [label + suffix + "/" + filename for suffix in ("", "-shared", "-baseline")
                     for filename in ("switch.sv", "interface.json")]
        if any(name not in hashes for name in required):
            raise ValueError("Receipt omits required checked input artifact")


def map_configuration(run, out, tools, receipt, config, libraries, models):
    n, m, d, w = config
    label = f"i{n}-o{m}-d{d}-w{w}"
    origin = receipt.parent / label
    rows = [json.loads(line) for line in (origin / "stimulus.jsonl").read_text().splitlines()]
    frames = [json.loads(line) for line in (origin / "oracle-trace.jsonl").read_text().splitlines()]
    results = {}
    for variant, suffix in (("original", ""), ("shared", "-shared"), ("baseline", "-baseline")):
        source = receipt.parent / (label + suffix)
        data = json.loads((source / "interface.json").read_text())
        results[variant] = {}
        for corner, library in libraries.items():
            directory = out / f"{label}-{variant}-{corner}"
            directory.mkdir()
            rtl, tb = directory / "source.sv", directory / "tb.sv"
            shutil.copyfile(source / "switch.sv", rtl)
            tb.write_text(sw.testbench(data, rows, False))
            constr = directory / "abc.constr"
            constr.write_text("set_driving_cell sg13cmos5l_buf_2\nset_load 10\n")
            script, netlist, netjson = directory / "map.ys", directory / "mapped.v", directory / "mapped.json"
            script.write_text(f"libcache -scl -dir {rr.yosys_quote(out / 'scl-cache')}\nlibcache -list\n"
                f"read_verilog -sv {rr.yosys_quote(rtl)}\n"
                f"hierarchy -check -top {data['module']}\nsynth -top {data['module']} -noabc\n"
                f"dfflibmap -liberty {rr.yosys_quote(library)}\n"
                f"abc -liberty {rr.yosys_quote(library)} -constr {rr.yosys_quote(constr)} -D 10000\n"
                f"read_liberty -lib {rr.yosys_quote(library)}\nclean\ncheck -assert\nstat -liberty {rr.yosys_quote(library)}\n"
                f"write_verilog -noattr {rr.yosys_quote(netlist)}\nwrite_json {rr.yosys_quote(netjson)}\n")
            log = run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-map")
            area = re.findall(r"Chip area for module.*?:\s*([\d.]+)", log)
            delays = re.findall(r"ABC(?: RESULTS|):.*?Delay\s*=\s*([\d.]+)", log)
            if not area or not delays:
                raise ValueError("Missing mapped area or ABC delay report")
            cache_inputs = []
            for filename in re.findall(r"ABC:\s*\+ read_scl (\S+)", log):
                path = Path(filename).resolve()
                if not path.is_relative_to((out / "scl-cache").resolve()) or not path.is_file():
                    raise ValueError("ABC consumed a library cache outside this evidence bundle")
                cache_inputs.append({"path": str(path.relative_to(out)), "sha256": sha(path)})
            if not cache_inputs:
                raise ValueError("Missing evidence for ABC's actual merged SCL input")
            module = json.loads(netjson.read_text())["modules"][data["module"]]
            cells = Counter(cell["type"] for cell in module["cells"].values())
            if any(not name.startswith("sg13cmos5l_") for name in cells):
                raise ValueError("Technology mapping left unmapped cells")
            available_models = json.loads(models[corner].with_suffix(".json").read_text())["modules"]
            if not set(cells) <= set(available_models):
                raise ValueError("Mapped cells have no complete functional Liberty model")
            executable = directory / "sim.vvp"
            run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, models[corner], netlist, tb], directory.name + "-compile")
            trace = run([tools["vvp"], executable], directory.name + "-simulate")
            (directory / "trace.txt").write_text(trace)
            edges = sw.check_rtl_trace(trace, frames, False)
            results[variant][corner] = {"cell_area_sum_library_units": float(area[-1]),
                "abc_combinational_delay_ps": float(delays[-1]), "mapped_cells": sum(cells.values()),
                "cell_types": dict(cells), "replayed_edges": edges,
                "rtl_sha256": sha(rtl), "mapped_sha256": sha(netlist), "abc_scl_inputs": cache_inputs}
            print(f"MAPPED {config} {variant} {corner}: area={area[-1]}, ABC delay={delays[-1]}", flush=True)
    return {"configuration": config, "variants": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    parser.add_argument("--config", action="append", type=sw.model_checks.parse_config)
    args = parser.parse_args()
    configs = args.config or sw.MATRIX
    if len(configs) != len(set(configs)):
        parser.error("Configurations must be distinct")
    out = fresh_directory(ROOT / "build/switch-technology", args.tag)
    (out / "scl-cache").mkdir()
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "constraints": {"abc": "set_driving_cell sg13cmos5l_buf_2; set_load 10", "output_load_fF": 10,
                        "abc_target_ps": 10000, "scl_cache": "fresh private directory in evidence bundle"},
        "boundary": "Matched independent per-corner technology mapping; Liberty cell area sums and ABC "
        "combinational delay estimates only. Mapped functional cell models are generated from the same pinned "
        "Liberty files and replayed from reset against checked independent traces. No placement/routing, "
        "parasitics, clock tree, setup/clock-to-Q, full STA, frequency, power or fabrication qualification."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        lib_manifest, libraries = verified_libraries()
        report["library_manifest"] = lib_manifest
        receipt = args.positive_report.resolve()
        verify_receipt(receipt, report["tool_sha256"], configs)
        report["positive_report"] = {"path": str(receipt), "sha256": sha(receipt)}
        models = {}
        for corner, library in libraries.items():
            target, script = out / (corner + "-models.v"), out / (corner + "-models.ys")
            # Skip unsupported library cells, then require that none were used
            # by the mapped design. Never simulate a black-box fallback.
            script.write_text(f"read_liberty -ignore_miss_func {rr.yosys_quote(library)}\ncheck -assert\n"
                f"write_json {rr.yosys_quote(target.with_suffix('.json'))}\n"
                f"write_verilog -noattr {rr.yosys_quote(target)}\n")
            run([tools["yosys"], "-Q", "-T", "-s", script], corner + "-models")
            models[corner] = target
        for config in configs:
            report["configurations"].append(map_configuration(run, out, tools, receipt, config, libraries, models))
        if report["source_sha256"] != sources() or report["tool_sha256"] != rr.tool_hashes(paths):
            raise RuntimeError("Sources/tools changed during mapping")
        verified_libraries()
        verify_receipt(receipt, report["tool_sha256"], configs)
        if sha(receipt) != report["positive_report"]["sha256"]:
            raise RuntimeError("Positive receipt changed during mapping")
        for config in report["configurations"]:
            for corners in config["variants"].values():
                for evidence in corners.values():
                    for cache in evidence["abc_scl_inputs"]:
                        if sha(out / cache["path"]) != cache["sha256"]:
                            raise RuntimeError("An actual ABC library input changed during mapping")
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
