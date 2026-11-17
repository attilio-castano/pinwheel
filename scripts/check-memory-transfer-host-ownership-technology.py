#!/usr/bin/env python3
"""Compare original, phase-only ownership, and independent host accelerators."""
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


def helper(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


baseline = helper("host_baseline_checks", "check-memory-transfer-host-ownership.py")
technology = helper("host_mapping_library_checks", "check-switch-technology.py")
rr, host = baseline.rr, baseline.host


def sources():
    return dict(sorted({**baseline.sources(), **technology.sources(),
        "scripts/check-memory-transfer-host-ownership-technology.py": sha(Path(__file__))}.items()))


def verify_receipt(receipt, tools_hash):
    report = json.loads(receipt.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != baseline.sources() or \
            report.get("tool_sha256") != tools_hash:
        raise ValueError("Require a passed host ownership receipt matching current sources/tools")
    covered = [tuple(c["configuration"]) for c in report.get("configurations", [])]
    if len(covered) != len(set(covered)) or set(covered) != set(host.MATRIX):
        raise ValueError("Require the full host ownership matrix exactly once")
    hashes = report.get("artifact_sha256")
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("Missing ownership artifact identities")
    for name, digest in hashes.items():
        path = (receipt.parent / name).resolve()
        if not path.is_relative_to(receipt.parent.resolve()) or sha(path) != digest:
            raise ValueError("Changed or escaping checked ownership artifact: " + name)
    for config in host.MATRIX:
        label = "host-" + "-".join(map(str, config))
        for name in ("source.sv", "reference.sv", "baseline.sv", "interface.json", "stimulus.jsonl", "oracle-trace.jsonl", "startup.json"):
            if label + "/" + name not in hashes:
                raise ValueError("Ownership receipt omits checked input artifact: " + name)


def map_configuration(run, out, tools, receipt, config, libraries, models):
    label = "host-" + "-".join(map(str, config))
    source = receipt.parent / label
    data = json.loads((source / "interface.json").read_text())
    host.validate_descriptor(data, *config)
    rows = [json.loads(line) for line in (source / "stimulus.jsonl").read_text().splitlines()]
    frames = [json.loads(line) for line in (source / "oracle-trace.jsonl").read_text().splitlines()]
    startup = json.loads((source / "startup.json").read_text())
    results = {}
    for variant, filename in (("reference", "reference.sv"), ("ownership", "source.sv"), ("baseline", "baseline.sv")):
        results[variant] = {}
        for corner, library in libraries.items():
            directory = out / f"{label}-{variant}-{corner}"
            directory.mkdir()
            rtl, tb = directory / "source.sv", directory / "tb.sv"
            shutil.copyfile(source / filename, rtl)
            tb.write_text(host.testbench(data, startup, rows, False))
            constr = directory / "abc.constr"
            constr.write_text("set_driving_cell sg13cmos5l_buf_2\nset_load 10\n")
            script, netlist, netjson = directory / "map.ys", directory / "mapped.v", directory / "mapped.json"
            script.write_text(f"libcache -scl -dir {rr.yosys_quote(out / 'scl-cache')}\nlibcache -list\n"
                f"read_verilog -sv {rr.yosys_quote(rtl)}\nhierarchy -check -top {data['module']}\n"
                f"synth -top {data['module']} -noabc\n"
                f"dfflibmap -liberty {rr.yosys_quote(library)}\n"
                f"abc -liberty {rr.yosys_quote(library)} -constr {rr.yosys_quote(constr)} -D 10000\n"
                f"read_liberty -lib {rr.yosys_quote(library)}\nclean\ncheck -assert\nstat -liberty {rr.yosys_quote(library)}\n"
                f"write_verilog -noattr {rr.yosys_quote(netlist)}\nwrite_json {rr.yosys_quote(netjson)}\n")
            log = run([tools["yosys"], "-Q", "-T", "-s", script], directory.name + "-map")
            area = re.findall(r"Chip area for module.*?:\s*([\d.]+)", log)
            delays = re.findall(r"ABC(?: RESULTS|):.*?Delay\s*=\s*([\d.]+)", log)
            if not area or not delays:
                raise ValueError("Missing mapped area or ABC delay report")
            caches = []
            for cache_name in re.findall(r"ABC:\s*\+ read_scl (\S+)", log):
                path = Path(cache_name).resolve()
                if not path.is_relative_to((out / "scl-cache").resolve()) or not path.is_file():
                    raise ValueError("ABC consumed a library cache outside this evidence bundle")
                caches.append({"path": str(path.relative_to(out)), "sha256": sha(path)})
            if not caches:
                raise ValueError("Missing ABC merged SCL input evidence")
            module = json.loads(netjson.read_text())["modules"][data["module"]]
            cells = Counter(cell["type"] for cell in module["cells"].values())
            if any(not name.startswith("sg13cmos5l_") for name in cells):
                raise ValueError("Technology mapping left unmapped cells")
            available = json.loads(models[corner].with_suffix(".json").read_text())["modules"]
            if not set(cells) <= set(available):
                raise ValueError("Mapped cells lack functional Liberty models")
            executable = directory / "sim.vvp"
            run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, models[corner], netlist, tb], directory.name + "-compile")
            trace = run([tools["vvp"], executable], directory.name + "-simulate")
            (directory / "trace.txt").write_text(trace)
            host.memory.check_trace(trace, host.controller.expected(frames, False))
            results[variant][corner] = {"cell_area_sum_library_units": float(area[-1]),
                "abc_combinational_delay_ps": float(delays[-1]), "mapped_cells": sum(cells.values()),
                "cell_types": dict(cells), "replayed_edges": len(rows),
                "rtl_sha256": sha(rtl), "mapped_sha256": sha(netlist), "abc_scl_inputs": caches}
            print(f"MAPPED {config} {variant} {corner}: area={area[-1]}, ABC delay={delays[-1]}", flush=True)
    return {"configuration": config, "variants": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    args = parser.parse_args()
    out = fresh_directory(ROOT / "build/memory-transfer-host-ownership-technology", args.tag)
    (out / "scl-cache").mkdir()
    report = {"schema": 1, "status": "running", "commands": [], "configurations": [],
        "constraints": {"abc": "set_driving_cell sg13cmos5l_buf_2; set_load 10", "output_load_fF": 10,
            "abc_target_ps": 10000, "scl_cache": "fresh private directory in evidence bundle"},
        "boundary": "Matched independent per-corner technology mapping; Liberty area sums in library units "
            "and ABC combinational delay estimates only. Mapped functional models come from the same pinned "
            "Liberty files and replay checked reset/host-loading traffic. Memory contents/Q are not initialized "
            "by reset. No post-synthesis kernel proof, placement, routing, parasitics, clock tree, setup/clock-to-Q, "
            "full STA, frequency, power or fabrication qualification."}
    run, started = rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        lib_manifest, libraries = technology.verified_libraries()
        report["library_manifest"] = lib_manifest
        receipt = args.positive_report.resolve()
        verify_receipt(receipt, report["tool_sha256"])
        report["positive_report"] = {"path": str(receipt), "sha256": sha(receipt)}
        shutil.copyfile(receipt, out / "positive-report.json")
        models = {}
        for corner, library in libraries.items():
            target, script = out / (corner + "-models.v"), out / (corner + "-models.ys")
            script.write_text(f"read_liberty -ignore_miss_func {rr.yosys_quote(library)}\ncheck -assert\n"
                f"write_json {rr.yosys_quote(target.with_suffix('.json'))}\n"
                f"write_verilog -noattr {rr.yosys_quote(target)}\n")
            run([tools["yosys"], "-Q", "-T", "-s", script], corner + "-models")
            models[corner] = target
        for config in host.MATRIX:
            report["configurations"].append(map_configuration(run, out, tools, receipt, config, libraries, models))
        if sources() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Sources/tools changed during host mapping")
        technology.verified_libraries()
        verify_receipt(receipt, report["tool_sha256"])
        if sha(receipt) != report["positive_report"]["sha256"]:
            raise RuntimeError("Positive receipt changed during host mapping")
        for config in report["configurations"]:
            for corners in config["variants"].values():
                for result in corners.values():
                    for cache in result["abc_scl_inputs"]:
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
