#!/usr/bin/env python3
"""Require the netlist regression to notice every clock gate stuck open or shut.

Run `check-physical-netlist.py` first with the same label: this reuses its
testbench and reference. Each mutant ties one integrated clock gate's enable to a
constant. Zero-delay gate simulation; a rejected mutant shows sensitivity of the
traces, not correctness of the gated design.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess

import physical_receipt

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "build/physical"
GATE = "sg13cmos5l_lgcp_1"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("netlist", type=Path)
    parser.add_argument("--label", required=True, help="Label of the completed check-physical-netlist.py run")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.label) or args.jobs <= 0:
        parser.error("Use a simple label and a positive number of jobs")
    check = BASE / (args.label + "-check")
    passed = json.loads((check / "report.json").read_text())
    if physical_receipt.recorded_digest(passed["sha256"], args.netlist, ROOT) != sha(args.netlist):
        raise RuntimeError("The completed netlist check covers a different netlist")
    out = BASE / (args.label + "-gates")
    out.mkdir(parents=True, exist_ok=True)
    (out / "report.json").unlink(missing_ok=True)
    text = args.netlist.read_text()
    gates = [(m.start(), m.end(), m[1], m[0]) for m in re.finditer(GATE + r"\s+(\S+)\s*\((.*?)\);", text, re.S)]
    if not gates: raise RuntimeError("No integrated clock gates in this netlist")
    suite = ROOT / "build/tools/oss-cad-suite/bin"
    models = BASE / "pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog/sg13cmos5l_stdcell.v"
    primitives = models.with_name("sg13cmos5l_udp.v")
    bench, reference = check / "tb.sv", check / "reference.sv"
    vector_files = re.findall(r'\$fopen\(\s*("(?:[^"\\]|\\.)*")\s*,\s*"r"\s*\)', bench.read_text())
    if len(vector_files) != 1:
        raise RuntimeError("Expected exactly one oracle vector file in the retained testbench")
    vectors = Path(json.loads(vector_files[0]))
    if not vectors.is_absolute():
        vectors = ROOT / vectors
    for path in (models, primitives, vectors):
        if physical_receipt.recorded_digest(passed["sha256"], path, ROOT) != sha(path):
            raise RuntimeError(f"Netlist-check input changed: {physical_receipt.path_key(path, ROOT)}")
    # Older receipts did not hash the generated bench/reference. Recheck the
    # unmodified design below as well as verifying those hashes when available.
    for path in (bench, reference):
        expected = physical_receipt.recorded_digest(passed["sha256"], path, ROOT)
        if expected is not None and expected != sha(path):
            raise RuntimeError(f"Netlist-check artifact changed: {physical_receipt.path_key(path, ROOT)}")
    inputs = [args.netlist, models, primitives, vectors, bench, reference, check / "report.json",
              Path(__file__).resolve(), Path(physical_receipt.__file__)]
    hashes = {physical_receipt.path_key(p, ROOT): sha(p) for p in inputs}

    def simulate(netlist, executable):
        compiled = subprocess.run([str(suite / "iverilog"), "-g2012", "-DFUNCTIONAL", "-s", "loader_tb", "-o",
            str(executable), str(netlist), str(models), str(primitives), str(reference), str(bench)],
            cwd=ROOT, capture_output=True, text=True)
        if compiled.returncode:
            raise RuntimeError(f"Netlist did not compile: {compiled.stderr[-500:]}")
        result = subprocess.run([str(suite / "vvp"), str(executable)], cwd=ROOT, capture_output=True, text=True)
        executable.unlink(missing_ok=True)
        return result

    baseline = simulate(args.netlist, out / "baseline.vvp")
    (out / "baseline.log").write_text(baseline.stdout + baseline.stderr)
    if baseline.returncode or "Passed" not in baseline.stdout:
        raise RuntimeError("Unmodified netlist failed the retained testbench; no mutant rejection can be counted")

    def trial(job):
        index, value = job
        start, end, name, body = gates[index]
        mutated, count = re.subn(r"\.GATE\(([^)]*)\)", f".GATE(1'b{value})", body, count=1)
        if count != 1: raise RuntimeError(f"Clock gate {name} has no enable connection")
        work = out / f"{index}-{value}"
        work.mkdir(exist_ok=True)
        (work / "mutant.v").write_text(text[:start] + mutated + text[end:])
        result = simulate(work / "mutant.v", work / "sim.vvp")
        (work / "mutant.v").unlink()
        work.rmdir()
        edge = re.search(r"(?:NETLIST|LOADER) edge (\d+)", result.stdout)
        return {"gate": name, "enable": value, "rejected_at_edge": int(edge[1]) if result.returncode and edge else None}

    jobs = [(index, value) for index in range(len(gates)) for value in (0, 1)]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        trials = list(pool.map(trial, jobs))
    survivors = [t for t in trials if t["rejected_at_edge"] is None]
    if hashes != {physical_receipt.path_key(p, ROOT): sha(p) for p in inputs}:
        raise RuntimeError("Inputs changed during the clock-gate check")
    report = {"clock_gates": len(gates), "mutants": len(trials), "rejected": len(trials) - len(survivors),
              "survivors": survivors, "trials": trials,
              "baseline_simulation": baseline.stdout.strip(), "sha256": hashes,
              "boundary": "Zero-delay gate simulation of stuck clock-gate enables against the retained oracle traces. "
                          "It measures trace sensitivity; it is not an equivalence proof or timing simulation."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{report['rejected']} of {report['mutants']} stuck-enable mutants rejected across {len(gates)} clock gates.")
    if survivors:
        raise SystemExit("Surviving mutants: " + ", ".join(f"{t['gate']}={t['enable']}" for t in survivors))


if __name__ == "__main__":
    main()
