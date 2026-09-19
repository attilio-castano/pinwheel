#!/usr/bin/env python3
"""Clock-gate exactly the registers a Lean gating plan names, and verify it.

Lean certifies that each planned register loads under an enable and otherwise
holds (`Circuit.Enables`). This step applies that plan to unchanged RTL: Yosys
infers every enable, enables of unplanned registers are folded back into
multiplexers, and only the remainder is converted to integrated clock gates.
The result is then checked bit by bit against the plan, simulated against the
independent oracle with every storage register observed, mutated at every gate,
and mapped for an area screen. No placement, routing or timing claim follows.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TOP = "pinwheel_atomic_small_dense_cached"
GATE = "sg13cmos5l_lgcp_1"
ENABLED_FLOPS = ("$dffe", "$sdffe", "$sdffce", "$adffe", "$aldffe", "$dffsre")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rtl", type=Path, required=True, help="Emitted SystemVerilog, unchanged")
    parser.add_argument("--plan", type=Path, required=True, help="Lean gating plan: register name, width per line")
    parser.add_argument("--testbench", type=Path, required=True,
                        help="Directory of a completed measure-storage-variant.py run for the same RTL interface")
    parser.add_argument("--tag", required=True)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--skip-mutants", action="store_true", help="Skip the stuck-enable mutation pass")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.tag): parser.error("Invalid tag")
    out = ROOT / "build/gated" / args.tag
    if out.exists(): raise RuntimeError("Choose a fresh tag to retain earlier evidence")
    out.mkdir(parents=True)
    plan = {}
    for line in args.plan.read_text().splitlines():
        if line.strip():
            name, width = line.split("\t")
            plan[name] = int(width)
    sources = [args.rtl, args.plan, args.testbench / "tb.sv", args.testbench / "vectors.txt",
               args.testbench / "observe.svh", Path(__file__).resolve(), ROOT / "tools/technology-library.json"]
    hashes = {str(p.resolve()): sha(p) for p in sources}
    suite = ROOT / "build/tools/oss-cad-suite/bin"
    library = ROOT / "build/tools/ihp-cmos5l"
    commands, started = [], time.monotonic()

    def run(command, label, timeout=1800):
        command = list(map(str, command))
        then = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        (out / f"{label}.log").write_text(result.stdout + result.stderr)
        commands.append({"argv": command, "exit_code": result.returncode, "seconds": round(time.monotonic() - then, 3)})
        if result.returncode: raise RuntimeError(f"{label}: {(result.stdout + result.stderr)[-3000:]}")
        return result.stdout + result.stderr

    # 1. Gate the planned registers only.
    (out / "gate-stub.v").write_text(f"(* blackbox *) module {GATE}(input CLK, input GATE, output GCLK); endmodule\n")
    names = list(plan)
    marks = [f"setattr -set pinwheel_gate 1 {' '.join('w:' + n for n in names[k:k + 40])}"
             for k in range(0, len(names), 40)]
    enabled = " ".join(f"t:{kind}" + (" %u" if k else "") for k, kind in enumerate(ENABLED_FLOPS))
    script = [f"read_verilog -lib {out}/gate-stub.v", f"read_verilog -sv {args.rtl.resolve()}",
              f"hierarchy -check -top {TOP}", "proc", "opt_clean", "opt_dff", *marks,
              "select -set planned " + ("a:pinwheel_gate %ci t:$dffe %i" if names else "t:pinwheel_no_such_cell"),
              f"select -set others {enabled} @planned %d", "dffunmap -ce-only @others"]
    if names: script.append(f"clockgate -pos {GATE} GATE:CLK:GCLK -min_net_size 1")
    script += ["opt_clean", "check -assert", f"write_json {out}/gated.json", f"write_verilog -noattr {out}/gated.v", ""]
    (out / "gate.ys").write_text("\n".join(script))
    run([suite / "yosys", "-Q", "-T", "-s", out / "gate.ys"], "gate")

    # 2. Bit-level agreement between the netlist and the plan.
    module = json.loads((out / "gated.json").read_text())["modules"][TOP]
    gated_clocks = {bit for c in module["cells"].values() if c["type"] == GATE for bit in c["connections"]["GCLK"]}
    root_clock = module["ports"]["clk"]["bits"][0]
    flop_clock, enabled_bits = {}, set()
    for cell in module["cells"].values():
        if cell["type"].startswith(("$dff", "$sdff", "$adff", "$aldff")) or cell["type"] in ENABLED_FLOPS:
            for bit in cell["connections"]["Q"]:
                flop_clock[bit] = cell["connections"]["CLK"][0]
                if "EN" in cell["connections"]: enabled_bits.add(bit)
    registers = {n: v["bits"] for n, v in module["netnames"].items() if re.fullmatch(r"r_\w+", n)}
    problems = []
    for name, bits in registers.items():
        clocks = {flop_clock.get(b) for b in bits}
        if name in plan:
            if len(bits) != plan[name]: problems.append(f"{name}: width {len(bits)} differs from plan")
            if not clocks <= gated_clocks or len(clocks) != 1: problems.append(f"{name}: planned but not behind one clock gate")
            if enabled_bits & set(bits): problems.append(f"{name}: gated flip-flop kept an enable")
        elif clocks != {root_clock}:
            problems.append(f"{name}: unplanned register is not on the root clock")
    problems += [f"{n}: planned register missing from the netlist" for n in plan if n not in registers]
    if problems: raise RuntimeError("Netlist disagrees with the gating plan:\n" + "\n".join(problems[:20]))
    gates = sum(c["type"] == GATE for c in module["cells"].values())

    # 3. Independent oracle, observing every storage register by name.
    models = ROOT / "build/physical/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog/sg13cmos5l_stdcell.v"
    primitives = models.with_name("sg13cmos5l_udp.v")
    bench = [args.testbench / "tb.sv"]

    def simulate(netlist, label, directory):
        compiled = subprocess.run([str(suite / "iverilog"), "-g2012", "-DFUNCTIONAL", "-s", "loader_tb", "-o",
            str(directory / f"{label}.vvp"), str(netlist), str(models), str(primitives), *map(str, bench)],
            cwd=ROOT, capture_output=True, text=True)
        if compiled.returncode: raise RuntimeError(f"{label} did not compile: {compiled.stderr[-1500:]}")
        result = subprocess.run([str(suite / "vvp"), str(directory / f"{label}.vvp")], cwd=ROOT,
                                capture_output=True, text=True)
        (directory / f"{label}.vvp").unlink()
        return result

    passed = simulate(out / "gated.v", "regression", out)
    (out / "regression.log").write_text(passed.stdout + passed.stderr)
    if passed.returncode or "Passed" not in passed.stdout:
        raise RuntimeError(f"Gated netlist failed the oracle: {passed.stdout[-1500:]}")
    simulation = passed.stdout.strip().splitlines()[0]

    # 4. Every gate stuck open or shut must be noticed.
    mutants = {"mutants": 0, "rejected": 0, "survivors": []}
    if names and not args.skip_mutants:
        text = (out / "gated.v").read_text()
        instances = [(m.start(), m.end(), m[1], m[0]) for m in re.finditer(GATE + r"\s+(\S+)\s*\((.*?)\);", text, re.S)]
        if len(instances) != gates: raise RuntimeError("Could not locate every clock gate in the written netlist")
        work = out / "mutants"
        work.mkdir()

        def trial(job):
            index, value = job
            start, end, name, body = instances[index]
            mutated, count = re.subn(r"\.GATE\(([^)]*)\)", f".GATE(1'b{value})", body, count=1)
            if count != 1: raise RuntimeError(f"Clock gate {name} has no enable connection")
            path = work / f"{index}-{value}.v"
            path.write_text(text[:start] + mutated + text[end:])
            result = simulate(path, f"{index}-{value}", work)
            path.unlink()
            edge = re.search(r"LOADER edge (\d+)", result.stdout)
            return (name, value, int(edge[1]) if result.returncode and edge else None)

        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            trials = list(pool.map(trial, [(k, v) for k in range(len(instances)) for v in (0, 1)]))
        work.rmdir()
        survivors = [f"{name}={value}" for name, value, edge in trials if edge is None]
        mutants = {"mutants": len(trials), "rejected": len(trials) - len(survivors), "survivors": survivors}
        if survivors: raise RuntimeError(f"{len(survivors)} stuck-enable mutants survived: {survivors[:10]}")

    # 5. Technology-mapped area screen with the project's mapping recipe.
    lock = json.loads((ROOT / "tools/technology-library.json").read_text())
    for item in lock["files"]:
        if sha(library / item["name"]) != item["sha256"]: raise RuntimeError("Technology library changed")
    (out / "abc.constr").write_text("set_driving_cell sg13cmos5l_buf_2\nset_load 10\n")
    metrics = {}
    for corner, libname in (("typical", "sg13cmos5l_stdcell_typ_1p20V_25C.lib"),
                            ("slow", "sg13cmos5l_stdcell_slow_1p08V_125C.lib")):
        lib = library / libname
        (out / f"{corner}.ys").write_text("\n".join([f"read_liberty -lib {lib}", f"read_verilog {out}/gated.v",
            f"hierarchy -check -top {TOP}", f"synth -top {TOP} -noabc", f"dfflibmap -liberty {lib}",
            f"abc -liberty {lib} -constr {out}/abc.constr -D 10000", "clean", "check -assert",
            f"stat -liberty {lib}", f"write_json {out}/{corner}.json", ""]))
        log = run([suite / "yosys", "-Q", "-T", "-s", out / f"{corner}.ys"], corner)
        cells = json.loads((out / f"{corner}.json").read_text())["modules"][TOP]["cells"]
        kinds = [c["type"] for c in cells.values()]
        metrics[corner] = {"standard_cell_area_um2": float(re.findall(r"Chip area for module.*?:\s*([\d.]+)", log)[-1]),
                           "abc_combinational_delay_ps": float(re.findall(r"ABC(?: RESULTS)?:.*?Delay\s*=\s*([\d.]+)", log)[-1]),
                           "cells": len(kinds), "flip_flops": sum(k.startswith("sg13cmos5l_df") for k in kinds),
                           "clock_gates": kinds.count(GATE), "mux2": kinds.count("sg13cmos5l_mux2_1")}
    if hashes != {str(p.resolve()): sha(p) for p in sources}: raise RuntimeError("Inputs changed during the run")
    report = {"rtl_sha256": sha(args.rtl), "plan_sha256": sha(args.plan), "planned_registers": len(plan),
              "planned_bits": sum(plan.values()), "clock_gates": gates, "registers_checked": len(registers),
              "simulation": simulation, "stuck_enable_mutants": mutants, "mapping": metrics,
              "source_sha256": hashes, "commands": commands,
              "artifact_sha256": {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()},
              "elapsed_seconds": round(time.monotonic() - started, 3),
              "boundary": "Generic-cell netlist with integrated clock gates, produced from unchanged RTL. Zero-delay "
                          "simulation against the independent oracle with every storage register observed, plus "
                          "stuck-enable mutants; not an equivalence proof. Mapped area excludes clock trees, hold "
                          "repair, placement and routing."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{gates} clock gates over {sum(plan.values())} bits match the plan; {simulation}; "
          f"{mutants['rejected']}/{mutants['mutants']} mutants rejected; "
          f"typical area {metrics['typical']['standard_cell_area_um2']:.0f} um2.")


if __name__ == "__main__":
    main()
