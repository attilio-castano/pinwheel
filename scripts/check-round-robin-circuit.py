#!/usr/bin/env python3
"""Exhaustive legal-cursor selector RTL simulation and generic synthesis smoke.

The Lean audit proves the structural selector's semantics. The exported and
synthesized Verilog are checked by simulation; this runner does not construct a
kernel-checked RTL interpretation certificate or establish physical timing.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import time

import process_group
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
COUNTS = (1, 2, 3, 5, 8)
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")


def source_hashes():
    """Follow owning local imports, excluding unrelated work in progress."""
    pending = [ROOT / "test/RoundRobinCircuit.lean"]
    sources = set()
    while pending:
        path = pending.pop()
        if path in sources:
            continue
        sources.add(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for module in match[1].split("--", 1)[0].split():
                    if module == "Pinwheel" or module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    sources.update(ROOT / name for name in (
        "lakefile.toml", "lean-toolchain", "lake-manifest.json", "tools/hardware-toolchain.json",
        "scripts/check-round-robin-circuit.py", "scripts/validation_run.py", "scripts/process_group.py"))
    return {str(path.relative_to(ROOT)): sha(path) for path in sorted(sources)}


class Commands:
    """Retain diagnostics separately from stdout used as generated Verilog."""

    def __init__(self, out, records):
        self.out, self.records = out, records

    def __call__(self, command, label, timeout=300):
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", label):
            raise ValueError("Invalid command label")
        log = self.out / (label + ".log")
        if log.exists():
            raise FileExistsError(f"Preserve the earlier command log: {log}")
        argv = list(map(str, command))
        record = {"label": label, "argv": argv, "timeout_seconds": timeout}
        self.records.append(record)
        started = time.monotonic()
        try:
            result = process_group.run_captured(argv, cwd=ROOT, timeout=timeout, log_path=log)
            record["exit_code"] = result.returncode
            if result.returncode:
                raise RuntimeError(f"{label} failed; see {log}\n{result.stderr[-2000:]}")
        except BaseException as error:
            record["error"] = type(error).__name__
            raise
        finally:
            record["seconds"] = round(time.monotonic() - started, 3)
        print(f"{label}: passed", flush=True)
        return result.stdout


def selected_tools():
    manifest = json.loads((ROOT / "tools/hardware-toolchain.json").read_text())
    installed = ROOT / "build/tools/installed.json"
    if json.loads(installed.read_text()) != manifest:
        raise RuntimeError("Installed hardware tool manifest differs from the pinned manifest")
    packages = manifest["packages"]
    circt = ROOT / "build/tools" / packages["circt"]["directory"]
    cad = ROOT / "build/tools" / packages["oss-cad-suite"]["directory"]
    tools = {"circt": circt / "bin/circt-opt"}
    tools.update({name: cad / "bin" / name for name in ("iverilog", "vvp", "yosys")})
    # OSS CAD binaries are shell launchers; record the executables they select,
    # ABC used by synth, and Icarus's compiler backend, as well as the launchers.
    paths = {installed, *tools.values(), cad / "bin/yosys-abc"}
    paths.update(cad / "libexec" / name for name in ("iverilog", "vvp", "yosys", "yosys-abc"))
    paths.update(path for path in (cad / "lib/ivl").rglob("*") if path.is_file())
    return manifest, tools, sorted(paths)


def tool_hashes(paths):
    return {str(path.relative_to(ROOT)): sha(path) for path in paths}


def descriptor(path, count):
    data = json.loads(path.read_text())
    required = {"schema": 1, "request_count": count, "registers": [],
                "cursor_encoding": "one_hot", "latency_cycles": 0}
    for key, value in required.items():
        if data.get(key) != value:
            raise ValueError(f"{path}: unexpected {key}")
    if not isinstance(data.get("module"), str) or not IDENTIFIER.fullmatch(data["module"]):
        raise ValueError(f"{path}: invalid module name")
    for key, size in (("requests", count), ("cursor", count), ("grants", count)):
        names = data.get(key)
        if not isinstance(names, list) or len(names) != size:
            raise ValueError(f"{path}: invalid {key} port count")
    names = data["requests"] + data["cursor"] + data["grants"] + [data.get("any_grant")]
    if any(not isinstance(name, str) or not IDENTIFIER.fullmatch(name) for name in names):
        raise ValueError(f"{path}: invalid port name")
    if len(names) != len(set(names)):
        raise ValueError(f"{path}: duplicate ports")
    for key, expected in (("inputs", data["requests"] + data["cursor"]),
                          ("outputs", data["grants"] + [data["any_grant"]])):
        ports = data.get(key)
        if not isinstance(ports, list) or len(ports) != len(expected):
            raise ValueError(f"{path}: invalid {key}")
        if any(port.get("width") != 1 for port in ports) or \
                sorted(port.get("name", "") for port in ports) != sorted(expected):
            raise ValueError(f"{path}: {key} must enumerate the named one-bit ports")
    return data


def testbench(data):
    count = data["request_count"]
    connections = []
    for names, signal in ((data["requests"], "requests"), (data["cursor"], "cursor_bits"),
                          (data["grants"], "grants")):
        connections.extend(f".{name}({signal}[{index}])" for index, name in enumerate(names))
    connections.append(f".{data['any_grant']}(any_grant)")
    return f"""`timescale 1ns/1ps
module tb;
reg [{count - 1}:0] requests = 0, cursor_bits = 0;
wire [{count - 1}:0] grants;
wire any_grant;
{data['module']} dut({', '.join(connections)});
integer cursor, mask;
initial begin
  for (cursor = 0; cursor < {count}; cursor = cursor + 1) begin
    for (mask = 0; mask < {1 << count}; mask = mask + 1) begin
      requests = mask;
      cursor_bits = 1 << cursor;
      #1;
      $display("RR,%0d,%0d,%0d,%0d", cursor, mask, grants, any_grant);
    end
  end
  $display("RR_DONE");
  $finish;
end
endmodule
"""


def expected_grant(count, cursor, mask):
    """Independent arithmetic scan; no Lean expressions or RTL shape inspection."""
    for offset in range(count):
        index = (cursor + offset) % count
        if mask & (1 << index):
            return 1 << index
    return 0


def check_trace(text, count):
    rows, done = [], 0
    for line in text.splitlines():
        if line == "RR_DONE":
            done += 1
        elif line.startswith("RR,"):
            if done:
                raise AssertionError("Trace has observations after completion")
            fields = line.split(",")[1:]
            if len(fields) != 4 or any(not field.isdecimal() for field in fields):
                raise AssertionError(f"Malformed or unknown-valued RTL observation: {line}")
            rows.append(tuple(map(int, fields)))
        elif line.strip() and not re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)", line):
            raise AssertionError(f"Unexpected simulator output: {line}")
    if done != 1 or len(rows) != count * (1 << count):
        raise AssertionError(f"Incomplete trace for N={count}: {len(rows)} rows, {done} completions")
    for cursor in range(count):
        for mask in range(1 << count):
            grant = expected_grant(count, cursor, mask)
            expected = (cursor, mask, grant, int(grant != 0))
            observed = rows[cursor * (1 << count) + mask]
            if observed != expected:
                raise AssertionError(f"N={count}: expected {expected}, observed {observed}")
    return len(rows)


def checker_self_test():
    """Prove the comparator rejects missing, reordered and incorrect observations."""
    count = 3
    rows = [(c, m, expected_grant(count, c, m), int(m != 0))
            for c in range(count) for m in range(1 << count)]

    def encode(values):
        return "".join("RR," + ",".join(map(str, row)) + "\n" for row in values) + "RR_DONE\n"

    check_trace(encode(rows), count)
    priority = [(c, m, m & -m, int(m != 0)) for c, m, _, _ in rows]
    flipped = list(rows)
    c, m, grant, any_grant = flipped[1]
    flipped[1] = (c, m, grant ^ 1, any_grant)
    mutations = {"fixed_priority": encode(priority), "wrong_grant": encode(flipped),
                 "missing_row": encode(rows[:-1]), "reordered_rows": encode(list(reversed(rows))),
                 "unknown_bit": encode(rows).replace("RR,0,0,0,0", "RR,0,0,x,0"),
                 "missing_completion": encode(rows).replace("RR_DONE\n", "")}
    for name, trace in mutations.items():
        try:
            check_trace(trace, count)
        except AssertionError:
            continue
        raise AssertionError(f"Comparator accepted intentional mutation: {name}")
    return list(mutations)


def yosys_quote(path):
    return json.dumps(str(path))


def configuration(run, out, tools, count):
    label = f"rr_{count}"
    data = descriptor(out / (label + ".json"), count)
    rtl, tb = out / (label + ".sv"), out / (label + "_tb.sv")
    rtl.write_text(run([tools["circt"], out / (label + ".mlir"), "--canonicalize", "--lower-seq-to-sv",
                        "--lower-hw-to-sv", "--hw-legalize-modules", "--export-verilog", "-o", "/dev/null"],
                       label + "-export"))
    tb.write_text(testbench(data))

    def simulate(source, stage):
        executable = out / (label + "-" + stage + ".vvp")
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb],
            label + "-" + stage + "-compile")
        trace = run([tools["vvp"], executable], label + "-" + stage + "-simulate")
        (out / (label + "-" + stage + "-trace.txt")).write_text(trace)
        return check_trace(trace, count)

    rtl_cases = simulate(rtl, "rtl")
    stats, netlist, gates = (out / (label + suffix) for suffix in ("-stats.json", "-netlist.json", "-gates.sv"))
    script = out / (label + "-synth.ys")
    script.write_text("\n".join((
        "read_verilog -sv " + yosys_quote(rtl),
        "hierarchy -check -top " + data["module"],
        "synth -top " + data["module"], "check -assert",
        "tee -o " + yosys_quote(stats) + " stat -json",
        "write_json " + yosys_quote(netlist), "write_verilog -noattr " + yosys_quote(gates), "")))
    run([tools["yosys"], "-Q", "-s", script], label + "-synth")
    modules = json.loads(netlist.read_text())["modules"]
    if set(modules) != {data["module"]}:
        raise AssertionError("Unexpected module hierarchy after selector synthesis")
    module = modules[data["module"]]
    cells = Counter(cell["type"] for cell in module.get("cells", {}).values())
    if module.get("memories") or any(not re.fullmatch(
            r"\$_(?:NOT|BUF|AND|NAND|OR|NOR|XOR|XNOR|ANDNOT|ORNOT|MUX|NMUX|AOI[34]|OAI[34])_", kind)
            for kind in cells):
        raise AssertionError(f"Expected only combinational generic cells, got {dict(cells)}")
    reported = json.loads(stats.read_text())["modules"]["\\" + data["module"]]
    if reported["num_cells"] != sum(cells.values()) or reported["num_cells_by_type"] != dict(cells):
        raise AssertionError("Synthesis statistics disagree with saved netlist")
    gate_cases = simulate(gates, "gates")
    result = {"request_count": count, "rtl_cases": rtl_cases, "synthesized_cases": gate_cases,
              "generic_cells": sum(cells.values()), "generic_cells_by_type": dict(sorted(cells.items())),
              "wire_bits": reported["num_wire_bits"], "cursor_encoding": "one_hot",
              "coverage": "Every binary request mask crossed with every legal one-hot cursor"}
    print(f"PASS N={count}: {rtl_cases} cases in each RTL form; {sum(cells.values())} generic cells", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", help="Fresh evidence directory name; never overwrites an earlier run")
    parser.add_argument("--self-test", action="store_true", help="Check the portable trace comparator only")
    args = parser.parse_args()
    if args.self_test:
        print("Rejected comparator mutations: " + ", ".join(checker_self_test()))
        return
    if not args.tag:
        parser.error("--tag is required unless --self-test is used")
    out = fresh_directory(ROOT / "build/round-robin-circuit", args.tag)
    started = time.monotonic()
    records = []
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "boundary": "Lean structural selector proof audit; exhaustive finite binary RTL simulation "
                          "for legal one-hot cursors at N=1,2,3,5,8; generic Yosys synthesis smoke. "
                          "No kernel-certified RTL artifact interpretation, invalid-cursor behavior contract, "
                          "sequential fairness, switch implementation, physical area or timing claim.",
              "tool_hash_scope": "Selected launchers, underlying executables, ABC and Icarus backend; "
                                 "not a complete host dynamic-library closure."}
    run = Commands(out, records)
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, tool_paths = selected_tools()
        report["tool_manifest"] = manifest
        report["tool_sha256"] = tool_hashes(tool_paths)
        report["comparator_mutations_rejected"] = checker_self_test()
        run(["lake", "env", "lean", "--version"], "lean-version")
        run([tools["circt"], "--version"], "circt-version")
        run([tools["iverilog"], "-V"], "iverilog-version")
        run([tools["yosys"], "-V"], "yosys-version")
        run(["lake", "build", "Pinwheel.Hardware.Arbitration.RoundRobinCircuit", "Pinwheel.Hardware.Emit"],
            "build", timeout=900)
        lean_output = run(["lake", "env", "lean", "-DwarningAsError=true", "--run",
                           "test/RoundRobinCircuit.lean", out], "structural-audit-and-emit")
        match = re.search(r"Structural round-robin: ([0-9]+) exhaustive selections passed\.", lean_output)
        if match is None or "standard axioms only" not in lean_output:
            raise AssertionError("Missing structural exhaustive selection result or proof audit")
        report["lean_structural_cases"] = int(match[1])
        for count in COUNTS:
            report["configurations"].append(configuration(run, out, tools, count))
        if source_hashes() != report["source_sha256"]:
            raise RuntimeError("Owning sources changed during validation; use a fresh tag")
        if tool_hashes(tool_paths) != report["tool_sha256"]:
            raise RuntimeError("Selected tools changed during validation; use a fresh tag")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["artifact_sha256"] = {str(path.relative_to(out)): sha(path)
                                     for path in sorted(out.rglob("*")) if path.is_file()}
        report["seconds"] = round(time.monotonic() - started, 3)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
