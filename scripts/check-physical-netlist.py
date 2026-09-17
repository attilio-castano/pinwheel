#!/usr/bin/env python3
"""Check implemented netlist behavior against atomic vectors and the source RTL.

This is zero-delay gate simulation, not a timing simulation or universal proof.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "build/physical"
TOP = "pinwheel_atomic_small_dense_cached"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("netlist", type=Path)
    parser.add_argument("--label", default="netlist")
    parser.add_argument("--vectors", type=Path, default=ROOT / "build/storage/small-dense-cached/vectors.txt",
                        help="Atomic oracle vectors; the selected file is included in the receipt")
    args = parser.parse_args()
    out = BASE / (args.label + "-check")
    out.mkdir(parents=True, exist_ok=True)
    (out / "report.json").unlink(missing_ok=True)
    source = (BASE / "core/design.sv").read_text()
    ports = []
    direction = None
    width = 1
    for statement in source.split(");", 1)[0].split("(\n", 1)[1].split(","):
        match = re.fullmatch(r"\s*(?:(input|output)\s+(?:\[(\d+):0\]\s*)?)?(\w+)\s*", statement)
        if not match:
            raise RuntimeError(f"Unrecognized port declaration: {statement}")
        kind, bits, name = match.groups()
        if kind:
            direction, width = kind, int(bits) + 1 if bits else 1
        ports.append((name, direction, width))
    outputs = [(n, w) for n, d, w in ports if d == "output"]
    width = sum(w for _, w in outputs)
    tb = (ROOT / "test/loader_tb.sv").read_text().replace("pinwheel_atomic_indexed", TOP)
    start = tb.index("  wire [63:0] observed")
    end = tb.index("  integer file", start)
    tb = tb[:start] + tb[end:]
    tb = tb.replace("    for (k = 0; k < 644; k = k+1) known[k] = 0;\n", "")
    start = tb.index("      if (e_push) begin")
    end = tb.index("      clk = 1;", start)
    tb = tb[:start] + tb[end:]
    start = tb.index("      for (k = 0; k < 644;")
    end = tb.index("      count = count+1;", start)
    tb = tb[:start] + tb[end:]
    tb = tb.replace('"build/loader/vectors.txt"', json.dumps(str(args.vectors.resolve())))
    wires = "".join(f"  wire [{w-1}:0] g_{n};\n" for n, w in outputs)
    connections = ", ".join(f".{n}({'g_' if d == 'output' else ''}{n})" for n, d, _ in ports)
    wires += f"  pinwheel_reference golden({connections});\n"
    for prefix, label in [("g_", "golden"), ("", "gate")]:
        wires += f"  wire [{width-1}:0] {label}_bus = {{" + ",".join(prefix+n for n, _ in outputs) + "};\n"
    wires += f"""  integer compared = 0, bit_index;
  task compare_ports;
    begin
      for (bit_index = 0; bit_index < {width}; bit_index = bit_index+1)
        if (golden_bus[bit_index] === 0 || golden_bus[bit_index] === 1) begin
          if (gate_bus[bit_index] !== golden_bus[bit_index])
            $fatal(1, "NETLIST edge %0d output bit %0d differs", count, bit_index);
          compared = compared+1;
        end
    end
  endtask
"""
    tb = tb.replace("  initial begin", wires + "  initial begin")
    # Ignore only reference-X bits from intentionally uninitialized storage.
    tb = tb.replace("      #1;", "      #1; compare_ports;")
    tb = tb.replace("      clk = 1; #1;", "      clk = 1; #1; compare_ports;")
    tb = tb.replace('"Passed %0d atomic loader edges and %0d physical storage observations", count, storage_checks',
                    '"Passed %0d atomic edges and %0d defined output-bit comparisons", count, compared')
    (out / "tb.sv").write_text(tb)
    (out / "reference.sv").write_text(source.replace("module " + TOP, "module pinwheel_reference", 1))
    suite = ROOT / "build/tools/oss-cad-suite/bin"
    models = BASE / "pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog/sg13cmos5l_stdcell.v"
    primitives = models.with_name("sg13cmos5l_udp.v")
    command = [str(suite / "iverilog"), "-g2012", "-DFUNCTIONAL", "-s", "loader_tb", "-o", str(out / "sim.vvp"), str(args.netlist), str(models), str(primitives), str(out / "reference.sv"), str(out / "tb.sv")]
    for cmd, name in [(command, "compile.log"), ([str(suite / "vvp"), str(out / "sim.vvp")], "simulation.log")]:
        result = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        (out / name).write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f"Netlist check failed; see {out / name}")
    simulation = result.stdout
    original = args.netlist.read_text()
    header_end = original.index(");") + 2
    vector_driver = re.search(r"\bassign\s+levels\s*=\s*([^;]+);", original)
    if vector_driver:
        # Preserve both ANSI/non-ANSI port declarations and similarly named
        # state such as r_levels. Corrupt only the public output expression.
        mutant = (original[:vector_driver.start(1)] + "(" + vector_driver[1]
                  + ") ^ 3'b001" + original[vector_driver.end(1):])
        corruption = ""
    elif re.search(r"(?<![\w$])levels\[0\]", original):
        mutant = re.sub(r"(?<![\w$])levels\[0\]", "corrupt_level0", original)
        mutant = mutant[:header_end] + "\nwire corrupt_level0;\n" + mutant[header_end:]
        corruption = "\nassign levels[0] = ~corrupt_level0;\n"
    else:
        # CIRCT RTL uses an ANSI vector port; mapped netlists above use bit nets.
        # Retain the public port name and rename only its internal driver.
        body, count = re.subn(r'\blevels\b', 'corrupt_levels', original[header_end:])
        if not count or not re.search(r'output\b[^;]*\blevels\b', original[:header_end], re.S):
            raise RuntimeError("Mutation anchor is missing")
        mutant = original[:header_end] + "\nwire [2:0] corrupt_levels;\n" + body
        corruption = "\nassign levels = corrupt_levels ^ 3'b001;\n"
    end = mutant.rindex("endmodule")
    mutant = mutant[:end] + corruption + mutant[end:]
    (out / "mutant.v").write_text(mutant)
    mutated_command = [str(out / "mutant.v") if x == str(args.netlist) else x for x in command]
    result = subprocess.run(mutated_command, cwd=ROOT, capture_output=True, text=True)
    (out / "mutant-compile.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError("Mutant compilation failed; this does not establish detection")
    result = subprocess.run([str(suite / "vvp"), str(out / "sim.vvp")], cwd=ROOT, capture_output=True, text=True)
    (out / "mutant.log").write_text(result.stdout + result.stderr)
    if result.returncode == 0 or not any(s in result.stdout for s in ["NETLIST edge", "LOADER edge"]):
        raise RuntimeError("Output corruption was not rejected by the behavioral check")
    receipt = {"simulation": simulation, "mutants_rejected": 1, "boundary": "Zero-delay gate simulation; reference-X bits excluded. No timing simulation or universal equivalence proof."}
    paths = [args.netlist, models, primitives, BASE / "core/design.sv", ROOT / "test/loader_tb.sv", args.vectors, Path(__file__).resolve()]
    receipt["sha256"] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (out / "report.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(simulation + "Rejected output corruption mutant.")


if __name__ == "__main__":
    main()
