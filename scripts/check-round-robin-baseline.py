#!/usr/bin/env python3
"""Compare generated selectors with an independent two-pass priority baseline.

Both implementations are rebuilt, exhaustively simulated before and after the
same generic synthesis flow, and compared by Yosys SAT under a one-hot cursor
condition. Generic cell counts are not physical area or timing measurements.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import time

ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT / "scripts/check-round-robin-circuit.py"
spec = importlib.util.spec_from_file_location("round_robin_circuit_validation", HELPER)
rr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rr)


def source_hashes():
    result = rr.source_hashes()
    result[str(Path(__file__).resolve().relative_to(ROOT))] = rr.sha(__file__)
    return dict(sorted(result.items()))


def baseline_verilog(data):
    """Decode the cursor once, then use masked and unmasked priority encoders.

    This implementation deliberately does not inspect the generated expression
    tree. Port metadata supplies only the interface and its cardinality.
    """
    count = data["request_count"]
    ports = [f"input wire {name}" for name in data["requests"] + data["cursor"]]
    ports += [f"output wire {name}" for name in data["grants"] + [data["any_grant"]]]
    requests = ", ".join(reversed(data["requests"]))
    cursor = ", ".join(reversed(data["cursor"]))
    connections = "\n".join(f"assign {name} = grant[{index}];"
                             for index, name in enumerate(data["grants"]))
    return f"""// Independent conventional round-robin selector; combinational.
// Contract: cursor is exactly one-hot. Invalid encodings are unspecified.
module {data['module']}(
  {', '.join(ports)}
);
localparam integer N = {count};
wire [N-1:0] requests = {{{requests}}};
wire [N-1:0] cursor = {{{cursor}}};

// Prefix OR decodes one cursor into the positions at or above it, once.
wire [N-1:0] at_or_above_cursor;
assign at_or_above_cursor[0] = cursor[0];
genvar position;
generate
  for (position = 1; position < N; position = position + 1) begin: cursor_decode
    assign at_or_above_cursor[position] = at_or_above_cursor[position-1] | cursor[position];
  end
endgenerate
wire [N-1:0] masked_requests = requests & at_or_above_cursor;

function automatic [N-1:0] first_request(input [N-1:0] candidates);
  integer index;
  reg found;
  begin
    first_request = {{N{{1'b0}}}};
    found = 1'b0;
    for (index = 0; index < N; index = index + 1) begin
      if (candidates[index] && !found) begin
        first_request[index] = 1'b1;
        found = 1'b1;
      end
    end
  end
endfunction

wire [N-1:0] masked_grant = first_request(masked_requests);
wire [N-1:0] wrapped_grant = first_request(requests);
wire [N-1:0] grant = (|masked_requests) ? masked_grant : wrapped_grant;
{connections}
assign {data['any_grant']} = |requests;
endmodule
"""


def simulate(run, tools, directory, data, source, stage):
    label = f"{directory.name}-{stage}"
    tb = directory / "tb.sv"
    if not tb.exists():
        tb.write_text(rr.testbench(data))
    executable = directory / (stage + ".vvp")
    run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, source, tb], label + "-compile")
    trace = run([tools["vvp"], executable], label + "-simulate")
    (directory / (stage + "-trace.txt")).write_text(trace)
    return rr.check_trace(trace, data["request_count"])


def synthesize(run, tools, directory, data):
    """One identical synthesis recipe for generated and handwritten sources."""
    rtl, gates = directory / "selector.sv", directory / "gates.sv"
    stats, netlist = directory / "stats.json", directory / "netlist.json"
    script = directory / "synth.ys"
    script.write_text("\n".join((
        "read_verilog -sv " + rr.yosys_quote(rtl),
        "hierarchy -check -top " + data["module"],
        "synth -top " + data["module"], "check -assert",
        "tee -o " + rr.yosys_quote(stats) + " stat -json",
        "write_json " + rr.yosys_quote(netlist), "write_verilog -noattr " + rr.yosys_quote(gates), "")))
    run([tools["yosys"], "-Q", "-s", script], directory.name + "-synth")
    modules = json.loads(netlist.read_text())["modules"]
    if set(modules) != {data["module"]}:
        raise AssertionError("Unexpected hierarchy after selector synthesis")
    module = modules[data["module"]]
    cells = Counter(cell["type"] for cell in module.get("cells", {}).values())
    if module.get("memories") or any(not re.fullmatch(
            r"\$_(?:NOT|BUF|AND|NAND|OR|NOR|XOR|XNOR|ANDNOT|ORNOT|MUX|NMUX|AOI[34]|OAI[34])_", kind)
            for kind in cells):
        raise AssertionError(f"Expected combinational generic cells, got {dict(cells)}")
    reported = json.loads(stats.read_text())["modules"]["\\" + data["module"]]
    if reported["num_cells"] != sum(cells.values()) or reported["num_cells_by_type"] != dict(cells):
        raise AssertionError("Statistics disagree with saved netlist")
    return {"generic_cells": sum(cells.values()), "generic_cells_by_type": dict(sorted(cells.items())),
            "wire_bits": reported["num_wire_bits"]}


def equivalence_wrapper(generated, baseline):
    count = generated["request_count"]

    def instance(data, prefix):
        connections = []
        for key, signal in (("requests", "requests"), ("cursor", "cursor"),
                            ("grants", prefix + "_grants")):
            connections.extend(f".{name}({signal}[{index}])"
                               for index, name in enumerate(data[key]))
        connections.append(f".{data['any_grant']}({prefix}_any)")
        return f"{data['module']} {prefix}({', '.join(connections)});"

    return f"""module equivalence(
  input wire [{count-1}:0] requests,
  input wire [{count-1}:0] cursor,
  output wire bad
);
wire [{count-1}:0] generated_grants, baseline_grants;
wire generated_any, baseline_any;
{instance(generated, 'generated')}
{instance(baseline, 'baseline')}
// Exactly one binary cursor bit is high; other cursor encodings are excluded.
wire legal_cursor = (cursor != 0) && ((cursor & (cursor - 1'b1)) == 0);
assign bad = legal_cursor && ({{generated_grants, generated_any}} != {{baseline_grants, baseline_any}});
endmodule
"""


def prove_equivalence(run, tools, out, generated, baseline, directories, stage):
    count = generated["request_count"]
    wrapper = out / f"rr_{count}-equivalence.sv"
    if not wrapper.exists():
        wrapper.write_text(equivalence_wrapper(generated, baseline))
    source = "selector.sv" if stage == "rtl" else "gates.sv"
    script = out / f"rr_{count}-{stage}-equivalence.ys"
    script.write_text("\n".join((
        "read_verilog -sv " + " ".join(rr.yosys_quote(path / source) for path in directories)
        + " " + rr.yosys_quote(wrapper),
        "prep -top equivalence -flatten", "check -assert",
        "sat -verify -prove bad 0 -show-inputs -show-outputs", "")))
    result = run([tools["yosys"], "-Q", "-s", script], f"rr_{count}-{stage}-equivalence")
    if "SAT proof finished - no model found: SUCCESS!" not in result:
        raise AssertionError("Missing Yosys SAT equivalence success result")


def configuration(run, out, emitted, tools, count):
    generated = rr.descriptor(emitted / f"rr_{count}.json", count)
    baseline = dict(generated, module=f"round_robin_baseline_{count}")
    descriptions = {"generated": generated, "baseline": baseline}
    directories = {name: out / f"{name}-{count}" for name in descriptions}
    results = {}
    for name, data in descriptions.items():
        directory = directories[name]
        directory.mkdir()
        (directory / "interface.json").write_text(json.dumps(data, indent=2) + "\n")
        source = directory / "selector.sv"
        if name == "generated":
            source.write_text(run([tools["circt"], emitted / f"rr_{count}.mlir", "--canonicalize",
                                   "--lower-seq-to-sv", "--lower-hw-to-sv", "--hw-legalize-modules",
                                   "--export-verilog", "-o", "/dev/null"], f"generated-{count}-export"))
        else:
            source.write_text(baseline_verilog(data))
        rtl_cases = simulate(run, tools, directory, data, source, "rtl")
        stats = synthesize(run, tools, directory, data)
        gate_cases = simulate(run, tools, directory, data, directory / "gates.sv", "gates")
        results[name] = dict(stats, rtl_cases=rtl_cases, synthesized_cases=gate_cases)
    for stage in ("rtl", "gates"):
        prove_equivalence(run, tools, out, generated, baseline, list(directories.values()), stage)
    generated_cells, baseline_cells = (results[name]["generic_cells"] for name in descriptions)
    delta = generated_cells - baseline_cells
    result = dict(request_count=count, **results, generated_minus_baseline_cells=delta,
                  generated_to_baseline_ratio=round(generated_cells / baseline_cells, 4) if baseline_cells else None,
                  legal_cursor_sat_equivalence={"rtl": True, "gates": True})
    print(f"N={count}: generated={generated_cells}, baseline={baseline_cells}, delta={delta:+d} generic cells",
          flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True, help="Fresh evidence directory name")
    args = parser.parse_args()
    out = rr.fresh_directory(ROOT / "build/round-robin-baseline", args.tag)
    emitted = out / "emitted"
    emitted.mkdir()
    started = time.monotonic()
    records = []
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "baseline": "One shared prefix-OR cursor decode; priority encode masked requests, "
                          "otherwise priority encode all requests. No per-cursor rotated selector trees.",
              "boundary": "Fresh matched generic synthesis comparison; exhaustive binary simulations "
                          "and Yosys SAT equivalence before/after synthesis for exactly one-hot cursors. "
                          "Lean structural proof audit covers the generated selector. No Lean proof of "
                          "the handwritten baseline or kernel-certified RTL correspondence; no physical "
                          "area, timing, sequential fairness or whole-switch conclusion. Invalid cursor "
                          "behavior may differ, so optimizations outside the legal domain may differ.",
              "synthesis_settings": "Yosys read_verilog -sv; hierarchy -check; synth with default "
                                    "generic ABC mapping; check -assert; stat -json. No cell library.",
              "tool_hash_scope": "Selected launchers, executables, ABC and Icarus backend; "
                                 "not a complete host dynamic-library closure."}
    run = rr.Commands(out, records)
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, tool_paths = rr.selected_tools()
        report["tool_manifest"] = manifest
        report["tool_sha256"] = rr.tool_hashes(tool_paths)
        report["comparator_mutations_rejected"] = rr.checker_self_test()
        run(["lake", "env", "lean", "--version"], "lean-version")
        run([tools["circt"], "--version"], "circt-version")
        run([tools["iverilog"], "-V"], "iverilog-version")
        run([tools["yosys"], "-V"], "yosys-version")
        run(["lake", "build", "Pinwheel.Hardware.Arbitration.RoundRobinCircuit", "Pinwheel.Hardware.Emit"],
            "build", timeout=900)
        lean_output = run(["lake", "env", "lean", "-DwarningAsError=true", "--run",
                           "test/RoundRobinCircuit.lean", emitted], "structural-audit-and-emit")
        match = re.search(r"Structural round-robin: ([0-9]+) exhaustive selections passed\.", lean_output)
        if match is None or "standard axioms only" not in lean_output:
            raise AssertionError("Missing structural exhaustive selection result or proof audit")
        report["lean_structural_cases"] = int(match[1])
        for count in rr.COUNTS:
            report["configurations"].append(configuration(run, out, emitted, tools, count))
        if source_hashes() != report["source_sha256"]:
            raise RuntimeError("Owning sources changed during validation; use a fresh tag")
        if rr.tool_hashes(tool_paths) != report["tool_sha256"]:
            raise RuntimeError("Selected tools changed during validation; use a fresh tag")
        report["generated_cell_regressions"] = [row["request_count"] for row in report["configurations"]
                                                if row["generated_minus_baseline_cells"] > 0]
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["artifact_sha256"] = {str(path.relative_to(out)): rr.sha(path)
                                     for path in sorted(out.rglob("*")) if path.is_file()}
        report["seconds"] = round(time.monotonic() - started, 3)
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
