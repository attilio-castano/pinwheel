#!/usr/bin/env python3
"""Independent conventional switch baseline under matched generic synthesis.

The baseline is handwritten SystemVerilog with occupancy-counted shift FIFOs,
binary round-robin cursors and per-output holding registers. It is tested from
reset against the independent deque oracle; it has no Lean correctness proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("switch_circuit_checks", ROOT / "scripts/check-switch-circuit.py")
sw = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sw)
rr = sw.rr
COMBINATIONAL = re.compile(r"\$_(?:NOT|BUF|AND|NAND|OR|NOR|XOR|XNOR|ANDNOT|ORNOT|MUX|NMUX|AOI[34]|OAI[34])_\Z")
SEQUENTIAL = re.compile(r"\$_(?:DFF|DFFE|SDFF|SDFFE|SDFFCE)_[PN01]+_\Z")


def source_hashes():
    result = sw.source_hashes()
    for name in ("scripts/check-switch-baseline.py", "test/test_switch_baseline.py"):
        result[name] = rr.sha(ROOT / name)
    return dict(sorted(result.items()))


def baseline_verilog(data):
    """Consume only external port metadata and dimensions, never Lean AST/state."""
    ni, no, depth, width, dw = (data[k] for k in
        ("input_count", "output_count", "depth", "payload_width", "destination_width"))
    roles = data["roles"]
    ports = ["input wire " + data["clock"]]
    ports += [f"input wire [{p['width']-1}:0] {p['name']}" for p in data["inputs"]]
    ports += [f"output wire [{p['width']-1}:0] {p['name']}" for p in data["outputs"]]
    wiring = [f"wire reset = {roles['reset']};"]
    for role, signal in (("in_valid", "in_valid"), ("out_ready", "out_ready")):
        wiring.append(f"wire [{len(roles[role])-1}:0] {signal} = {{{', '.join(reversed(roles[role]))}}};")
    for source in range(ni):
        wiring.extend((f"assign in_destination[{source}] = {roles['in_destination'][source]};",
                       f"assign in_payload[{source}] = {roles['in_payload'][source]};",
                       f"assign {roles['in_ready'][source]} = in_ready[{source}];"))
    for output in range(no):
        wiring.extend((f"assign {roles['out_valid'][output]} = out_valid[{output}];",
                       f"assign {roles['out_payload'][output]} = out_payload[{output}];"))
    return f"""// Independent reference architecture. Behavior is specified from a reset edge.
// Private FIFO counters/storage and binary cursors need not match generated RTL.
module {data['module']}(
  {', '.join(ports)}
);
localparam integer INPUTS = {ni}, OUTPUTS = {no}, DEPTH = {depth};
localparam integer WIDTH = {width}, DEST_WIDTH = {dw};
localparam integer COUNT_WIDTH = (DEPTH < 2) ? 1 : $clog2(DEPTH + 1);
localparam integer CURSOR_WIDTH = (INPUTS < 2) ? 1 : $clog2(INPUTS);
wire [DEST_WIDTH-1:0] in_destination [0:INPUTS-1];
wire [WIDTH-1:0] in_payload [0:INPUTS-1];
wire [INPUTS-1:0] in_ready, head_valid, pop;
wire [DEST_WIDTH-1:0] head_destination [0:INPUTS-1];
wire [WIDTH-1:0] head_payload [0:INPUTS-1];
wire [OUTPUTS-1:0] out_valid;
wire [WIDTH-1:0] out_payload [0:OUTPUTS-1];
wire [INPUTS-1:0] grants [0:OUTPUTS-1];
{chr(10).join(wiring)}

genvar source, output_index;
generate
  for (source = 0; source < INPUTS; source = source + 1) begin: fifo
    reg [COUNT_WIDTH-1:0] count;
    reg [DEST_WIDTH+WIDTH-1:0] storage [0:DEPTH-1];
    wire [OUTPUTS-1:0] takes;
    for (output_index = 0; output_index < OUTPUTS; output_index = output_index + 1) begin: consumers
      assign takes[output_index] = grants[output_index][source];
    end
    assign pop[source] = |takes;
    assign head_valid[source] = (count != 0);
    assign head_destination[source] = storage[0][WIDTH +: DEST_WIDTH];
    assign head_payload[source] = storage[0][0 +: WIDTH];
    wire legal_destination = (in_destination[source] < OUTPUTS);
    wire space_available = (count < DEPTH) || pop[source];
    wire push = !reset && in_valid[source] && legal_destination && space_available;
    assign in_ready[source] = !reset && (!in_valid[source] || legal_destination) && space_available;
    integer cell_index;
    always @(posedge {data['clock']}) begin
      if (reset) begin
        count <= 0;
        for (cell_index = 0; cell_index < DEPTH; cell_index = cell_index + 1)
          storage[cell_index] <= 0;
      end else begin
        case ({{push, pop[source]}})
          2'b10: count <= count + 1'b1;
          2'b01: count <= count - 1'b1;
          default: count <= count;
        endcase
        if (pop[source]) begin
          for (cell_index = 0; cell_index < DEPTH-1; cell_index = cell_index + 1)
            storage[cell_index] <= storage[cell_index+1];
          storage[DEPTH-1] <= 0;
        end
        // Appending after the shift also permits replacement of a full queue.
        if (push) storage[count - pop[source]] <= {{in_destination[source], in_payload[source]}};
      end
    end
  end

  for (output_index = 0; output_index < OUTPUTS; output_index = output_index + 1) begin: output_slot
    reg occupied;
    reg [WIDTH-1:0] payload;
    reg [CURSOR_WIDTH-1:0] cursor;
    wire can_load = !occupied || out_ready[output_index];
    wire [INPUTS-1:0] requests;
    for (source = 0; source < INPUTS; source = source + 1) begin: candidates
      assign requests[source] = head_valid[source] && (head_destination[source] == output_index);
    end
    reg [INPUTS-1:0] selected;
    reg found;
    reg [WIDTH-1:0] selected_payload;
    reg [CURSOR_WIDTH-1:0] following_cursor;
    integer candidate;
    always @* begin
      selected = 0;
      found = 0;
      // First scan at/above the binary cursor; second scan handles wraparound.
      for (candidate = 0; candidate < INPUTS; candidate = candidate + 1) begin
        if (!found && (candidate >= cursor) && requests[candidate]) begin
          selected[candidate] = 1;
          found = 1;
        end
      end
      for (candidate = 0; candidate < INPUTS; candidate = candidate + 1) begin
        if (!found && requests[candidate]) begin
          selected[candidate] = 1;
          found = 1;
        end
      end
      selected_payload = 0;
      following_cursor = cursor;
      for (candidate = 0; candidate < INPUTS; candidate = candidate + 1) begin
        selected_payload = selected_payload | ({{WIDTH{{selected[candidate]}}}} & head_payload[candidate]);
        if (selected[candidate])
          following_cursor = (candidate == INPUTS-1) ? 0 : candidate + 1;
      end
    end
    assign grants[output_index] = {{INPUTS{{!reset && can_load}}}} & selected;
    assign out_valid[output_index] = !reset && occupied;
    assign out_payload[output_index] = reset ? 0 : payload;
    always @(posedge {data['clock']}) begin
      if (reset) begin
        occupied <= 0;
        payload <= 0;
        cursor <= 0;
      end else if (can_load) begin
        occupied <= |selected;
        payload <= selected_payload;
        if (|selected) cursor <= following_cursor;
      end
    end
  end
endgenerate
endmodule
"""


def generic_depth(module):
    """Unit-cost combinational cell levels between inputs/Q and outputs/D/E/R.

    Every generic combinational cell has cost one, including MUX/AOI/OAI. Flops
    cut the paths, and clock inputs are excluded as endpoints. This deliberately
    measures graph structure, not gate delay, fanout, routing or physical timing.
    """
    sources, drivers, cells = set(), {}, module.get("cells", {})
    endpoints, register_bits = {}, 0
    for name, port in module["ports"].items():
        if port["direction"] == "input":
            sources.update(port["bits"])
        elif port["direction"] == "output":
            for index, bit in enumerate(port["bits"]):
                endpoints[f"output:{name}[{index}]"] = bit
        else:
            raise ValueError("Unsupported inout port in logic-depth metric")
    for name, cell in cells.items():
        kind, connections = cell["type"], cell["connections"]
        if SEQUENTIAL.fullmatch(kind):
            sources.update(connections["Q"])
            register_bits += len(connections["Q"])
            for port, direction in cell["port_directions"].items():
                if direction == "input" and port != "C":
                    for index, bit in enumerate(connections[port]):
                        endpoints[f"register:{name}.{port}[{index}]"] = bit
        elif COMBINATIONAL.fullmatch(kind):
            for port, direction in cell["port_directions"].items():
                if direction == "output":
                    for bit in connections[port]:
                        if not isinstance(bit, int) or bit in drivers:
                            raise ValueError("Constant or multiply-driven combinational output")
                        drivers[bit] = name
        else:
            raise ValueError(f"Unsupported logic-depth cell: {kind}")
    if set(drivers) & sources:
        raise ValueError("Combinational driver aliases a primary input or register output")
    cache, active = {}, set()

    def path(bit):
        if isinstance(bit, str) or bit in sources:
            return 0, []
        if bit in cache:
            return cache[bit]
        if bit not in drivers:
            raise ValueError(f"Undriven bit in logic-depth cone: {bit}")
        name = drivers[bit]
        if name in active:
            raise ValueError("Combinational cycle in logic-depth cone")
        active.add(name)
        cell = cells[name]
        inputs = [b for p, direction in cell["port_directions"].items() if direction == "input"
                  for b in cell["connections"][p]]
        longest = max((path(b) for b in inputs), key=lambda item: item[0], default=(0, []))
        result = longest[0] + 1, longest[1] + [{"cell": name, "type": cell["type"]}]
        active.remove(name)
        cache[bit] = result
        return result

    measured = {name: path(bit) for name, bit in endpoints.items()}
    worst = max(measured, key=lambda name: measured[name][0], default=None)
    return {"max_combinational_cell_levels": measured[worst][0] if worst else 0,
            "max_output_levels": max((value[0] for name, value in measured.items()
                                      if name.startswith("output:")), default=0),
            "max_register_input_levels": max((value[0] for name, value in measured.items()
                                              if name.startswith("register:")), default=0),
            "register_bits": register_bits, "endpoint_count": len(endpoints),
            "worst_endpoint": worst, "worst_path": measured[worst][1] if worst else [],
            "definition": "One level per generic combinational cell, inputs/Q depth zero, "
                          "outputs and register D/E/R endpoints; clock endpoints excluded. Not timing."}


def synthesis_script(source, top, directory):
    return "\n".join(("read_verilog -sv " + rr.yosys_quote(source),
        "hierarchy -check -top " + top, "synth -top " + top, "check -assert",
        "tee -o " + rr.yosys_quote(directory / "stats.json") + " stat -json",
        "write_json " + rr.yosys_quote(directory / "netlist.json"),
        "write_verilog -noattr " + rr.yosys_quote(directory / "gates.sv"), ""))


def resources(directory, top):
    modules = json.loads((directory / "netlist.json").read_text())["modules"]
    if set(modules) != {top} or modules[top].get("memories"):
        raise AssertionError("Expected a completely synthesized single module")
    module = modules[top]
    cells = Counter(cell["type"] for cell in module.get("cells", {}).values())
    reported = json.loads((directory / "stats.json").read_text())["modules"]["\\" + top]
    if reported["num_cells"] != sum(cells.values()) or reported["num_cells_by_type"] != dict(cells):
        raise AssertionError("Synthesis statistics disagree with saved netlist")
    return {"generic_cells": sum(cells.values()), "generic_cells_by_type": dict(sorted(cells.items())),
            "generic_wire_bits": reported["num_wire_bits"], "logic_depth": generic_depth(module)}


def reset_coverage(rows, logical):
    empty, loaded, signatures = 0, 0, set()
    previous = None
    for row, frame in zip(rows, logical, strict=True):
        if row["reset"]:
            if previous is not None:
                signature = (tuple(len(q) for q in previous["queues"]),
                             tuple(p is not None for p in previous["slots"]), tuple(previous["cursor"]))
                signatures.add(signature)
                if any(signature[0]) or any(signature[1]):
                    loaded += 1
                else:
                    empty += 1
        previous = frame["state"]
    if loaded == 0:
        raise AssertionError("Traffic must exercise reset of a loaded switch")
    return {"power_up_reset": True, "loaded_reset_edges": loaded, "empty_reset_edges": empty,
            "distinct_reset_pre_state_shapes": len(signatures)}


def configuration(run, out, tools, config, random_edges):
    # The existing campaign reruns generated RTL, exact Lean replay, the deque
    # oracle, every register, and actual RTL negative controls under this tag.
    generated_evidence = sw.configuration(run, out, tools, config, random_edges)
    ni, no, depth, width = config
    label = f"i{ni}-o{no}-d{depth}-w{width}"
    generated_dir = out / label
    data = sw.descriptor(generated_dir / "interface.json", config)
    expected_script = synthesis_script(generated_dir / "switch.sv", data["module"], generated_dir)
    if (generated_dir / "synth.ys").read_text() != expected_script:
        raise AssertionError("Frozen generated synthesis settings diverged from the matched baseline flow")
    generated_stats = resources(generated_dir, data["module"])
    rows, _ = sw.traffic(config, random_edges)
    _, logical, frames = sw.expected_frames(data, rows, config)
    reset_cases = reset_coverage(rows, logical)
    directory = out / (label + "-baseline")
    directory.mkdir()
    baseline_data = {key: data[key] for key in ("schema", "input_count", "output_count", "depth",
        "payload_width", "destination_width", "clock", "inputs", "outputs", "roles")}
    baseline_data.update(module=data["module"] + "_baseline", registers=[],
                         state_contract="Private occupancy counters and binary cursors; reset required before use")
    (directory / "interface.json").write_text(json.dumps(baseline_data, indent=2) + "\n")
    source = directory / "switch.sv"
    source.write_text(baseline_verilog(baseline_data))
    tb = directory / "tb.sv"
    tb.write_text(sw.testbench(baseline_data, rows, False))

    def simulate(rtl, stage):
        executable = directory / (stage + ".vvp")
        run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, rtl, tb],
            label + "-baseline-" + stage + "-compile")
        text = run([tools["vvp"], executable], label + "-baseline-" + stage + "-simulate")
        (directory / (stage + "-trace.txt")).write_text(text)
        return sw.check_rtl_trace(text, frames, False)

    rtl_edges = simulate(source, "rtl")
    script = directory / "synth.ys"
    script.write_text(synthesis_script(source, baseline_data["module"], directory))
    run([tools["yosys"], "-Q", "-s", script], label + "-baseline-synth", timeout=300)
    baseline_stats = resources(directory, baseline_data["module"])
    gate_edges = simulate(directory / "gates.sv", "gates")
    generated_cells, baseline_cells = generated_stats["generic_cells"], baseline_stats["generic_cells"]
    result = {"configuration": config, "edges_per_implementation_per_form": len(rows),
              "generated": generated_stats, "baseline": dict(baseline_stats, rtl_edges=rtl_edges,
                                                               synthesized_edges=gate_edges),
              "generated_minus_baseline_cells": generated_cells - baseline_cells,
              "generated_to_baseline_cell_ratio": round(generated_cells / baseline_cells, 4),
              "generated_minus_baseline_logic_levels":
                  generated_stats["logic_depth"]["max_combinational_cell_levels"] -
                  baseline_stats["logic_depth"]["max_combinational_cell_levels"],
              "reset_coverage": reset_cases, "coverage": generated_evidence["coverage"],
              "accounting": generated_evidence["accounting"],
              "generated_rtl_negative_controls": generated_evidence["rtl_negative_controls"]}
    (directory / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"MATCHED {config}: generated={generated_cells}, baseline={baseline_cells} generic cells; "
          f"levels={generated_stats['logic_depth']['max_combinational_cell_levels']}/"
          f"{baseline_stats['logic_depth']['max_combinational_cell_levels']}", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--config", action="append", type=sw.model_checks.parse_config)
    parser.add_argument("--random-edges", type=int, default=384)
    args = parser.parse_args()
    configs = args.config or sw.MATRIX
    if args.random_edges < 0 or len(configs) != len(set(configs)):
        parser.error("Use nonnegative random edges and distinct configurations")
    out = rr.fresh_directory(ROOT / "build/switch-baseline", args.tag)
    started, records = time.monotonic(), []
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "baseline_architecture": "Independently authored SV: bounded shift FIFO per input with "
                                       "occupancy counter; payload holding register and binary round-robin "
                                       "cursor per output; two ascending priority scans; no input bypass.",
              "boundary": "Baseline validation evidence only: exact sampled pre/post outputs from reset "
                          "against the independent deque oracle, before and after matched generic synthesis. "
                          "Baseline private state representation differs and is not compared to Lean state. "
                          "No Lean baseline proof, arbitrary uninitialized-state equivalence, sequential SAT "
                          "equivalence, RTL artifact certificate, physical area or timing claim. "
                          "Generated-circuit proofs are separately audited.",
              "synthesis_settings": "Identical read_verilog -sv; hierarchy -check; synth default generic "
                                    "ABC mapping; check -assert; stat -json; no technology cell library.",
              "tool_hash_scope": "Selected launchers, executables, ABC and Icarus backend; "
                                 "not a complete host dynamic-library closure."}
    run = rr.Commands(out, records)
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        report["trace_mutations_rejected"] = sw.checker_self_test()
        run([sys.executable, "-B", "-m", "unittest", "discover", "-s", "test", "-p", "test_switch_baseline.py", "-v"],
            "depth-metric-tests")
        run(["lake", "env", "lean", "--version"], "lean-version")
        for tool, option in (("circt", "--version"), ("iverilog", "-V"), ("yosys", "-V")):
            run([tools[tool], option], tool + "-version")
        run(["lake", "build", "Pinwheel.Hardware.Switch.CircuitProofs", "Pinwheel.Hardware.Emit"], "build", timeout=900)
        audit_file = out / "ProofAudit.lean"
        audit_file.write_text(sw.audit_source())
        if "standard axioms only" not in run(
                ["lake", "env", "lean", "-DwarningAsError=true", audit_file], "generated-proof-audit"):
            raise AssertionError("Missing generated-circuit proof audit")
        run([sys.executable, "-B", "-m", "unittest", "discover", "-s", "test", "-p", "test_switch_oracle.py", "-v"],
            "oracle-tests")
        for config in configs:
            report["configurations"].append(configuration(run, out, tools, config, args.random_edges))
        if source_hashes() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources or tools changed during validation; use a fresh tag")
        report["status"] = "passed"
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): rr.sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
