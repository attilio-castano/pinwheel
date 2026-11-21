#!/usr/bin/env python3
"""Isolate shared winner decoding across grant, payload and next-cursor outputs.

Both expression implementations use the same external signals and no state.
This is an isolated localization experiment, not a whole-switch resource claim.
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


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


rr = load("selector_tools", "check-round-robin-circuit.py")
metrics = load("selector_metrics", "check-switch-baseline.py")
MATRIX = tuple((count, width) for count in (1, 2, 3, 5, 8) for width in (1, 8, 17))


def source_hashes():
    result, pending = {}, [ROOT / "test/OneHotSelect.lean"]
    while pending:
        path = pending.pop()
        name = str(path.relative_to(ROOT))
        if name in result:
            continue
        result[name] = rr.sha(path)
        for line in path.read_text().splitlines():
            match = re.match(r"^import\s+(.+)$", line)
            if match:
                for module in match[1].split("--", 1)[0].split():
                    if module.startswith(("Pinwheel.", "test.")):
                        pending.append(ROOT / (module.replace(".", "/") + ".lean"))
    for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json", "tools/hardware-toolchain.json",
                 "scripts/check-one-hot-select.py", "scripts/check-switch-baseline.py",
                 "scripts/check-switch-circuit.py", "scripts/check-switch-model.py", "scripts/switch_oracle.py",
                 "scripts/check-round-robin-circuit.py", "scripts/validation_run.py", "scripts/process_group.py"):
        result[name] = rr.sha(ROOT / name)
    return dict(sorted(result.items()))


def descriptor(path, count, width, mode):
    data = json.loads(path.read_text())
    for key, value in (("schema", 1), ("request_count", count), ("width", width), ("mode", mode), ("registers", [])):
        if data.get(key) != value:
            raise ValueError(f"Descriptor {key} mismatch")
    if not rr.IDENTIFIER.fullmatch(data["module"]):
        raise ValueError("Invalid module name")
    names = []
    for group in ("inputs", "outputs"):
        for port in data[group]:
            if not rr.IDENTIFIER.fullmatch(port["name"]) or type(port["width"]) is not int or port["width"] <= 0:
                raise ValueError("Invalid port")
            names.append(port["name"])
    if len(names) != len(set(names)):
        raise ValueError("Duplicate ports")
    ins, outs = {}, {}
    for role, bits, target in (("requests", 1, ins), ("cursor", 1, ins), ("values", width, ins),
                               ("grants", 1, outs), ("next_cursor", 1, outs)):
        if len(data[role]) != count:
            raise ValueError("Wrong role count")
        for name in data[role]:
            if name in target:
                raise ValueError("Duplicate role")
            target[name] = bits
    ins[data["fallback"]], outs[data["any_grant"]], outs[data["payload"]] = width, 1, width
    if ins != {p["name"]: p["width"] for p in data["inputs"]} or \
            outs != {p["name"]: p["width"] for p in data["outputs"]}:
        raise ValueError("Role map does not cover every port")
    return data


def testbench(data):
    n = data["request_count"]
    declarations = [f"{kind} [{p['width']-1}:0] {p['name']};"
                    for group, kind in (("inputs", "reg"), ("outputs", "wire")) for p in data[group]]
    connections = ", ".join(f".{p['name']}({p['name']})" for p in data["inputs"] + data["outputs"])
    assignments = []
    for k in range(n):
        assignments.extend((f"{data['requests'][k]} = (mask >> {k}) & 1;",
                            f"{data['cursor'][k]} = (cursor == {k});",
                            f"{data['values'][k]} = (mask + 17) * {k+3} + cursor * 5;"))
    assignments.append(f"{data['fallback']} = 131071 - mask * 3 + cursor;")
    return "`timescale 1ns/1ps\nmodule tb;\n" + "\n".join(declarations) + f"""
{data['module']} dut({connections});
wire [{n-1}:0] grants = {{{', '.join(reversed(data['grants']))}}};
wire [{n-1}:0] following = {{{', '.join(reversed(data['next_cursor']))}}};
integer cursor, mask;
initial begin
  for (cursor=0; cursor<{n}; cursor=cursor+1) begin
    for (mask=0; mask<{1 << n}; mask=mask+1) begin
      {chr(10).join(assignments)}
      #1;
      $display("SEL,%0d,%0d,%0d,%0d,%0d,%0d", cursor, mask, grants, {data['any_grant']}, {data['payload']}, following);
    end
  end
  $display("SEL_DONE");
  $finish;
end
endmodule
"""


def check_trace(text, n, width):
    observations, done = [], 0
    for line in text.splitlines():
        if line == "SEL_DONE":
            done += 1
        elif line.startswith("SEL,"):
            fields = line.split(",")[1:]
            if done or len(fields) != 6 or any(not field.isdecimal() for field in fields):
                raise AssertionError("Malformed, unknown-valued or late observation")
            observations.append(tuple(map(int, fields)))
        elif line and not re.fullmatch(r".*: \$finish called at [0-9]+ \([0-9]+[smunpf]s?\)", line):
            raise AssertionError("Unexpected simulator output")
    if done != 1 or len(observations) != n * (1 << n):
        raise AssertionError("Incomplete selector trace")
    for cursor in range(n):
        for mask in range(1 << n):
            winner = next(((cursor + offset) % n for offset in range(n)
                           if mask & (1 << ((cursor + offset) % n))), None)
            payload = (131071 - mask * 3 + cursor) if winner is None else (mask + 17) * (winner + 3) + cursor * 5
            expected = (cursor, mask, 0 if winner is None else 1 << winner, int(winner is not None),
                        payload & ((1 << width) - 1), 1 << (cursor if winner is None else (winner + 1) % n))
            if observations[cursor * (1 << n) + mask] != expected:
                raise AssertionError(f"Wrong selector observation: expected {expected}")
    return len(observations)


def sat_wrapper(left, right):
    declarations = [f"input wire [{p['width']-1}:0] {p['name']}" for p in left["inputs"]] + ["output wire bad"]
    lines = ["module equivalence(" + ", ".join(declarations) + ");"]
    for side, data in (("left", left), ("right", right)):
        lines.extend(f"wire [{p['width']-1}:0] {side}_{p['name']};" for p in data["outputs"])
        ports = [f".{p['name']}({p['name']})" for p in data["inputs"]]
        ports += [f".{p['name']}({side}_{p['name']})" for p in data["outputs"]]
        lines.append(f"{data['module']} {side}({', '.join(ports)});")
    n = left["request_count"]
    lines.append(f"wire [{n-1}:0] cursor = {{{', '.join(reversed(left['cursor']))}}};")
    lines.append("wire legal = (cursor != 0) && ((cursor & (cursor - 1'b1)) == 0);")
    mismatch = " || ".join(f"(left_{p['name']} != right_{p['name']})" for p in left["outputs"])
    lines.extend(("assign bad = legal && (" + mismatch + ");", "endmodule", ""))
    return "\n".join(lines)


def configuration(run, out, tools, count, width):
    results, data_by_mode = {}, {}
    for mode in ("masked", "shared"):
        name = f"select_{mode}_{count}_w{width}"
        data = descriptor(out / "emitted" / (name + ".json"), count, width, mode)
        data_by_mode[mode] = data
        directory = out / name
        directory.mkdir()
        source, tb = directory / "selector.sv", directory / "tb.sv"
        source.write_text(run([tools["circt"], out / "emitted" / (name + ".mlir"), "--canonicalize",
                               "--lower-seq-to-sv", "--lower-hw-to-sv", "--hw-legalize-modules",
                               "--export-verilog", "-o", "/dev/null"], name + "-lower"))
        tb.write_text(testbench(data))
        script = directory / "synth.ys"
        script.write_text(metrics.synthesis_script(source, data["module"], directory))
        run([tools["yosys"], "-Q", "-s", script], name + "-synth")
        result = metrics.resources(directory, data["module"])
        if result["logic_depth"]["register_bits"]:
            raise AssertionError("Combinational selector unexpectedly contains registers")
        for stage, rtl in (("rtl", source), ("gates", directory / "gates.sv")):
            executable = directory / (stage + ".vvp")
            run([tools["iverilog"], "-g2012", "-s", "tb", "-o", executable, rtl, tb], name + "-" + stage + "-compile")
            text = run([tools["vvp"], executable], name + "-" + stage + "-simulate")
            (directory / (stage + "-trace.txt")).write_text(text)
            result[stage + "_cases"] = check_trace(text, count, width)
        # The operation cache emits each identical textual DAG node at most
        # once; record the full bundle to make sharing inspectable in artifacts.
        mlir = (out / "emitted" / (name + ".mlir")).read_text()
        operations = re.findall(r"^\s*%v[0-9]+ = (.+)$", mlir, re.MULTILINE)
        if len(operations) != len(set(operations)):
            raise AssertionError("Emitter repeated an identical cached operation")
        result["emitted_unique_operations"] = len(operations)
        results[mode] = result
    wrapper = out / f"equivalence_{count}_w{width}.sv"
    wrapper.write_text(sat_wrapper(data_by_mode["masked"], data_by_mode["shared"]))
    for stage, file in (("rtl", "selector.sv"), ("gates", "gates.sv")):
        script = out / f"equivalence_{count}_w{width}_{stage}.ys"
        sources = [out / f"select_{mode}_{count}_w{width}" / file for mode in ("masked", "shared")]
        script.write_text("\n".join(("read_verilog -sv " + " ".join(map(rr.yosys_quote, sources + [wrapper])),
            "prep -top equivalence -flatten", "check -assert", "sat -verify -prove bad 0 -show-inputs -show-outputs", "")))
        text = run([tools["yosys"], "-Q", "-s", script], f"equivalence-{count}-w{width}-{stage}")
        if "SAT proof finished - no model found: SUCCESS!" not in text:
            raise AssertionError("Missing SAT success")
    result = {"request_count": count, "width": width, **results,
              "cell_delta_shared_minus_masked": results["shared"]["generic_cells"] - results["masked"]["generic_cells"],
              "sat_equivalence_all_values_and_fallback": {"rtl": True, "gates": True}}
    print(f"BUNDLE N={count} W={width}: masked={results['masked']['generic_cells']}, "
          f"shared={results['shared']['generic_cells']}; "
          f"levels={results['masked']['logic_depth']['max_output_levels']}/"
          f"{results['shared']['logic_depth']['max_output_levels']}", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    args = parser.parse_args()
    out = rr.fresh_directory(ROOT / "build/one-hot-select", args.tag)
    (out / "emitted").mkdir()
    started, records = time.monotonic(), []
    report = {"schema": 1, "status": "running", "commands": records, "configurations": [],
              "experiment": "Identical combinational bundle: request/cursor/value/fallback inputs; "
                            "grant vector, any, payload and next-cursor outputs. Only selection architecture changes.",
              "boundary": "Universal Lean selector proof and standard-axiom audit; finite exhaustive legal "
                          "cursor/request simulation with chosen data patterns, plus Yosys SAT for every binary "
                          "value/fallback under legal one-hot cursors, before/after generic synthesis. "
                          "No switch state/control changes, kernel RTL certificate or physical area/timing claim."}
    run = rr.Commands(out, records)
    try:
        report["source_sha256"] = source_hashes()
        manifest, tools, paths = rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, rr.tool_hashes(paths)
        run(["lake", "build", "Pinwheel.Hardware.Arbitration.OneHotSelect", "Pinwheel.Hardware.Emit"], "build", timeout=900)
        audit = run(["lake", "env", "lean", "-DwarningAsError=true", "--run", "test/OneHotSelect.lean", out / "emitted"],
                    "proof-audit-and-emit", timeout=900)
        if "standard axioms only" not in audit or "6726 exhaustive cursor/request cases" not in audit:
            raise AssertionError("Missing shared selector proof/exhaustive test receipt")
        for count, width in MATRIX:
            report["configurations"].append(configuration(run, out, tools, count, width))
        if source_hashes() != report["source_sha256"] or rr.tool_hashes(paths) != report["tool_sha256"]:
            raise RuntimeError("Owning sources/tools changed during validation; use a fresh tag")
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
