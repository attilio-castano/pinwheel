#!/usr/bin/env python3
"""Matched pre-layout OpenSTA under explicit interface and wire-load assumptions.

Consumes already checked mapped netlists, without remapping. A completed
analysis is distinct from meeting the declared timing/electrical constraints.
Only the pinned typical/slow corners are covered; no fast-corner hold or
physical qualification is implied.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import time
import uuid

from streaming_tt_physical import inspect_runtime
from validation_run import fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]
FF = "sg13cmos5l_dfrbpq_1"
POLICY = {"period_ns": 10.0, "input_max_ns": 1.0, "input_min_ns": 0.2,
          "output_max_ns": 1.0, "output_min_ns": -0.2, "external_output_hold_ns": 0.2,
          "clock_transition_ns": 0.1, "driver_input_transition_ns": 0.1,
          "setup_uncertainty_ns": 0.1, "hold_uncertainty_ns": 0.05,
          "output_load_pf": 0.010, "input_driver": "sg13cmos5l_buf_2", "input_driver_pin": "X",
          "clock": "ideal, zero insertion/skew; no propagated clock", "wire_load_model": "Zero",
          "wire_load_mode": "top", "timing_exceptions": [], "case_analysis": [],
          "boundary": "Comparison assumptions, not a board/interface specification. Named Zero has nonzero Liberty RC."}
SECTIONS = ("UNITS", "CHECK_SETUP", "SETUP", "HOLD", "REG_SETUP", "REG_HOLD", "ELECTRICAL")


def mapper(ownership=False):
    filename = "check-memory-transfer-host-ownership-technology.py" if ownership else "check-memory-transfer-host-technology.py"
    spec = importlib.util.spec_from_file_location("host_sta_mapper", ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sources(mapping):
    result = mapping.sources()
    result.update({name: sha(ROOT / name) for name in (
        "scripts/check-memory-transfer-host-sta.py", "scripts/streaming_tt_physical.py",
        "tools/physical-toolchain.json", "test/test_memory_transfer_host_sta.py")})
    return dict(sorted(result.items()))


def contained(base, name):
    if type(name) is not str:
        raise ValueError("Receipt artifact name must be a string")
    path = (base / name).resolve()
    if not path.is_relative_to(base.resolve()):
        raise ValueError("Receipt artifact escapes its bundle")
    return path


def verify_receipt(path, mapping, tool_hashes, ownership=False):
    report = json.loads(path.read_text())
    if report.get("status") != "passed" or report.get("source_sha256") != mapping.sources() or \
            report.get("tool_sha256") != tool_hashes:
        raise ValueError("Require a passed source-current technology receipt with identical selected tools")
    lib_manifest, libraries = mapping.technology.verified_libraries()
    if report.get("library_manifest") != lib_manifest:
        raise ValueError("Technology receipt uses a different pinned library set")
    configurations = [tuple(row["configuration"]) for row in report.get("configurations", [])]
    if len(set(configurations)) != len(configurations) or set(configurations) != set(mapping.host.MATRIX):
        raise ValueError("Require the complete host matrix exactly once")
    hashes = report.get("artifact_sha256")
    if type(hashes) is not dict or not hashes:
        raise ValueError("Missing mapped artifact identities")
    for name, digest in hashes.items():
        if sha(contained(path.parent, name)) != digest:
            raise ValueError("Mapped artifact changed: " + name)
    parent = report.get("positive_report", {})
    parent_path = Path(parent.get("path", "")).resolve()
    if not parent_path.is_file() or sha(parent_path) != parent.get("sha256") or \
            sha(path.parent / "positive-report.json") != parent.get("sha256"):
        raise ValueError("Technology parent receipt binding changed")
    mapping.verify_receipt(parent_path, tool_hashes)
    variants = {"reference": "reference.sv", "ownership": "source.sv", "baseline": "baseline.sv"} if ownership else \
               {"lean": "source.sv", "baseline": "baseline.sv"}
    for entry in report["configurations"]:
        label = "host-" + "-".join(map(str, entry["configuration"]))
        origin = parent_path.parent / label
        data = json.loads((origin / "interface.json").read_text())
        mapping.host.validate_descriptor(data, *entry["configuration"])
        frames = [json.loads(line) for line in (origin / "oracle-trace.jsonl").read_text().splitlines()]
        if set(entry.get("variants", {})) != set(variants):
            raise ValueError("Wrong matched variant inventory")
        for variant, results in entry["variants"].items():
            if set(results) != set(libraries):
                raise ValueError("Wrong matched corner inventory")
            for corner, result in results.items():
                directory = path.parent / f"{label}-{variant}-{corner}"
                for name in ("source.sv", "mapped.v", "mapped.json", "trace.txt", "map.ys", "abc.constr"):
                    if f"{directory.name}/{name}" not in hashes:
                        raise ValueError("Missing consumed mapped artifact: " + name)
                if sha(directory / "source.sv") != sha(origin / variants[variant]) or \
                        sha(directory / "source.sv") != result.get("rtl_sha256") or \
                        sha(directory / "mapped.v") != result.get("mapped_sha256"):
                    raise ValueError("Variant/corner RTL binding mismatch")
                mapping.host.memory.check_trace((directory / "trace.txt").read_text(),
                                               mapping.host.controller.expected(frames, False))
                if result.get("replayed_edges") != len(frames):
                    raise ValueError("Mapped replay edge count mismatch")
    return report, libraries, parent_path


def wire_model(path):
    text = path.read_text()
    names = re.findall(r"\blibrary\s*\(\s*([^\s)]+)\s*\)", text)
    if len(names) != 1 or 'time_unit : "1ns";' not in text or 'capacitive_load_unit (1,pf);' not in text or \
            'pulling_resistance_unit : "1kohm";' not in text:
        raise ValueError("Unexpected Liberty identity or time/capacitance/resistance units")
    blocks = re.findall(r'\bwire_load\s*\(\s*"Zero"\s*\)\s*\{([^}]+)\}', text)
    if len(blocks) != 1:
        raise ValueError("Missing unique named Zero wire-load model")
    result = {"library": names[0], "name": "Zero", "mode": "top", "configured_min_max": "both",
              "selection_evidence": "Successful explicit set_wire_load_model command; model coefficients from hashed Liberty. No independent native selected-model accessor.",
              "effective_selection_independently_queried": False,
              "time_unit": "ns", "capacitance_unit": "pF", "resistance_unit": "kOhm",
              "coefficient_length_unit": "Liberty model length unit; no physical geometry inferred",
              "literal_liberty_model": blocks[0].strip(), "liberty_sha256": sha(path)}
    for key in ("area", "capacitance", "resistance", "slope"):
        values = re.findall(r"\b" + key + r"\s*:\s*([0-9.eE+-]+)\s*;", blocks[0])
        if len(values) != 1 or not math.isfinite(float(values[0])) or float(values[0]) < 0:
            raise ValueError("Malformed wire-load coefficient")
        result[key] = float(values[0])
    result["fanout_length"] = [[int(a), float(b)] for a, b in
                               re.findall(r"fanout_length\s*\(\s*(\d+)\s*,\s*([0-9.eE+-]+)\s*\)", blocks[0])]
    if not result["fanout_length"] or any(not math.isfinite(b) or b < 0 for _, b in result["fanout_length"]):
        raise ValueError("Malformed wire-load table")
    result["zero_interconnect_rc"] = False
    return result


def inventory(netlist, netjson, top):
    graph = json.loads(netjson.read_text())["modules"][top]
    text = netlist.read_text()
    declarations = {}
    for direction, high, low, name in re.findall(
            r"^\s*(input|output)\s+(?:\[(\d+)\s*:\s*(\d+)\]\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*;", text, re.M):
        if name in declarations:
            raise ValueError("Repeated saved Verilog port declaration")
        declarations[name] = (direction, int(high) if high else None, int(low) if low else None)
    if set(declarations) != set(graph["ports"]):
        raise ValueError("Saved Verilog and mapped JSON port inventories differ")
    if graph.get("memories"):
        raise ValueError("STA profile requires mapped standard-cell storage")
    ports = {"input": [], "output": []}
    constant_outputs = {}
    for name, p in graph["ports"].items():
        if p["direction"] not in ports or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
            raise ValueError("Unsupported top port")
        if p.get("upto", 0) or p.get("offset", 0):
            raise ValueError("Noncanonical top bus indexing")
        direction, high, low = declarations[name]
        vector = high is not None
        if direction != p["direction"] or (vector and (low != 0 or high+1 != len(p["bits"]))) or \
                (not vector and len(p["bits"]) != 1):
            raise ValueError("Saved Verilog and mapped JSON port widths differ")
        for k, bit in enumerate(p["bits"]):
            signal = f"{name}[{k}]" if vector else name
            ports[p["direction"]].append(signal)
            if p["direction"] == "output" and type(bit) is str:
                if bit not in ("0", "1"):
                    raise ValueError("Unknown constant output")
                constant_outputs[signal] = int(bit)
    if "clk" not in ports["input"] or len(graph["ports"]["clk"]["bits"]) != 1:
        raise ValueError("Require a single-bit clk input")
    clock_bit = graph["ports"]["clk"]["bits"][0]
    cells = Counter(c["type"] for c in graph["cells"].values())
    ff_count = cells[FF]
    if ff_count == 0 or any(not name.startswith("sg13cmos5l_") for name in cells):
        raise ValueError("Missing mapped registers or unmapped cells")
    for c in graph["cells"].values():
        if c["type"] == FF and (c["connections"].get("CLK") != [clock_bit] or c["connections"].get("RESET_B") != ["1"]):
            raise ValueError("Require direct single clock and tied-inactive asynchronous reset")
    ff, constant_data = {}, {}
    for match in re.finditer(r"\b" + FF + r"\s+(\S+)\s*\((.*?)\);", text, re.S):
        name = match[1].removeprefix("\\")
        pins = dict(re.findall(r"\.(\w+)\s*\(([^)]+)\)", match[2]))
        pins = {k: v.strip() for k, v in pins.items()}
        if name in ff or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) or \
                set(pins) != {"CLK", "D", "Q", "RESET_B"} or pins["CLK"] != "clk" or pins["RESET_B"] != "1'h1":
            raise ValueError("Saved Verilog register/clock/reset inventory is not canonical")
        ff[name] = FF
        if pins["D"] in ("1'h0", "1'h1"):
            constant_data[name + "/D"] = int(pins["D"][-1])
    if len(ff) != ff_count:
        raise ValueError("Saved Verilog and mapped JSON register counts differ")
    endpoints = sorted((set(ports["output"]) - set(constant_outputs)) |
                       ({name + "/D" for name in ff} - set(constant_data)))
    return {"ports": {k: sorted(v) for k, v in ports.items()}, "registers": ff,
            "clock_pins": sorted(name + "/CLK" for name in ff),
            "data_pins": sorted(name + "/D" for name in ff),
            "async_pins": sorted(name + "/RESET_B" for name in ff),
            "constant_outputs": constant_outputs, "constant_data_pins": constant_data,
            "required_endpoints": endpoints, "mapped_cells": dict(cells)}


def tcl_list(values):
    if any(any(c in value for c in "{}\\\n\r\t") for value in values):
        raise ValueError("Unsafe literal Tcl name")
    return "[list " + " ".join("{" + value + "}" for value in values) + "]"


def constraints(inv, model):
    # Literal bus bits are resolved one at a time with escaped glob brackets.
    return f"""set_cmd_units -time ns -capacitance pF -resistance kOhm
create_clock -name clk -period 10 [exact_ports [list clk]]
set input_ports [exact_ports {tcl_list([p for p in inv['ports']['input'] if p != 'clk'])}]
set output_ports [exact_ports {tcl_list(inv['ports']['output'])}]
set_input_delay -clock clk -max 1.0 $input_ports
set_input_delay -clock clk -min 0.2 $input_ports
set_output_delay -clock clk -max 1.0 $output_ports
set_output_delay -clock clk -min -0.2 $output_ports
set_driving_cell -lib_cell sg13cmos5l_buf_2 -pin X -input_transition_rise 0.1 -input_transition_fall 0.1 $input_ports
set_load 0.010 $output_ports
set_clock_transition 0.1 [get_clocks clk]
set_clock_uncertainty -setup 0.1 [get_clocks clk]
set_clock_uncertainty -hold 0.05 [get_clocks clk]
set_wire_load_mode top
set_wire_load_model -name Zero -library {model['library']}
"""


def timing_script(top, inv, model):
    return """if {[catch {
set sta_report_default_digits 9
proc names {objects} {set result {}; foreach object $objects {lappend result [get_full_name $object]}; return [lsort $result]}
proc exact_ports {wanted} {
  set result {}
  foreach name $wanted {
    set pattern [string map {[ \\[ ] \\]} $name]
    set found [get_ports -quiet $pattern]
    if {[llength $found] != 1 || [names $found] ne [list $name]} {error "Missing/ambiguous port $name"}
    lappend result [lindex $found 0]
  }
  return $result
}
read_liberty cells.lib
read_verilog mapped.v
""" + f"link_design {top}\nsource constraints.sdc\n" + """
puts "STA_VERSION\t[sta::version]"
puts "STA_CLOCK\t[get_property [get_clocks clk] is_propagated]\t[llength [get_clocks *]]"
puts "STA_SECTION_BEGIN\tUNITS"
report_units
puts "STA_SECTION_END\tUNITS"
foreach direction {input output} {
  if {$direction eq "input"} {set ports [all_inputs]} else {set ports [all_outputs]}
  foreach name [names $ports] {puts "STA_PORT\t$direction\t$name"}
}
foreach cell [all_registers] {puts "STA_REGISTER\t[get_full_name $cell]\t[get_property $cell ref_name]"}
foreach cell [all_registers -clock [get_clocks clk]] {puts "STA_CLOCKED\t[get_full_name $cell]"}
foreach kind {clock data async} {
  if {$kind eq "clock"} {set pins [all_registers -clock_pins]}
  if {$kind eq "data"} {set pins [all_registers -data_pins]}
  if {$kind eq "async"} {set pins [all_registers -async_pins]}
  foreach name [names $pins] {puts "STA_PIN\t$kind\t$name"}
}
""" + f'puts "STA_WIRE_CONFIGURED\t{model["library"]}\tZero\ttop\tmin_max"\n' + """
puts "STA_SECTION_BEGIN\tCHECK_SETUP"
check_setup -verbose -no_input_delay -no_output_delay -multiple_clock -no_clock -unconstrained_endpoints -loops -generated_clocks
puts "STA_SECTION_END\tCHECK_SETUP"
foreach kind {max min} {
  puts "STA_SLACK\t$kind\t[format %.12g [worst_slack -$kind]]"
  foreach path [find_timing_paths -path_delay $kind -unique_paths_to_endpoint -group_path_count 1000000] {
    puts "STA_PATH\t$kind\t[get_full_name [get_property $path endpoint]]\t[get_full_name [get_property $path startpoint]]\t[get_property $path slack]"
  }
}
puts "STA_SECTION_BEGIN\tSETUP"
report_checks -path_delay max -group_path_count 5 -fields {slew cap fanout} -format full_clock_expanded
puts "STA_SECTION_END\tSETUP"
puts "STA_SECTION_BEGIN\tHOLD"
report_checks -path_delay min -group_path_count 5 -fields {slew cap fanout} -format full_clock_expanded
puts "STA_SECTION_END\tHOLD"
puts "STA_SECTION_BEGIN\tREG_SETUP"
report_checks -from [all_registers -clock_pins] -to [all_registers -data_pins] -path_delay max -group_path_count 2 -fields {slew cap fanout} -format full_clock_expanded
puts "STA_SECTION_END\tREG_SETUP"
puts "STA_SECTION_BEGIN\tREG_HOLD"
report_checks -from [all_registers -clock_pins] -to [all_registers -data_pins] -path_delay min -group_path_count 2 -fields {slew cap fanout} -format full_clock_expanded
puts "STA_SECTION_END\tREG_HOLD"
puts "STA_SECTION_BEGIN\tELECTRICAL"
report_check_types -max_slew -max_capacitance -max_fanout -min_pulse_width -min_period -violators
puts "STA_SECTION_END\tELECTRICAL"
} message]} {puts stderr "STA_FATAL $message"; exit 1}
puts "STA_COMPLETE"
exit 0
"""


def finite(value):
    if not re.fullmatch(r"[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?", value):
        raise ValueError("Missing or nonnumeric STA value")
    result = float(value)
    if not math.isfinite(result):
        raise ValueError("Nonfinite STA value")
    return result


def parse_timing(text, inv, model):
    if re.search(r"(?im)^(?:Error:|Warning:|STA_FATAL\b)", text):
        raise ValueError("STA warning/error: incomplete or ambiguous analysis")
    sections, current, records, completed = {}, None, [], False
    for line in text.splitlines():
        if line.startswith("STA_SECTION_BEGIN\t"):
            name = line.split("\t")[1]
            if completed or current is not None or name not in SECTIONS or name in sections:
                raise ValueError("Invalid/repeated STA section")
            current, sections[name] = name, []
        elif line.startswith("STA_SECTION_END\t"):
            if current is None or line != "STA_SECTION_END\t" + current:
                raise ValueError("Mismatched STA section boundary")
            current = None
        elif current is not None:
            sections[current].append(line)
        elif line == "STA_COMPLETE":
            if completed:
                raise ValueError("Repeated completion marker")
            completed = True
        elif line.strip():
            if completed or not line.startswith("STA_"):
                raise ValueError("Unexpected STA output")
            records.append(line.split("\t"))
    if not completed or current is not None or set(sections) != set(SECTIONS):
        raise ValueError("Incomplete STA sections/completion")
    if any(line.strip() for line in sections["CHECK_SETUP"]):
        raise ValueError("Incomplete timing constraints: " + "\n".join(sections["CHECK_SETUP"]))
    units = dict(line.strip().split(maxsplit=1) for line in sections["UNITS"] if line.strip())
    if units.get("time") != "1ns" or units.get("capacitance") != "1pF" or units.get("resistance") != "1kohm":
        raise ValueError("Unexpected native timing units")
    ports = {"input": [], "output": []}
    pins = {"clock": [], "data": [], "async": []}
    registers, clocked, paths, slacks, versions, clocks, wires = {}, [], {"max": {}, "min": {}}, {}, [], [], []
    for row in records:
        if row[0] == "STA_PORT" and len(row) == 3 and row[1] in ports:
            ports[row[1]].append(row[2])
        elif row[0] == "STA_PIN" and len(row) == 3 and row[1] in pins:
            pins[row[1]].append(row[2])
        elif row[0] == "STA_REGISTER" and len(row) == 3 and row[1] not in registers:
            registers[row[1]] = row[2]
        elif row[0] == "STA_CLOCKED" and len(row) == 2:
            clocked.append(row[1])
        elif row[0] == "STA_PATH" and len(row) == 5 and row[1] in paths and row[2] not in paths[row[1]]:
            paths[row[1]][row[2]] = {"startpoint": row[3], "slack_ns": finite(row[4])}
        elif row[0] == "STA_SLACK" and len(row) == 3 and row[1] in paths and row[1] not in slacks:
            slacks[row[1]] = finite(row[2])
        elif row[0] == "STA_VERSION" and len(row) == 2:
            versions.append(row[1])
        elif row[0] == "STA_CLOCK" and len(row) == 3:
            clocks.append(row[1:])
        elif row[0] == "STA_WIRE_CONFIGURED" and len(row) == 5:
            wires.append(row[1:])
        else:
            raise ValueError("Malformed/duplicate STA observation: " + repr(row))
    if ports != inv["ports"] or registers != inv["registers"] or sorted(clocked) != sorted(registers) or \
            pins["clock"] != inv["clock_pins"] or pins["async"] != inv["async_pins"] or \
            pins["data"] != sorted(inv["data_pins"] + inv["async_pins"]):
        raise ValueError("Native port/register/clock/pin inventory mismatch")
    if versions != ["2.7.0"] or clocks != [["0", "1"]] or \
            wires != [[model["library"], "Zero", "top", "min_max"]] or set(slacks) != {"max", "min"}:
        raise ValueError("Native engine/clock or configured wire-command evidence mismatch")
    for kind in paths:
        if sorted(paths[kind]) != inv["required_endpoints"] or not paths[kind]:
            raise ValueError("Missing/extra required timed endpoints: " + kind)
        if abs(min(p["slack_ns"] for p in paths[kind].values()) - slacks[kind]) > 2e-5:
            raise ValueError("Worst slack does not match complete endpoint ledger")
    for name, kind in (("SETUP", "max"), ("HOLD", "min"), ("REG_SETUP", "max"), ("REG_HOLD", "min")):
        body = "\n".join(sections[name])
        if "Startpoint:" not in body or "Endpoint:" not in body or f"Path Type: {kind}" not in body or "slack (" not in body:
            raise ValueError("Missing detailed timing paths: " + name)
        if name.startswith("REG_") and ("/CLK" not in body or "/Q" not in body or "/D" not in body or
                ("library setup time" if kind == "max" else "library hold time") not in body):
            raise ValueError("Sequential clock-to-Q/setup/hold arc evidence missing")
    categories = ("max fanout", "max slew", "max capacitance", "min pulse width", "min period")
    electrical = {name: [] for name in categories}
    category = None
    for raw in sections["ELECTRICAL"]:
        line = raw.strip()
        if line in electrical:
            category = line
        elif not line or set(line) == {"-"} or line.startswith(("Pin ", "Clock ")):
            continue
        elif category is not None and "(VIOLATED)" in line:
            fields = line.removesuffix("(VIOLATED)").split()
            if not line.endswith("(VIOLATED)") or len(fields) not in (3, 4):
                raise ValueError("Malformed electrical violation")
            for value in fields[1:]:
                finite(value)
            electrical[category].append({"type": category, "endpoint": fields[0],
                "limit": finite(fields[1]), "actual": finite(fields[2]),
                "reported_slack": finite(fields[3]) if len(fields) == 4 else None, "raw": line})
        else:
            raise ValueError("Unrecognized electrical section row: " + line)
    violations = {kind: {name: row for name, row in endpoints.items() if row["slack_ns"] < 0}
                  for kind, endpoints in paths.items()}
    met = slacks["max"] >= 0 and slacks["min"] >= 0 and not any(electrical.values())
    return {"analysis_completed": True, "constraints_met": met,
            "setup_hold_met": slacks["max"] >= 0 and slacks["min"] >= 0,
            "electrical_constraints_met": not any(electrical.values()), "setup_slack_ns": slacks["max"],
            "hold_slack_ns": slacks["min"], "endpoint_paths": paths, "violating_endpoints": violations,
            "electrical_violations": electrical, "required_endpoint_count": len(inv["required_endpoints"]),
            "complete_native_endpoint_coverage": True, "clock_to_q_setup_hold_arcs_reported": True}


def docker_run(run, out, report, image, argv, label, folder=None):
    name = "pinwheel-host-sta-" + uuid.uuid4().hex
    report["containers"][name] = "unconfirmed"
    command = ["docker", "run", "--rm", "--pull", "never", "--name", name, "--network", "none",
               "--read-only", "--cpus", "1", "--memory", "1g", "--memory-swap", "1g",
               "--tmpfs", "/tmp:rw,size=64m", "--env", "PYTHONDONTWRITEBYTECODE=1"]
    if folder is not None:
        command += ["--mount", f"type=bind,source={folder.resolve()},target=/work,readonly", "--workdir", "/work"]
    command += [image, *argv]
    try:
        return run(command, label, timeout=120)
    finally:
        query = subprocess.run(["docker", "inspect", "--type", "container", name], capture_output=True, text=True, timeout=15)
        record = {"argv": ["docker", "inspect", "--type", "container", name], "exit_code": query.returncode,
                  "stdout": query.stdout, "stderr": query.stderr}
        if query.returncode and "No such " in query.stderr and name in query.stderr:
            report["containers"][name] = "absent"
        elif query.returncode == 0:
            cleanup = subprocess.run(["docker", "rm", "--force", name], capture_output=True, text=True, timeout=20)
            record["cleanup"] = {"exit_code": cleanup.returncode, "stdout": cleanup.stdout, "stderr": cleanup.stderr}
            report["containers"][name] = "cleanup_required"
            (out / (label + "-container.json")).write_text(json.dumps(record, indent=2) + "\n")
            raise RuntimeError("STA container was not removed normally; retained cleanup evidence")
        else:
            raise RuntimeError("Cannot establish STA container termination: " + query.stderr)
        (out / (label + "-container.json")).write_text(json.dumps(record, indent=2) + "\n")


def engine_identity(run, out, report, image, label):
    code = ("import hashlib,json,pathlib,shutil,subprocess; "
            "p=pathlib.Path(shutil.which('sta')).resolve(); "
            "print(json.dumps({'executable':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),"
            "'version':subprocess.check_output([str(p),'-version'],text=True).strip()}))")
    result = json.loads(docker_run(run, out, report, image, ["python3", "-B", "-c", code], label))
    if result.get("version") != "2.7.0" or not re.fullmatch(r"[0-9a-f]{64}", result.get("sha256", "")) or \
            not result.get("executable", "").startswith("/nix/store/"):
        raise ValueError("Unexpected pinned STA executable identity")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--positive-report", type=Path, required=True)
    parser.add_argument("--ownership", action="store_true", help="Use the trusted three-variant ownership mapper")
    parser.add_argument("--config", action="append", help="Optional matched subset ADDRESS,INPUT,OUTPUT")
    args = parser.parse_args()
    mapping = mapper(args.ownership)
    configs = [tuple(map(int, item.split(","))) for item in args.config] if args.config else mapping.host.MATRIX
    if len(set(configs)) != len(configs) or not configs or not set(configs) <= set(mapping.host.MATRIX):
        parser.error("Configurations must be a nonempty distinct subset of the trusted matrix")
    out = fresh_directory(ROOT / "build/memory-transfer-host-sta", args.tag)
    report = {"schema": 1, "status": "running", "analysis_completed": False, "constraints_met": None,
              "commands": [], "containers": {}, "configurations": [], "policy": POLICY,
              "variant_profile": "ownership" if args.ownership else "original",
              "corner_coverage": {"available": ["typical", "slow"], "fast_hold_corner": False},
              "boundary": "Pre-layout standalone STA of exact checked mapped netlists with ideal clock and explicit "
                  "nonzero Liberty Zero wire-load model. Includes sequential clock-to-Q/setup/hold arcs. "
                  "No extracted wires, clock tree/skew, fast hold corner, complete PVT, frequency/board contract, "
                  "post-mapping kernel proof or physical qualification. Analysis completion does not imply constraints met."}
    run, started = mapping.rr.Commands(out, report["commands"]), time.monotonic()
    try:
        report["source_sha256"] = sources(mapping)
        manifest, _, tool_paths = mapping.rr.selected_tools()
        report["tool_manifest"], report["tool_sha256"] = manifest, mapping.rr.tool_hashes(tool_paths)
        lock = json.loads((ROOT / "tools/physical-toolchain.json").read_text())
        runtime = inspect_runtime(lock)
        report["runtime"] = runtime
        docker = Path(shutil.which("docker")).resolve()
        report["docker_client"] = {"path": str(docker), "sha256": sha(docker)}
        receipt = args.positive_report.resolve()
        positive, libraries, parent = verify_receipt(receipt, mapping, report["tool_sha256"], args.ownership)
        report["positive_report"] = {"path": str(receipt), "sha256": sha(receipt)}
        shutil.copyfile(receipt, out / "positive-report.json")
        report["library_manifest"] = positive["library_manifest"]
        report["wire_models"] = {corner: wire_model(path) for corner, path in libraries.items()}
        report["sta_engine"] = engine_identity(run, out, report, runtime["image_id"], "engine-before")
        run(["python3", "-B", "test/test_memory_transfer_host_sta.py"], "parser-tests")
        for entry in positive["configurations"]:
            if tuple(entry["configuration"]) not in configs:
                continue
            label = "host-" + "-".join(map(str, entry["configuration"]))
            data = json.loads((parent.parent / label / "interface.json").read_text())
            result = {"configuration": entry["configuration"], "variants": {}}
            for variant, corners in entry["variants"].items():
                result["variants"][variant] = {}
                for corner in corners:
                    name = f"{label}-{variant}-{corner}"
                    directory, origin = out / name, receipt.parent / name
                    directory.mkdir()
                    for filename in ("mapped.v", "mapped.json"):
                        shutil.copyfile(origin / filename, directory / filename)
                    shutil.copyfile(libraries[corner], directory / "cells.lib")
                    inv = inventory(directory / "mapped.v", directory / "mapped.json", data["module"])
                    model = report["wire_models"][corner]
                    (directory / "inventory.json").write_text(json.dumps(inv, indent=2) + "\n")
                    (directory / "policy.json").write_text(json.dumps(POLICY, indent=2) + "\n")
                    (directory / "constraints.sdc").write_text(constraints(inv, model))
                    (directory / "timing.tcl").write_text(timing_script(data["module"], inv, model))
                    frozen = {p.name: sha(p) for p in directory.iterdir() if p.is_file()}
                    log = docker_run(run, out, report, runtime["image_id"],
                                     ["sta", "-no_init", "-no_splash", "-exit", "timing.tcl"], name, directory)
                    (directory / "sta.log").write_text(log)
                    measured = parse_timing(log, inv, model)
                    if any(sha(directory / name) != digest for name, digest in frozen.items()):
                        raise RuntimeError("Staged STA input changed")
                    measured.update(input_sha256=frozen, mapped_sha256=sha(directory / "mapped.v"),
                                    wire_model=model, output_min_convention="external hold+0.2ns -> SDC min−0.2ns")
                    (directory / "result.json").write_text(json.dumps(measured, indent=2) + "\n")
                    result["variants"][variant][corner] = measured
                    print(f"STA {name}: setup={measured['setup_slack_ns']:.6f}ns hold={measured['hold_slack_ns']:.6f}ns "
                          f"constraints_met={measured['constraints_met']}", flush=True)
            report["configurations"].append(result)
        if sources(mapping) != report["source_sha256"] or mapping.rr.tool_hashes(tool_paths) != report["tool_sha256"] or \
                inspect_runtime(lock) != runtime or sha(docker) != report["docker_client"]["sha256"]:
            raise RuntimeError("STA sources/tools/runtime changed")
        if engine_identity(run, out, report, runtime["image_id"], "engine-after") != report["sta_engine"]:
            raise RuntimeError("STA executable changed")
        verify_receipt(receipt, mapping, report["tool_sha256"], args.ownership)
        if sha(receipt) != report["positive_report"]["sha256"]:
            raise RuntimeError("Positive receipt changed")
        for entry in report["configurations"]:
            label = "host-" + "-".join(map(str, entry["configuration"]))
            for variant, corners in entry["variants"].items():
                for corner, result in corners.items():
                    directory = out / f"{label}-{variant}-{corner}"
                    if any(sha(directory / filename) != digest for filename, digest in result["input_sha256"].items()):
                        raise RuntimeError("A previously analyzed staged input changed before closeout")
        report["constraints_met"] = all(value["constraints_met"] for entry in report["configurations"]
                                         for corners in entry["variants"].values() for value in corners.values())
        report.update(status="completed", analysis_completed=True)
    except BaseException as error:
        report["status"], report["error"] = "failed", f"{type(error).__name__}: {error}"
        raise
    finally:
        report["seconds"] = round(time.monotonic() - started, 3)
        report["artifact_sha256"] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob("*")) if p.is_file()}
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
