"""Audit endpoint and electrical-check coverage on the retained hold/cap matrix."""

import argparse
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

import streaming_8x4_draft_rc_timing as draft
import streaming_8x4_e982_eco_electrical as electrical
from streaming_8x4_e982_eco_timing import verified_layout
from streaming_8x4_e982_native import IMAGE, TOP, read, require, run_native, sha, write
from streaming_8x4_hold_cap_physical import EVIDENCE, TARGET, TRIAL, setup
from streaming_tt_certificate import eval_boolean
from streaming_tt_simulation import libraries


SCHEMA = "pinwheel.streaming-8x4-hold-cap-timing-coverage.v1"
NL, SDC, RUN, OUT = electrical.NL, electrical.SDC, electrical.RUN, electrical.OUT
PATH_LIMIT = 20000
CASE_TIMEOUT = 120
TCL_EXTRA = r"""
    puts "PINWHEEL_COVERAGE_SETUP_BEGIN"
    check_setup -verbose
    puts "PINWHEEL_COVERAGE_SETUP_END"
    foreach pin [sta::endpoints] {
        puts "PINWHEEL_COVERAGE_ENDPOINT\t[get_full_name $pin]\t[sta::pin_sim_logic_value $pin]"
    }
    foreach pin [get_pins -of_objects [all_registers -cells]] {
        set name [get_full_name $pin]
        if {[regexp {/(D|CLK|RESET_B)$} $name -> kind]} {
            puts "PINWHEEL_COVERAGE_REGISTER\t$kind\t$name\t[sta::pin_sim_logic_value $pin]"
        }
    }
    foreach direction {input output} ports [list [all_inputs] [all_outputs]] {
        foreach port $ports {puts "PINWHEEL_COVERAGE_PORT\t$direction\t[get_full_name $port]"}
    }
    foreach mode {min max} {
        set paths [find_timing_paths -corner $corner -path_delay $mode -unique_paths_to_endpoint \
            -endpoint_path_count 1 -group_path_count 20000]
        foreach path $paths {
            if {[$path is_unconstrained]} {error "Unexpected unconstrained path in constrained search"}
            set endpoint [get_full_name [get_property $path endpoint]]
            puts "PINWHEEL_COVERAGE_PATH\t$mode\t$endpoint\t[get_property $path slack]"
        }
        puts "PINWHEEL_COVERAGE_PATH_COUNT $mode [llength $paths]"
        foreach port [all_inputs] {
            set name [get_full_name $port]
            if {$name eq {clk}} {continue}
            set input_paths [find_timing_paths -corner $corner -path_delay $mode -from $port \
                -endpoint_path_count 1 -group_path_count 1]
            if {[llength $input_paths] == 0} {
                puts "PINWHEEL_COVERAGE_INPUT\t$mode\t$name\tNONE\tNONE"
                continue
            }
            set input_path [lindex $input_paths 0]
            set start [get_full_name [get_property $input_path startpoint]]
            if {[$input_path is_unconstrained] || $start ne $name} {error "Wrong input path startpoint"}
            set endpoint [get_full_name [get_property $input_path endpoint]]
            puts "PINWHEEL_COVERAGE_INPUT\t$mode\t$name\t$endpoint\t[get_property $input_path slack]"
        }
    }
    puts "PINWHEEL_COVERAGE_PULSE_BEGIN"
    report_pulse_width_checks -corner $corner -digits 6 -no_line_splits
    puts "PINWHEEL_COVERAGE_PULSE_END"
"""
COMPLETE = '    puts "PINWHEEL_ELECTRICAL_COMPLETE $corner"\n'
require(electrical.TCL.count(COMPLETE) == 1, "Electrical probe completion marker changed")
TCL = electrical.TCL.replace(COMPLETE, TCL_EXTRA + COMPLETE)


def expectations(inventory, corner_libraries):
    library, _ = libraries(corner_libraries, {"sg13cmos5l_tiehi", "sg13cmos5l_tielo"})
    ties = {}
    for name, cell in library.cells.items():
        require(not cell.sequential and cell.directions == {cell.output: "output"}, "Unexpected tie-cell model")
        ties[name, cell.output] = int(eval_boolean(cell.function, {}))
    require(set(ties.values()) == {0, 1}, "Pinned Liberty tie functions differ")

    drivers, loaded_nets = {}, set()
    registers = {key: [] for key in ("D", "CLK", "RESET_B")}
    instances = inventory["instances"]
    for name, instance in instances.items():
        for pin, terminal in instance["terminals"].items():
            if terminal["direction"] == "OUTPUT" and terminal["net"] is not None:
                drivers.setdefault(terminal["net"], []).append((instance["master"], pin))
            if terminal["direction"] == "INPUT" and terminal["net"] is not None:
                loaded_nets.add(terminal["net"])
        if instance["master"] == "sg13cmos5l_dfrbpq_1":
            for pin in registers:
                registers[pin].append(f"{name}/{pin}")
    require(all(len(names) == 6039 for names in registers.values()), "Wrong physical FF inventory")

    def tied_value(net):
        sources = drivers.get(net, [])
        return ties.get(sources[0]) if len(sources) == 1 else None

    reset_nets = {instances[name.removesuffix("/RESET_B")]["terminals"]["RESET_B"]["net"]
                  for name in registers["RESET_B"]}
    require(len(reset_nets) == 6039 and all(tied_value(net) == 1 for net in reset_nets),
            "Expected a distinct constant-high driver on every physical reset")
    ports = {direction: sorted(name for name, row in inventory["public_bterms"].items()
                              if row["direction"] == direction) for direction in ("input", "output")}
    constant_outputs = {name: value for name in ports["output"]
                        if (value := tied_value(inventory["public_bterms"][name]["net"])) is not None}
    sinkless_inputs = [name for name in ports["input"] if inventory["public_bterms"][name]["net"] not in loaded_nets]
    require(len(ports["input"]) == 19 and len(ports["output"]) == 24 and len(constant_outputs) == 12
            and set(constant_outputs.values()) == {0} and sinkless_inputs == [f"uio_in[{bit}]" for bit in range(8)],
            "Wrong public port, tied-output or sinkless-input inventory")
    return dict(registers={key: sorted(names) for key, names in registers.items()}, ports=ports,
                static_reset_nets=len(reset_nets), constant_outputs=constant_outputs, sinkless_inputs=sinkless_inputs)


def prepare(context):
    attempt = TRIAL / "timing"
    timing_path = attempt / "timing-readback.json"
    digest = EVIDENCE["timing/timing-readback.json"]
    require(sha(timing_path) == digest, "Retained independent timing readback changed")
    timing = read(timing_path)
    require(timing["target_name"] == "hold-cap-trial" and timing["status"] == "diagnostic"
            and timing["target_odb_sha256"] == TARGET["odb_sha256"]
            and timing["target_gds_sha256"] == TARGET["gds_sha256"]
            and timing["parasitics_preflight_passed"] is True and timing["qualified_timing"] is False,
            "Wrong retained hold/cap timing matrix")
    pins = {str(timing_path): digest}

    def reopen(path):
        item = draft.bound(path)
        require(timing["verified_file_sha256"].get(item["path"]) == item["sha256"],
                f"Reviewed timing input changed: {path}")
        pins[item["path"]] = item["sha256"]
        return item

    _, layout = verified_layout(context)
    for item in layout.values():
        require(reopen(item["path"]) == item, "Retained layout role changed")
    run = attempt / "run"
    request_item = reopen(attempt / "inputs/request.json")
    request = read(request_item["path"])
    native = read(reopen(attempt / "native-readback.json")["path"])
    execution_item = reopen(run / "execution.json")
    execution = read(execution_item["path"])
    require(native["status"] == "completed" and native["target_name"] == "hold-cap-trial"
            and native["target_odb_sha256"] == TARGET["odb_sha256"] and native["gds_sha256"] == TARGET["gds_sha256"]
            and native["request"] == request_item == timing["request"] and native["execution"] == execution_item
            and native["passes"] == reopen(run / "native-passes.json")
            and execution["status"] == "completed" and execution["exit_code"] == 0
            and execution["container_termination"]["status"] == "absent" and execution["argv"].count(IMAGE) == 1,
            "Retained native matrix custody differs")
    require(request["layout"] == timing["target"] == layout and request["policy"] == draft.policy()
            and request["model_rules_sha256"] == draft.RULE_SHA, "Retained matrix inputs differ")
    original = read(reopen(request["original_resolved"]["path"])["path"])
    common = {NL: layout["netlist"]["sha256"], SDC: layout["sdc"]["sha256"]}
    require(all(request["input_sha256"][name] == digest for name, digest in common.items()),
            "Retained netlist or SDC differs")
    rows, corner_libraries = [], {}
    require(set(timing["model_matrix"]) == set(draft.MODELS), "Wrong retained extraction models")
    for model in draft.MODELS:
        evidence = timing["model_matrix"][model]
        spef = f"{RUN}{model}/flow/01-openroad-rcx/nom/{TOP}.nom.spef"
        item = reopen(run / spef.removeprefix(RUN))
        require(evidence["spef"] == item and set(evidence["cases"]) == set(draft.CORNERS),
                "Retained SPEF or PVT matrix differs")
        journal = reopen(run / model / "native-journal.jsonl")
        calls = [row for row in draft.calls(journal["path"]) if Path(row["argv"][0]).name == "sta"]
        for corner in draft.CORNERS:
            call, = [row for row in calls if row["env"]["_CURRENT_CORNER_NAME"] == corner]
            env = call["env"]
            scripts = env["SCRIPTS_DIR"]
            libs = env["_CURRENT_CORNER_LIBS"].split()
            require(re.fullmatch(r"/nix/store/[^/]+/.+/librelane/scripts", scripts)
                    and call["argv"][1:] == ["-no_splash", "-exit", f"{scripts}/openroad/sta/corner.tcl"]
                    and (env["CURRENT_NL"], env["_SDC_IN"], env["_CURRENT_SPEF_BY_CORNER"]) == (NL, SDC, spef)
                    and env["DESIGN_NAME"] == TOP and env["OPENLANE_SDC_IDEAL_CLOCKS"] == "0"
                    and libs == original["CELL_LIBS"][corner] and len(libs) == 2
                    and not any(env.get(key) for key in ("EXTRA_LIBS", "EXTRA_VERILOG_MODELS",
                        "_CURRENT_CORNER_EXTRA_SPEFS_BACKCOMPAT", "_CURRENT_CORNER_SPEFS", "_CURRENT_CORNER_NETLISTS")),
                    f"Canonical STA inputs differ for {model}/{corner}")
            files = {**common, spef: item["sha256"]}
            for lib in libs:
                require(lib.startswith("/work/pdk/") and ".." not in Path(lib).parts, "Unexpected Liberty mount")
                binding = reopen(context["pdk"] / lib.removeprefix("/work/pdk/"))
                require(request["input_sha256"][lib] == binding["sha256"], "Canonical Liberty hash differs")
                files[lib] = binding["sha256"]
                if "/sg13cmos5l_stdcell/" in lib:
                    require(corner_libraries.setdefault(corner, binding) == binding, "PVT Liberty changed across models")
            for name in ("common/io.tcl", "common/set_global_connections.tcl", "sta/corner.tcl"):
                files[f"{scripts}/openroad/{name}"] = request["native_package_sha256"][f"scripts/openroad/{name}"]
            case = evidence["cases"][corner]
            rows.append(dict(model=model, corner=corner, sta_sha256=call["executable_sha256"], input_sha256=files,
                             env={key: env[key] for key in electrical.ENV_KEYS},
                             canonical_ws_ns={"min": case["hold_ws_ns"], "max": case["setup_ws_ns"]}))
    require(len(rows) == 9 and len({row["sta_sha256"] for row in rows}) == 1, "Canonical STA identity differs")
    return rows, layout, pins, expectations(read(layout["inventory"]["path"]), corner_libraries)


def native():
    request = read(OUT / "request.json")
    script = OUT / "probe.tcl"
    require(script.read_text() == TCL and request["schema"] == SCHEMA, "Native timing coverage request differs")
    executable = Path(shutil.which("sta") or "/missing-sta").resolve(strict=True)
    digest = sha(executable)
    base = {key: os.environ[key] for key in ("PATH", "HOME") if key in os.environ}
    base.update(_TCL_ENV_IN="/dev/null", LC_ALL="C")
    for row in request["cases"]:
        require(digest == row["sta_sha256"], "Native STA executable differs from retained run")
        for name, expected in row["input_sha256"].items():
            require(sha(name) == expected, f"Native STA input changed: {name}")
        log = OUT / f"{row['model']}-{row['corner']}.log"
        with log.open("x") as stream:
            subprocess.run([executable, "-no_splash", "-exit", script], check=True, timeout=CASE_TIMEOUT,
                           stdin=subprocess.DEVNULL, stdout=stream, stderr=subprocess.STDOUT,
                           env={**base, **row["env"]})
    write(OUT / "tool.json", dict(executable=str(executable), sha256=digest, completed_cases=len(request["cases"])))


def parse_coverage(log, row, expected):
    checks = electrical.parse_log(log, row)
    setup_report = electrical.one(log, r"^PINWHEEL_COVERAGE_SETUP_BEGIN\n([\s\S]*?)^PINWHEEL_COVERAGE_SETUP_END$", "setup diagnostics")
    registers = {}
    for kind in ("D", "CLK", "RESET_B"):
        pairs = re.findall(rf"^PINWHEEL_COVERAGE_REGISTER\t{kind}\t([^\t\n]+)\t(\S+)$", log, re.M)
        require(len(pairs) == len(dict(pairs)) and sorted(dict(pairs)) == expected["registers"][kind],
                f"Native {kind} pin inventory differs")
        registers[kind] = dict(pairs)
    require(set(registers["RESET_B"].values()) == {"1"}, "Native async reset values are not all constant high")
    for direction in ("input", "output"):
        names = re.findall(rf"^PINWHEEL_COVERAGE_PORT\t{direction}\t([^\t\n]+)$", log, re.M)
        require(sorted(names) == expected["ports"][direction], f"Native {direction} port inventory differs")
    endpoint_rows = re.findall(r"^PINWHEEL_COVERAGE_ENDPOINT\t([^\t\n]+)\t(\S+)$", log, re.M)
    endpoints = dict(endpoint_rows)
    require(endpoints and len(endpoint_rows) == len(endpoints), "Missing or duplicate native search endpoint inventory")
    expected_data = set(registers["D"]) | set(expected["ports"]["output"])
    search_reset = set(endpoints) & registers["RESET_B"].keys()
    require(all(endpoints[name] == "1" for name in search_reset), "Static search reset value differs")
    constants = {**{name: int(value) for name, value in registers["D"].items() if value in ("0", "1")},
                 **expected["constant_outputs"]}
    require(all(name not in endpoints or endpoints[name] == str(value) for name, value in constants.items()),
            "Search endpoint constant differs from observed graph or tied-output evidence")
    timing_paths = {}
    for mode in ("min", "max"):
        paths = re.findall(rf"^PINWHEEL_COVERAGE_PATH\t{mode}\t([^\t\n]+)\t({electrical.NUMBER})$", log, re.M)
        count = int(electrical.one(log, rf"^PINWHEEL_COVERAGE_PATH_COUNT {mode} (\d+)$", mode + " path count"))
        require(len(paths) == count and 0 < count < PATH_LIMIT, "Incomplete or truncated constrained path search")
        covered = {name for name, value in paths if math.isfinite(float(value))}
        require(covered, "No finite constrained paths")
        input_rows = re.findall(rf"^PINWHEEL_COVERAGE_INPUT\t{mode}\t([^\t\n]+)\t([^\t\n]+)\t({electrical.NUMBER}|NONE)$", log, re.M)
        require(len(input_rows) == 18 and sorted(name for name, _, _ in input_rows) ==
                sorted(set(expected["ports"]["input"]) - {"clk"}), "Missing or repeated input path query")
        input_paths = {}
        for name, endpoint, slack in input_rows:
            if slack == "NONE":
                require(endpoint == "NONE", "Malformed absent input path")
                input_paths[name] = None
            else:
                value = float(slack)
                require(endpoint in expected_data and math.isfinite(value), "Invalid constrained input path")
                input_paths[name] = dict(endpoint=endpoint, slack_ns=value)
        timing_paths[mode] = dict(paths=count, data_and_output_endpoints=len(covered & expected_data),
                                  static_endpoints_without_path=sorted(set(constants) - covered),
                                  unexplained_endpoints_without_path=sorted(expected_data - covered - constants.keys()),
                                  other_constrained_endpoints=sorted(covered - expected_data), input_paths=input_paths,
                                  consumed_inputs_without_path=sorted(name for name, path in input_paths.items()
                                                                      if path is None and name not in expected["sinkless_inputs"]),
                                  sinkless_inputs_with_path=sorted(name for name in expected["sinkless_inputs"]
                                                                  if input_paths[name] is not None))
    pulse = electrical.one(log, r"^PINWHEEL_COVERAGE_PULSE_BEGIN\n([\s\S]*?)^PINWHEEL_COVERAGE_PULSE_END$", "full pulse width report")
    pulse_pins, pulse_slacks = [], []
    number = electrical.NUMBER
    pulse_rows = re.findall(rf"^\s*(\S+)\s+\((high|low)\)\s+({number})\s+({number})\s+({number})\s+\((MET|VIOLATED)\)\s*$", pulse, re.M)
    require(len(pulse_rows) == len(re.findall(r"\((?:MET|VIOLATED)\)", pulse)), "Unparsed full pulse width check")
    for pin, side, required, actual, slack, label in pulse_rows:
        value = float(slack)
        require(math.isfinite(value) and abs(float(actual) - float(required) - value) <= 5e-6
                and (value == 0 or (value < 0) == (label == "VIOLATED")), "Invalid pulse width slack")
        pulse_pins.append((pin, side))
        pulse_slacks.append(value)
    require(pulse_pins and len(pulse_pins) == len(set(pulse_pins))
            and math.isclose(min(pulse_slacks), checks["min_pulse_width"]["worst_slack_ns"], abs_tol=1e-6, rel_tol=0),
            "Full pulse width report disagrees with native worst check")
    ff_checks = {(name, side) for name in registers["CLK"] for side in ("high", "low")}
    return dict(checks=checks, setup_diagnostics=setup_report.strip(), native_search_endpoints=len(endpoints),
                native_search_data_and_outputs=len(set(endpoints) & expected_data), native_search_static_resets=len(search_reset),
                native_search_other={name: endpoints[name] for name in sorted(set(endpoints) - expected_data - search_reset)},
                data_or_output_missing_from_native_search=sorted(expected_data - endpoints.keys()),
                data_and_output_endpoints=len(expected_data), static_data_and_output_endpoints=constants,
                static_reset_pins=len(registers["RESET_B"]), sinkless_inputs=expected["sinkless_inputs"],
                constrained_path_coverage=timing_paths,
                pulse_width=dict(total_checks=len(pulse_pins), worst_slack_ns=min(pulse_slacks),
                                 violations=sum(value < 0 for value in pulse_slacks),
                                 clock_pin_edges_checked=len(ff_checks & set(pulse_pins)),
                                 other_checked_pin_edges=[list(item) for item in sorted(set(pulse_pins) - ff_checks)],
                                 missing_clock_pin_edges=[list(item) for item in sorted(ff_checks - set(pulse_pins))]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--deadline", type=int, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.parent == TRIAL and not out.exists(), "Use a fresh sibling of the retained timing output")
    context = setup(args.history.resolve(strict=True))
    rows, layout, pins, expected = prepare(context)
    out.mkdir(exist_ok=False)
    request = out / "request.json"
    script = out / "probe.tcl"
    source = Path(__file__).resolve()
    write(request, dict(schema=SCHEMA, cases=rows, layout=layout, endpoint_expectations=expected))
    script.write_text(TCL)
    for path in (request, script, source, Path(electrical.__file__).resolve()):
        pins[str(path)] = sha(path)
    run_native(context, out, "python3", ["-B", f"/work/scripts/{source.name}", "native"],
               [(source.parent, "/work/scripts", False), (TRIAL / "timing/run", RUN.rstrip("/"), False),
                (Path(layout["netlist"]["path"]), NL, False), (Path(layout["sdc"]["path"]), SDC, False)],
               1200, args.deadline, memory="3g")
    require(all(sha(path) == digest for path, digest in pins.items()), "Retained timing input changed")
    tool = read(out / "tool.json")
    require(tool["sha256"] == rows[0]["sta_sha256"] and tool["completed_cases"] == 9, "Native timing matrix incomplete")
    for row in rows:
        log = out / f"{row['model']}-{row['corner']}.log"
        row.update(log=draft.bound(log), coverage=parse_coverage(log.read_text(), row, expected))
    write(out / "readback.json", dict(schema=SCHEMA, status="diagnostic", target_odb_sha256=TARGET["odb_sha256"],
          target_gds_sha256=TARGET["gds_sha256"], image=IMAGE, tool=tool, execution=draft.bound(out / "execution.json"),
          input_artifact_sha256=pins, cases=rows, model_qualified=False, qualified_timing=False, tapeout_ready=False,
          scope="Retained draft timing inputs, constrained-path coverage, native setup diagnostics and electrical checks."))
    print(out / "readback.json")


if __name__ == "__main__":
    import sys

    if sys.argv[1:] == ["native"]:
        native()
    else:
        main()
