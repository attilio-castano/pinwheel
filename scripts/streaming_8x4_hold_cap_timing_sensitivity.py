"""Vary the assumed drives and edge budgets of two frozen 8x4 inputs."""

import argparse
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

import streaming_8x4_draft_rc_timing as draft
import streaming_8x4_e982_eco_electrical as electrical
import streaming_8x4_hold_cap_timing_coverage as coverage
from streaming_8x4_e982_native import IMAGE, read, require, run_native, sha, write
from streaming_8x4_hold_cap_physical import TARGET, TRIAL, setup
from streaming_8x4_hold_cap_timing_intake import COVERAGE, COVERAGE_SHA


SCHEMA = "pinwheel.streaming-8x4-hold-cap-timing-sensitivity.v1"
OUT = Path("/work/export")
PORTS = ("ui_in[3]", "ui_in[5]")
CASES = {(model, draft.CORNERS[0]) for model in draft.MODELS} | {("MAX", draft.CORNERS[1])}
SCENARIOS = {
    # Each row gives the minimum input delay, hold uncertainty and drive.
    "baseline": ("0.200", "0.200", "buf_2"),
    "early_160": ("0.160", "0.200", "buf_2"),
    "joint_180_220": ("0.180", "0.220", "buf_2"),
    "uncertainty_240": ("0.200", "0.240", "buf_2"),
    "weaker_drive": ("0.200", "0.200", "buf_1"),
    "stronger_drive": ("0.200", "0.200", "buf_4"),
    "restored": ("0.200", "0.200", "buf_2"),
}
TARGETS = ("global", *PORTS)
TOLERANCE_NS = 3e-6

TCL = electrical.TCL.split('    puts "PINWHEEL_ELECTRICAL_CORNER $corner"', 1)[0] + r"""
    set selected_ports {}
    foreach port [all_inputs] {
        if {[get_full_name $port] in {{ui_in[3]} {ui_in[5]}}} { lappend selected_ports $port }
    }
    if {[llength $selected_ports] != 2} { error "Wrong public input ports" }
    set scenarios %s
    foreach {name minimum uncertainty driver} $scenarios {
        if {$name ne "baseline"} {
            set_input_delay -clock clk -min $minimum $selected_ports
            set_clock_uncertainty -hold $uncertainty $clock
            set_driving_cell -lib_cell sg13cmos5l_$driver -pin X $selected_ports
        }
        foreach mode {min max} {
            puts "PINWHEEL_SENSITIVITY\t$name\t$mode\tglobal\tGLOBAL\t[worst_slack -corner $corner -$mode]"
            foreach port $selected_ports {
                set name_port [get_full_name $port]
                set paths [find_timing_paths -corner $corner -path_delay $mode -from $port \
                    -endpoint_path_count 1 -group_path_count 1]
                if {[llength $paths] != 1} { error "Expected one constrained path for $name_port/$mode" }
                set path [lindex $paths 0]
                set start [get_full_name [get_property $path startpoint]]
                set endpoint [get_full_name [get_property $path endpoint]]
                if {[$path is_unconstrained] || $start ne $name_port} { error "Unexpected path source or coverage" }
                puts "PINWHEEL_SENSITIVITY\t$name\t$mode\t$name_port\t$endpoint\t[get_property $path slack]"
            }
        }
    }
    puts "PINWHEEL_SENSITIVITY_COMPLETE $corner"
} message]} {
    puts stderr "PINWHEEL_SENSITIVITY_ERROR $message"
    exit 1
}
""" % ("{" + " ".join(" ".join((name, *settings)) for name, settings in SCENARIOS.items()) + "}")


def native():
    request = read(OUT / "request.json")
    script = OUT / "probe.tcl"
    require(request["schema"] == SCHEMA
            and {(row["model"], row["corner"]) for row in request["cases"]} == CASES
            and len(request["cases"]) == len(CASES) and script.read_text() == TCL,
            "Wrong native timing sensitivity request")
    executable = Path(shutil.which("sta") or "/missing-sta").resolve(strict=True)
    digest = sha(executable)
    env = {key: os.environ[key] for key in ("PATH", "HOME") if key in os.environ}
    env.update(_TCL_ENV_IN="/dev/null", LC_ALL="C")
    for case in request["cases"]:
        require(digest == case["sta_sha256"], "Native OpenSTA identity differs")
        for name, expected in case["input_sha256"].items():
            require(sha(name) == expected, f"Native STA input changed: {name}")
        log = OUT / f"{case['model']}-{case['corner']}.log"
        with log.open("x") as stream:
            subprocess.run([executable, "-no_splash", "-exit", script], check=True, timeout=35,
                           stdin=subprocess.DEVNULL, stdout=stream, stderr=subprocess.STDOUT,
                           env={**env, **case["env"]})
    write(OUT / "tool.json", dict(sha256=digest, completed_cases=len(request["cases"])))


def parse(log, row, margins):
    require(not re.search(r"^(?:Error[: ]|\[ERROR\]|PINWHEEL_SENSITIVITY_ERROR)", log, re.M)
            and electrical.one(log, r"^PINWHEEL_SENSITIVITY_COMPLETE (\S+)$", "completion") == row["corner"],
            "OpenSTA reported an error or wrong corner")
    fields = re.findall(r"^PINWHEEL_SENSITIVITY\t(\w+)\t(min|max)\t([^\t\n]+)\t([^\t\n]+)"
                        rf"\t({electrical.NUMBER})$", log, re.M)
    values = {(case, mode, port): dict(endpoint=endpoint, slack_ns=float(value))
              for case, mode, port, endpoint, value in fields}
    expected = {(case, mode, port) for case in SCENARIOS for mode in ("min", "max") for port in TARGETS}
    require(values.keys() == expected and len(fields) == len(values)
            and all(math.isfinite(row["slack_ns"]) for row in values.values()), "Incomplete slack matrix")

    def close(actual, predicted):
        return math.isclose(actual, predicted, rel_tol=0, abs_tol=TOLERANCE_NS)

    # Each port keeps its original driver and max-side delay under these three
    # experiments. Both early data and higher clock uncertainty reduce hold.
    for mode in ("min", "max"):
        baseline = row["canonical_ws_ns"][mode]
        require(close(values["baseline", mode, "global"]["slack_ns"], baseline),
                "Baseline global slack differs from canonical draft STA")
        for port in TARGETS:
            base = values["baseline", mode, port]
            restored = values["restored", mode, port]
            require(restored["endpoint"] == base["endpoint"] and close(restored["slack_ns"], base["slack_ns"]),
                    "Restoring constraints changed slack or the endpoint")
            if port != "global":
                reference = margins["constrained_path_coverage"][mode]["input_paths"][port]
                require(base["endpoint"] == reference["endpoint"] and close(base["slack_ns"], reference["slack_ns"]),
                        f"Baseline input slack differs from retained replay for {port}")
            for name in ("early_160", "joint_180_220", "uncertainty_240"):
                measured = values[name, mode, port]["slack_ns"]
                if mode == "max":
                    require(close(measured, base["slack_ns"]), "A hold-only change moved a setup path")
                elif port != "global":
                    require(close(measured, base["slack_ns"] - 0.040), f"Unexpected {name} hold shift for {port}")
    return {case: {mode: {port: values[case, mode, port] for port in TARGETS} for mode in ("min", "max")}
            for case in SCENARIOS}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--deadline", type=int, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.parent == TRIAL and not out.exists(), "Use a fresh folder beside the frozen timing data")
    context = setup(args.history.resolve(strict=True))
    rows, layout, pins, _ = coverage.prepare(context)
    cases = [row for row in rows if (row["model"], row["corner"]) in CASES]
    require(sha(COVERAGE) == COVERAGE_SHA, "Retained timing coverage receipt changed")
    references = {(row["model"], row["corner"]): row["coverage"] for row in read(COVERAGE)["cases"]}
    require(set(references) == {(row["model"], row["corner"]) for row in rows}
            and CASES <= references.keys(), "Retained timing coverage matrix differs")
    out.mkdir()
    request, probe = out / "request.json", out / "probe.tcl"
    source = Path(__file__).resolve()
    write(request, dict(schema=SCHEMA, cases=cases, layout=layout, scenarios=SCENARIOS))
    probe.write_text(TCL)
    for path in (request, probe, source, Path(electrical.__file__).resolve(),
                 Path(coverage.__file__).resolve(), COVERAGE):
        pins[str(path)] = sha(path)
    run_native(context, out, "python3", ["-B", f"/work/scripts/{source.name}", "native"],
               [(source.parent, "/work/scripts", False), (TRIAL / "timing/run", coverage.RUN.rstrip("/"), False),
                (Path(layout["netlist"]["path"]), coverage.NL, False),
                (Path(layout["sdc"]["path"]), coverage.SDC, False)],
               140, args.deadline, memory="3g")
    require(all(sha(path) == digest for path, digest in pins.items()), "Retained timing input changed")
    tool = read(out / "tool.json")
    require(tool["sha256"] == cases[0]["sta_sha256"] and tool["completed_cases"] == len(CASES),
            "Native timing sensitivity matrix incomplete")
    results = {}
    for row in cases:
        key = row["model"], row["corner"]
        name = "-".join(key)
        log = out / f"{name}.log"
        results[name] = dict(log=draft.bound(log), scenario_slacks=parse(log.read_text(), row, references[key]))
    write(out / "readback.json", dict(schema=SCHEMA, status="diagnostic", target_odb_sha256=TARGET["odb_sha256"],
          target_gds_sha256=TARGET["gds_sha256"], image=IMAGE, tool=tool, execution=draft.bound(out / "execution.json"),
          scenarios=SCENARIOS, results=results, input_artifact_sha256=pins, model_qualified=False,
          qualified_timing=False, tapeout_ready=False))
    print(out / "readback.json")


if __name__ == "__main__":
    if sys.argv[1:] == ["native"]:
        native()
    else:
        main()
