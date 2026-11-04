"""Read the four omitted OpenSTA electrical checks on the exact draft ECO matrix."""

import argparse
import math
import os
from pathlib import Path
import re
import shutil
import subprocess

from streaming_8x4_e982_native import IMAGE, TOP, read, require, sha, write


CHECKS = ("recovery", "removal", "min_pulse_width", "min_period")
NL = "/work/views/signoff-views/implemented.v"
SDC = "/work/inputs/core.sdc"
RUN = "/work/result/"
OUT = Path("/work/export")
ENV_KEYS = (
    "SCRIPTS_DIR", "DESIGN_NAME", "CURRENT_NL", "_SDC_IN", "CLOCK_PERIOD",
    "OPENLANE_SDC_IDEAL_CLOCKS", "_CURRENT_CORNER_NAME", "_CURRENT_CORNER_LIBS",
    "_CURRENT_CORNER_NETLISTS", "_CURRENT_CORNER_SPEFS", "_CURRENT_SPEF_BY_CORNER",
    "IO_DELAY_CONSTRAINT", "TIME_DERATING_CONSTRAINT", "MAX_FANOUT_CONSTRAINT",
    "CLOCK_UNCERTAINTY_CONSTRAINT", "CLOCK_TRANSITION_CONSTRAINT", "OUTPUT_CAP_LOAD",
)
NUMBER = r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?"
TCL = """\
if {[catch {
    source $::env(SCRIPTS_DIR)/openroad/common/io.tcl
    set_cmd_units -time ns -capacitance pF -current mA -voltage V -resistance kOhm -distance um
    set sta_report_default_digits 6
    read_timing_info
    read_spefs
    set corner $::env(_CURRENT_CORNER_NAME)
    set corners [lln::get_corner_dict]
    if {[dict keys $corners] ne [list $corner]} {error "Unexpected STA corner inventory"}
    lln::set_sta_cmd_corner $corner
    set clocks [all_clocks]
    set clock [lindex $clocks 0]
    if {[llength $clocks] != 1 || [get_property $clock name] ne "clk"
        || abs([get_property $clock period] - 20.0) > 1e-9
        || ![get_property $clock is_propagated]} {error "Expected one propagated 20 ns clk"}
    puts "PINWHEEL_ELECTRICAL_CORNER $corner"
    foreach mode {min max} {
        puts "PINWHEEL_ELECTRICAL_WS $mode [worst_slack -corner $corner -$mode]"
    }
    set pulse [sta::min_pulse_width_check_slack [dict get $corners $corner]]
    set period [sta::min_period_check_slack]
    puts "PINWHEEL_ELECTRICAL_APPLICABLE min_pulse_width [expr {$pulse ne {NULL}}]"
    puts "PINWHEEL_ELECTRICAL_APPLICABLE min_period [expr {$period ne {NULL}}]"
    foreach check {recovery removal min_pulse_width min_period} {
        puts "PINWHEEL_ELECTRICAL_BEGIN $check"
        report_check_types -corner $corner -verbose -digits 6 -$check
        puts "PINWHEEL_ELECTRICAL_END $check"
    }
    puts "PINWHEEL_ELECTRICAL_COMPLETE $corner"
} message]} {
    puts stderr "PINWHEEL_ELECTRICAL_ERROR $message"
    exit 1
}
"""


def one(text, pattern, description):
    matches = re.findall(pattern, text, re.M)
    require(len(matches) == 1, f"Missing or ambiguous {description}")
    return matches[0]


def parse_log(text, row):
    corner = row["corner"]
    require(not re.search(r"^(?:Error[: ]|\[ERROR\]|PINWHEEL_ELECTRICAL_ERROR)", text, re.M),
            f"OpenSTA reported an error in {corner}")
    for marker in ("CORNER", "COMPLETE"):
        require(one(text, rf"^PINWHEEL_ELECTRICAL_{marker} (\S+)$", marker) == corner,
                "Unexpected electrical report corner")
    for mode, canonical in row["canonical_ws_ns"].items():
        observed = float(one(text, rf"^PINWHEEL_ELECTRICAL_WS {mode} ({NUMBER})$", mode + " slack"))
        require(math.isclose(observed, canonical, rel_tol=0, abs_tol=1e-6),
                f"Replay differs from canonical {corner} {mode} worst slack")
    results = {}
    for check in CHECKS:
        begin, end = (f"PINWHEEL_ELECTRICAL_{marker} {check}" for marker in ("BEGIN", "END"))
        require(text.splitlines().count(begin) == text.splitlines().count(end) == 1,
                f"Missing or duplicate markers for {check}")
        body = one(text, rf"^{begin}\n([\s\S]*?)^{end}$", check)
        slacks = re.findall(rf"^[ \t]*({NUMBER})[ \t]+slack \((MET|VIOLATED)\)[ \t]*$", body, re.M)
        if check in ("recovery", "removal"):
            absent = body.strip() == "No paths found."
            require(absent or len(re.findall(r"^Endpoint: .+$", body, re.M)) == len(slacks),
                    f"Incomplete paths in {check}")
        else:
            applicable = one(text, rf"^PINWHEEL_ELECTRICAL_APPLICABLE {check} ([01])$", check + " applicability")
            absent = applicable == "0"
            require((absent and not body.strip()) or (not absent and len(slacks) == 1
                    and len(re.findall(r"^Pin: .+$", body, re.M)) == 1), f"Incomplete {check} report")
        require(absent or slacks, f"No check result or explicit absence for {check}")
        if absent:
            results[check] = dict(status="no_applicable_check_observed", worst_slack_ns=None)
        else:
            worst, label = min(((float(value), label) for value, label in slacks),
                               key=lambda item: (item[0], item[1] != "VIOLATED"))
            require(math.isfinite(worst) and not (worst > 0 and label == "VIOLATED")
                    and not (worst < 0 and label == "MET"), f"Malformed {check} worst slack")
            results[check] = dict(status=label.lower(), worst_slack_ns=worst, reported_checks=len(slacks))
    return results


def prepare(attempt, timing_digest, context):
    import streaming_8x4_draft_rc_timing as draft
    from streaming_8x4_e982_eco_timing import verified_layout

    timing_path = attempt / "timing-readback.json"
    require(draft.bound(timing_path)["sha256"] == timing_digest, "Reviewed timing readback SHA differs")
    timing = read(timing_path)
    require(timing["schema"] == "pinwheel.streaming-8x4-e982-eco-timing-readback.v1"
            and timing["status"] == "diagnostic" and timing["target_name"] == "eco"
            and timing["parasitics_preflight_passed"] is True and timing["qualified_timing"] is False,
            "Expected the exact independently reopened ECO draft matrix")
    pins = {str(timing_path): timing_digest}

    def reopen(path):
        item = draft.bound(path)
        require(timing["verified_file_sha256"].get(item["path"]) == item["sha256"],
                f"Reviewed timing input changed: {path}")
        pins[item["path"]] = item["sha256"]
        return item

    run = attempt / "run"
    native = read(reopen(attempt / "native-readback.json")["path"])
    request_item = reopen(attempt / "inputs/request.json")
    execution_item = reopen(run / "execution.json")
    _, layout = verified_layout(context)
    require(native["schema"] == "pinwheel.e982-five-layer-timing-native.v1" and native["status"] == "completed"
            and native["target_name"] == "eco" and native["target_odb_sha256"] == layout["odb"]["sha256"]
            and native["gds_sha256"] == layout["gds"]["sha256"] and native["request"] == request_item == timing["request"]
            and native["execution"] == execution_item and native["passes"] == reopen(run / "native-passes.json"),
            "Native/request evidence belongs to a different candidate or attempt")
    execution = read(execution_item["path"])
    require(execution["status"] == "completed" and execution["exit_code"] == 0
            and execution["container_termination"]["status"] == "absent" and execution["argv"].count(IMAGE) == 1,
            "Canonical native image/run did not close")
    request = read(request_item["path"])
    require(request["layout"] == timing["target"] == layout and request["policy"] == draft.policy()
            and request["model_rules_sha256"] == draft.RULE_SHA, "Wrong retained draft settings or ECO views")
    original = read(reopen(request["original_resolved"]["path"])["path"])
    common_inputs = {}
    for name, role in ((NL, "netlist"), (SDC, "sdc")):
        digest = reopen(layout[role]["path"])["sha256"]
        require(request["input_sha256"][name] == digest, f"Canonical hash differs: {name}")
        common_inputs[name] = digest
    rows = []
    require(set(timing["model_matrix"]) == set(draft.MODELS), "Wrong draft extraction model matrix")
    for model in draft.MODELS:
        evidence = timing["model_matrix"][model]
        spef = f"{RUN}{model}/flow/01-openroad-rcx/nom/{TOP}.nom.spef"
        item = reopen(run / spef.removeprefix(RUN))
        require(evidence["spef"] == item and set(evidence["cases"]) == set(draft.CORNERS),
                "Extracted SPEF or corner matrix differs")
        journal = reopen(run / model / "native-journal.jsonl")
        calls = [call for call in draft.calls(journal["path"]) if Path(call["argv"][0]).name == "sta"]
        for corner in draft.CORNERS:
            call, = [call for call in calls if call["env"]["_CURRENT_CORNER_NAME"] == corner]
            env = call["env"]
            scripts = env["SCRIPTS_DIR"]
            libs = env["_CURRENT_CORNER_LIBS"].split()
            require(re.fullmatch(r"/nix/store/[^/]+/.+/librelane/scripts", scripts)
                    and call["argv"][1:] == ["-no_splash", "-exit", f"{scripts}/openroad/sta/corner.tcl"]
                    and re.fullmatch(r"[0-9a-f]{64}", call["executable_sha256"])
                    and (env["CURRENT_NL"], env["_SDC_IN"], env["_CURRENT_SPEF_BY_CORNER"]) == (NL, SDC, spef)
                    and env["DESIGN_NAME"] == TOP and env["OPENLANE_SDC_IDEAL_CLOCKS"] == "0"
                    and libs == original["CELL_LIBS"][corner] and len(libs) == 2
                    and not any(env.get(k) for k in ("EXTRA_LIBS", "EXTRA_VERILOG_MODELS",
                        "_CURRENT_CORNER_EXTRA_SPEFS_BACKCOMPAT", "_CURRENT_CORNER_SPEFS", "_CURRENT_CORNER_NETLISTS")),
                    f"Unexpected canonical STA inputs or invocation in {model}/{corner}")
            files = {**common_inputs, spef: item["sha256"]}
            for lib in libs:
                require(lib.startswith("/work/pdk/") and ".." not in Path(lib).parts, "Unexpected Liberty mount")
                digest = reopen(context["pdk"] / lib.removeprefix("/work/pdk/"))["sha256"]
                require(request["input_sha256"][lib] == digest, f"Canonical Liberty hash differs: {lib}")
                files[lib] = digest
            for name in ("common/io.tcl", "common/set_global_connections.tcl", "sta/corner.tcl"):
                files[f"{scripts}/openroad/{name}"] = request["native_package_sha256"][f"scripts/openroad/{name}"]
            case = evidence["cases"][corner]
            rows.append(dict(model=model, corner=corner, sta_sha256=call["executable_sha256"], input_sha256=files,
                             env={key: env[key] for key in ENV_KEYS},
                             canonical_ws_ns={"min": case["hold_ws_ns"], "max": case["setup_ws_ns"]}))
    require(len({row["sta_sha256"] for row in rows}) == 1, "Canonical matrix changed STA executables")
    return rows, layout, pins


def native():
    request = read(OUT / "request.json")
    script = OUT / "probe.tcl"
    require(script.read_text() == TCL, "Native electrical Tcl differs")
    executable = Path(shutil.which("sta") or "/missing-sta").resolve(strict=True)
    digest = sha(executable)
    # These are the journal values consumed by canonical io.tcl. Set them directly
    # in the process instead of sourcing LibreLane's generated environment dump.
    base = {key: os.environ[key] for key in ("PATH", "HOME") if key in os.environ}
    base.update(_TCL_ENV_IN="/dev/null", LC_ALL="C")
    for row in request["cases"]:
        require(digest == row["sta_sha256"], "Native STA executable differs from the canonical journal")
        for name, expected in row["input_sha256"].items():
            require(sha(name) == expected, f"Native electrical input changed: {name}")
        log = OUT / f"{row['model']}-{row['corner']}.log"
        with log.open("x") as stream:
            subprocess.run([executable, "-no_splash", "-exit", script], check=True, timeout=60,
                           stdin=subprocess.DEVNULL, stdout=stream, stderr=subprocess.STDOUT,
                           env={**base, **row["env"]})
    write(OUT / "tool.json", dict(executable=str(executable), sha256=digest))


def main():
    import streaming_8x4_draft_rc_timing as draft
    from streaming_8x4_e982_eco_signoff import ECO_ROOT, setup
    from streaming_8x4_e982_native import run_native

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", type=Path, required=True)
    parser.add_argument("--timing-sha256", required=True)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--deadline", type=int, required=True)
    args = parser.parse_args()
    attempt, out = args.attempt.resolve(strict=True), args.out.resolve()
    require(attempt.is_relative_to(ECO_ROOT) and out.is_relative_to(ECO_ROOT) and not out.exists()
            and not out.is_relative_to(attempt), "Use a fresh ignored output outside the retained ECO attempt")
    context = setup(args.history.resolve(strict=True), ECO_ROOT / "signoff-01")
    rows, layout, pins = prepare(attempt, args.timing_sha256, context)
    out.mkdir(exist_ok=False)
    request = out / "request.json"
    script = out / "probe.tcl"
    write(request, dict(cases=rows, target_odb_sha256=layout["odb"]["sha256"], target_gds_sha256=layout["gds"]["sha256"]))
    script.write_text(TCL)
    source = Path(__file__).resolve()
    for path in (request, script, source):
        pins[str(path)] = sha(path)
    run_native(context, out, "python3", ["-B", f"/work/scripts/{source.name}", "native"],
               [(source.parent, "/work/scripts", False), (attempt / "run", RUN.rstrip("/"), False),
                (Path(layout["netlist"]["path"]), NL, False), (Path(layout["sdc"]["path"]), SDC, False)],
               600, args.deadline, memory="3g")
    require(all(sha(path) == digest for path, digest in pins.items()), "Reviewed electrical inputs changed")
    tool = read(out / "tool.json")
    require(tool["sha256"] == rows[0]["sta_sha256"], "Electrical runtime tool receipt differs")
    for row in rows:
        log = out / f"{row['model']}-{row['corner']}.log"
        row.update(log=draft.bound(log), checks=parse_log(log.read_text(), row))
    write(out / "readback.json", dict(schema="pinwheel.streaming-8x4-e982-eco-electrical.v1",
          status="diagnostic", image=IMAGE, target_odb_sha256=layout["odb"]["sha256"],
          target_gds_sha256=layout["gds"]["sha256"], tool=tool, execution=draft.bound(out / "execution.json"),
          input_artifact_sha256=pins, cases=rows, model_qualified=False, qualified_timing=False,
          scope="Worst reported checks on the retained Liberty, propagated-clock SDC and draft SPEFs. "
                "Zero observed applicability is scoped to these loaded inputs."))
    print(out / "readback.json")


if __name__ == "__main__":
    import sys

    if sys.argv[1:] == ["native"]:
        native()
    else:
        main()
