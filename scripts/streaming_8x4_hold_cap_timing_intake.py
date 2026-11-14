"""Exercise the exact-target timing intake and rederive draft I/O timing margins."""

import argparse
from decimal import Decimal
from pathlib import Path
import re
import shutil

import streaming_8x4_draft_rc_timing as draft
import streaming_8x4_e982_eco_timing_readback as timing_readback
import streaming_8x4_e982_parasitics_preflight as preflight
from streaming_8x4_e982_g4_transport import emit
from streaming_8x4_e982_native import ROOT, TOP, bind, read, require, sha
from streaming_8x4_hold_cap_physical import EVIDENCE, TRIAL


COVERAGE = TRIAL / "timing-coverage-01/readback.json"
COVERAGE_SHA = "19892a8d2aba61b4d5c0ef8fa3bf8255bb154b39f6099f25eec2b8caeab2a88c"
TIMING = TRIAL / "timing/timing-readback.json"
TIMING_SHA = EVIDENCE["timing/timing-readback.json"]
SDC = TRIAL / "timing/run/MIN/flow/final/sdc/core.sdc"
OUTPUT_PATH = re.compile(r"^PINWHEEL_COVERAGE_PATH\t(min|max)\t((?:uo_out|uio_out|uio_oe)\[\d+\])"
                         rf"\t({timing_readback.NUMBER})$", re.M)
INPUT_MIN_NS = Decimal("0.2")
INPUT_MAX_NS = Decimal("4")
OUTPUT_MIN_NS = Decimal("0.2")
OUTPUT_MAX_NS = Decimal("4")
UNCERTAINTY_NS = Decimal("0.2")
ACTIVE_INPUTS = {"ena", "rst_n", *(f"ui_in[{bit}]" for bit in range(8))}
ACTIVE_OUTPUTS = {*(f"uo_out[{bit}]" for bit in range(6)),
                  *(f"uio_{port}[{bit}]" for port in ("oe", "out") for bit in range(3))}


def verified(path, expected):
    item = draft.bound(path)
    require(item["sha256"] == expected, f"Retained timing input changed: {path}")
    return path


def retained():
    timing = read(verified(TIMING, TIMING_SHA))
    coverage = read(verified(COVERAGE, COVERAGE_SHA))
    for document in (timing, coverage):
        require(document["target_odb_sha256"] == preflight.HOLD_CAP_TARGET["odb"]
                and document["target_gds_sha256"] == preflight.HOLD_CAP_TARGET["gds"]
                and document["status"] == "diagnostic" and document["qualified_timing"] is False,
                "Wrong frozen draft timing evidence")
    expected_cases = {(model, corner) for model in draft.MODELS for corner in draft.CORNERS}
    cases = coverage["cases"]
    require(len(cases) == len(expected_cases)
            and {(row["model"], row["corner"]) for row in cases} == expected_cases,
            "Incomplete or duplicate timing scenario")
    for model, entry in timing["model_matrix"].items():
        require(model in draft.MODELS and set(entry["cases"]) == set(draft.CORNERS), "Wrong raw timing corner")
    require(set(timing["model_matrix"]) == set(draft.MODELS), "Wrong timing model inventory")
    return timing, cases


def retained_artifact(timing, path):
    return verified(path, timing["verified_file_sha256"][str(path)])


def artifact_directory(run, model, corner):
    return run / model / "flow/02-openroad-stapostpnr" / corner


def draft_request(out, timing, cases):
    run = TIMING.parent / "run"
    inputs = TIMING.parent / "inputs"
    execution = read(retained_artifact(timing, run / "execution.json"))
    mounts = timing_readback.host_mounts(execution, run, inputs)
    target = {key: bind(retained_artifact(timing, Path(timing["target"][key]["path"])))
              for key in preflight.HOLD_CAP_TARGET}
    require({key: item["sha256"] for key, item in target.items()} == preflight.HOLD_CAP_TARGET,
            "Draft timing target bindings differ")
    sdc = bind(verified(SDC, draft.SDC_SHA))
    lib_assets = out / "liberties"
    lib_assets.mkdir()
    scenarios = {}
    for row in cases:
        model, corner = row["model"], row["corner"]
        name = f"{model}-{corner}"
        sta_reports = artifact_directory(run, model, corner)
        raw_checks = retained_artifact(timing, sta_reports / "checks.rpt")
        entry = timing["model_matrix"][model]["spef"]
        spef = bind(verified(Path(entry["path"]), entry["sha256"]))
        env = row["env"]
        require(row["input_sha256"][env["_CURRENT_SPEF_BY_CORNER"]] == spef["sha256"]
                and row["input_sha256"][env["_SDC_IN"]] == sdc["sha256"]
                and row["input_sha256"][env["CURRENT_NL"]] == target["netlist"]["sha256"],
                f"Retained STA data disagrees with the extracted artifacts for {name}")
        libs = []
        for native_path in env["_CURRENT_CORNER_LIBS"].split():
            source = retained_artifact(timing, timing_readback.resolve_mount(mounts, native_path))
            copy = lib_assets / source.name
            if not copy.exists():
                shutil.copyfile(source, copy)
            libs.append(bind(verified(copy, row["input_sha256"][native_path])))
        annotation = bind(raw_checks)
        run_receipt = out / f"{name}.json"
        emit(run_receipt, dict(schema=preflight.ANALYSIS, top=TOP, scenario=name, rc_corner=model,
             sta_corner=corner, mode="draft", runtime_sha256=row["sta_sha256"], annotation_mode="read_spef",
             exit_code=execution["exit_code"], liberty_sha256=[item["sha256"] for item in libs],
             **{key + "_sha256": item["sha256"] for key, item in
                dict(odb=target["odb"], gds=target["gds"], netlist=target["netlist"], sdc=sdc,
                     spef=spef, annotation=annotation).items()}))
        scenarios[name] = dict(rc_corner=model, sta_corner=corner, mode="draft", sdc=sdc, spef=spef,
                               annotation=annotation, run=bind(run_receipt), liberties=libs)
    return dict(schema=preflight.REQUEST, target=target, scenarios=scenarios)


def path_margin(slack, delay, kind):
    baseline = Decimal(str(slack))
    require(baseline.is_finite(), "Non-finite native path slack")
    return {"slack_ns": str(baseline),
            "break_even_external_delay_ns": str(delay - baseline if kind == "min" else delay + baseline)}


def margins(timing, cases):
    summary = {"input": {}, "output": {}, "falling_ui_in[5]": {}}

    def retain(role, port, mode, slack, external, model, corner, endpoint):
        record = dict(path_margin(slack, external, mode), rc_model=model, liberty_corner=corner, endpoint=endpoint)
        entry = summary[role].setdefault(port, {})
        if mode not in entry or Decimal(record["slack_ns"]) < Decimal(entry[mode]["slack_ns"]):
            entry[mode] = record

    for row in cases:
        model, corner = row["model"], row["corner"]
        name = f"{model}-{corner}"
        log = verified(COVERAGE.parent / f"{name}.log", row["log"]["sha256"]).read_text()
        output_rows = OUTPUT_PATH.findall(log)
        for mode, input_delay, output_delay in (("min", INPUT_MIN_NS, OUTPUT_MIN_NS), ("max", INPUT_MAX_NS, OUTPUT_MAX_NS)):
            by_output = [(port, Decimal(slack)) for kind, port, slack in output_rows if kind == mode]
            require({port for port, _ in by_output} == ACTIVE_OUTPUTS, f"Wrong constrained output set for {name}/{mode}")
            for port, slack in by_output:
                retain("output", port, mode, slack, output_delay, model, corner, port)
            inputs = row["coverage"]["constrained_path_coverage"][mode]["input_paths"]
            require(ACTIVE_INPUTS == {port for port, record in inputs.items() if record is not None},
                    f"Wrong constrained input set for {name}/{mode}")
            for port in sorted(ACTIVE_INPUTS):
                record = inputs[port]
                retain("input", port, mode, record["slack_ns"], input_delay, model, corner, record["endpoint"])
        sta_reports = artifact_directory(TIMING.parent / "run", model, corner)
        sta_log = retained_artifact(timing, sta_reports / "sta.log").read_text()
        for mode in ("min", "max"):
            path = timing_readback.hold_path(sta_log, mode)
            require(path == timing["model_matrix"][model]["cases"][corner]["targeted_paths"][mode],
                    f"Targeted path differs from original timing receipt for {name}/{mode}")
            retain("falling_ui_in[5]", path["startpoint"], mode, path["slack_ns"], Decimal(str(path["external_delay_ns"])),
                   model, corner, path["endpoint"])
    return dict(schema="pinwheel.streaming-8x4-hold-cap-io-margins.v1", status="diagnostic",
                target=dict(odb_sha256=timing["target_odb_sha256"], gds_sha256=timing["target_gds_sha256"]),
                cases=len(cases), sdc=bind(verified(SDC, draft.SDC_SHA)), coverage=bind(COVERAGE), timing=bind(TIMING),
                clock_period_ns="20", clock_uncertainty_ns=str(UNCERTAINTY_NS), input_drive="sg13cmos5l_buf_2/X",
                output_load_pf="0.010", ports=summary,
                draft_delays_ns=dict(input=dict(min=str(INPUT_MIN_NS), max=str(INPUT_MAX_NS)),
                                     output=dict(min=str(OUTPUT_MIN_NS), max=str(OUTPUT_MAX_NS))),
                interpretation="Shift one external delay at a time with clock edges, duty, driver/slew, loads, "
                               "other delays and extraction fixed. Shared input/output paths can see both budget changes.",
                qualified_timing=False, tapeout_ready=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.parent == TRIAL and not out.exists(), "Use a fresh local timing-intake directory beside the frozen data")
    timing, cases = retained()
    report = margins(timing, cases)
    out.mkdir()
    request = draft_request(out, timing, cases)
    emit(out / "draft-request.json", request)
    result = preflight.preflight(ROOT, request, target_name="hold-cap-trial")
    emit(out / "draft-preflight.json", dict(request=bind(out / "draft-request.json"), **result))
    sources = dict(extraction_receipt=TIMING, corner_matrix=COVERAGE, host_timing_contract=SDC)
    intake = dict(schema=preflight.INTAKE_REQUEST, target=request["target"],
                  authority={role: bind(path) for role, path in sources.items()},
                  scenarios={name: {key: value for key, value in row.items() if key not in {"annotation", "run"}}
                             for name, row in request["scenarios"].items()})
    emit(out / "draft-intake-request.json", intake)
    emit(out / "io-margins.json", report)


if __name__ == "__main__":
    main()
