"""Independently reopen a completed frozen-layout draft RCX/STA matrix."""

import argparse
from decimal import DecimalException
import math
from pathlib import Path, PurePosixPath
import re

import streaming_8x4_draft_rc_timing as draft
import streaming_8x4_draft_rc_timing_observe as observer
from streaming_8x4_e982_eco_digital import ECO_GDS, ECO_ODB
from streaming_8x4_e982_eco_timing import HOLD_PROBE
import streaming_8x4_e982_parasitics_preflight as preflight
from physical_checkpoint_sta import measurement_quality
from physical_timing_acceptance import assess_timing
from streaming_8x4_e982_g4_transport import TARGET_GDS, TARGET_ODB, bind, emit, read_bound, reopen, require
from streaming_8x4_e982_g4_wire import verify_pins
from streaming_8x4_e982_native import IMAGE
from streaming_tt_quality import inventory_context


SCHEMA = "pinwheel.streaming-8x4-e982-eco-timing-readback.v1"
LAYOUT = {"odb", "gds", "def", "netlist", "powered_netlist", "inventory", "views_receipt",
          "inventory_receipt", "sdc"}
HOLD_PORT = "ui_in[5]"
HOLD_FF = "engine.frontend._0230_"
NUMBER = r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?"
PATH_DISPLAY_TOLERANCE_NS = 5e-6


def exact_line(text, expression, label):
    rows = re.findall(expression, text, re.M)
    require(len(rows) == 1, f"Expected one {label}, observed {len(rows)}")
    return rows[0]


def host_mounts(execution, run, inputs):
    argv = execution["argv"]
    require(execution["status"] == "completed" and type(execution["exit_code"]) is int
            and execution["exit_code"] == 0 and execution["container_termination"]["status"] == "absent",
            "Bounded native run or owned cleanup did not complete")
    require(argv.count(IMAGE) == 1, "Native image identity differs")
    offset = argv.index(IMAGE)
    require(argv[offset + 1:] == ["-B", "/work/diagnostic/producer/" + draft.OWN, "native",
                                  "--inputs", "/work/diagnostic", "--output", "/work/result"]
            and argv[argv.index("--network") + 1] == "none", "Native invocation or network policy differs")
    mounts = {}
    for index, flag in enumerate(argv[:offset]):
        if flag != "--mount":
            continue
        mount = re.fullmatch(r"type=bind,source=([^,]+),target=([^,]+)(,readonly)?", argv[index + 1])
        require(mount is not None, "Unsupported native mount declaration")
        host, target, readonly = mount.groups()
        key = PurePosixPath(target)
        require(key.is_absolute() and ".." not in key.parts and key not in mounts and Path(host).is_absolute(),
                "Invalid or duplicate native mount")
        mounts[key] = Path(host), bool(readonly)
    require(mounts.get(PurePosixPath("/work/result")) == (run, False)
            and mounts.get(PurePosixPath("/work/diagnostic")) == (inputs, True),
            "Native output or sealed diagnostic inputs mount differs")
    return mounts


def resolve_mount(mounts, path):
    path = PurePosixPath(path)
    require(path.is_absolute() and ".." not in path.parts, f"Unsafe container path: {path}")
    mount = next((root for root in sorted(mounts, key=lambda p: len(p.parts), reverse=True)
                  if path.is_relative_to(root)), None)
    require(mount is not None, f"Unresolved native input mount: {path}")
    host, readonly = mounts[mount]
    require(readonly, f"Native input is writable: {path}")
    return host / str(path.relative_to(mount))


def hold_path(text, mode):
    """Read one exact falling-input path and reconcile rounded path arithmetic."""
    begin, end = f"PINWHEEL_ECO_TIMING_PATH_BEGIN {mode}", f"PINWHEEL_ECO_TIMING_PATH_END {mode}"
    require(text.splitlines().count(begin) == text.splitlines().count(end) == 1,
            f"Missing or repeated exact {mode} path markers")
    path = exact_line(text, rf"^{begin}\n([\s\S]*?)^{end}$",
                      f"targeted {mode} path section")
    start = exact_line(path, r"^Startpoint:\s+(\S+).*$", "targeted startpoint")
    endpoint = exact_line(path, r"^Endpoint:\s+(\S+).*$", "targeted endpoint")
    path_type = exact_line(path, r"^Path Type:\s+(\S+)\s*$", "targeted path type")
    require(start == HOLD_PORT and endpoint == HOLD_FF and path_type == mode,
            "Targeted path source, endpoint or sense differs")

    def pin(name, transition):
        return float(exact_line(path, rf"^[ \t]*.*?({NUMBER})[ \t]+{transition}[ \t]+{re.escape(name)}[ \t]+\(",
                                f"targeted pin {name}"))

    pin(HOLD_PORT, "v")
    arrival = pin(HOLD_FF + "/D", r"[\^v]")
    capture = pin(HOLD_FF + "/CLK", r"\^")
    edges = list(map(float, re.findall(rf"^[ \t]*{NUMBER}[ \t]+({NUMBER})[ \t]+clock clk \(rise edge\)[ \t]*$",
                                      path, re.M)))
    require(edges == [0.0, 0.0 if mode == "min" else 20.0], "Targeted launch or capture clock edge differs")
    term = "hold" if mode == "min" else "setup"
    library_term, required = map(float, exact_line(path,
        rf"^[ \t]*({NUMBER})[ \t]+({NUMBER})[ \t]+library {term} time[ \t]*$", f"library {term} term"))
    uncertainty = float(exact_line(path,
        rf"^[ \t]*({NUMBER})[ \t]+{NUMBER}[ \t]+clock uncertainty[ \t]*$", "targeted clock uncertainty"))
    external = float(exact_line(path,
        rf"^[ \t]*({NUMBER})[ \t]+{NUMBER}[ \t]+v[ \t]+input external delay[ \t]*$", "falling input budget"))
    slack, label = exact_line(path, rf"^[ \t]*({NUMBER})[ \t]+slack \((MET|VIOLATED)\)[ \t]*$", "targeted slack")
    slack = float(slack)
    expected = arrival - required if mode == "min" else required - arrival
    # OpenSTA prints separate six-place values after its single-precision time arithmetic.
    require(abs(expected - slack) <= PATH_DISPLAY_TOLERANCE_NS
            and (slack == 0 or (slack < 0) == (label == "VIOLATED")),
            "Targeted path rounded slack arithmetic differs")
    return dict(startpoint=start, endpoint=endpoint + "/D", input_transition="fall", path_type=mode,
                external_delay_ns=external, data_arrival_ns=arrival, capture_clock_pin_time_ns=capture,
                capture_clock_latency_ns=round(capture - edges[1], 6), capture_clock_edge_ns=edges[1],
                uncertainty_term_ns=uncertainty, signed_library_term_ns=library_term, required_ns=required,
                slack_ns=slack, raw_status=label)


def raw_timing(dest, corner, metrics, pins):
    summary = {}
    for mode, purpose in (("min", "hold"), ("max", "setup")):
        for kind in ("ws", "wns", "tns"):
            path = dest / f"{kind}.{mode}.rpt"
            metric = metrics[f"timing__{purpose}__{kind}__corner:{corner}"]
            bind(pins, path)
            raw = float(exact_line(path.read_text(), rf"^{re.escape(corner)}:[ \t]+({NUMBER})[ \t]*$",
                                   f"{corner} {kind} {mode}"))
            require(type(metric) in (int, float) and math.isfinite(metric) and metric == raw,
                    f"Raw {kind}.{mode}.rpt differs from STA metrics")
            summary[f"{purpose}_{kind}_ns"] = raw
        path = dest / f"{mode}.rpt"
        bind(pins, path)
        reports = re.split(r"(?m)^Startpoint: ", path.read_text())
        require(2 <= len(reports) <= 1001, f"Missing or oversized ranked {mode} path report")
        first = reports[1]
        start = first.splitlines()[0]
        end = exact_line(first, r"^Endpoint:\s+(.+)$", "ranked endpoint")
        slack, _ = exact_line(first, rf"^[ \t]*({NUMBER})[ \t]+slack \((MET|VIOLATED)\)[ \t]*$", "ranked slack")
        require(abs(float(slack) - summary[f"{purpose}_ws_ns"]) < 1e-6,
                f"Ranked {mode} worst path differs from STA metric")
        summary[f"worst_{purpose}_path"] = dict(startpoint=start, endpoint=end, slack_ns=float(slack))
        summary[f"ranked_{purpose}_paths"] = len(reports) - 1
    return summary


def extra_checks(checks, violator_list, metrics):
    setup_cmd = ("check_setup -verbose -unconstrained_endpoints -multiple_clock "
                 "-no_clock -no_input_delay -loops -generated_clocks")
    setup = exact_line(checks, rf"^{re.escape(setup_cmd)}\n=+\n([\s\S]*)\Z", "check_setup section").strip()
    rows = []
    lines = [line.strip() for line in violator_list.splitlines()
             if line.strip() and set(line.strip()) != {"="} and line.strip() != "Violator List"]
    for line in lines:
        match = re.fullmatch(rf"\[(hold|setup) (in-reg|reg-reg|reg-out|in-out)\] (\S+) -> (\S+) : ({NUMBER})", line)
        require(match is not None, f"Unrecognized violation row: {line}")
        purpose, family, start, end, slack = match.groups()
        require(float(slack) <= 0, "Positive slack in the negative path inventory")
        rows.append(dict(check=purpose, family=family, startpoint=start, endpoint=end, slack_ns=float(slack)))
    for purpose in ("hold", "setup"):
        require(sum(row["check"] == purpose for row in rows) == metrics[f"{purpose}_violations"],
                f"Listed {purpose} paths differ from the negative endpoint count")
    for name, key in (("slew", "slew_violations"), ("fanout", "fanout_violations"),
                      ("cap", "capacitance_violations")):
        value = int(exact_line(checks, rf"^max {name} violation count (\d+)[ \t]*$", f"max {name} count"))
        require(value == metrics[key], f"Raw {name} count differs from the STA metric")
    return dict(negative_endpoint_rows=rows,
                check_setup=dict(status="findings_reported" if setup else "no_findings_printed", raw_findings=setup),
                dedicated_recovery_removal_pulse_width="open_no_dedicated_reports",
                full_unconstrained_endpoint_inventory="open_check_setup_diagnostic_only")


def completed_model(root, run, pins, request, original, seed, inventory, context, disconnected, model):
    directory = run / model
    flow = directory / "flow"
    staged = read_bound(pins, root / "inputs" / f"{model}-config.json")
    config = read_bound(pins, flow / "resolved.json")
    delta = draft.config_delta(original, config, model)
    require(staged == config, "Native resolved config differs from the sealed diagnostic input")
    states = sorted(flow.glob("*/state_out.json"))
    require(len(states) == 2 and states[0].parent.name.endswith("-openroad-rcx")
            and states[1].parent.name.endswith("-openroad-stapostpnr"), "Expected precisely canonical RCX then STA")
    rcx, sta = [read_bound(pins, path) for path in states]
    roles = ("odb", "def", "nl", "sdc") + (("pnl",) if "pnl" in seed else ())
    require(all(state[role] == seed[role] for state in (rcx, sta) for role in roles)
            and set(rcx["spef"]) == {"nom_*"} and rcx["spef"] == sta["spef"], "Wrong seed views or SPEF state")
    spef_name = rcx["spef"]["nom_*"]
    mount = PurePosixPath(f"/work/result/{model}/flow")
    relative = PurePosixPath(spef_name).relative_to(mount)
    require(".." not in relative.parts and relative.suffix == ".spef", "Unexpected extracted SPEF path")
    spef = flow / str(relative)
    spef_item = bind(pins, spef)
    final_spef = flow / "final/spef/nom" / spef.name
    require(set(flow.rglob("*.spef")) == {spef, final_spef}, "Unexpected native or final SPEF inventory")
    bind(pins, final_spef, spef_item["sha256"])
    journal = directory / "native-journal.jsonl"
    bind(pins, journal)
    calls = draft.calls(journal)
    env = calls[0]["env"]
    require(env.get("RCX_RULESET") == f"/work/diagnostic/rules/{model}.rules"
            and env.get("SAVE_SPEF") == spef_name and env.get("RCX_MERGE_VIA_WIRE_RES") == "1"
            and env.get("CURRENT_DEF") == seed["def"] and env.get("RCX_LEF") == config["TECH_LEFS"]["nom_*"],
            "Canonical extraction source/model or policy differs")
    layout = preflight.expected_nets(inventory, context)
    try:
        with spef.open(encoding="ascii") as stream:
            coverage = dict(status="pass", **preflight.spef_evidence(stream, inventory, layout))
    except (ValueError, DecimalException) as exc:
        coverage = dict(status="rejected", reason=str(exc))
    metrics = sta["metrics"]
    assessment = assess_timing(metrics, draft.CORNERS)
    cases = {}
    for corner in draft.CORNERS:
        selected = [row for row in calls if row["env"].get("_CURRENT_CORNER_NAME") == corner
                    and Path(row["argv"][0]).name == "sta"]
        require(len(selected) == 1, "Missing or ambiguous actual standalone STA corner")
        env = selected[0]["env"]
        require(env.get("OPENLANE_SDC_IDEAL_CLOCKS") == "0" and env.get("_SDC_IN") == seed["sdc"]
                and env.get("STA_EXTRA_CORNER_TCL_FILE") == "/work/diagnostic/observe.tcl"
                and env.get("CURRENT_NL") == seed["nl"] and env.get("_CURRENT_SPEF_BY_CORNER") == spef_name
                and env.get("_CURRENT_CORNER_LIBS", "").split() == config["CELL_LIBS"][corner],
                "Actual STA clock, views, hook, model or Liberty binding differs")
        filters = [row for row in calls if any(arg.endswith("/filter_unannotated.py") for arg in row["argv"])
                   and "--corner" in row["argv"] and row["argv"][row["argv"].index("--corner") + 1] == corner]
        require(len(filters) == 1 and seed["odb"] in filters[0]["argv"]
                and any(arg.endswith(f"/{corner}/checks.rpt") for arg in filters[0]["argv"]),
                "Annotation filter targets another ODB/corner")
        dest = states[1].parent / corner
        raw = {}
        for name in ("sta.log", "checks.rpt", "clock.rpt", "unpropagated.rpt", "violator_list.rpt"):
            bind(pins, dest / name)
            raw[name] = (dest / name).read_text()
        clock = observer.check_observer(raw["sta.log"], request["observer_expectation"], corner,
                                        raw["clock.rpt"], raw["unpropagated.rpt"])
        filtered = read_bound(pins, dest / "filter_unannotated_metrics.json")
        quality = measurement_quality(raw["checks.rpt"], context, disconnected)
        count = assessment["corners"][corner]["fanout_violations"]
        require(count == len(quality["fanout_violations"]), "Raw fanout and STA metric differ")
        try:
            annotation = preflight.annotation_evidence(raw["checks.rpt"], corner, context, disconnected)
            require(annotation == quality["wire_annotation"]
                    and filtered[f"timing__unannotated_net__count__corner:{corner}"] == annotation["unannotated"]
                    and filtered[f"timing__unannotated_net_filtered__count__corner:{corner}"] == 0,
                    "Independent and canonical annotation counts differ")
            annotation = dict(status="pass", **annotation)
        except ValueError as exc:
            annotation = dict(status="rejected", reason=str(exc), **quality["wire_annotation"])
        paths = {mode: hold_path(raw["sta.log"], mode) for mode in ("min", "max")}
        other_checks = extra_checks(raw["checks.rpt"], raw["violator_list.rpt"], assessment["corners"][corner])
        cases[corner] = dict(clock=clock, annotation=annotation, canonical_annotation_metrics=filtered,
                             fanout_violations=quality["fanout_violations"], targeted_paths=paths,
                             ancillary_checks=other_checks,
                             **raw_timing(dest, corner, metrics, pins))
    return dict(model=model, config_delta=delta, rules_sha256=draft.RULE_SHA[model],
                spef=spef_item, spef_validation=coverage, assessment=assessment, cases=cases,
                direct_native_calls=len(calls))


def readback(attempt, expected_request=None, trial_layout=None):
    attempt = Path(attempt).absolute()
    inputs, run = attempt / "inputs", attempt / "run"
    pins = {}
    request = read_bound(pins, inputs / "request.json", expected_request)
    seed = read_bound(pins, inputs / "seed.json")
    require(request["schema"] == "pinwheel.streaming-8x4-draft-rc-timing-request.v1"
            and request["policy"] == draft.policy() and request["model_rules_sha256"] == draft.RULE_SHA
            and request["model_qualified"] is False and request["qualified_timing"] is False
            and request["target_name"] in {"baseline", "eco", "hold-cap-trial"} and set(request["layout"]) == LAYOUT,
            "Wrong draft diagnostic target or policy")
    execution = read_bound(pins, run / "execution.json")
    mounts = host_mounts(execution, run, inputs)
    native = read_bound(pins, attempt / "native-readback.json")
    require(native["schema"] == "pinwheel.e982-five-layer-timing-native.v1" and native["status"] == "completed"
            and native["target_name"] == request["target_name"] and native["model_qualified"] is False
            and native["qualified_timing"] is False, "Native runner closeout differs")
    for key, path in (("request", inputs / "request.json"), ("execution", run / "execution.json"),
                      ("passes", run / "native-passes.json")):
        require(reopen(pins, native[key])["path"] == str(path), f"Native {key} receipt is misbound")
    for item in request["layout"].values():
        reopen(pins, item)
    roles = request["layout"]
    expected_odb, expected_gds = (ECO_ODB, ECO_GDS) if request["target_name"] == "eco" else (TARGET_ODB, TARGET_GDS)
    if request["target_name"] == "hold-cap-trial":
        require(trial_layout is not None, "Explicit trial layout manifest required")
        manifest = read_bound(pins, trial_layout)
        require(Path(manifest["odb"]) == Path(roles["odb"]["path"])
                and Path(manifest["gds"]) == Path(roles["gds"]["path"]), "Trial layout paths differ")
        expected_odb, expected_gds = manifest["odb_sha256"], manifest["gds_sha256"]
    else:
        require(trial_layout is None, "Trial manifest is only valid for an explicit trial target")
    require(roles["odb"]["sha256"] == request["source_odb_sha256"]
            == native["target_odb_sha256"] == expected_odb
            and roles["gds"]["sha256"] == native["gds_sha256"] == expected_gds
            and roles["inventory"]["sha256"] == request["inventory_sha256"]
            and roles["sdc"]["sha256"] == draft.SDC_SHA, "Wrong exact target ODB, inventory or constraints")
    for key, role in (("odb", "odb"), ("def", "def"), ("nl", "netlist"), ("sdc", "sdc")):
        require(resolve_mount(mounts, seed[key]) == Path(roles[role]["path"])
                and request["input_sha256"][seed[key]] == roles[role]["sha256"], f"Wrong mounted seed {role}")
    for name, digest in request["input_sha256"].items():
        bind(pins, resolve_mount(mounts, name), digest)
    require(resolve_mount(mounts, "/work/views/actual-signal/inventory.json") == Path(roles["inventory"]["path"])
            and request["input_sha256"]["/work/views/actual-signal/inventory.json"] == roles["inventory"]["sha256"],
            "Mounted inventory is not the target inventory")
    reopen(pins, request["adapter"])
    require(request["adapter"]["path"] == str(Path(__file__).with_name("streaming_8x4_e982_eco_timing.py").resolve())
            and reopen(pins, request["rules_plan"])["sha256"] == draft.PLAN_SHA, "Timing producer or rule plan differs")
    manifest = reopen(pins, request["native_source_manifest"])
    source_receipt, package = draft.native_package(manifest["path"])
    require(source_receipt["image_id"] == IMAGE and request["native_package_sha256"] == package,
            "Native tool source and image binding differs")
    for name, digest in request["producer_sha256"].items():
        bind(pins, inputs / "producer" / name, digest)
    original_item = request["original_resolved"]
    original = read_bound(pins, original_item["path"], original_item["sha256"])
    inventory = read_bound(pins, roles["inventory"]["path"], roles["inventory"]["sha256"])
    receipt = read_bound(pins, roles["inventory_receipt"]["path"], roles["inventory_receipt"]["sha256"])
    require(receipt["database_sha256"] == request["source_odb_sha256"]
            and receipt["read_only_database"] is True
            and receipt["artifacts_sha256"]["inventory.json"] == request["inventory_sha256"],
            "Actual target inventory receipt differs")
    view = read_bound(pins, roles["views_receipt"]["path"], roles["views_receipt"]["sha256"])
    require(view["status"] == "pass" and view["target_odb_sha256"] == roles["odb"]["sha256"]
            and view["gds_sha256"] == roles["gds"]["sha256"]
            and all(view["view_sha256"][view_key] == roles[role]["sha256"] for view_key, role in
                    (("def", "def"), ("verilog", "netlist"), ("powered_verilog", "powered_netlist"))),
            "Canonical layout view receipt differs")
    observer_path = inputs / "observe.tcl"
    bind(pins, observer_path, request["observer_sha256"])
    source, expectation = observer.observer(inventory, request["source_odb_sha256"], request["inventory_sha256"])
    require(expectation == request["observer_expectation"] and observer_path.read_text() == source + HOLD_PROBE,
            "Native graph observer or exact hold probe differs")
    for model in draft.MODELS:
        bind(pins, inputs / "rules" / f"{model}.rules", draft.RULE_SHA[model])
        bind(pins, run / model / "invocation.json")
    for name in ("native-python.json", "native-passes.json"):
        bind(pins, run / name)
    passes = draft.checked_passes(run, {"request": request})
    context, disconnected = inventory_context(inventory)
    results = {model: completed_model(attempt, run, pins, request, original, seed, inventory, context,
                                      disconnected, model) for model in draft.MODELS}
    preflight_passed = all(result["spef_validation"]["status"] == "pass" and
                           all(row["annotation"]["status"] == "pass" for row in result["cases"].values())
                           for result in results.values())
    graph_ids = {result["spef_validation"].get("graph_sha256") for result in results.values()}
    bind(pins, Path(__file__).resolve())
    verify_pins(pins)
    return dict(schema=SCHEMA, status="diagnostic" if preflight_passed else "incomplete_readback",
                target_name=request["target_name"], target_odb_sha256=roles["odb"]["sha256"],
                target_gds_sha256=roles["gds"]["sha256"], target=roles, request=bind(pins, inputs / "request.json"),
                native_execution_completed=True, native_passes=passes, model_matrix=results,
                parasitics_preflight_passed=preflight_passed,
                distinct_extracted_spef_graphs=None if None in graph_ids else len(graph_ids),
                model_qualified=False, qualified_timing=False, tapeout_ready=False,
                scope="Three draft RC model copies crossed with the three pinned Liberty PVTs. "
                      "The selected path and ranked reports are samples, while violation counts are global. "
                      "Model admission, a qualified I/O contract and full timing closure remain separate.",
                verified_file_sha256=dict(sorted(pins.items())))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("attempt", type=Path)
    parser.add_argument("--request-sha256")
    parser.add_argument("--trial-layout", type=Path)
    args = parser.parse_args(argv)
    try:
        result = readback(args.attempt, args.request_sha256, args.trial_layout)
        output = args.attempt / "timing-readback.json"
        emit(output, result)
    except (OSError, ValueError, KeyError, TypeError, DecimalException) as exc:
        parser.exit(2, f"Draft timing readback rejected: {exc}\n")
    print(output)
    return 0 if result["parasitics_preflight_passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
