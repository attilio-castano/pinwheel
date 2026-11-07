"""Run physical checks on the exact November 7 hold/capacitance candidate."""

import argparse
from pathlib import Path
import time

from streaming_8x4_e982_native import (
    IMAGE, ROOT, TOP, bind, check_active_layout, checked_views, layout, local_inputs,
    read, require, run_native, sha, write,
)
from streaming_8x4_e982_eco_signoff import BASE_ROUTE_SHA, deck_args, pins
from streaming_8x4_enclosure_admission import (
    ENCLOSURE_GENERATOR, ENCLOSURE_RULES, ENCLOSURE_SUBSET, MAIN_GENERATOR, drc_report,
)

TRIAL = ROOT / "build/8x4-hold-cap-20261107/trial-02"
TARGET = dict(odb=TRIAL / "trial.odb", gds=TRIAL / "stream/design.gds",
              odb_sha256="dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73",
              gds_sha256="d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832")
EVIDENCE = {
    "connectivity-readback.json": "53f9d54453053d7d7f69cda953f012e24c2c062d29d2207915703ab19cc72b7f",
    "rail-readback.json": "fc07bcf4132faa8eac7f4928559cea9b0fae9916612de3d2539435793fb830d5",
    "views/rehearsal-view-readback.json": "1ffd35b51c7367380745356b78aaaeb9ec8b774cdd6723ab51f613b0c7c26729",
    "timing/timing-readback.json": "aaf351d84af3ae653a05999f8d5a402940596e0408abda69089f0e066cdba45c",
}


def setup(history):
    context = local_inputs(history, TRIAL)
    context["target"] = TARGET
    check_active_layout(context)
    for name, expected in EVIDENCE.items():
        pins(TRIAL / name, expected)
    checked_views(context)
    return context


def command(context, phase):
    if phase == "drc":
        return deck_args(context)
    source = context["source"]
    require(sha(source / "maximal-enclosure-subset.drc") == ENCLOSURE_SUBSET, "Enclosure deck changed")
    execution = pins(source / "execution.json", BASE_ROUTE_SHA)
    event, = [row for row in execution["phases"] if row["phase"] == "enclosure"]
    return event["argv"][event["argv"].index(IMAGE) + 1:]


def deck(context, phase, deadline):
    argv = command(context, phase)
    out = TRIAL / ("main-drc-01" if phase == "drc" else "enclosure-01")
    out.mkdir(parents=True, exist_ok=False)
    mounts = [(TARGET["gds"], "/work/export/design.gds", False)]
    if phase == "enclosure":
        mounts.append((context["source"] / "maximal-enclosure-subset.drc", ENCLOSURE_GENERATOR, False))
    run_native(context, out, "klayout", argv, mounts,
               3600 if phase == "drc" else 600, deadline)
    write(out / "readback.json", checked_deck(context, phase))


def checked_deck(context, phase):
    out = TRIAL / ("main-drc-01" if phase == "drc" else "enclosure-01")
    execution = read(out / "execution.json")
    argv = execution["argv"]
    require(execution["status"] == "completed" and execution["exit_code"] == 0
            and execution["container_termination"]["status"] == "absent"
            and argv[argv.index(IMAGE) + 1:] == command(context, phase)
            and argv[argv.index("--network") + 1] == "none"
            and f"type=bind,source={TARGET['gds']},target=/work/export/design.gds,readonly" in argv
            and f"type=bind,source={context['pdk']},target=/work/pdk,readonly" in argv,
            "Wrong or incomplete physical-check invocation")
    report = "drc_sg13cmos5l.xml" if phase == "drc" else "enclosure.xml"
    generator = MAIN_GENERATOR if phase == "drc" else ENCLOSURE_GENERATOR
    baseline, _ = drc_report(context["source"] / report, generator)
    categories, items = drc_report(out / report, generator)
    require(categories == baseline, "Physical rule coverage differs")
    if phase == "drc":
        require(len(categories) == 332 and "NW.b" in categories
                and "KLayout DRC run for tables 'main' completed" in (out / "container.log").read_text(),
                "Main-deck coverage or completion missing")
    else:
        require(set(categories) == set(ENCLOSURE_RULES), "Supplemental enclosure coverage differs")
        require(f"type=bind,source={context['source'] / 'maximal-enclosure-subset.drc'},"
                f"target={ENCLOSURE_GENERATOR},readonly" in argv, "Wrong mounted enclosure deck")
    check_active_layout(context)
    return dict(status="fail" if items else "pass", target_odb_sha256=TARGET["odb_sha256"],
                gds_sha256=TARGET["gds_sha256"], categories=sorted(categories), markers=dict(items),
                artifacts=[bind(out / name) for name in (report, "execution.json", "container.log")])


def checked_layout(context):
    views_root, view = checked_views(context)
    out = TRIAL / "layout"
    lvs = read(out / "rehearsal-lvs-readback.json")
    native = read(out / "native-result.json")
    execution = read(out / "execution.json")
    request = read(out / "inputs/request.json")
    require(execution["status"] == "completed" and execution["exit_code"] == 0
            and execution["container_termination"]["status"] == "absent"
            and [e["kind"] for e in native["events"]] == ["antenna", "lvs"]
            and all(e["exit_code"] == 0 for e in native["events"]), "Incomplete layout execution")
    argv = execution["argv"]
    require(argv[argv.index("--network") + 1] == "none" and argv[argv.index(IMAGE) + 1:] == [
        "-B", "/worker/scripts/streaming_8x4_signoff_execute.py", "native-layout",
        "--request", "/work/export/inputs/request.json"], "Wrong native layout invocation")
    for host, target in ((TARGET["gds"], "/input/actual.gds"),
                         (views_root / "complete-reference.cdl", "/input/actual.cdl"),
                         (context["pdk"], "/work/pdk")):
        require(f"type=bind,source={host},target={target},readonly" in argv, "Wrong layout input mount")
    expected_inputs = {"/input/actual.gds": TARGET["gds_sha256"],
                       "/input/actual.cdl": view["view_sha256"]["cdl"],
                       "/work/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/drc/rule_decks/antenna.drc":
                           "85f6d5a6ec9224cd78d3705835006e5741ea5a5d431cda692a96c0ac62437f38",
                       "/work/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/lvs/sg13cmos5l.lvs":
                           "6cf97a068d69abd590cc441f64ef69d34ef50aef113c00023f2a1a94ccbe6e18"}
    require(request["input_sha256"] == expected_inputs
            and request["source_odb_sha256"] == TARGET["odb_sha256"], "Wrong native layout request")
    for name, digest in request["producer_sha256"].items():
        require(sha(ROOT / name) == digest, "Layout worker source changed")
    require(lvs["target_odb_sha256"] == native["source_odb_sha256"] == TARGET["odb_sha256"]
            and lvs["gds_sha256"] == TARGET["gds_sha256"]
            and lvs["reference_cdl_sha256"] == view["view_sha256"]["cdl"]
            == sha(views_root / "complete-reference.cdl") and native["completed"] and native["inputs_unchanged"],
            "LVS target or complete CDL differs")
    for entry in lvs["artifacts"]:
        require(sha(ROOT / entry["path"]) == entry["sha256"], "LVS evidence changed")
    require("Selected NET_ONLY option: false" in (out / "lvs.native.log").read_text()
            and "Comparison in strict port mode" in (out / "lvs.native.log").read_text(),
            "Strict-port transistor LVS context missing")
    actual_lvs = read(out / "lvs-result.json")
    observed = actual_lvs["result"]
    require(actual_lvs["report_sha256"] == sha(out / "lvs.lvsdb")
            and observed["top"] == TOP and len(observed["circuits"]) == lvs["circuit_pairs"] == 39
            and {TOP, "sg13cmos5l_buf_2", "sg13cmos5l_dlygate4sd2_1"}
            <= {c["layout"] for c in observed["circuits"]}, "Wrong LVS report coverage")
    require(observed["passed"] == (lvs["status"] == "pass")
            and observed["passed"] == all(c["status"] == "Match" for c in observed["circuits"]),
            "Inconsistent LVS verdict")
    if observed["passed"]:
        require("Congratulations! Netlists match." in (out / "lvs.native.log").read_text(),
                "LVS success context missing")
    antenna = read(out / "antenna-result.json")
    baseline = read(ROOT / "build/e982-fanout-20261104/signoff-01/layout/antenna-result.json")
    require(antenna["result"]["categories"] == baseline["result"]["categories"]
            and antenna["report_sha256"] == sha(out / "antenna.xml")
            and lvs["antenna_categories"] == 23, "Foundry antenna coverage differs")
    require(antenna["result"]["passed"] == lvs["antenna_pass"]
            and antenna["result"]["passed"] == (antenna["result"]["violation_items"] == 0
                                                  and antenna["result"]["violation_multiplicity"] == 0),
            "Inconsistent foundry antenna verdict")
    return lvs, antenna


def decision(context):
    main, enclosure = (checked_deck(context, phase) for phase in ("drc", "enclosure"))
    lvs, antenna = checked_layout(context)
    passed = main["status"] == enclosure["status"] == lvs["status"] == "pass" and lvs["antenna_pass"]
    write(TRIAL / "physical-decision.json", dict(
        schema="pinwheel.hold-cap-physical-checks.v1", target_odb_sha256=TARGET["odb_sha256"],
        gds_sha256=TARGET["gds_sha256"], main_drc=main, enclosure=enclosure,
        lvs=lvs, foundry_antenna=antenna["result"], all_four_checks_passed=passed,
        native_producer_sha256=sha(__file__), carry_forward_for_qualification=passed,
        qualified_timing=False, electrical_power_qualified=False, tapeout_ready=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("drc", "enclosure", "lvs", "layout-readback", "decision"))
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--deadline", type=int, default=int(time.time()) + 7200)
    args = parser.parse_args()
    context = setup(args.history.resolve())
    if args.phase in {"drc", "enclosure"}:
        deck(context, args.phase, args.deadline)
    elif args.phase == "lvs":
        layout(context, args.deadline)
    elif args.phase == "layout-readback":
        lvs, antenna = checked_layout(context)
        write(TRIAL / "layout/independent-readback.json", dict(lvs=lvs, foundry_antenna=antenna["result"]))
    else:
        decision(context)


if __name__ == "__main__":
    main()
