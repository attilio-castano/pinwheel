"""Run and reopen physical checks on the exact five-net ECO derivative."""

import argparse
from collections import Counter
from pathlib import Path
import re

from streaming_8x4_e982_native import (
    IMAGE, ROOT, TOP, bind, check_active_layout, checked_views, layout, local_inputs,
    official, pg, read, require, run_native, sha, views, write,
)
from streaming_8x4_enclosure_admission import MAIN_DECK, MAIN_GENERATOR, def_components, drc_report


ECO_ROOT = ROOT / "build/e982-fanout-20261104"
TRIAL = ECO_ROOT / "five-01"
TARGET = {
    "odb": TRIAL / "trial.odb",
    "gds": TRIAL / "stream/design.gds",
    "odb_sha256": "e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9",
    "gds_sha256": "dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82",
}
DEF_SHA = "fbccaa1f145b74050eb5ff257db80cbdd9a3a1b56a530ab27a2d6ba9ad6d23ff"
SCREEN_SHA = "86eff28a562f4d51f3719f146e8529cb10db89c703bb8b87d8b992ab64e94170"
REVIEW_SHA = "34fe0a51cec73d9476887aefbdcfb8b118ff817fe848c09dfb063d9dd060c213"
BASE_INVENTORY_SHA = "00d4790acec3550a6a176566fae6abaa6f150903aeb2a6d4b640cf75dc1afd10"
BASE_ROUTE_SHA = "143ba01396beabbd43209d11c880f50a7583370f95331a03dff7215b8351ffc3"
RAILS = {"VDD": ("POWER", "VPWR"), "VSS": ("GROUND", "VGND")}


def pins(path, expected):
    require(path.is_file() and not path.is_symlink() and sha(path) == expected,
            f"Evidence is missing or changed: {path}")
    return read(path)


def setup(history, work):
    require(work.is_relative_to(ECO_ROOT) and work != ECO_ROOT, "Use a local ignored ECO output path")
    context = local_inputs(history, work)
    context["target"] = TARGET
    check_active_layout(context)
    require(sha(TRIAL / "trial.def") == DEF_SHA, "Exact ECO DEF changed")
    screen = pins(TRIAL / "screen.json", SCREEN_SHA)
    review = pins(TRIAL / "review.json", REVIEW_SHA)
    require(screen["passed"] and review["router_checks_passed"] and not review["fanout_violations"]
            and screen["trial_odb_sha256"] == review["trial_odb_sha256"] == TARGET["odb_sha256"]
            and screen["trial_def_sha256"] == review["trial_def_sha256"] == DEF_SHA
            and screen["gds_sha256"] == TARGET["gds_sha256"], "Existing ECO gates refer to a different layout")
    return context


def deck_args(context):
    execution = pins(context["source"] / "execution.json", BASE_ROUTE_SHA)
    phase, = [row for row in execution["phases"] if row["phase"] == "drc"]
    argv = phase["argv"][phase["argv"].index(IMAGE) + 1:]
    deck = context["pdk"] / MAIN_GENERATOR.removeprefix("/work/pdk/")
    require(sha(deck) == execution["deck_sha256"] == MAIN_DECK and argv[argv.index("-r") + 1] == MAIN_GENERATOR,
            "Pinned main DRC deck or invocation changed")
    return argv


def main_drc(context, deadline, out):
    out.mkdir(parents=True, exist_ok=False)
    run_native(context, out, "klayout", deck_args(context),
               [(TARGET["gds"], "/work/export/design.gds", False)], 3600, deadline)


def checked_drc(context, out):
    execution = read(out / "execution.json")
    argv = execution["argv"]
    offset = argv.index(IMAGE)
    require(execution["status"] == "completed" and execution["exit_code"] == 0
            and execution["container_termination"]["status"] == "absent"
            and argv[offset + 1:] == deck_args(context)
            and argv[argv.index("--network") + 1] == "none"
            and f"type=bind,source={TARGET['gds']},target=/work/export/design.gds,readonly" in argv
            and f"type=bind,source={context['pdk']},target=/work/pdk,readonly" in argv,
            "Incomplete main-deck execution or wrong mounted ECO inputs")
    report = out / "drc_sg13cmos5l.xml"
    baseline, _ = drc_report(context["source"] / report.name, MAIN_GENERATOR)
    categories, items = drc_report(report, MAIN_GENERATOR)
    log = (out / "container.log").read_text()
    require(categories == baseline and len(categories) == 332 and "NW.b" in categories
            and "KLayout DRC run for tables 'main' completed" in log, "Incomplete main-deck rule coverage")
    check_active_layout(context)
    return dict(status="fail" if items else "pass", categories=len(categories), markers=dict(items),
                artifact=bind(report), execution=bind(out / "execution.json"), log=bind(out / "container.log"))


def pg_pins(instance):
    return {pin: (terminal["signal_type"], terminal["net"])
            for pin, terminal in instance["terminals"].items() if terminal["signal_type"] in {"POWER", "GROUND"}}


def special_records(path):
    data = path.read_bytes()
    sections = re.findall(rb"(?ms)^SPECIALNETS 2 ;\n.*?^END SPECIALNETS\n", data)
    require(len(sections) == 1, f"Expected exactly two special nets in {path}")
    return sections[0]


def placements(path):
    _, components = def_components(path)
    positions = {}
    for name, (master, record) in components.items():
        if master.startswith(b"sg13cmos5l_decap_") or name.startswith(b"eco_net"):
            match = re.search(rb"\+ (?:PLACED|FIXED) \( (-?\d+) (-?\d+) \)", record)
            require(match is not None, "Missing placed decap/buffer coordinates")
            positions[name.decode()] = (master.decode(), int(match[1]), int(match[2]))
    return positions


def checked_power(context):
    views_root, view_report = checked_views(context)
    out = context["work"] / "pg"
    report_path = out / "rehearsal-pg-readback.json"
    report = read(report_path)
    require(report["status"] == "pass" and report["target_odb_sha256"] == TARGET["odb_sha256"]
            and report["gds_sha256"] == TARGET["gds_sha256"]
            and set(report["rails"]) == {"VPWR", "VGND"}
            and all(rail["iterms"] == 98900 and rail["bterms"] == 1 for rail in report["rails"].values()),
            "Incomplete exact ECO power-grid readback")
    for entry in report["artifacts"]:
        require(sha(ROOT / entry["path"]) == entry["sha256"], "ECO power evidence changed")
    baseline = pins(ROOT / "build/tt-rehearsal-20261104/views/actual-signal/inventory.json", BASE_INVENTORY_SHA)
    actual_root = views_root / "actual-signal"
    exporter = read(actual_root / "receipt.json")
    actual = pins(actual_root / "inventory.json", exporter["artifacts_sha256"]["inventory.json"])
    require(exporter["database_sha256"] == TARGET["odb_sha256"] and actual["top"] == baseline["top"] == TOP
            and actual["power_bterms"] == baseline["power_bterms"], "Power census target or ports differ")
    old, new = baseline["instances"], actual["instances"]
    removed, added = sorted(old.keys() - new.keys()), sorted(new.keys() - old.keys())
    require(len(old) == len(new) == 98900 and len(added) == len(removed) == 5
            and all(old[name]["master"] == "sg13cmos5l_decap_4" and pg_pins(old[name]) == RAILS for name in removed)
            and all(new[name]["master"] == "sg13cmos5l_buf_1" and pg_pins(new[name]) == RAILS for name in added)
            and all(old[name]["master"] == new[name]["master"] and pg_pins(old[name]) == pg_pins(new[name])
                    for name in old.keys() & new.keys()), "Unexpected rail-terminal or cell delta")
    trial_def = views_root / "design.def"
    require(sha(trial_def) == view_report["view_sha256"]["def"] == DEF_SHA
            and special_records(trial_def) == special_records(context["source"] / "design.def"),
            "Exact ECO DEF or special-net geometry differs")
    positions = placements(trial_def)
    decap = [(x, y) for master, x, y in positions.values() if master.startswith("sg13cmos5l_decap_")]
    nearby = {}
    for name in added:
        _, x, y = positions[name]
        distances = [max(abs(x - dx), abs(y - dy)) for dx, dy in decap]
        nearby[name] = {"nearest_origin_dbu": min(distances), "remaining_origins_within_10000_dbu":
                        sum(value <= 10000 for value in distances)}
    return dict(status="pass", rails=report["rails"], unchanged_special_net_geometry=True,
                decaps_removed=removed, buffers_added=added, local_decap_inventory=nearby,
                baseline_decap_counts=dict(Counter(row["master"] for row in old.values()
                                                   if row["master"].startswith("sg13cmos5l_decap_"))),
                eco_decap_counts=dict(Counter(row["master"] for row in new.values()
                                              if row["master"].startswith("sg13cmos5l_decap_"))),
                dynamic_droop_qualified=False, ir_drop_qualified=False, artifact=bind(report_path))


def decision(context, drc_out):
    drc = checked_drc(context, drc_out)
    power = checked_power(context)
    views_root, view_report = checked_views(context)
    report_path = context["work"] / "layout/rehearsal-lvs-readback.json"
    lvs = read(report_path)
    for entry in lvs["artifacts"]:
        require(sha(ROOT / entry["path"]) == entry["sha256"], "ECO LVS evidence changed")
    require(lvs["target_odb_sha256"] == TARGET["odb_sha256"] and lvs["gds_sha256"] == TARGET["gds_sha256"]
            and lvs["reference_cdl_sha256"] == view_report["view_sha256"]["cdl"]
            and lvs["reference_cdl_sha256"] == sha(views_root / "complete-reference.cdl")
            and "Comparison in strict port mode" in (report_path.parent / "lvs.native.log").read_text(),
            "LVS target, complete CDL or strict port mode differs")
    review = pins(TRIAL / "review.json", REVIEW_SHA)
    passed = (drc["status"] == power["status"] == lvs["status"] == "pass" and lvs["antenna_pass"] is True)
    write(context["work"] / "decision.json", dict(schema="pinwheel.e982-fanout-eco-physical-review.v1",
          target_odb_sha256=TARGET["odb_sha256"], gds_sha256=TARGET["gds_sha256"], def_sha256=DEF_SHA,
          drc=drc, power=power, lvs={key: lvs[key] for key in ("status", "circuit_pairs", "layout_devices",
                                                             "schematic_devices", "antenna_pass")},
          lvs_receipt=bind(report_path), collateral_signal_wires=len(review["changed_unrelated_nets"]),
          carry_forward_for_qualification=passed, promoted_for_release=False, tapeout_ready=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("drc", "views", "pg", "lvs", "official", "decision"))
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--deadline", type=int, required=True)
    parser.add_argument("--drc-run", type=Path, help="Reopen an existing exact-target main-deck execution")
    args = parser.parse_args()
    work = args.work.resolve()
    context = setup(args.history.resolve(), work)
    drc_out = (args.drc_run or work / "drc").resolve()
    require(drc_out.is_relative_to(ECO_ROOT) and drc_out != ECO_ROOT, "Use a local ignored main-deck run directory")
    if args.phase == "drc":
        main_drc(context, args.deadline, drc_out)
    elif args.phase == "decision":
        decision(context, drc_out)
    else:
        {"views": views, "pg": pg, "lvs": layout, "official": official}[args.phase](context, args.deadline)


if __name__ == "__main__":
    main()
