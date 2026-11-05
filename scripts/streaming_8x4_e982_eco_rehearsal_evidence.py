"""Independently reopen the retained physical evidence for the exact five-net ECO."""

import json
import math
from pathlib import Path
import re

from streaming_8x4_e982_eco_signoff import BASE_ROUTE_SHA, DEF_SHA, REVIEW_SHA, SCREEN_SHA, TARGET
from streaming_8x4_e982_native import IMAGE, ODB, TOP, normalized_gds
from streaming_8x4_enclosure_admission import (
    ENCLOSURE_GENERATOR, ENCLOSURE_RULES, ENCLOSURE_SUBSET, MAIN_DECK, MAIN_GENERATOR,
    drc_report, validate_antenna,
)
from streaming_8x4_geometry import template_pins
from streaming_8x4_power_grid import parse_log as parse_pg_log
from streaming_8x4_tt_rehearsal import (
    TT_CHECKS, UPSTREAM, VIEW_KEYS, file_record, integer_zero, local_path, native_scope, read_json, require,
)
from streaming_tt_layout import geometry_result
from streaming_tt_signoff import decode, selected_checks


ECO = "build/e982-fanout-20261104"
TRIAL = f"{ECO}/five-01"
SIGNOFF = f"{ECO}/signoff-01"
VIEWS = f"{SIGNOFF}/views"
OFFICIAL = f"{SIGNOFF}/official"
BASE_ROUTE = "build/e982-whole-route-20261104/native"
ODB_SHA, GDS_SHA = TARGET["odb_sha256"], TARGET["gds_sha256"]
PDK = "/work/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech"
ANTENNA_DECK = f"{PDK}/drc/rule_decks/antenna.drc"
LVS_DECK = f"{PDK}/lvs/sg13cmos5l.lvs"
LVS_SHA = "6cf97a068d69abd590cc441f64ef69d34ef50aef113c00023f2a1a94ccbe6e18"
ANTENNA_SHA = "85f6d5a6ec9224cd78d3705835006e5741ea5a5d431cda692a96c0ac62437f38"
EVIDENCE_PINS = {
    f"{TRIAL}/review.json": REVIEW_SHA,
    f"{TRIAL}/screen.json": SCREEN_SHA,
    f"{TRIAL}/execution.json": "917e9b5ddb90777666bd1599cb47409f753ab50371de3aa1af05267225d27ee1",
    f"{TRIAL}/container.log": "b4335e86d432ebec8f435d7665a4652a487efd16e8cadd0b1d6b6e53540728ae",
    f"{TRIAL}/stream/execution.json": "21ff53d13d7cea3b8ba83f09e9acd0e482dcb182b2d973e46b21b71704c310b6",
    f"{TRIAL}/reopen/execution.json": "2d3140be36c609466a66db83e4691ab1400426b249bca3daa40e885be5a92f00",
    f"{TRIAL}/reopen/result.json": "dd753e2ebaa0d0973977c6bb0aa8f45398512715fdbe9c64f67b737e7edb5625",
    f"{BASE_ROUTE}/execution.json": BASE_ROUTE_SHA,
    f"{SIGNOFF}/decision.json": "451f51bd3ca820d6d76ce4deb7bdfeae2a9d9e97ce4ad845c031e1320a3c317b",
    f"{VIEWS}/rehearsal-view-readback.json": "f3e019f5d4abf85e7d6f123c9d2f9d8282cca69e29b0e81e1db9ec34f048b045",
    f"{SIGNOFF}/eco-pin-geometry.json": "96b0c0f93fabb2df392cb9dde400b23bf12fcd107d40603dd00b219d6faf7fb2",
    f"{SIGNOFF}/cdl-independent-readback.json": "fcb297e6fa830a49d2790ae9efd825cff7836929033dea864211276fbc913316",
    f"{SIGNOFF}/layout/inputs/request.json": "079f23ec9f0afa3cff86065321abf49c2a6c02399f03221e900d9669e2c228af",
    f"{SIGNOFF}/layout/rehearsal-lvs-readback.json": "2518207acf1c17b1dfeece9533d155dc736d1abd6bbb6085aed8e3b7cf2a1428",
    f"{SIGNOFF}/pg/rehearsal-pg-readback.json": "869a4052c8ddd40d7bcf2a037f84856d1d4a00215ee4ae00cd2f0ea3de6ac81e",
    f"{OFFICIAL}/rehearsal-tt-precheck-readback.json": "dd3507c40f5e72f643c8f26a866f57e8d05fc83acb9f4bd5d911ff436bbce1ed",
    f"{OFFICIAL}/native-config.json": "1b538b307c4e99907e8d8157ec5662dc3ac7f05df60a1a84aad87a20ce922d2d",
    "tools/streaming-tt-signoff.json": "1899757179f032caffa456068bb7d5401b3bf596b674a618726fe2437a2e00e9",
}


class Evidence:
    def __init__(self, workspace, origin):
        self.workspace = Path(workspace).resolve(strict=True)
        self.origin = self.workspace if origin is None else Path(origin).absolute()
        self.files = {}

    def record(self, name, expected=None):
        name = Path(name)
        relative = (name.relative_to(self.origin) if name.is_absolute() else name).as_posix()
        path = local_path(self.workspace, relative)
        expected = expected or EVIDENCE_PINS.get(relative)
        if relative not in self.files:
            require(expected is not None, f"No reviewed digest for {relative}")
            self.files[relative] = file_record(self.workspace, relative, expected)
        require(expected is None or self.files[relative]["sha256"] == expected, f"Conflicting digest for {relative}")
        return self.files[relative]

    def path(self, name, expected=None):
        return self.workspace / self.record(name, expected)["path"]

    def read(self, name, expected=None):
        return read_json(self.path(name, expected))

    def artifacts(self, receipt):
        records = [self.record(item["path"], item["sha256"]) for item in receipt["artifacts"]]
        require(len(records) == len({item["path"] for item in records}), "Duplicate native artifact binding")
        return records

    def mounted(self, argv, source, destination):
        require(f"type=bind,source={self.origin / source},target={destination},readonly" in argv,
                f"Native input was not the exact read-only {source}")

    def unchanged(self):
        for item in self.files.values():
            file_record(self.workspace, item["path"], item["sha256"])


def exact_target(receipt):
    require(receipt["target_odb_sha256"] == ODB_SHA and receipt["gds_sha256"] == GDS_SHA,
            "Physical receipt targets a different ECO ODB or GDS")


def closed_execution(receipt):
    argv = receipt["argv"]
    require(receipt["status"] == "completed" and integer_zero(receipt["exit_code"])
            and receipt["container_termination"]["status"] == "absent"
            and receipt["container_termination"]["remaining"] == []
            and 0 < receipt["elapsed_seconds"] <= receipt["timeout_seconds"]
            and math.isfinite(receipt["timeout_seconds"]) and argv.count(IMAGE) == 1
            and argv[:4] == ["docker", "run", "--rm", "--pull"]
            and argv[argv.index("--network") + 1] == "none", "Native execution or cleanup did not close")
    return argv


def reopen_route(e):
    review = e.read(f"{TRIAL}/review.json")
    reopen = e.read(f"{TRIAL}/reopen/result.json")
    require(review["source_odb_sha256"] == ODB and review["trial_odb_sha256"] == reopen["target_odb_sha256"] == ODB_SHA
            and review["trial_def_sha256"] == DEF_SHA and review["router_checks_passed"] is True
            and review["net840_leaf_cut"] is True and review["strict_scope_passed"] is False
            and len(set(review["changed_unrelated_nets"])) == 19 and integer_zero(review["route_markers"])
            and not review["fanout_violations"] and not reopen["violators"]
            and reopen["highest_load_count"] == 8 and reopen["regular_signal_clock_nets"] == 44609,
            "Wrong router or independent fanout receipt")
    route = closed_execution(e.read(f"{TRIAL}/execution.json"))
    require(route[route.index(IMAGE) + 1:] == ["-exit", "-python", "/work/scripts/streaming_8x4_e982_fanout_trial.py"],
            "Unexpected ECO route invocation")
    stream = closed_execution(e.read(f"{TRIAL}/stream/execution.json"))
    e.mounted(stream, f"{TRIAL}/trial.def", "/work/export/design.def")
    require([f"--top", TOP] == stream[stream.index("--top"):stream.index("--top") + 2], "Wrong ECO streamout top")
    e.mounted(closed_execution(e.read(f"{TRIAL}/reopen/execution.json")), f"{TRIAL}/trial.odb", "/work/trial.odb")
    require(e.path(f"{TRIAL}/fanout.rpt", review["fanout_report_sha256"]).read_bytes() == b"", "Nonempty fanout report")
    log = e.path(f"{TRIAL}/container.log").read_text()
    require(re.findall(r"(?m)^\[INFO DRT-0199\] +Number of violations = (\d+)\.$", log)[-1:] == ["0"],
            "Final detailed-router markers are missing or nonzero")
    _, marker, antenna = log.partition("\ncheck_antennas\n")
    changed = re.findall(r"(?m)^check_antennas -net \{([^}]+)\}$", antenna)
    require(marker and changed == list(review["antenna_changed_nets"])
            and review["antenna_whole"] == "0" and set(review["antenna_changed_nets"].values()) == {"0"},
            "Wrong OpenROAD antenna scope")
    validate_antenna(antenna, explicit=False, count=1 + len(changed))
    return dict(status="pass", route_markers=0, fanout_limit=8, fanout_violations=0,
                checked_nets=44609, collateral_signal_nets=19), dict(status="pass", whole_block=True,
                scoped_nets=len(changed), net_violations=0, pin_violations=0)


def reopen_decks(e):
    decision = e.read(f"{SIGNOFF}/decision.json")
    exact_target(decision)
    require(decision["carry_forward_for_qualification"] is True and decision["promoted_for_release"] is False
            and decision["tapeout_ready"] is False and decision["def_sha256"] == DEF_SHA,
            "ECO decision has a different target or release scope")
    baseline = e.read(f"{BASE_ROUTE}/execution.json")
    require(baseline["image"] == IMAGE and baseline["deck_sha256"] == MAIN_DECK
            and baseline["frozen_inputs_unchanged"] is True, "Wrong pinned deck authority")
    screen = e.read(f"{TRIAL}/screen.json")
    require(screen["passed"] is True and screen["gds_sha256"] == GDS_SHA
            and screen["trial_odb_sha256"] == ODB_SHA and screen["trial_def_sha256"] == DEF_SHA,
            "Wrong geometry screen target")
    main = decision["drc"]
    require(main["status"] == "pass" and not main["markers"], "Native DRC readback failed")
    for role in ("artifact", "execution", "log"):
        e.record(main[role]["path"], main[role]["sha256"])
    require("KLayout DRC run for tables 'main' completed" in e.path(f"{TRIAL}/drc/container.log").read_text(),
            "Missing main-deck completion marker")
    rows = (("main_drc", "drc", "drc_sg13cmos5l.xml", MAIN_GENERATOR, 332, main["artifact"]["sha256"], main["execution"]["sha256"]),
            ("enclosure_subset", "enclosure", "enclosure.xml", ENCLOSURE_GENERATOR, 11,
             screen["checks"]["enclosure"]["report_sha256"], screen["checks"]["enclosure"]["execution_sha256"]),
            ("foundry_antenna", "foundry-antenna", "antenna.xml", ANTENNA_DECK, 23,
             screen["checks"]["foundry-antenna"]["report_sha256"], screen["checks"]["foundry-antenna"]["execution_sha256"]))
    results = {}
    for name, phase, report, generator, count, report_sha, execution_sha in rows:
        baseline_phase, = [row for row in baseline["phases"] if row["phase"] == phase]
        original = baseline_phase["argv"]
        argv = closed_execution(e.read(f"{TRIAL}/{phase}/execution.json", execution_sha))
        e.mounted(argv, f"{TRIAL}/stream/design.gds", "/work/export/design.gds")
        require(argv[argv.index(IMAGE) + 1:] == original[original.index(IMAGE) + 1:],
                f"Native {phase} deck invocation differs from the pinned authority")
        if phase == "enclosure":
            e.mounted(argv, f"{BASE_ROUTE}/maximal-enclosure-subset.drc", ENCLOSURE_GENERATOR)
            e.record(f"{BASE_ROUTE}/maximal-enclosure-subset.drc", ENCLOSURE_SUBSET)
        categories, markers = drc_report(e.path(f"{TRIAL}/{phase}/{report}", report_sha), generator)
        baseline_categories, _ = drc_report(e.path(f"{BASE_ROUTE}/{report}", baseline[f"{phase}_report_sha256"]), generator)
        require(categories == baseline_categories and len(categories) == count and not markers,
                f"Incomplete or failing raw {phase} report")
        require(phase != "drc" or "NW.b" in categories, "Missing NW.b from the main deck")
        require(phase != "enclosure" or categories == set(ENCLOSURE_RULES), "Wrong enclosure rule subset")
        results[name] = dict(status="pass", categories=count, markers=0)
    return results


def reopen_views(e):
    receipt = e.read(f"{VIEWS}/rehearsal-view-readback.json")
    exact_target(receipt)
    require(receipt["status"] == "pass" and receipt["view_sha256"]["def"] == DEF_SHA, "Wrong ECO canonical views")
    records = e.artifacts(receipt)
    names = {"def": "design.def", "lef": "official-format.lef", "cdl": "complete-reference.cdl",
             "nl": "signoff-views/implemented.v", "pnl": "signoff-views/implemented.power.v"}
    assets = {role: e.record(f"{VIEWS}/{filename}", receipt["view_sha256"][VIEW_KEYS[role]])
              for role, filename in names.items()}
    assets.update(odb=e.record(f"{TRIAL}/trial.odb", ODB_SHA), gds=e.record(f"{TRIAL}/stream/design.gds", GDS_SHA))
    native_scope(e.workspace, "views", receipt, records, assets, UPSTREAM)
    e.record(f"{TRIAL}/trial.def", DEF_SHA)
    native = e.read(f"{VIEWS}/native-report.json")
    exports = native["generated_files_sha256"]
    gds = e.path(assets["gds"]["path"])
    fresh = e.path(f"{VIEWS}/design.gds", exports["design.gds"])
    require(native["completed"] is True and native["source_odb_unchanged"] is True
            and native["source_odb_sha256"] == ODB_SHA and exports["design.def"] == DEF_SHA
            and normalized_gds(gds) == normalized_gds(fresh) == receipt["normalized_gds_sha256"],
            "Independent streamout disagrees with the exact ECO GDS")
    e.mounted(closed_execution(e.read(f"{VIEWS}/execution.json")), assets["odb"]["path"], "/work/target.odb")
    cdl = e.read(f"{SIGNOFF}/cdl-independent-readback.json")
    exact_target(cdl)
    require(cdl["verified"] is True and cdl["cdl_sha256"] == assets["cdl"]["sha256"]
            and cdl["instances"] == 98900 and cdl["terminal_bindings"] == 321974, "Wrong independent CDL result")
    for role in ("inventory", "top_cdl"):
        e.record(cdl[role]["path"], cdl[role]["sha256"])
    return assets, dict(status="pass", normalized_streamout_match=True, cdl_instances=98900,
                        cdl_terminal_bindings=321974), cdl["inventory"]["sha256"]


def reopen_pin_geometry(e, assets):
    check = e.read(f"{SIGNOFF}/eco-pin-geometry.json")
    exact_target(check)
    require(check["status"] == "pass", "ECO pin geometry failed")
    assets["allocation"] = e.record("physical/streaming_8x4/allocation.json", check["allocation_sha256"])
    allocation = e.read(assets["allocation"]["path"])
    template = e.path(f"{OFFICIAL}/tt/{allocation['template_path']}", allocation["template_sha256"])
    pins = template_pins(template.read_text())
    native_scope(e.workspace, "pin_geometry", check, [], assets, UPSTREAM)
    native = e.read(f"{VIEWS}/native-geometry.json")
    require(native["completed"] is True and native["input_sha256"]["/work/target.odb"] == ODB_SHA
            and native["input_sha256"]["/work/inputs/allocation.json"] == check["allocation_sha256"]
            and native["input_sha256"]["/work/inputs/tt_block_8x4_pgvdd.def"] == check["template_sha256"]
            and native["die_dbu"] == allocation["die_dbu"] and native["core_dbu"] == allocation["core_dbu"]
            and native["public_pins_dbu"] == {name: list(box) for name, box in pins.items()},
            "ODB geometry differs from the actual 8×4 template")
    measurement = check["measurement"]
    geometry = measurement["geometry"]
    require(measurement["top_level_cells"] == [TOP] and measurement["precision"] == 1e-9
            and measurement["unit"] == 1e-6 and geometry["top_bbox_um"] == [0, 0, 1724.16, 710.64],
            "Wrong GDS top, boundary or units")
    observed = {row["name"]: row for row in geometry["pins"]}
    require(observed.keys() == pins.keys(), "Wrong GDS signal pin membership")
    for name, (lx, ly, rx, ry) in pins.items():
        row = observed[name]
        center = [(lx + rx) / 2000, (ly + ry) / 2000]
        expected = dict(bounds_um=[lx / 1000, ly / 1000, rx / 1000, ry / 1000], center_um=center)
        labels = [label for label in geometry["top_labels"] if label["text"] == name]
        require(row["expected"] == expected and row["exact_pin_rectangle"] is True
                and row["exact_rectangle_count"] == row["label_count"] == 1 and row["exact_label"] is True
                and len(labels) == 1 and (labels[0]["layer"], labels[0]["texttype"]) == (50, 25)
                and all(abs(a - b) < 1e-6 for a, b in zip(labels[0]["origin"], center, strict=True)),
                f"GDS pin {name} differs from its official template location")
    return dict(status="pass", pins=43, tiles="8x4", boundary_um=[1724.16, 710.64])


def reopen_lvs(e, assets):
    out = f"{SIGNOFF}/layout"
    check = e.read(f"{out}/rehearsal-lvs-readback.json")
    exact_target(check)
    require(check["status"] == "pass" and check["deck_sha256"] == LVS_SHA, "Wrong LVS deck or result")
    records = e.artifacts(check)
    native_scope(e.workspace, "transistor_lvs", check, records, assets, UPSTREAM)
    request = e.read(f"{out}/inputs/request.json")
    require(request["source_odb_sha256"] == ODB_SHA and request["input_sha256"] == {
        "/input/actual.gds": GDS_SHA, "/input/actual.cdl": assets["cdl"]["sha256"],
        ANTENNA_DECK: ANTENNA_SHA, LVS_DECK: LVS_SHA}, "Native LVS request selected different physical inputs")
    argv = closed_execution(e.read(f"{out}/execution.json"))
    e.mounted(argv, assets["gds"]["path"], "/input/actual.gds")
    e.mounted(argv, assets["cdl"]["path"], "/input/actual.cdl")
    events = json.loads(e.path(f"{out}/native-journal.json").read_text())
    require(events == e.read(f"{out}/native-result.json")["events"] and [row["kind"] for row in events] == ["antenna", "lvs"]
            and all(integer_zero(row["exit_code"]) and "input=/input/actual.gds" in row["argv"] for row in events)
            and "schematic=/input/actual.cdl" in events[1]["argv"] and LVS_DECK in events[1]["argv"],
            "Missing or wrong exact native LVS run")
    result = e.read(f"{out}/lvs-result.json")["result"]
    log = e.path(f"{out}/lvs.native.log").read_text()
    require("Comparison in strict port mode" in log and len(result["circuits"]) == check["circuit_pairs"] == 37
            and all(row["status"] == "Match" and row["layout"] and row["schematic"] for row in result["circuits"])
            and result["layout_devices"] == result["schematic_devices"] == check["layout_devices"] == check["schematic_devices"] == 244,
            "LVS did not match all circuits in strict transistor and port mode")
    antenna = e.read(f"{out}/antenna-result.json")
    raw = e.path(f"{out}/antenna.xml", antenna["report_sha256"])
    result = geometry_result(raw, TOP, expected_categories=antenna["result"]["categories"])
    require(check["antenna_pass"] is True and result["passed"] is True
            and result["category_count"] == check["antenna_categories"] == 23,
            "LVS-associated antenna replay did not cover its complete rule inventory")
    return dict(status="pass", strict_ports=True, transistor_mode=True, circuit_pairs=37, foundry_antenna_categories=23)


def reopen_pg(e, assets, inventory_sha):
    out = f"{SIGNOFF}/pg"
    check = e.read(f"{out}/rehearsal-pg-readback.json")
    exact_target(check)
    require(check["status"] == "pass" and check["shorts_checked"] is False and check["ir_drop_qualified"] is False,
            "Wrong geometric rail status or scope")
    e.artifacts(check)
    e.mounted(closed_execution(e.read(f"{out}/execution.json")), assets["odb"]["path"], "/work/target.odb")
    native = e.read(f"{out}/native.json")
    leaf = e.read(f"{out}/leaf.json")
    log = e.path(f"{out}/openroad.log", leaf["log_sha256"]).read_text()
    rails = ("VGND", "VPWR")
    require(native["completed"] is True and native["canonical_inventory_rederived"] is True
            and native["source_odb_unchanged"] is True and native["geometric_open_path_connectivity"] is True
            and native["input_sha256"]["/work/target.odb"] == ODB_SHA
            and native["input_sha256"]["/work/pg/inputs/inventory.json"] == inventory_sha
            and native["inventory_totals"] == check["census_totals"]
            and leaf["completed"] is True and integer_zero(leaf["exit_code"])
            and set(native["rails"]) == set(check["rails"]) == set(rails)
            and [row["net"] for row in native["checks"]] == list(rails), "Incomplete exact-ODB PG native run")
    stats = parse_pg_log(log, rails)
    for index, row in enumerate(native["checks"]):
        rail = row["net"]
        counts = native["rails"][rail]
        name = f"rail-{index}-errors.rpt"
        require(row == dict(net=rail, argv=["check_power_grid", "-net", rail, "-error_file", f"/work/pg/{name}"],
                            catch_status=0, result="1", error_file=name, error_sha256=e.record(f"{out}/{name}")["sha256"],
                            error_bytes=0, floorplanning=False, dont_require_terminals=False)
                and e.path(f"{out}/{name}").read_bytes() == b""
                and len(counts["iterms"]) == counts["iterm_count"] == 98900
                and len(counts["bterms"]) == counts["bterm_count"] == 1
                and counts["skipped_iterms"] == counts["skipped_bpins"] == 0
                and check["rails"][rail] == dict(iterms=98900, bterms=1, psm=stats[rail]),
                f"Incomplete geometric rail connectivity for {rail}")
    return dict(status="pass", rails=check["rails"], shorts_checked=False, ir_drop_qualified=False)


def reopen_tt(e, assets):
    check = e.read(f"{OFFICIAL}/rehearsal-tt-precheck-readback.json")
    exact_target(check)
    require(check["status"] == "pass", "Pinned local Tiny Tapeout check failed")
    records = e.artifacts(check)
    assets["info_yaml"] = e.record("info.yaml", check["info_yaml_sha256"])
    native_scope(e.workspace, "tt_precheck", check, records, assets, UPSTREAM)
    lock = e.read("tools/streaming-tt-signoff.json")
    source = e.path(f"{OFFICIAL}/tt/precheck/precheck.py", lock["support_files"]["precheck/precheck.py"]["sha256"])
    require(check["support_revision"] == lock["support_commit"] and check["pdk_revision"] == lock["pdk_completion_revision"]
            and selected_checks(source.read_text(), UPSTREAM["pdk"]) == TT_CHECKS,
            "Pinned Tiny Tapeout source or selected check inventory differs")
    conf = e.read(f"{OFFICIAL}/native-config.json")
    original = e.origin / OFFICIAL
    staged = {"gds": f"{TOP}.gds", "lef": f"{TOP}.lef", "pnl": f"{TOP}.v", "info_yaml": "info.yaml"}
    for role, name in staged.items():
        e.record(f"{OFFICIAL}/design/{name}", assets[role]["sha256"])
    journal = [decode(line) for line in e.path(f"{OFFICIAL}/native-klayout.jsonl").read_text().splitlines()]
    require(conf["image_id"] == IMAGE and conf["out"] == str(original) and len(journal) == 6,
            "Pinned local Tiny Tapeout runtime or native journal differs")
    identities = set()
    for index, name in enumerate(("pin_label_purposes_overlapping_drawing", "sg13cmos5l", "zero_area")):
        intent, result = journal[2 * index:2 * index + 2]
        argv = intent["argv"]
        observed = check["native"]["reports"][name]
        report = original / f"tt/precheck/reports/drc_{name}.xml"
        require(intent["event"] == "intent" and result["event"] == "result" and intent["identity"] == result["identity"]
                and intent["identity"] not in identities and integer_zero(result["exit_code"])
                and result["seconds"] == observed["seconds"] and argv.count(IMAGE) == 1
                and argv[argv.index("--network") + 1] == "none"
                and f"org.pinwheel.signoff_owner={conf['owner']}" in argv
                and all(arg in argv for arg in (f"{name}=true", f"input={original / 'design' / staged['gds']}",
                                               f"report={report}", f"report_file={report}", "thr=1")),
                f"Incomplete or wrong native Tiny Tapeout invocation for {name}")
        identities.add(intent["identity"])
    return dict(status="pass", support_revision=check["support_revision"], checks=len(TT_CHECKS), native_klayout_runs=3)


def reopen_evidence(workspace: Path, *, origin: Path | None = None) -> dict:
    """Verify the preserved ECO receipts using only the workspace evidence mirror."""
    e = Evidence(workspace, origin)
    assets, views, inventory_sha = reopen_views(e)
    route, openroad_antenna = reopen_route(e)
    checks = dict(views=views, route=route, openroad_antenna=openroad_antenna, **reopen_decks(e),
                  pin_geometry=reopen_pin_geometry(e, assets), transistor_lvs=reopen_lvs(e, assets),
                  pg_connectivity=reopen_pg(e, assets, inventory_sha), tt_precheck=reopen_tt(e, assets))
    e.unchanged()
    return dict(target_odb_sha256=ODB_SHA, gds_sha256=GDS_SHA,
                views={name: {k: value[k] for k in ("path", "sha256")} for name, value in assets.items()},
                checks=checks, verified_file_sha256={path: item["sha256"] for path, item in sorted(e.files.items())})
