"""Reopen DC rail voltages, resolved sources and the CMOS5L current screen."""

import argparse
import csv
import math
from pathlib import Path
import re

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, sha, write
from streaming_8x4_hold_cap_activity import observed_pins
from streaming_8x4_hold_cap_ir import CORNER, VOLTAGES
from streaming_8x4_hold_cap_physical import EVIDENCE, TARGET, TRIAL, setup
from streaming_8x4_hold_cap_timing_coverage import prepare


DBU = 1000
SHEET = {"Metal1": 0.135, "Metal2": 0.103, "Metal3": 0.103, "Metal4": 0.103}
VIA = {("Metal1", "Metal2"): ("Via1", 2), ("Metal2", "Metal3"): ("Via2", 8),
       ("Metal3", "Metal4"): ("Via3", 16)}
PROCESS_SPEC = {
    "revision": "0.2, December 15, 2025, §3.5 and Appendix A.v",
    "sha256": "26e28c28024411a98b7f3dd586f2c4c8bba832904e5a75935cebeb3264b378cd",
    "url": "https://github.com/IHP-GmbH/IHP-Open-PDK/blob/2bbec755dc67ca3db0261c3d6163e15735d66710/"
           "ihp-sg13cmos5l/libs.doc/doc/SG13CMOS5L_os_process_spec.pdf#page=19",
    "reference_temperature_c": 105,
    "reference_lifetime_years": 11,
}


def metal_limit_ma(layer, width_um):
    minimum, knee, density = (0.16, 0.36, 1.0) if layer == "Metal1" else (0.20, 0.30, 2.0)
    if width_um < minimum:
        return None
    return density * max(width_um, knee)


def csv_rows(stream, header):
    rows = csv.reader(stream)
    require(next(rows) == header.split(","), "Unexpected native CSV schema")
    return rows


def node(name):
    kind, layer, x, y = name.split("_")
    return kind, layer, int(x), int(y)


def update(group, sample, limit):
    group["edges"] += 1
    if group["max_current"] is None or sample["current_ma"] > group["max_current"]["current_ma"]:
        group["max_current"] = sample
    if limit is None:
        group["outside_table"] += 1
        if group["max_outside_table"] is None or sample["current_ma"] > group["max_outside_table"]["current_ma"]:
            group["max_outside_table"] = sample
        return
    ratio = sample["current_ma"] / limit
    group["over_limit"] += ratio > 1
    if group["max_utilization"] is None or ratio > group["max_utilization"]["ratio"]:
        group["max_utilization"] = dict(sample, ratio=ratio, comparison_limit_ma=limit)


def electrical_edges(path, rail, sheet, cut):
    groups = {}
    sources = []
    loads = []
    terminal_edges = 0
    with (path / f"{rail}.spice").open() as spice, (path / f"{rail}-current.csv").open() as current:
        rows = csv_rows(current, "Node0 Layer,Node0 X location,Node0 Y location,Node1 Layer,Node1 X location,"
                                 "Node1 Y location,Current")
        for line in spice:
            if line.startswith("V"):
                _, name, reference, kind, voltage = line.split()
                require(reference == "0" and kind == "DC" and float(voltage) == VOLTAGES[rail],
                        "Unexpected resolved DC source")
                sources.append(node(name))
            if line.startswith("I"):
                _, name, reference, kind, amps = line.split()
                value = float(amps)
                require(reference == "0" and kind == "DC" and node(name)[0] == "ITermNode"
                        and math.isfinite(value) and value > 0, "Unexpected exported DC load")
                loads.append(value)
            if not line.startswith("R"):
                continue
            _, a, b, resistance = line.split()
            kind_a, layer_a, x_a, y_a = node(a)
            kind_b, layer_b, x_b, y_b = node(b)
            if (kind_a, kind_b) != ("Node", "Node"):
                require({kind_a, kind_b} & {"ITermNode", "BPinNode"}, "Unknown non-geometric resistor")
                terminal_edges += 1
                continue
            x0, y0, x1, y1 = (coordinate / DBU for coordinate in (x_a, y_a, x_b, y_b))
            layer0, xc0, yc0, layer1, xc1, yc1, value = next(rows)
            require((layer0, layer1) == (layer_a, layer_b)
                    and tuple(map(float, (xc0, yc0, xc1, yc1))) == (x0, y0, x1, y1),
                    "Current and SPICE endpoints differ")
            current_ma = float(value) * 1000
            ohm = float(resistance.removeprefix("R="))
            require(math.isfinite(current_ma) and current_ma >= 0 and math.isfinite(ohm) and ohm > 0,
                    "Invalid native electrical value")
            sample = dict(current_ma=current_ma, from_um=[x0, y0], to_um=[x1, y1])
            if layer_a == layer_b:
                length_dbu = max(abs(x_b - x_a), abs(y_b - y_a))
                width_dbu = sheet[layer_a] * length_dbu / ohm
                require(width_dbu > 0 and abs(width_dbu - round(width_dbu)) <= 0.01,
                        f"Cannot recover model width from resistor {a} {b}")
                layer = layer_a
                width = round(width_dbu) / DBU
                sample["effective_width_um"] = width
                limit = metal_limit_ma(layer, width)
            else:
                layer, expected_cuts = VIA[layer_a, layer_b]
                cuts = cut[layer] / ohm
                require(abs(cuts - expected_cuts) <= 1e-4, "Model via cut inventory differs")
                sample.update(cuts=expected_cuts, equal_share_ma_per_cut=current_ma / expected_cuts)
                limit = expected_cuts * 0.4
            group = groups.setdefault(layer, dict(edges=0, over_limit=0, outside_table=0, max_current=None,
                                                   max_utilization=None, max_outside_table=None))
            update(group, sample, limit)
        require(next(rows, None) is None and set(groups) == set(sheet) | set(cut), "Incomplete edge join")
    return groups, terminal_edges, sources, loads


def rail_rectangles(lef):
    lef_text = lef.read_text()
    result = {}
    for rail in VOLTAGES:
        section = lef_text.split(f"  PIN {rail}\n", 1)[1].split(f"  END {rail}\n", 1)[0]
        require(set(re.findall(r"^\s*LAYER (\w+)\s*;", section, re.M)) == {"Metal4"},
                "Expected only Metal4 on the power terminal")
        result[rail] = [tuple(map(float, rectangle.split()))
                        for rectangle in re.findall(r"^\s*RECT ([\d. ]+) ;$", section, re.M)]
        require(result[rail], f"Missing exported shapes for {rail}")
    return result


def check_sources(rail, sources, requested, rectangles, expected_nodes=None):
    require(len(sources) == len(set(sources)) > 0, "Repeated or absent source node")
    actual = {(x / DBU, y / DBU) for kind, layer, x, y in sources if (kind, layer) == ("Node", "Metal4")}
    require(len(actual) == len(sources), "Unexpected source layer")

    def contained(x, y, radius):
        return any(x0 <= x - radius <= x + radius <= x1 and y0 <= y - radius <= y + radius <= y1
                   for x0, y0, x1, y1 in rectangles)

    require(all(contained(x, y, 0) for x, y in actual), "Source node lies outside its exported rail shapes")
    if expected_nodes is not None:
        require(requested is not None and actual == {tuple(point) for point in expected_nodes},
                "Parent source solve selected a different set of nodes")
    elif requested is not None:
        contacts = [tuple(map(float, line.split(","))) for line in Path(requested["path"]).read_text().splitlines()]
        require(len(contacts) == 4 and all(size == 1 and voltage == VOLTAGES[rail] and contained(x, y, size / 2)
                                         for x, y, size, voltage in contacts),
                "Wrong sparse contact geometry or supply")
        require(actual == {(x, y) for x, y, _, _ in contacts}, "Sparse sources snapped or selected extra nodes")
    else:
        require(len(actual) == 5215, "Wrong distributed source census")
    return dict(count=len(actual), sparse_centers_um=sorted(actual) if requested else None)


def instance_voltages(path, rail, terminals):
    values = {}
    with (path / f"{rail}-voltage.csv").open() as stream:
        for instance, terminal, layer, x, y, voltage in csv_rows(
                stream, "Instance,Terminal,Layer,X location,Y location,Voltage"):
            key = (instance, terminal)
            require(key in terminals and instance not in values and layer == "Metal1",
                    "Unexpected terminal voltage row")
            values[instance] = float(voltage)
    require(len(values) == len(terminals) == 98904 and all(math.isfinite(v) for v in values.values()),
            "Incomplete rail terminal voltages")
    return values


def reopen_case(path, expected, inventory, rects, workload, unused_drivers):
    result = read(path / "readback.json")
    request = read(path / "request.json")
    execution = read(path / "execution.json")
    require(result["status"] == "completed" and bound(path / "request.json") == result["request"]
            and execution["exit_code"] == 0 and execution["status"] == "completed"
            and execution["container_termination"]["status"] == "absent",
            "Incomplete native case or cleanup")
    require(all(bound(item["path"]) == item for item in result["artifacts"] + [request["analysis_tcl"]]
                + list(request["inputs"].values())), "Native result artifact changed")
    require(request["inputs"]["/input/trial.odb"]["sha256"] == TARGET["odb_sha256"]
            and request["target_gds_sha256"] == TARGET["gds_sha256"] and request["rail_voltages_v"] == VOLTAGES
            and request["clock_period_ns"] == 20 and request["corner"] == CORNER
            and request["inputs"]["/input/core.sdc"]["sha256"] == expected["/work/inputs/core.sdc"]
            and request["inputs"]["/input/typ.spef"]["sha256"] ==
                next(digest for name, digest in expected.items() if name.endswith(".spef"))
            and request["liberty"] == {name: digest for name, digest in expected.items() if name.endswith(".lib")},
            "Case input differs from the exact typical diagnostic")
    log = (path / "container.log").read_text()
    require(not re.search(r"^\[ERROR ", log, re.M), "OpenROAD reported an error")
    metrics = read(path / "metrics.json")
    power = read(path / "power.json")["Total"]
    require(power["total"] == result["power_w"] and power["total"] > 0, "Vacuous power report")
    parasitics = (path / "parasitics.rpt").read_text().splitlines()
    require(parasitics == ["Found 282 unannotated drivers.", *[f" {name}" for name in unused_drivers],
                           "Found 0 partially unannotated drivers."], "Unexpected native parasitic annotation")
    annotated_count = None
    if request["activity"]["kind"] == "functional_vcd":
        require(request["inputs"]["/input/activity.vcd"] == workload["artifacts"]["activity.vcd"]
                and request["activity"]["scope"] == workload["waveform"]["scope"] == "streaming_quad_host_bridge/dut",
                "Wrong bound workload activity")
        pins, _ = observed_pins(inventory)
        expected_pins = {f"{name}/{pin}" for name, pin in pins} | inventory["public_bterms"].keys()
        activity = (path / "activity.rpt").read_text()
        names = re.findall(r"^\s+vcd (\S+)$", activity, re.M)
        require(len(names) == len(expected_pins) == 124219 and set(names) == expected_pins
                and re.search(r"^unannotated\s+0$", activity, re.M)
                and activity.split("Unannotated pins:", 1)[1].strip() == "",
                "Native VCD does not annotate the complete signal inventory")
        annotated_count = len(names)
    sheet = {layer: value * request.get("sheet_resistance_scale", {}).get(layer, 1) for layer, value in SHEET.items()}
    cut = {layer: 20.0 for layer, _ in VIA.values()}
    resistances = {name: float(value) for name, value in re.findall(r"^  (\w+): (\S+) Ohm per (?:square|cut)$", log, re.M)}
    require(all(math.isclose(resistances[layer], value, rel_tol=5e-6)
                for layer, value in (sheet | cut).items()), "Solver resistance differs from declared assumptions")
    expected_parent_nodes = {}
    parent_binding = {}
    if "parent_contacts" in request:
        from streaming_8x4_hold_cap_parent_power import check_resolved

        parent, item = check_resolved(Path(request["parent_contacts"]["path"]))
        require(item == request["parent_contacts"]
                and {rail: value["external_ohm"] for rail, value in parent["rails"].items()} == request["external_ohm_per_source"]
                and all(request["inputs"][f"/input/{rail}.vsrc"] == value["vsrc"] for rail, value in parent["rails"].items()),
                "Native case does not bind the resolved parent boundary")
        native_resistance = re.findall(r"^PINWHEEL_DC_EXTERNAL_OHM (\w+) (\S+)$", log, re.M)
        require(len(native_resistance) == len(VOLTAGES)
                and {rail: float(value) for rail, value in native_resistance} == request["external_ohm_per_source"]
                and [float(value) for _, value in native_resistance] == sorted(float(value) for _, value in native_resistance),
                "Series resistance command or application order differs")
        expected_parent_nodes = {rail: value["nodes_um"] for rail, value in parent["rails"].items()}
        parent_binding["parent_contacts"] = item
    require(request.get("expected_source_nodes_um", {}) == expected_parent_nodes, "Source node expectation changed")
    rails, volts = {}, {}
    for rail in VOLTAGES:
        run_log = log.split(f"PINWHEEL_DC_BEGIN {rail}\n", 1)[1].split(f"PINWHEEL_DC_END {rail}\n", 1)[0]
        require(not (path / f"{rail}-errors.rpt").exists() or (path / f"{rail}-errors.rpt").stat().st_size == 0,
                "PSM reported disconnected geometry")
        groups, terminal_edges, sources, loads = electrical_edges(path, rail, sheet, cut)
        load_ma = math.fsum(loads) * 1000
        require(loads and math.isclose(load_ma, power["total"] / VOLTAGES["VPWR"] * 1000, rel_tol=5e-4),
                "Exported PSM loads do not agree with the total power model")
        expected_nodes = expected_parent_nodes.get(rail)
        source_data = check_sources(rail, sources, request["inputs"].get(f"/input/{rail}.vsrc"), rects[rail], expected_nodes)
        require(set(map(int, re.findall(r"^Source nodes: (\d+)$", run_log, re.M))) == {source_data["count"]},
                "Native source count differs from resolved SPICE source map")
        terminal_set = {(name, pin) for name, inst in inventory["instances"].items()
                        for pin, term in inst["terminals"].items() if term["net"] == rail}
        volts[rail] = instance_voltages(path, rail, terminal_set)
        worst = metrics[f"design_powergrid__drop__worst__net:{rail}__corner:{CORNER}"]
        max_current = metrics[f"design_powergrid__current__max__net:{rail}__corner:{CORNER}"]
        require(math.isfinite(worst) and worst > 0
                and math.isclose(max_current * 1000, max(g["max_current"]["current_ma"] for g in groups.values()),
                                 rel_tol=5e-4), "Native current or voltage summary differs")
        rails[rail] = dict(worst_drop_mv=worst * 1000, source=source_data, segments=groups,
                           max_current_ma=max_current * 1000, excluded_terminal_edges=terminal_edges,
                           exported_loads=len(loads), exported_load_ma=load_ma)
    worst_inst = min(volts["VPWR"], key=lambda name: volts["VPWR"][name] - volts["VGND"][name])
    return dict(case=path.name, request=bound(path / "request.json"), native=bound(path / "readback.json"),
                power_w=power, modeled_rail_load_ma=power["total"] / VOLTAGES["VPWR"] * 1000,
                sheet_temperature_c=request.get("sheet_temperature_c", 25), activity=request["activity"],
                vcd_annotated_pins=annotated_count, external_ohm_per_source=request["external_ohm_per_source"],
                rails=rails, minimum_instance_differential_v=volts["VPWR"][worst_inst] - volts["VGND"][worst_inst],
                worst_instance=worst_inst, elapsed_seconds=execution["elapsed_seconds"], **parent_binding)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--workload", type=Path, action="append", default=[],
                        help="Additional checked waveform receipt for these cases")
    parser.add_argument("cases", type=Path, nargs="+")
    args = parser.parse_args()
    out = args.out.resolve()
    root = TRIAL / "power-dc"
    paths = [path.resolve(strict=True) for path in args.cases]
    require(out.parent == root and not out.exists() and all(path.parent == root for path in paths)
            and len(set(paths)) == len(paths), "Use existing cases and a fresh readback in power-dc")
    context = setup(args.history.resolve(strict=True))
    rows, layout, _, _ = prepare(context)
    row, = [row for row in rows if row["model"] == "TYP" and row["corner"] == CORNER]
    inventory = read(layout["inventory"]["path"])
    views = read(TRIAL / "views/rehearsal-view-readback.json")
    lef = TRIAL / "views/official-format.lef"
    require(sha(lef) == views["view_sha256"]["lef"], "Exported macro LEF changed")
    rects = rail_rectangles(lef)
    timing = TRIAL / "timing/timing-readback.json"
    require(sha(timing) == EVIDENCE["timing/timing-readback.json"], "Timing annotation receipt changed")
    unused = read(timing)["model_matrix"]["TYP"]["cases"][CORNER]["annotation"]["unused_drivers"]
    workload_path = TRIAL / "workload-activity-01/receipt.json"
    by_vcd_path = {}
    workload_bindings = []
    for path in [workload_path, *args.workload]:
        item = bound(path)
        workload = read(path)
        vcd = workload["artifacts"]["activity.vcd"]
        require(workload["target_odb_sha256"] == TARGET["odb_sha256"]
                and workload["target_gds_sha256"] == TARGET["gds_sha256"]
                and workload["all_public_observations_replayed"] is True and workload["waveform"]["clock_period_ps"] == 20000
                and workload["waveform"]["actual_signal_pins_declared"] == 124176 and bound(vcd["path"]) == vcd
                and bound(path) == item and vcd["path"] not in by_vcd_path, "Invalid or repeated activity replay receipt")
        by_vcd_path[vcd["path"]] = workload
        workload_bindings.append(item)
    cases = []
    for path in paths:
        activity = read(path / "request.json")["inputs"].get("/input/activity.vcd")
        require(activity is None or activity["path"] in by_vcd_path, "Pass a receipt for every additional waveform")
        workload = by_vcd_path[activity["path"]] if activity is not None else None
        cases.append(reopen_case(path, row["input_sha256"], inventory, rects, workload, unused))
    report = dict(schema="pinwheel.streaming-8x4-hold-cap-ir-em.v1", status="diagnostic", cases=cases,
                  target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
                  process_spec=PROCESS_SPEC, workload=workload_bindings[0], lef=bound(lef), inventory=layout["inventory"],
                  qualified_ir_drop=False, qualified_em=False, transient_droop_analyzed=False)
    if args.workload:
        report["additional_workloads"] = workload_bindings[1:]
    write(out, report)


if __name__ == "__main__":
    main()
