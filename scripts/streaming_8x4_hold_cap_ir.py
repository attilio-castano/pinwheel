"""Solve both DC supply grids on the frozen 8×4 under explicit local assumptions."""

import argparse
from pathlib import Path
import re
import time

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import IMAGE, TOP, read, require, run_native, sha, write
from streaming_8x4_hold_cap_physical import TARGET, TRIAL, setup
from streaming_8x4_hold_cap_timing_coverage import prepare


OPENROAD = "dcf36133a369abc8f3c5e5738cd4d82e4903c0e0"
CORNER = "nom_typ_1p20V_25C"
VOLTAGES = {"VPWR": 1.2, "VGND": 0.0}
SHEET_TC = {"Metal1": 0.0034, "Metal2": 0.0035, "Metal3": 0.0035, "Metal4": 0.0035}
TCL = """\
if {[catch {
    define_corners @CORNER@
@LIBRARIES@
    read_db /input/trial.odb
    if {[[ord::get_db_block] getName] ne "@TOP@"} {error "Wrong OpenDB top"}
    set_cmd_units -time ns -capacitance pF -current mA -voltage V -resistance kOhm -distance um
    set ::env(CLOCK_PERIOD) 20.0
    set ::env(OPENLANE_SDC_IDEAL_CLOCKS) 0
    read_sdc /input/core.sdc
    read_spef -corner @CORNER@ /input/typ.spef
    set clock [get_clocks clk]
    if {[llength [all_clocks]] != 1 || [get_property $clock period] != 20.0
        || ![get_property $clock is_propagated]} {error "Wrong analysis clock"}
    report_parasitic_annotation -report_unannotated > /work/export/parasitics.rpt
    @ACTIVITY@
    report_activity_annotation -report_annotated -report_unannotated > /work/export/activity.rpt
    report_power -corner @CORNER@ -digits 9 -format json > /work/export/power.json
    @SHEET_MODEL@
    set_debug_level PSM resistance 2
    set_debug_level PSM solve 3
    set_pdnsim_net_voltage -net VPWR -voltage 1.2 -corner @CORNER@
    set_pdnsim_net_voltage -net VGND -voltage 0 -corner @CORNER@
    set external_ohm [dict create @EXTERNAL_OHM@]
    # The native setter ignores zero after a positive value. Solve the rail
    # with lower resistance first so an ideal rail inherits the native default.
    set rails {VPWR VGND}
    if {[dict get $external_ohm VGND] < [dict get $external_ohm VPWR]} {
        set rails {VGND VPWR}
    }
    foreach rail $rails {
        puts "PINWHEEL_DC_BEGIN $rail"
        set_pdnsim_source_settings -external_resistance [dict get $external_ohm $rail]
        puts "PINWHEEL_DC_EXTERNAL_OHM $rail [dict get $external_ohm $rail]"
        set src {}
        if {[file exists /input/$rail.vsrc]} {set src [list -vsrc /input/$rail.vsrc]}
        analyze_power_grid -net $rail -corner @CORNER@ {*}$src -enable_em \
            -em_outfile /work/export/$rail-current.csv \
            -error_file /work/export/$rail-errors.rpt -voltage_file /work/export/$rail-voltage.csv
        write_pg_spice -net $rail -corner @CORNER@ {*}$src /work/export/$rail.spice
        puts "PINWHEEL_DC_END $rail"
    }
} message]} {
    puts stderr "PINWHEEL_DC_ERROR $message"
    exit 1
}
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    activity = parser.add_mutually_exclusive_group(required=True)
    activity.add_argument("--input-activity", type=float, help="Transitions per 20 ns period, duty 0.5")
    activity.add_argument("--vcd", type=Path)
    parser.add_argument("--scope", help="Slash-separated VCD hierarchy")
    contacts = parser.add_mutually_exclusive_group()
    contacts.add_argument("--contacts", type=Path, help="Directory containing explicit VPWR.vsrc and VGND.vsrc")
    contacts.add_argument("--parent-contacts", type=Path, help="Resolved parent contact receipt")
    parser.add_argument("--external-ohm", type=float, help="Shared series resistance per resolved source")
    parser.add_argument("--sheet-temperature", type=int, choices=(25, 105), default=25,
                        help="Temperature sensitivity for sheet R only; Liberty and via R remain fixed")
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.is_relative_to(TRIAL / "power-dc") and not out.exists(), "Use a fresh ignored power-dc case directory")
    resistance = args.external_ohm if args.external_ohm is not None else 0.0
    require(0 <= resistance <= 100 and (not resistance or args.contacts is not None), "Invalid external resistance")
    external = dict.fromkeys(VOLTAGES, resistance)
    source = dict(source_model="explicit" if args.contacts else "distributed block pins",
                  external_ohm_per_source=resistance)
    if args.vcd:
        require(args.scope and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_/]*", args.scope), "Supply the exact VCD scope")
        activity_model = dict(kind="functional_vcd", scope=args.scope)
        activity_cmd = f"read_vcd -scope {args.scope} /input/activity.vcd"
    else:
        require(args.scope is None and 0 <= args.input_activity <= 2, "Invalid vectorless activity")
        activity_model = dict(kind="vectorless", transitions_per_period=args.input_activity, duty=0.5)
        activity_cmd = f"set_power_activity -input -activity {args.input_activity} -duty 0.5"

    context = setup(args.history.resolve(strict=True))
    rows, layout, pins, _ = prepare(context)
    row, = [row for row in rows if row["model"] == "TYP" and row["corner"] == CORNER]
    libs = row["env"]["_CURRENT_CORNER_LIBS"].split()
    require(all(sha(context["pdk"] / path.removeprefix("/work/pdk/")) == row["input_sha256"][path]
                for path in libs), "Typical Liberty inputs changed")
    spef, = [path for path in row["input_sha256"] if path.endswith(".spef")]
    inputs = {
        "/input/trial.odb": TARGET["odb"],
        "/input/core.sdc": Path(layout["sdc"]["path"]),
        "/input/typ.spef": TRIAL / "timing/run" / spef.removeprefix("/work/result/"),
    }
    if args.vcd:
        inputs["/input/activity.vcd"] = args.vcd.resolve(strict=True)
    if args.contacts:
        for rail in VOLTAGES:
            inputs[f"/input/{rail}.vsrc"] = (args.contacts / f"{rail}.vsrc").resolve(strict=True)
    if args.parent_contacts:
        from streaming_8x4_hold_cap_parent_power import check_resolved

        require(args.external_ohm is None, "Parent contact receipts supply the two series resistance values")
        parent, parent_item = check_resolved(args.parent_contacts.resolve(strict=True))
        for rail, resolved in parent["rails"].items():
            inputs[f"/input/{rail}.vsrc"] = Path(resolved["vsrc"]["path"])
            external[rail] = resolved["external_ohm"]
        pins[parent_item["path"]] = parent_item["sha256"]
        pins.update({item["path"]: item["sha256"] for item in parent["inputs"]})
        source = dict(source_model="resolved parent contact rectangles", parent_contacts=parent_item,
                      external_ohm_per_source=external,
                      expected_source_nodes_um={rail: resolved["nodes_um"] for rail, resolved in parent["rails"].items()})
    bindings = {mount: bound(path) for mount, path in inputs.items()}
    require(bindings["/input/typ.spef"]["sha256"] == row["input_sha256"][spef], "Typical SPEF changed")
    producer = bound(Path(__file__).resolve())
    sheet_scale = {layer: (1 + tc * (args.sheet_temperature + 273.15 - 300))
                         / (1 + tc * (25 + 273.15 - 300)) for layer, tc in SHEET_TC.items()}
    sheet_model = ""
    if args.sheet_temperature != 25:
        sheet_model = """
    set tech [ord::get_db_tech]
    set dbu [[ord::get_db_block] getDbUnitsPerMicron]
    foreach {name factor} {@FACTORS@} {
        set layer [$tech findLayer $name]
        set width_um [expr {double([$layer getWidth]) / $dbu}]
        set kiloohm_per_um [expr {[$layer getResistance] * $factor / (1000.0 * $width_um)}]
        set_layer_rc -corner @CORNER@ -layer $name -resistance $kiloohm_per_um
    }""".replace("@FACTORS@", " ".join(f"{layer} {scale:.15g}" for layer, scale in sheet_scale.items()))
        sheet_model = sheet_model.replace("@CORNER@", CORNER)
    substitutions = {
        "CORNER": CORNER, "TOP": TOP, "ACTIVITY": activity_cmd,
        "EXTERNAL_OHM": " ".join(f"{rail} {value}" for rail, value in external.items()),
        "LIBRARIES": "\n".join(f"    read_liberty -corner {CORNER} {path}" for path in libs),
        "SHEET_MODEL": sheet_model,
    }
    script = re.sub(r"@([A-Z_]+)@", lambda match: substitutions[match[1]], TCL)
    out.mkdir(parents=True, exist_ok=False)
    tcl = out / "analysis.tcl"
    tcl.write_text(script)
    tcl_binding = bound(tcl)
    write(out / "request.json", dict(schema="pinwheel.streaming-8x4-hold-cap-dc.v1", producer=producer,
          analysis_tcl=tcl_binding, inputs=bindings, target_gds_sha256=TARGET["gds_sha256"], image=IMAGE,
          openroad_commit=OPENROAD, corner=CORNER, clock_period_ns=20.0, temperature_c=25,
          sheet_temperature_c=args.sheet_temperature, sheet_resistance_scale=sheet_scale,
          parasitics="retained draft TYP signal SPEF; OpenDB PDN resistance with optional sheet-only scaling",
          liberty={path: row["input_sha256"][path] for path in libs}, activity=activity_model,
          rail_voltages_v=VOLTAGES, qualified=False, **source))
    mounts = [(path, mount, False) for mount, path in inputs.items()]
    mounts.append((tcl, "/input/analysis.tcl", False))
    execution = run_native(context, out, "openroad",
                           ["-exit", "-threads", "1", "-metrics", "/work/export/metrics.json", "/input/analysis.tcl"],
                           mounts, 360, int(time.time()) + 600, memory="6g")
    require(all(bound(inputs[mount]) == item for mount, item in bindings.items())
            and bound(tcl) == tcl_binding and bound(Path(__file__).resolve()) == producer
            and all(sha(path) == digest for path, digest in pins.items()), "Frozen analysis input changed")
    log = (out / "container.log").read_text()
    require(OPENROAD in log and all(log.count(f"PINWHEEL_DC_END {rail}") == 1 for rail in VOLTAGES),
            "Native IR solve did not complete on both rails")
    artifacts = [out / name for name in ("container.log", "execution.json", "power.json", "metrics.json",
                                          "activity.rpt", "parasitics.rpt")]
    for rail in VOLTAGES:
        artifacts.extend(out / f"{rail}-{kind}.csv" for kind in ("voltage", "current"))
        artifacts.append(out / f"{rail}.spice")
    write(out / "readback.json", dict(status="completed", request=bound(out / "request.json"),
          artifacts=[bound(path) for path in artifacts], elapsed_seconds=execution["elapsed_seconds"],
          power_w=read(out / "power.json")["Total"]["total"], qualification=False))


if __name__ == "__main__":
    main()
