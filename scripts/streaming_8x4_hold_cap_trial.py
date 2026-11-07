"""Route and time a local hold/capacitance derivative of the verified fanout ECO."""

import argparse
from collections import Counter, defaultdict
import os
from pathlib import Path
import shutil
import subprocess
import time

from streaming_8x4_e982_native import ROOT, IMAGE, read, require, run_native, sha, views, write
from streaming_8x4_e982_eco_signoff import ECO_ROOT, TARGET, setup
from streaming_8x4_e982_fanout_trial import FILLERS, blocked_sites, pin_xy, def_nets, terminals
from streaming_8x4_pg_diode import intersect
from streaming_8x4_enclosure_admission import def_components
from streaming_tt_apply_fanout import checked_tcl

DRIVERS = ("fanout2219", "fanout1798", "fanout2439", "fanout875", "fanout2425")
OUT_ROOT = ROOT / "build/8x4-hold-cap-20261107"
# The first routed trial moved this leaf around the relocated cap buffer.
# Re-extract its geometry and propagate its clock through the full STA matrix.
COLLATERAL_CLOCK = "clknet_leaf_721_clk"


def native():
    import odb
    from openroad import Design, Tech

    out = Path("/work/export")
    request = read(out / "request.json")
    require(sha("/work/input.odb") == TARGET["odb_sha256"], "Wrong starting ECO")
    require(request["source_odb_sha256"] == TARGET["odb_sha256"]
            and request["producer_sha256"] == sha(__file__), "Native producer changed")
    tech = Tech()
    tech.readLiberty("/work/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lib/sg13cmos5l_stdcell_typ_1p20V_25C.lib")
    design = Design(tech)
    design.readDb("/work/input.odb")
    block, db = design.getBlock(), design.getDb()
    journal, edits, dirty = [], [], set()
    before_census = Counter(i.getMaster().getName() for i in block.getInsts())
    replaceable = FILLERS | {"sg13cmos5l_decap_4", "sg13cmos5l_decap_8"}
    blocked = blocked_sites(block)

    def tcl(command):
        print(command, flush=True)
        return checked_tcl(design, command, journal)

    def place_in_fillers(master, name, anchor):
        rows = defaultdict(list)
        for instance in block.getInsts():
            if instance.getMaster().getName() in replaceable:
                x, y = instance.getLocation()
                rows[y, str(instance.getOrient())].append((x, instance.getMaster().getWidth(), instance.getName()))
        candidates = []
        for (y, orient), row in rows.items():
            row.sort()
            for start, (x, _, _) in enumerate(row):
                end, removed = x, []
                for pos, width, filler in row[start:start + 10]:
                    if pos != end:
                        break
                    end += width
                    removed.append(filler)
                    if end >= x + master.getWidth():
                        if not any(intersect((x, y, end, y + master.getHeight()), b) for b in blocked):
                            candidates.append((x, y, orient, tuple(removed), end))
                        break
        require(candidates, f"No replaceable footprint for {name}")
        site = min(candidates, key=lambda s: (abs(s[0] - anchor[0]) + abs(s[1] - anchor[1]), s))
        x, y, orient, removed, end = site
        for filler in removed:
            odb.dbInst.destroy(block.findInst(filler))
        instance = odb.dbInst_create(block, master, name)
        instance.setOrient(orient)
        instance.setLocation(x, y)
        instance.setPlacementStatus("PLACED")
        for pin, rail in (("VDD", "VPWR"), ("VSS", "VGND")):
            term = instance.findITerm(pin)
            term.connect(block.findNet(rail))
            term.setSpecial()
        fill_master = db.findMaster("sg13cmos5l_fill_1")
        for index, pos in enumerate(range(x + master.getWidth(), end, fill_master.getWidth())):
            fill = odb.dbInst_create(block, fill_master, f"holdcap_tail_{name}_{index}")
            fill.setOrient(orient)
            fill.setLocation(pos, y)
            fill.setPlacementStatus("PLACED")
            for pin, rail in (("VDD", "VPWR"), ("VSS", "VGND")):
                term = fill.findITerm(pin)
                term.connect(block.findNet(rail))
                term.setSpecial()
        return instance, site

    for name in DRIVERS:
        old = block.findInst(name)
        require(old.getMaster().getName() == "sg13cmos5l_buf_1", "Unexpected cap driver")
        location, orient = old.getLocation(), old.getOrient()
        nets = {pin: old.findITerm(pin).getNet() for pin in ("A", "X")}
        dirty.update(n.getName() for n in nets.values())
        # Move only this driver and restore a decap in its old footprint.
        temporary, site = place_in_fillers(db.findMaster("sg13cmos5l_buf_2"), name + "_replacement", location)
        for pin, net in nets.items():
            temporary.findITerm(pin).connect(net)
        old_width = old.getMaster().getWidth()
        odb.dbInst.destroy(old)
        temporary.rename(name)
        fill_master = db.findMaster("sg13cmos5l_decap_4")
        require(old_width == fill_master.getWidth(), "Unexpected old buffer footprint")
        for index in range(1):
            fill = odb.dbInst_create(block, fill_master, f"holdcap_fill_{name}_{index}")
            fill.setOrient(orient)
            fill.setLocation(location[0] + index * fill_master.getWidth(), location[1])
            fill.setPlacementStatus("PLACED")
            for pin, rail in (("VDD", "VPWR"), ("VSS", "VGND")):
                term = fill.findITerm(pin)
                term.connect(block.findNet(rail))
                term.setSpecial()
        edits.append(dict(instance=name, old_master="sg13cmos5l_buf_1", new_master="sg13cmos5l_buf_2",
                          old_location=location, site=site))

    sink = block.findInst("engine.frontend._0230_").findITerm("D")
    source = sink.getNet()
    require(source.getName() == "engine.frontend._1956_.Y[1]"
            and len(list(source.getITerms())) == 2 and not list(source.getBTerms()), "Hold leaf changed")
    delay, site = place_in_fillers(db.findMaster(request["delay_master"]), "holdcap_delay", pin_xy(sink))
    branch = odb.dbNet_create(block, "holdcap_delayed_data")
    branch.setSigType("SIGNAL")
    delay.findITerm("A").connect(source)
    delay.findITerm("X").connect(branch)
    sink.connect(branch)
    dirty.update((source.getName(), branch.getName()))
    edits.append(dict(instance="holdcap_delay", new_master=request["delay_master"], site=site))
    for name in sorted(dirty):
        net = block.findNet(name)
        require(str(net.getSigType()) == "SIGNAL" and not net.isSpecial()
                and (net.getWire() is None or str(net.getWireType()) == "ROUTED"), "Protected route touched")
        if net.getWire() is not None:
            odb.dbWire.destroy(net.getWire())
        net.clearGuides()
        net.setWireType("ROUTED")
    after_census = Counter(i.getMaster().getName() for i in block.getInsts())
    write(out / "edits.json", dict(edits=edits, dirty_nets=sorted(dirty),
          master_count_delta={n: after_census[n] - before_census[n] for n in before_census.keys() | after_census.keys()
                              if after_census[n] != before_census[n]}))
    tcl("check_placement -verbose")
    tcl("set_thread_count 1")
    tcl("set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4")
    tcl("set_global_routing_layer_adjustment * 0.3")
    tcl("set_nets_to_route {" + " ".join(sorted(dirty)) + "}")
    tcl("global_route -guide_file /work/export/eco.guide")
    tcl("detailed_route -droute_end_iter 16 -or_seed 42 -verbose 1 -output_drc /work/export/route.drc")
    tcl("check_placement -verbose")
    markers = int(tcl("drt::detailed_route_num_drvs"))
    antenna = tcl("check_antennas")
    tcl("write_db /work/export/trial.odb")
    tcl("write_def /work/export/trial.def")
    tcl("write_verilog /work/export/trial.v")
    write(out / "native-result.json", dict(route_markers=markers, antenna=antenna, tcl=journal))


def route(context, out, deadline, delay_master):
    out.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(__file__, out / "worker.py")
    write(out / "request.json", dict(source_odb_sha256=TARGET["odb_sha256"], delay_master=delay_master,
                                     producer_sha256=sha(out / "worker.py"),
                                     producer_commit=subprocess.check_output(
                                         ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()))
    run_native(context, out, "openroad", ["-exit", "-python", "/work/export/worker.py"],
               [(ROOT / "scripts", "/work/scripts", False), (TARGET["odb"], "/work/input.odb", False)],
               1200, deadline, environment=("PYTHONPATH=/work/scripts", "PINWHEEL_HOLD_CAP_NATIVE=1"))
    review_route(out)


def review_route(out):
    before_body, before_cells = def_components(TARGET["odb"].with_suffix(".def"))
    after_body, after_cells = def_components(out / "trial.def")
    old_head, old_tail, old_nets = def_nets(before_body)
    new_head, new_tail, new_nets = def_nets(after_body)
    require(old_head == new_head and old_tail == new_tail, "Public or special-net geometry changed")
    changed = sorted(n for n in old_nets if old_nets[n] != new_nets.get(n))
    dirty = set(read(out / "edits.json")["dirty_nets"])
    collateral = sorted(set(changed) - dirty)
    require(all(terminals(old_nets[n]) == terminals(new_nets[n]) and b"+ FIXED" not in old_nets[n]
                and (b"+ USE SIGNAL" in old_nets[n] or
                     (n == COLLATERAL_CLOCK and b"+ USE CLOCK" in old_nets[n]))
                for n in collateral), "Collateral protected route changed")
    retained = before_cells.keys() & after_cells.keys() - {n.encode() for n in DRIVERS}
    require(all(before_cells[n] == after_cells[n] for n in retained), "Retained instance changed")
    require(all(before_cells[n][0].decode() in FILLERS | {"sg13cmos5l_decap_4", "sg13cmos5l_decap_8"}
                for n in before_cells.keys() - after_cells.keys()),
            "Removed a non-filler cell")
    result = read(out / "native-result.json")
    write(out / "route-readback.json", dict(result, collateral_nets=collateral,
          changed_clock_nets=[n for n in changed if b"+ USE CLOCK" in old_nets[n]],
          verifier_sha256=sha(__file__),
          odb_sha256=sha(out / "trial.odb"), def_sha256=sha(out / "trial.def"), qualified_timing=False))


def timing(context, out, deadline):
    from streaming_8x4_e982_eco_timing import execute

    verify_route(out)
    stream = out / "stream"
    stream.mkdir(exist_ok=False)
    prior = read(TARGET["gds"].parent / "execution.json")["argv"]
    offset = prior.index(IMAGE)
    entrypoint = prior[prior.index("--entrypoint") + 1]
    run_native(context, stream, entrypoint, prior[offset + 1:],
               [(out / "trial.def", "/work/export/design.def", False)], 180, deadline, memory="3g")
    context["target"] = dict(odb=out / "trial.odb", gds=stream / "design.gds",
                             odb_sha256=sha(out / "trial.odb"), gds_sha256=sha(stream / "design.gds"))
    context["work"] = out
    write(out / "layout.json", {key: str(value) for key, value in context["target"].items()})
    views(context, deadline)
    inventory = read(out / "views/actual-signal/inventory.json")
    for name, instance in inventory["instances"].items():
        rails = {pin: (term["signal_type"], term["net"]) for pin, term in instance["terminals"].items()
                 if term["signal_type"] in {"POWER", "GROUND"}}
        require(rails == {"VDD": ("POWER", "VPWR"), "VSS": ("GROUND", "VGND")},
                f"Wrong rail bindings on {name}")
    write(out / "rail-readback.json", dict(status="pass", target_odb_sha256=context["target"]["odb_sha256"],
          inventory_sha256=sha(out / "views/actual-signal/inventory.json"), instances=len(inventory["instances"])))
    execute(context, out / "timing", "hold-cap-trial", deadline)


def verify_route(out):
    """Reopen exact cell membership and the complete signal-terminal delta."""
    request, result, edits = (read(out / name) for name in ("request.json", "route-readback.json", "edits.json"))
    require(request["source_odb_sha256"] == TARGET["odb_sha256"]
            and result["odb_sha256"] == sha(out / "trial.odb")
            and result["def_sha256"] == sha(out / "trial.def"), "Route target changed")
    before_body, before = def_components(TARGET["odb"].with_suffix(".def"))
    after_body, after = def_components(out / "trial.def")
    removed = {n.encode() for edit in edits["edits"] for n in edit["site"][3]}
    added = {b"holdcap_delay"} | {f"holdcap_fill_{n}_0".encode() for n in DRIVERS}
    widths = {"sg13cmos5l_buf_2": 2400, "sg13cmos5l_dlygate4sd2_1": 3840,
              "sg13cmos5l_dlygate4sd3_1": 4320}
    for edit in edits["edits"]:
        x, _, _, _, end = edit["site"]
        width = widths[edit["new_master"]]
        added.update(f"holdcap_tail_{edit['instance']}_replacement_{i}".encode()
                     if edit["instance"] in DRIVERS else f"holdcap_tail_holdcap_delay_{i}".encode()
                     for i, _ in enumerate(range(x + width, end, 480)))
    require(before.keys() - after.keys() == removed and after.keys() - before.keys() == added,
            "Unexpected instance membership delta")
    for name in before.keys() & after.keys():
        if name.decode() in DRIVERS:
            require(after[name][0] == b"sg13cmos5l_buf_2", "Missing stronger buffer")
        else:
            require(before[name] == after[name], "Retained instance changed")
    require(after[b"holdcap_delay"][0].decode() == request["delay_master"], "Wrong delay cell")
    for name in added - {b"holdcap_delay"}:
        expected_master = b"sg13cmos5l_decap_4" if name.startswith(b"holdcap_fill_") else b"sg13cmos5l_fill_1"
        require(after[name][0] == expected_master, "Unexpected backfill master")
    old_head, old_tail, old = def_nets(before_body)
    new_head, new_tail, new = def_nets(after_body)
    require(old_head == new_head and old_tail == new_tail and new.keys() - old.keys() == {"holdcap_delayed_data"}
            and old.keys() <= new.keys(), "Unexpected public geometry or net membership")
    for name, record in old.items():
        expected = terminals(record)
        if name == "engine.frontend._1956_.Y[1]":
            expected = expected - {("engine.frontend._0230_", "D")} | {("holdcap_delay", "A")}
        require(terminals(new[name]) == expected, f"Wrong terminal delta on {name}")
        if b"+ FIXED" in record or (b"+ USE CLOCK" in record and name != COLLATERAL_CLOCK):
            require(record == new[name], "Protected routed net changed")
    require(terminals(new["holdcap_delayed_data"]) == {("holdcap_delay", "X"), ("engine.frontend._0230_", "D")},
            "Wrong delayed leaf connectivity")
    require(result["route_markers"] == 0 and str(result["antenna"]) == "0", "Router or antenna checks failed")
    write(out / "connectivity-readback.json", dict(status="pass", source_odb_sha256=TARGET["odb_sha256"],
          target_odb_sha256=result["odb_sha256"], target_def_sha256=result["def_sha256"],
          added_instances=sorted(n.decode() for n in added), removed_instances=sorted(n.decode() for n in removed),
          all_regular_net_terminals_verified=True, fixed_routes_unchanged=True))


def main():
    if os.environ.get("PINWHEEL_HOLD_CAP_NATIVE") == "1":
        native()
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("route", "review", "timing"))
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--delay-master", default="sg13cmos5l_dlygate4sd2_1",
                        choices=("sg13cmos5l_dlygate4sd2_1", "sg13cmos5l_dlygate4sd3_1"))
    parser.add_argument("--deadline", type=int, default=int(time.time()) + 7200)
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.is_relative_to(OUT_ROOT) and out != OUT_ROOT, "Use a fresh ignored local trial directory")
    context = setup(args.history.resolve(), ECO_ROOT / "signoff-01")
    if args.phase == "route":
        route(context, out, args.deadline, args.delay_master)
    elif args.phase == "review":
        review_route(out)
        verify_route(out)
    else:
        timing(context, out, args.deadline)


if __name__ == "__main__":
    main()
