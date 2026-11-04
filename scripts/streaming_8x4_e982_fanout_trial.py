"""Try a bounded five-net fanout ECO on a copy of the frozen 8x4 layout."""

import argparse
from collections import defaultdict
from itertools import combinations
import os
from pathlib import Path
import re
import shutil

from streaming_8x4_e982_native import ODB, ROOT, local_inputs, read, require, run_native, sha, write
from streaming_8x4_enclosure_admission import def_components
from streaming_8x4_pg_diode import blocked_regions, intersect
from streaming_tt_apply_fanout import checked_tcl, execute


LOAD_COUNTS = {"net2157": (8, 4), "net2298": (8, 2), "net11223": (4, 5),
               "net2333": (8, 1), "net840": (6, 3)}
LIMIT = 8
BUFFER = "sg13cmos5l_buf_1"
DIODE = "sg13cmos5l_antennanp"
FILLERS = {"sg13cmos5l_fill_1", "sg13cmos5l_fill_2"}
REPLACEABLE = FILLERS | {"sg13cmos5l_decap_4"}
OPENROAD = "b2159d4a99a9b236a6e95bbf6efc88bcfd2b843df273e97f169b456bc3b0453b"
TYP = "34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad"
FROZEN_DEF = "8802555ed7800ac6bcf92680793380d4a0a4deee0f7e6cd584044c084fe86350"
CLONE_NETS = {"net2157", "net2298", "net11223", "net840"}


def blocked_sites(block):
    special = [
        (net.getName(), box.getTechLayer().getName(),
         (box.xMin(), box.yMin(), box.xMax(), box.yMax()), str(box.getWireShapeType()))
        for net in block.getNets() if net.isSpecial()
        for wire in net.getSWires() for box in wire.getWires() if not box.isVia()
    ]
    require(special, "Missing power routing")
    return [box for _, _, box in blocked_regions(special, {"dpl_used_layers": [1, 2]})]


def filler_sites(block, master):
    """Enumerate exact footprints covered by contiguous ordinary fillers."""
    by_row = defaultdict(list)
    blocked = blocked_sites(block)
    for instance in block.getInsts():
        if instance.getMaster().getName() in REPLACEABLE:
            x, y = instance.getLocation()
            by_row[y, str(instance.getOrient())].append(
                (x, instance.getMaster().getWidth(), instance.getName()))
    for (y, orient), row in by_row.items():
        row.sort()
        for start, (x, _, _) in enumerate(row):
            end = x
            names = []
            for pos, width, name in row[start:start + 4]:
                if pos != end:
                    break
                end += width
                names.append(name)
                if end >= x + master.getWidth():
                    if end == x + master.getWidth() and not any(
                            intersect((x, y, end, y + master.getHeight()), box) for box in blocked):
                        yield x, y, orient, tuple(names)
                    break


def pin_key(term):
    return term.getInst().getName(), term.getMTerm().getName()


def pin_xy(term):
    valid, x, y = term.getAvgXY()
    require(valid, f"No pin location for {pin_key(term)}")
    return x, y


def choose_split(block, name, available):
    net = block.findNet(name)
    require(net is not None and not net.isSpecial() and net.getWire() is not None
            and not list(net.getBTerms()) and str(net.getSigType()) == "SIGNAL",
            f"Unexpected source branch {name}")
    terms = list(net.getITerms())
    driver, = [term for term in terms if str(term.getIoType()) == "OUTPUT"]
    require(pin_key(driver) == (f"fanout{name[3:]}", "X")
            and driver.getInst().getMaster().getName() == BUFFER, f"Unexpected driver for {name}")
    loads = sorted((term for term in terms if term != driver), key=pin_key)
    require(all(str(term.getIoType()) == "INPUT" for term in loads), f"Unexpected load direction on {name}")
    functional = [term for term in loads if term.getInst().getMaster().getName() != DIODE]
    diodes = [term for term in loads if term.getInst().getMaster().getName() == DIODE]
    require((len(functional), len(diodes)) == LOAD_COUNTS[name], f"Changed load census on {name}")
    clone = name in CLONE_NETS
    source = driver.getInst()
    upstream = source.findITerm("A").getNet() if clone else net
    if clone:
        require(upstream is not None and upstream.getWire() is not None
                and str(upstream.getWireType()) == "ROUTED" and not upstream.isSpecial()
                and not list(upstream.getBTerms())
                and sum(str(term.getIoType()) == "INPUT" for term in upstream.getITerms()) < LIMIT,
                f"No upstream headroom on {name}")
    needed = len(loads) + (0 if clone else 1) - LIMIT
    source_x, source_y = pin_xy(driver)
    locations = {pin_key(term): pin_xy(term) for term in functional}

    def score(site, keys):
        x, y = site[:2]
        return (abs(source_x - x) + abs(source_y - y)
                + sum(abs(locations[key][0] - x) + abs(locations[key][1] - y) for key in keys))

    # Favor a tight downstream branch so the unprotected branch stays short.
    def span(keys):
        xs, ys = zip(*(locations[key] for key in keys))
        return max(xs) - min(xs) + max(ys) - min(ys)

    selected = (("fanout833", "A"),) if name == "net840" else min(
        combinations(locations, needed), key=lambda keys: (span(keys), keys))
    site = min(available, key=lambda candidate: (score(candidate, selected), candidate))
    return {"kind": "clone" if clone else "signal_buffer", "source_net": name, "upstream_net": upstream.getName(),
            "source_instance": source.getName() if clone else None, "master": BUFFER, "new_instance": f"eco_{name}_buf",
            "new_net": f"eco_{name}_branch", "loads": [("iterm", *key) for key in selected],
            "antenna_inputs": [pin_key(term) for term in diodes], "site": site,
            "old_wire_type": str(net.getWireType())}


def native(directory):
    import odb
    from openroad import Design, Tech

    require(sha(Path(shutil.which("openroad")).resolve()) == OPENROAD and sha("/work/frozen.odb") == ODB
            and sha("/work/frozen.def") == FROZEN_DEF,
            "Native OpenROAD or baseline ODB changed")
    request = read(directory / "request.json")
    require(request["nets"] in (list(LOAD_COUNTS), list(LOAD_COUNTS)[:-1]), "Unexpected ECO scope")
    tech = Tech()
    liberty = ("/work/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lib/"
               "sg13cmos5l_stdcell_typ_1p20V_25C.lib")
    require(sha(liberty) == TYP, "Pinned Liberty changed")
    tech.readLiberty(liberty)
    design = Design(tech)
    design.readDb("/work/frozen.odb")
    block, database = design.getBlock(), design.getDb()
    master = database.findMaster(BUFFER)
    sites = list(filler_sites(block, master))
    require(sites, "No exact filler footprint available")
    operations = []
    dirty = set()
    journal = []
    def tcl(command):
        print(command, flush=True)
        return checked_tcl(design, command, journal)

    for name in request["nets"]:
        op = choose_split(block, name, sites)
        x, y, orient, replaced = op["site"]
        sites = [candidate for candidate in sites if set(candidate[3]).isdisjoint(replaced)]
        for filler in replaced:
            odb.dbInst.destroy(block.findInst(filler))
        if name == "net840":
            from streaming_8x4_e982_net840_cut import apply_cut
            op["fixed_leaf_cut"] = apply_cut(odb, block, database.getTech())
        execute(odb, database, block, op)
        buffer = block.findInst(op["new_instance"])
        buffer.setOrient(orient)
        buffer.setLocation(x, y)
        for pin, rail in (("VDD", "VPWR"), ("VSS", "VGND")):
            term = buffer.findITerm(pin)
            require(term.getNet().getName() == rail and term.getNet().isSpecial(), "New buffer rail mismatch")
            term.setSpecial()
        old = block.findNet(name)
        new = block.findNet(op["new_net"])
        require(sum(str(term.getIoType()) == "INPUT" for term in old.getITerms()) == LIMIT
                and sum(str(term.getIoType()) == "INPUT" for term in new.getITerms()) == len(op["loads"]),
                "Partition did not reach the eight-load limit")
        if name == "net840":
            from streaming_8x4_e982_net840_cut import verify_cut
            verify_cut(block, op["new_net"])
        else:
            dirty.add(name)
        dirty.update((op["new_net"], op["upstream_net"]))
        operations.append(op)
    dirty = sorted(dirty)
    for name in dirty:
        net = block.findNet(name)
        if net.getWire() is not None:
            # A disconnected pin's old metal still conducts until it is cut or rerouted.
            require(str(net.getWireType()) == "ROUTED", f"Refusing to rip up fixed wire {name}")
            odb.dbWire.destroy(net.getWire())
        net.clearGuides()
        net.setWireType("ROUTED")
    write(directory / "partition.json", {"operations": operations, "released_for_routing": dirty})
    tcl("check_placement -verbose")
    tcl("write_db /work/export/partition.odb")
    tcl("write_def /work/export/partition.def")
    require(not compare(Path("/work/frozen.def"), directory / "partition.def", operations),
            "Partition changed unrelated DEF routing")
    tcl("set_thread_count 1")
    tcl("set_routing_layers -signal Metal2-Metal4 -clock Metal2-Metal4")
    tcl("set_global_routing_layer_adjustment * 0.3")
    tcl("set_nets_to_route {" + " ".join(dirty) + "}")
    tcl("global_route -guide_file /work/export/eco.guide")
    tcl("write_db /work/export/guided.odb")
    tcl("detailed_route -droute_end_iter 16 -or_seed 42 -verbose 1 -output_drc /work/export/route.drc")
    if "net840" in request["nets"]:
        verify_cut(block, "eco_net840_branch")
    route_markers = int(tcl("drt::detailed_route_num_drvs"))
    tcl("write_db /work/export/trial.odb")
    tcl("write_def /work/export/trial.def")
    tcl("write_verilog -include_pwr_gnd /work/export/trial.power.v")
    tcl("write_verilog /work/export/trial.v")
    tcl("report_check_types -max_fanout -violators > /work/export/fanout.rpt")
    antenna = tcl("check_antennas")
    branch_antenna = {net: tcl("check_antennas -net {" + net + "}")
                      for net in sorted(set(dirty) | set(request["nets"]))}
    write(directory / "native-result.json", {"route_markers": route_markers, "antenna_whole": antenna,
          "antenna_changed_nets": branch_antenna, "dirty_nets": dirty, "tcl": journal})


def def_nets(data):
    header, separator, tail = data.partition(b"\nNETS ")
    require(separator, "Missing regular NETS section")
    count, remainder = tail.split(b" ;\n", 1)
    records, rest = remainder.split(b"END NETS\n", 1)
    rows = list(re.finditer(rb"(?ms)^[ \t]*-[ \t]+(\S+).*?;", records))
    result = {row[1].decode(): row[0] for row in rows}
    require(len(rows) == len(result) == int(count), "DEF net membership differs")
    return header, rest, result


def terminals(record):
    rows = [tuple(pair.decode().split()) for pair in re.findall(rb"\(\s+([^()]+?)\s+\)",
                                                              record.split(b" +", 1)[0])]
    require(len(rows) == len(set(rows)), "Duplicate DEF terminal")
    return set(rows)


def compare(before, after, operations):
    before_body, before_cells = def_components(before)
    after_body, after_cells = def_components(after)
    old_head, old_tail, old_nets = def_nets(before_body)
    new_head, new_tail, new_nets = def_nets(after_body)
    require(old_head == new_head and old_tail == new_tail, "Die, public pins, tracks, or special-net DEF changed")
    removed = {name.encode() for op in operations for name in op["site"][3]}
    added = {op["new_instance"].encode() for op in operations}
    require(set(before_cells) - set(after_cells) == removed and set(after_cells) - set(before_cells) == added
            and all(before_cells[name][0].decode() in REPLACEABLE for name in removed)
            and all(after_cells[name][0].decode() == BUFFER for name in added)
            and all(after_cells[name] == row for name, row in before_cells.items() if name not in removed),
            "Unexpected cell or placement delta")
    changed = {name for name, record in old_nets.items() if new_nets.get(name) != record}
    declared = {op[key] for op in operations for key in ("source_net", "upstream_net")}
    require(declared <= changed and set(old_nets) <= set(new_nets)
            and set(new_nets) - set(old_nets) == {op["new_net"] for op in operations},
            "Unexpected net membership or absent partition")
    for op in operations:
        moved = {tuple(load[1:]) for load in op["loads"]}
        old = terminals(old_nets[op["source_net"]])
        buffer = op["new_instance"]
        expected = old - moved
        if op["kind"] == "signal_buffer":
            expected.add((buffer, "A"))
        else:
            upstream = op["upstream_net"]
            require(terminals(new_nets[upstream]) == terminals(old_nets[upstream]) | {(buffer, "A")},
                    "Clone upstream terminal readback differs")
        require(moved <= old and terminals(new_nets[op["source_net"]]) == expected
                and terminals(new_nets[op["new_net"]]) == moved | {(buffer, "X")}
                and {tuple(pin) for pin in op["antenna_inputs"]}.isdisjoint(moved), "Split terminal readback differs")
    unrelated = sorted(changed - declared)
    require(all(terminals(old_nets[name]) == terminals(new_nets[name])
                and b"+ USE SIGNAL" in old_nets[name] and b"+ FIXED" not in old_nets[name] for name in unrelated),
            "Collateral change touched connectivity, clock or fixed wires")
    return unrelated


def review(before, out):
    partition = read(out / "partition.json")
    operations = partition["operations"]
    require(not compare(before, out / "partition.def", operations), "Partition disturbed unrelated routing")
    unrelated = compare(before, out / "trial.def", operations)
    result = read(out / "native-result.json")
    antenna = [result["antenna_whole"], *result["antenna_changed_nets"].values()]
    fanout = (out / "fanout.rpt").read_text()
    fanout_violations = [line.strip() for line in fanout.splitlines() if "(VIOLATED)" in line]
    router_pass = result["route_markers"] == 0 and all(str(value) == "0" for value in antenna)
    return dict(result, source_odb_sha256=ODB, trial_odb_sha256=sha(out / "trial.odb"),
                trial_def_sha256=sha(out / "trial.def"), changed_unrelated_nets=unrelated,
                net840_leaf_cut=any(op["source_net"] == "net840" for op in operations),
                fanout_violations=fanout_violations, fanout_report_sha256=sha(out / "fanout.rpt"),
                router_checks_passed=router_pass, strict_scope_passed=not unrelated,
                clean_router_trial=router_pass and not unrelated and not fanout_violations,
                qualified=False, fabrication_ready=False)


def main():
    if os.environ.get("PINWHEEL_E982_FANOUT_WORKER") == "1":
        native(Path("/work/export"))
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--deadline", required=True, type=int)
    parser.add_argument("--leave-net840", action="store_true")
    args = parser.parse_args()
    out = args.output.resolve()
    require(out.is_relative_to(ROOT / "build/e982-fanout-20261104"), "Use an ignored trial output directory")
    context = local_inputs(args.history.resolve(), out)
    out.mkdir(parents=True, exist_ok=False)
    write(out / "request.json", {"nets": list(LOAD_COUNTS)[:-1] if args.leave_net840 else list(LOAD_COUNTS)})
    worker = ROOT / "scripts"
    before = context["source"] / "design.def"
    run_native(context, out, "openroad", ["-exit", "-python", "/work/scripts/" + Path(__file__).name],
               [(worker, "/work/scripts", False), (context["odb"], "/work/frozen.odb", False),
                (before, "/work/frozen.def", False)],
               900, args.deadline, environment=("PYTHONPATH=/work/scripts", "PINWHEEL_E982_FANOUT_WORKER=1"))
    write(out / "readback.json", review(before, out))


if __name__ == "__main__":
    main()
