"""Bounded fixture qualification inside the pinned offline CAD container.

This is an experimental comparison recipe, not a full SRAM signoff flow.
It copies the deck, preserves source inputs, and refuses existing output paths.
"""

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

import klayout.db as db

HERE = Path(__file__).resolve().parent
DRIVER = "RM_IHPSG13_1P_WLDRV16X8"
DELAY = "RM_IHPSG13_1P_DLY_2"
DUMMY = "RSC_IHPSG13_CDLYX1_DUMMY"
POLICY = "physical-boundary-and-dimensional-resistors-v4"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def value(obj, name):
    result = getattr(obj, name)
    return result() if callable(result) else result


def check_inputs(root, filename):
    identities = json.loads((HERE / filename).read_text())
    for name, digest in identities.items():
        require(sha(root / name) == digest, "Changed pinned input: " + name)
    return identities


def prepare_deck(source, output):
    identities = check_inputs(source, "deck-inputs.json")
    require({str(p.relative_to(source)) for p in source.rglob("*") if p.is_file()}
            == set(identities), "Unexpected deck input files")
    deck = output / "deck"
    shutil.copytree(source, deck)
    path = deck / "sg13cmos5l.lvs"
    text = path.read_text()
    replacements = [
        ("  target_netlist.simplify if SIMPLIFY",
         "  if SIMPLIFY\n"
         "    target_netlist.combine_devices\n"
         "    target_netlist.each_circuit { |circuit| circuit.purge_nets_keep_pins }\n"
         "  end"),
        ("  # === Aligns the extracted netlist vs. the schematic ===",
         (HERE / "policy.rb").read_text()
         + "\n  # === Aligns the extracted netlist vs. the schematic ==="),
        ("  #=== IGNORE EXTREME VALUES ===",
         "  pw_verify_prepared.call\n  #=== IGNORE EXTREME VALUES ==="),
        ("  #------------- COMPARISON RESULTS ---------------",
         "  pw_finish.call(success)\n  #------------- COMPARISON RESULTS ---------------"),
    ]
    for before, after in replacements:
        require(text.count(before) == 1, "Pinned deck patch anchor changed")
        text = text.replace(before, after)
    path.write_text(text)
    changed = [name for name, digest in identities.items() if sha(deck / name) != digest]
    require(changed == ["sg13cmos5l.lvs"], "Unexpected private deck changes")
    return deck, changed


def readback(path):
    result = db.LayoutVsSchematic()
    result.read(str(path))
    xref = result.xref()
    rows = []
    for pair in xref.each_circuit_pair():
        row = {"status": str(pair.status())}
        for side, circuit in [("layout", pair.first()), ("schematic", pair.second())]:
            row[side] = None if circuit is None else {
                "name": circuit.name,
                "devices": dict(Counter(d.device_class().name for d in circuit.each_device())),
                "pins": [value(p, "name") for p in circuit.each_pin()],
            }
        for kind, iterator in [("device", xref.each_device_pair), ("net", xref.each_net_pair),
                               ("pin", xref.each_pin_pair), ("subcircuit", xref.each_subcircuit_pair)]:
            row[kind + "_statuses"] = dict(Counter(str(p.status()) for p in iterator(pair)))
        rows.append(row)
    return {"circuits": rows, "match": bool(rows) and all(r["status"] == "Match" for r in rows)}


def accepted(row, log):
    audit = row.get("policy", {})
    stages = {"before_preparation", "layout_flatten", "schematic_flatten", "after_flatten",
              "bound_layout_ports", "after_simplify", "prepared_layout_ports",
              "layout_prepared", "schematic_prepared"}
    complete = stages <= audit.get("stages", {}).keys() and bool(audit.get("physical_port_witnesses"))
    return (row["exit_code"] == 0 and row.get("match", False) and complete
            and audit.get("policy") == POLICY and audit.get("top") == row["top"]
            and audit.get("status") == "matched" and audit.get("native_success") is True
            and "Congratulations! Netlists match." in log)


def compare(deck, output, label, top, mode, gds, cdl, reasons=()):
    folder = output / label
    folder.mkdir()
    audit = folder / "policy.json"
    command = ["python3", "-B", str(deck / "run_lvs.py"), "--layout=" + str(gds),
               "--netlist=" + str(cdl), "--topcell=" + top, "--run_mode=" + mode,
               "--run_dir=" + str(folder / "lvs")]
    start = time.monotonic()
    with (folder / "native.log").open("w") as log:
        result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=60,
                                env=dict(os.environ, QT_QPA_PLATFORM="offscreen", OMP_NUM_THREADS="4",
                                         PINWHEEL_POLICY_REPORT=str(audit),
                                         PINWHEEL_POLICY_CONTRACT=str(HERE / "contract.json")))
    row = dict(top=top, mode=mode, command=command, exit_code=result.returncode,
               seconds=round(time.monotonic() - start, 3), gds_sha256=sha(gds), cdl_sha256=sha(cdl))
    if audit.exists():
        row["policy"] = json.loads(audit.read_text())
    database = folder / "lvs" / (gds.stem + ".lvsdb")
    if database.exists():
        row.update(readback(database))
    log = (folder / "native.log").read_text()
    row["accepted"] = accepted(row, log)
    policy = row.get("policy", {})
    row["policy_rejection"] = (policy.get("status") == "rejected"
                               and any(reason in policy.get("reason", "") for reason in reasons)
                               and "PINWHEEL_POLICY_REJECT:" in log)
    row["native_rejection"] = (policy.get("status") == "no_match"
                               and policy.get("native_success") is False and row.get("match") is False
                               and "ERROR : Netlists don't match" in log)
    # A crash or absent result alone is never a successful negative control.
    row["expected_result_observed"] = (not row["accepted"] and
                                       (row["policy_rejection"] or row["native_rejection"]))
    return row


def top_geometry(layout, top):
    cell = layout.cell(top)
    return {str(layout.get_info(i)): db.Region(cell.begin_shapes_rec(i)) for i in layout.layer_indexes()}


def top_texts(layout, top):
    result = Counter()
    for index in layout.layer_indexes():
        iterator = layout.cell(top).begin_shapes_rec(index)
        while not iterator.at_end():
            if iterator.shape().is_text():
                result[(str(layout.get_info(index)), str(iterator.shape().text.transformed(iterator.trans())))] += 1
            iterator.next()
    return result


def identical_geometry(source, target, top):
    before, after = top_geometry(source, top), top_geometry(target, top)
    for name in before.keys() | after.keys():
        require((before.get(name, db.Region()) ^ after.get(name, db.Region())).is_empty(), "Carrier changed polygons")
    require(top_texts(source, top) == top_texts(target, top), "Carrier changed text")


def controls(fixtures, output):
    """Faults preserve the full parent; geometry edits affect its six dummy instances."""
    import re
    inputs = output / "mutations"
    inputs.mkdir()
    cases = []
    driver = (fixtures / (DRIVER + ".cdl")).read_text()
    delay = (fixtures / (DELAY + ".metal1.cdl")).read_text()
    header = re.search(r"^\.SUBCKT " + DRIVER + r"[^\n]*", driver, re.M)[0]
    disconnected = ("Disconnected declared port",)
    port_identity = ("Declared port identity/order changed",)
    changes = {
        "driver_open": (DRIVER, driver.replace("XBUF<0> A<0> Z<0>", "XBUF<0> A<0> fault_open"), disconnected),
        "driver_short": (DRIVER, driver.replace("XBUF<0> A<0> Z<0>", "XBUF<0> A<0> VSS"), disconnected),
        "driver_missing_nmos": (DRIVER, re.sub(r"^MN1[^\n]*\n", "", driver, flags=re.M), ()),
        "driver_internal_open": (DRIVER, driver.replace("MN1 Z ", "MN1 fault_open "), ()),
        "port_missing": (DRIVER, driver.replace(header, header.replace(" Z<0>", "")), port_identity),
        "port_extra": (DRIVER, driver.replace(header, header + " EXTRA"), port_identity),
        "port_renamed": (DRIVER, driver.replace("Z<0>", "RENAMED"), port_identity),
        "input_ports_swapped": (DRIVER, driver.replace("XBUF<0> A<0>", "XBUF<0> A<1>").replace("XBUF<1> A<1>", "XBUF<1> A<0>"), ()),
        "output_ports_swapped": (DRIVER, driver.replace("XBUF<0> A<0> Z<0>", "XBUF<0> A<0> Z<1>").replace("XBUF<1> A<1> Z<1>", "XBUF<1> A<1> Z<0>"), ()),
        "delay_wrong_width": (DELAY, delay.replace("w=2.6e-07", "w=5.2e-07"), ()),
        "delay_wrong_length": (DELAY, delay.replace("l=6e-07", "l=1.2e-06"), ()),
        "delay_same_ratio_wrong_dimensions": (DELAY, delay.replace("w=2.6e-07", "w=5.2e-07").replace("l=6e-07", "l=1.2e-06"), ()),
        "untranslated_model": (DELAY, delay.replace(" res_metal1 ", " lvsres "), ("Unsupported active model lvsres",)),
        "missing_width": (DELAY, delay.replace(" w=2.6e-07", ""), ("Missing or invalid resistor dimensions",)),
    }
    for label, (top, text, reasons) in changes.items():
        require(text != (driver if top == DRIVER else delay), "Missing mutation target: " + label)
        path = inputs / (label + ".cdl")
        path.write_text(text)
        cases.append((label, top, fixtures / (top + ".gds"), path, reasons))

    source = db.Layout()
    source.read(str(fixtures / (DELAY + ".gds")))
    instances = sum(len(list(i.cell_inst.each_trans())) for i in source.cell(DELAY).each_inst()
                    if source.cell(i.cell_index).name == DUMMY)
    require(instances == 6, "Wrong physical neighborhood")
    carrier = db.Layout()
    carrier.read(str(fixtures / (DELAY + ".gds")))
    carrier.cell(DUMMY).flatten(True)
    carrier_path = inputs / "delay_physical_carrier.gds"
    carrier.write(str(carrier_path))
    reread = db.Layout()
    reread.read(str(carrier_path))
    identical_geometry(source, reread, DELAY)
    cases.append(("delay_physical_carrier", DELAY, carrier_path, fixtures / (DELAY + ".metal1.cdl"), ()))
    dummy = source.cell(DUMMY)
    gates = ((db.Region(dummy.begin_shapes_rec(source.find_layer(1, 0)))
              - db.Region(dummy.begin_shapes_rec(source.find_layer(14, 0))))
             & db.Region(dummy.begin_shapes_rec(source.find_layer(5, 0))))
    require(not gates.is_empty(), "Missing NMOS gate geometry")
    geometry_checks = {}
    mutations = {
        "delay_physical_open": ((8, 0), "remove", db.Region(db.Box(1290, 3400, 1320, 3700)),
                                 ("Flattening lost physical port A", "Disconnected physical port A")),
        "delay_physical_short": ((8, 0), "add", db.Region(db.Box(905, 3330, 1705, 3470)), ()),
        "delay_physical_missing_nmos": ((5, 0), "remove", gates, ()),
    }
    for label in [*mutations, "physical_port_missing", "physical_port_renamed",
                  "physical_ports_swapped", "physical_port_off_metal"]:
        target = db.Layout()
        target.read(str(fixtures / (DELAY + ".gds")))
        top = target.cell(DELAY)
        if label in mutations:
            layer, operation, region, reasons = mutations[label]
            child = target.cell(DUMMY)
            child.flatten(True)
            identical_geometry(source, target, DELAY)
            index = target.find_layer(*layer)
            before = db.Region(child.begin_shapes_rec(index))
            after = before - region if operation == "remove" else before + region
            require(not (before ^ after).is_empty(), "Geometry mutation changed nothing")
            child.shapes(index).clear()
            child.shapes(index).insert(after)
            geometry_checks[label] = {"changed_area_dbu2": (before ^ after).area(), "layer": str(layer),
                                      "edited_dummy_instances": instances}
        else:
            count = 0
            for shape in list(top.shapes(target.find_layer(8, 25)).each()):
                if not shape.is_text():
                    continue
                text = shape.text
                if label == "physical_port_missing" and text.string == "A":
                    shape.delete()
                    count += 1
                elif label == "physical_port_renamed" and text.string == "A":
                    text.string = "RENAMED"
                    shape.text = text
                    count += 1
                elif label == "physical_ports_swapped" and text.string in ("A", "Z"):
                    text.string = {"A": "Z", "Z": "A"}[text.string]
                    shape.text = text
                    count += 1
                elif label == "physical_port_off_metal" and text.string == "A":
                    text.x = text.y = -1000
                    shape.text = text
                    count += 1
            require(count == (2 if label == "physical_ports_swapped" else 1), "Missing label mutation target")
            before = top_geometry(source, DELAY)
            for name, polygons in top_geometry(target, DELAY).items():
                require((before[name] ^ polygons).is_empty(), "Label mutation changed polygons")
            geometry_checks[label] = {"polygons_preserved": True, "changed_labels": count}
            reasons = (() if label == "physical_ports_swapped" else
                       ("Boundary label does not probe a top net",) if label == "physical_port_off_metal" else
                       ("Physical boundary labels missing",))
        path = inputs / (label + ".gds")
        target.write(str(path))
        cases.append((label, DELAY, path, fixtures / (DELAY + ".metal1.cdl"), reasons))
    return cases, geometry_checks


def evidence_controls(positive, log):
    require(accepted(positive, log), "Positive evidence control failed")
    results = {}
    for label, audit in [("absent_policy", {}), ("incomplete_policy", {"status": "prepared"}),
                         ("native_failure", dict(positive["policy"], native_success=False)),
                         ("absent_stages", dict(positive["policy"], stages={})),
                         ("absent_physical_witnesses", dict(positive["policy"], physical_port_witnesses=[]))]:
        results[label] = not accepted(dict(positive, policy=audit), log)
    results["absent_native_final_pass"] = not accepted(positive, "")
    results["nonzero_exit"] = not accepted(dict(positive, exit_code=1), log)
    results["database_mismatch"] = not accepted(dict(positive, match=False), log)
    require(all(results.values()), "Incomplete evidence was accepted")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdk-lvs-dir", type=Path, required=True)
    parser.add_argument("--fixtures-dir", type=Path, default=HERE.parent / "sram-context")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--controls", action="store_true")
    args = parser.parse_args()
    source, fixtures, output = [p.resolve() for p in (args.pdk_lvs_dir, args.fixtures_dir, args.output)]
    fixture_hashes = check_inputs(fixtures, "fixture-inputs.json")
    output.mkdir()  # Never overwrite an executed comparison.
    deck, changed = prepare_deck(source, output)
    contract = json.loads((HERE / "contract.json").read_text())
    report = dict(status="running", physical_qualification=False, changed_private_deck_files=changed,
                  policy_sha256=sha(HERE / "policy.rb"), contract_sha256=sha(HERE / "contract.json"),
                  candidate_deck_sha256=sha(deck / "sg13cmos5l.lvs"), comparisons={})
    def save():
        write_json(output / "report.json", report)
    save()
    for top in contract["tops"]:
        for mode in ("deep", "flat"):
            label = top + "_" + mode
            row = compare(deck, output, label, top, mode, fixtures / (top + ".gds"),
                          fixtures / (top + (".metal1.cdl" if "DLY" in top else ".cdl")))
            row["expected_result_observed"] = row["accepted"]
            report["comparisons"][label] = row
            save()
            print(label, "accepted", row["accepted"], flush=True)
    positive_label = DRIVER + "_deep"
    report["evidence_refusals"] = evidence_controls(report["comparisons"][positive_label],
                                                   (output / positive_label / "native.log").read_text())
    if args.controls:
        cases, geometry = controls(fixtures, output)
        report["mutation_geometry"] = geometry
        for label, top, gds, cdl, reasons in cases:
            for mode in ("deep", "flat"):
                name = label + "_" + mode
                row = compare(deck, output, name, top, mode, gds, cdl, reasons)
                if label == "delay_physical_carrier":
                    row["expected_result_observed"] = row["accepted"]
                report["comparisons"][name] = row
                save()
                print(name, "expected result", row["expected_result_observed"], flush=True)
    require(check_inputs(fixtures, "fixture-inputs.json") == fixture_hashes, "Fixture inputs changed")
    check_inputs(source, "deck-inputs.json")
    report["sources_unchanged"] = True
    report["status"] = ("completed" if all(r["expected_result_observed"] for r in report["comparisons"].values())
                        else "rejected")
    save()
    require(report["status"] == "completed", "Fixture policy did not qualify")


if __name__ == "__main__":
    main()
