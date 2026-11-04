"""Admit the exact November 4 e982 physical continuation evidence, read-only."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
from xml.etree import ElementTree


TOP = "tt_um_pinwheel_streaming_ready_d2"
PREFILL_ODB = "e982e1a2949db8d6f34ef2666002b31be2a770093a0631e98b3442a27387c8f4"
POSTFILL_ODB = "be42e7dd1729c3d56ac08b7f02d90c7ce5c58e11c1d5bf9539b4e829f116a41e"
POSTFILL_GDS = "97f916dee9b33831c4935d0615a3e13af4bf14eebd201f3f72a066d19c160ec4"
MAIN_DECK = "12b03e309986ed7f079ca9283eb29d6635918f53ddd09c3c82ea232cca739567"
MAXIMAL_DECK = "e793b434ff6a2fc0fd44a3bbad3688ca6019aa89bdb8367632a848d1b6586bf9"
ENCLOSURE_SUBSET = "457b2aff2f55aa5c38a9d47493c773385c336bb72c639e3c504818ae4ee6fc85"
MAIN_GENERATOR = "/work/pdk/ihp-sg13cmos5l/libs.tech/klayout/tech/drc/ihp-sg13cmos5l.drc"
ENCLOSURE_GENERATOR = "/work/export/maximal-enclosure-subset.drc"
ENCLOSURE_RULES = (
    "M1.c", "M1.c1", "M2.c", "M2.c1", "M3.c", "M3.c1", "M4.c", "M4.c1",
    "V1.c1", "V2.c1", "V3.c1",
)
WARNING_LINES = tuple(
    "[WARNING DRT-0349] LEF58_ENCLOSURE with no CUTCLASS is not supported. Skipping for layer " + layer
    for layer in ("Cont", "Via1", "Via1", "Via2", "Via3", "TopVia1", "TopVia1")
)
DIAGNOSTIC = re.compile(
    r"\[(?:WARNING|ERROR|FATAL)\b|^\s*(?:WARNING|ERROR|FATAL)\b|"
    r"\b\w*(?:Warning|Error)\s*:|Traceback \(most recent call last\)", re.I | re.M,
)

# Pin the actual receipts and sidecars that they do not themselves digest. These
# anchors deliberately admit one observation, rather than define a general warning exception.
CHECK_PINS = {
    "execution.json": "fea720332531d799fb517f432b003e9645e683fcf449a9be6884afc112c8fd8d",
    "independent-readback.json": "7ed52dbaa154f3a4bc94cf5fac1cc7246c037dab18a34d5ab539d9509bd39bf3",
    "invocation.json": "e08c534bc21643f5e8c05eb0e32f28d4b1427e9aa5d5a53c833618bac739cff6",
    "native.py": "f0cb0a93547a6e76ef1ab98d5d47b308e03f1da65dde7f13474269bd4ee9becf",
    "container.log": "4c3ce2764c3c1ca3a3e624f2acfca5b6b9aad0198dea95d79018cbf9be24b228",
    "flow/step/fullbox.log": "7cf82e5485a5fd872cb185093315ad73009be974519210e7a98812e9ce878a06",
    "flow/step/whole-antenna.log": "752bcec5c27bafec8873845d5785cfe2f12e618ce3f1e8776c35a735edbc42a7",
    "flow/step/net840-antenna.log": "8d08b1ff1caf34260d7289339a4827017199549737d2907b9ab1d106ded19eac",
}
FILL_PINS = {
    "independent-readback.json": "1b27ac7930ce35a899a0069d74cb15cf181393ef1f162d135131634e36c86f7f",
    "native/execution.json": "14615bc0e848c2f88f2bfd4c3bbea0f8e7236960ec4f7c99b7b0add8aa4a61f7",
    "native/fill.py": "28b5d22d2bf8ac16ca27133f4ab776527cddafdec6d87fcc9d9ec2d56d4e1d75",
    "native/fill-command.json": "274d3f16f77feb38702b3da5ea8b3922c45d5d4de3cc6079bfeed513070a1250",
    "native/fill.log": "68c533e2c97033bced54c8ce42b2e5676e663b3d2078b38739ac7372f32c814b",
    "native/enclosure-source.json": "144a19918ae5601317a755b1053ceadd8ea7c0efb5deffd44968009082fb5c32",
    "native/enclosure.log": "69758a9e857ab890502c0eca7e06169fbe7f18541b98295e51a3a5602eed259e",
    "native/enclosure-deck.log": "9415f4386257d6f36ea1d5480900c9a71c30b9f644489cf2307d2c4803b99886",
    "native/drc.log": "f2b8e40665eaec943fb983e6224454f66294a46878fce9096a47e26aeab0899e",
    f"native/{TOP}.pnl.v": "e96a9ba1da1ce4560180e118342b793b713c5413406ddee930b4b6f5e110c5e1",
    "native/postfill-antenna.tcl": "6e8216037bac5748eea87da6599e8550920723c5ed68a621b3d50c547f49e845",
    "native/reexport.tcl": "cfdbaa57de4cf5eba7709f04b333036e8352ea6e58b2e2f3bd871bcadaa522bf",
}
FILLERS = {"sg13cmos5l_decap_4": 5678, "sg13cmos5l_decap_8": 31183,
           "sg13cmos5l_fill_1": 10826, "sg13cmos5l_fill_2": 9009}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    require(path.is_file(), f"Missing regular evidence file: {path}")
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def match_digest(path, expected):
    require(digest(path) == expected, f"Evidence SHA-256 differs: {path}")


def check_pins(root, pins):
    for name, expected in pins.items():
        match_digest(root / name, expected)


def read_json(path):
    return json.loads(path.read_text())


def check_inputs(receipt):
    require(receipt["target_odb_sha256"] == PREFILL_ODB and receipt["frozen_inputs_unchanged"] is True,
            "Execution does not bind the original e982 input with closed custody")
    inputs = receipt["input_sha256"]
    for name, expected in inputs.items():
        match_digest(Path(name), expected)
    seeds = [Path(name) for name, value in inputs.items() if Path(name).name == "applied.odb" and value == PREFILL_ODB]
    require(len(seeds) == 1, "Exact original e982 ODB binding missing")
    return seeds[0]


def validate_checker_logs(fullbox, raw):
    begin = "PINWHEEL_POLICY2_FULLBOX_BEGIN\n"
    end = "PINWHEEL_POLICY2_FULLBOX_END\n"
    complete = "PINWHEEL_POLICY2_CHECKS_COMPLETE\n"
    require(raw.count(begin) == raw.count(end) == raw.count(complete) == 1,
            "Missing or repeated raw checker completion boundaries")
    before, scoped = raw.split(begin)
    embedded, after = scoped.split(end)
    require(embedded + "\n" == fullbox and complete in after, "Captured fullbox does not match the raw checker")
    diagnostics = tuple(line for line in fullbox.splitlines() if DIAGNOSTIC.search(line))
    require(diagnostics == WARNING_LINES, "Fullbox diagnostics differ from the exact ordered seven warnings")
    require(not DIAGNOSTIC.search(before) and not DIAGNOSTIC.search(after),
            "Unexpected raw checker warning or error outside fullbox")


def validate_antenna(text, *, explicit, count):
    require(not DIAGNOSTIC.search(text) and not re.search(r"\bVIOLATED\b", text), "Unexpected antenna diagnostic")
    for code, name in (("0002", "net"), ("0001", "pin")):
        values = re.findall(rf"^\[INFO ANT-{code}\] Found (\d+) {name} violations\.$", text, re.M)
        require(values == ["0"] * count, f"Missing or nonzero {name} antenna counts")
    require(re.findall(r"^Net: (\S+)\s*$", text, re.M) == (["net840"] if explicit else []),
            "Wrong explicit antenna target")


def validate_checker(check):
    root = check / "checks"
    check_pins(root, CHECK_PINS)
    execution = read_json(root / "execution.json")
    seed = check_inputs(execution)
    require(execution["exit_code"] == 0 and execution["container_absent"] is True
            and 0 < execution["elapsed_seconds"] <= execution["timeout_seconds"], "Checker execution failed")
    match_digest(root / "checks.tcl", execution["checker_sha256"])
    invocation = read_json(root / "invocation.json")
    require(invocation["env"]["CURRENT_ODB"] == "/work/seed.odb", "Wrong checker input role")
    readback = read_json(root / "independent-readback.json")
    historical = seed.parents[2] / "checks"
    match_digest(historical / "native/inspection/native.json", readback["historical_inspection_sha256"])
    step = root / "flow/step"
    for extension in ("def", "tsv", "guides.tsv"):
        before = digest(step / f"before.{extension}")
        match_digest(historical / f"flow/step/before.{extension}", before)
        match_digest(step / f"after.{extension}", before)
    rows = (step / "checks.tsv").read_text().splitlines()
    require(rows == ["ROLE\tnet840\tSIGNAL\t0\tFIXED", "OTHER_ROUTED\t41780", "FULLBOX_MARKERS\t0",
                     "ARC_WHOLE\t0", "ARC_NET840\t0"] and (step / "fullbox.drc").read_bytes() == b"",
            "Fullbox and whole/explicit antenna results are incomplete or nonzero")
    require(readback["target_odb_sha256"] == PREFILL_ODB and readback["fresh_native_rows"] == rows
            and readback["exit_code"] == 0 and readback["checked_PG_rails_and_diode_pin_access"] is True
            and readback["checked_original_diode_count"] == readback["prior_diode_count"] == 160
            and readback["fresh_before_def_projection"]["complete_ordered_projection"] is True
            and readback["full_existing_readback_error"] == "Physical Policy2 has no ABI warning/error exception",
            "Independent checker readback or historical verdict differs")
    raw = (root / "container.log").read_text()
    validate_checker_logs((step / "fullbox.log").read_text(), raw)
    for name, explicit in (("whole-antenna.log", False), ("net840-antenna.log", True)):
        text = (step / name).read_text()
        require(text.removesuffix("\n") in raw, f"Captured {name} differs from raw checker")
        validate_antenna(text, explicit=explicit, count=1)
    return seed, step / "before.def"


def def_components(path):
    data = path.read_bytes()
    parts = list(re.finditer(rb"(?ms)^COMPONENTS (\d+) ;\n(.*?)^END COMPONENTS\n", data))
    require(len(parts) == 1, f"Missing or repeated DEF components section: {path}")
    part = parts[0]
    rows = list(re.finditer(rb"(?ms)^[ \t]*-[ \t]+(\S+)\s+(\S+).*?;", part[2]))
    result = {row[1]: (row[2], row[0]) for row in rows}
    require(len(result) == len(rows) == int(part[1]), f"Incomplete or duplicate DEF components: {path}")
    return data[:part.start()] + data[part.end():], result


def validate_geometry(before_path, after_path, powered_path):
    before_body, before = def_components(before_path)
    after_body, after = def_components(after_path)
    require(before_body == after_body and len(before) == 42204 and len(after) == 98900
            and all(after.get(name) == record for name, record in before.items()),
            "Filler insertion changed the original component or non-component DEF bytes")
    added = {name: master for name, (master, _) in after.items() if name not in before}
    require(Counter(master.decode() for master in added.values()) == FILLERS, "Unexpected fillers")
    power = re.findall(rb"(?m)^\s*(sg13cmos5l_(?:decap_[48]|fill_[12]))\s+(\S+)\s+"
                       rb"\(\.VDD\(VPWR\),\s*\.VSS\(VGND\)\);", powered_path.read_bytes())
    require(len(power) == len(added) and {name: master for master, name in power} == added,
            "Filler rails are not fully bound")


def drc_report(path, generator):
    xml = ElementTree.parse(path).getroot()
    require(xml.tag == "report-database" and xml.findtext("top-cell") == TOP
            and xml.findtext("generator") == f"drc: script='{generator}'", f"Wrong KLayout report identity: {path}")
    names = [category.findtext("name") for category in xml.findall("./categories/category")]
    items = xml.findall("./items/item")
    require(xml.find("items") is not None and all(names) and len(names) == len(set(names)),
            f"Incomplete KLayout report structure: {path}")
    return set(names), Counter(item.findtext("category", "").strip("'") for item in items)


def validate_fill(fill, seed, checked_def):
    check_pins(fill, FILL_PINS)
    native = fill / "native"
    receipt = read_json(native / "execution.json")
    require(check_inputs(receipt) == seed, "Fill and checker refer to different e982 sources")
    phases = receipt["phases"]
    require([row["phase"] for row in phases] == ["fill", "enclosure", "drc"] and all(
        row["status"] == "completed" and row["exit_code"] == 0 and row["container_absent"] is True
        and 0 < row["elapsed_seconds"] <= row["timeout_seconds"] for row in phases), "Fill execution did not close")
    require(receipt["postfill_odb_sha256"] == POSTFILL_ODB and receipt["gds_sha256"] == POSTFILL_GDS
            and receipt["deck_sha256"] == MAIN_DECK and receipt["maximal_subset_sha256"] == ENCLOSURE_SUBSET,
            "Post-fill target or deck identities differ")
    for name, key in ((f"{TOP}.odb", "postfill_odb_sha256"), ("design.gds", "gds_sha256"),
                      ("design.def", "def_sha256"), (f"{TOP}.def", "def_sha256"),
                      ("postfill-antenna.log", "antenna_sha256"), ("drc_sg13cmos5l.xml", "drc_report_sha256"),
                      ("enclosure.xml", "enclosure_report_sha256"), ("maximal-enclosure-subset.drc", "maximal_subset_sha256")):
        match_digest(native / name, receipt[key])
    prefill = Path(next(name for name in receipt["input_sha256"] if name.endswith("/native/drc_sg13cmos5l.xml"))).parent
    match_digest(prefill / "design.def", digest(checked_def))
    validate_geometry(checked_def, native / "design.def", native / f"{TOP}.pnl.v")
    antenna = (native / "postfill-antenna.log").read_text()
    validate_antenna(antenna, explicit=True, count=2)
    require(antenna.endswith("POSTFILL_ARC_WHOLE 0\nPOSTFILL_ARC_NET840 0\nPOSTFILL_ANTENNA_COMPLETE\n"),
            "Post-fill antenna terminal result missing")
    require("113392 connections made, 0 conflicts skipped" in (native / "fill.log").read_text(), "Fill rails did not close")

    source = read_json(native / "enclosure-source.json")
    original = Path(source["source"])
    match_digest(original, MAXIMAL_DECK)
    lines = original.read_bytes().splitlines(keepends=True)
    subset = b"".join(b"".join(lines[start - 1:end]) for start, end in source["ranges"])
    require(subset == (native / "maximal-enclosure-subset.drc").read_bytes()
            and tuple(source["rule_names"]) == ENCLOSURE_RULES, "Supplemental deck differs from pinned source")
    pre_names, pre_items = drc_report(prefill / "drc_sg13cmos5l.xml", MAIN_GENERATOR)
    main_names, main_items = drc_report(native / "drc_sg13cmos5l.xml", MAIN_GENERATOR)
    enc_names, enc_items = drc_report(native / "enclosure.xml", ENCLOSURE_GENERATOR)
    require(pre_items == {"NW.b": 2697} and main_names == pre_names and len(main_names) == 332
            and not main_items, "Full main DRC coverage changed or has violations")
    require(enc_names == set(ENCLOSURE_RULES) and not enc_items, "Supplemental enclosure coverage changed or has violations")
    for name in ("fill.log", "drc.log", "enclosure.log", "enclosure-deck.log"):
        require(not DIAGNOSTIC.search((native / name).read_text()), f"Unexpected diagnostic in {name}")
    main_log = (native / "drc.log").read_text()
    require("Executing rule NW.b\n" in main_log and "KLayout DRC run for tables 'main' completed" in main_log,
            "Main-deck completion evidence missing")
    enclosure_log = (native / "enclosure.log").read_text()
    logged = re.findall(r"^Rule (\S+): (\d+) error\(s\)$", enclosure_log, re.M)
    require(logged == [(rule, "0") for rule in ENCLOSURE_RULES]
            and "Number of DRC errors for maximum rule set: 0\n" in enclosure_log
            and "KLayout DRC run for maximum ruleSet completed" in (native / "enclosure-deck.log").read_text(),
            "Supplemental raw completion evidence missing or nonzero")
    readback = read_json(fill / "independent-readback.json")
    require(readback["target_odb_sha256"] == PREFILL_ODB and readback["postfill_odb_sha256"] == POSTFILL_ODB
            and readback["postfill_gds_sha256"] == POSTFILL_GDS and readback["main_categories"] == 332
            and readback["postfill_main_items"] == 0 and readback["enclosure_items_by_rule"] == dict.fromkeys(ENCLOSURE_RULES, 0)
            and readback["enclosure_log_hier_counts"] == dict.fromkeys(ENCLOSURE_RULES, 0)
            and readback["physical_diagnostic_pass"] is True and readback["historical_warning_free_admission_closed"] is False,
            "Independent fill readback disagrees with raw evidence")


def admit(check, fill):
    seed, before_def = validate_checker(check)
    validate_fill(fill, seed, before_def)
    checked_files = {str(check / "checks" / name): pin for name, pin in CHECK_PINS.items()}
    checked_files.update({str(fill / name): pin for name, pin in FILL_PINS.items()})
    for root in (check / "checks", fill / "native"):
        receipt = read_json(root / "execution.json")
        checked_files.update(receipt["input_sha256"])
    checked_files.update({
        str(before_def): digest(before_def),
        str(fill / "native" / f"{TOP}.odb"): POSTFILL_ODB,
        str(fill / "native/design.gds"): POSTFILL_GDS,
    })
    return {
        "schema": "pinwheel.streaming-8x4-enclosure-admission.v1",
        "scope": "exact e982 standalone physical continuation with filler-only post-fill geometry",
        "admitted": True,
        "route_dispatch_admitted": True,
        "target_odb_sha256": PREFILL_ODB,
        "prefill_odb_sha256": PREFILL_ODB,
        "postfill_odb_sha256": POSTFILL_ODB,
        "postfill_gds_sha256": POSTFILL_GDS,
        "fullbox_drt_0349_warnings": list(WARNING_LINES),
        "postfill_main_categories": 332,
        "postfill_main_items": 0,
        "postfill_enclosure_items_by_rule": dict.fromkeys(ENCLOSURE_RULES, 0),
        "verified_file_sha256": dict(sorted(checked_files.items())),
        "historical_warning_free_admission_closed": False,
        "whole_route_replayed": False,
        "full_tapeout_ready": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path, required=True)
    parser.add_argument("--fill", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = admit(args.check.resolve(), args.fill.resolve())
    except (OSError, ValueError, KeyError, StopIteration, ElementTree.ParseError) as exc:
        parser.exit(1, f"Admission rejected: {exc}\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
