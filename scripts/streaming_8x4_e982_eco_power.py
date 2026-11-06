"""Report the exact fanout ECO's cell-level power deltas and decap geometry."""

import argparse
from collections import Counter
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import re
import sys

from streaming_8x4_enclosure_admission import def_components, require
from streaming_tt_signoff import decode, sha


ROOT = Path(__file__).resolve().parents[1]
BASE = "build/tt-rehearsal-20261104/views/design.def"
ECO = "build/e982-fanout-20261104/five-01"
INPUTS = {
    BASE: "8802555ed7800ac6bcf92680793380d4a0a4deee0f7e6cd584044c084fe86350",
    f"{ECO}/trial.def": "fbccaa1f145b74050eb5ff257db80cbdd9a3a1b56a530ab27a2d6ba9ad6d23ff",
    f"{ECO}/trial.odb": "e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9",
    f"{ECO}/stream/design.gds": "dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82",
    f"{ECO}/partition.json": "906430380175db7dc7f4cc118d6114a0a6a2352f0dde3c12ccd8b3a3752de215",
}
LIBERTY = {
    "fast_1p32V_m40C": "af12d75a72d19648fa690027d29843fbae550aa91f4e40dd3339c7116d6e425d",
    "typ_1p20V_25C": "34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad",
    "slow_1p08V_125C": "3ee222c580ba33acb2131ac2bf224ff8ee9700751835b73aaec72b670bb31d3c",
}
SPICE = "7dd7f87104bf1c539be47a7dc2510166bc82e060fc0139d97d8617cdf8f4c5da"
MODEL_REVISION = "2bbec755dc67ca3db0261c3d6163e15735d66710"
# Resolved SG13G2 model bytes shared by the SG13CMOS5L source links.
MODEL_BLOBS = {
    "cornerMOSlv.lib": "f86c3efa204a27a4bcadd3cf3fcd67da8793b293",
    "sg13g2_moslv_mod.lib": "71ed6d7c7e2117d7d44d00225862a9a598802e39",
    "sg13g2_moslv_parm.lib": "b159fc32a1dd3f21c71d62b14a7e46b6922e97ab",
}
# PSP 103.6 TT parameter card values. Both TOXO multipliers equal one.
TOXO_NM = {"sg13_lv_nmos": "2.2404", "sg13_lv_pmos": "1.9704"}
DECAP = b"sg13cmos5l_decap_4"
BUFFER = b"sg13cmos5l_buf_1"
DECAP8 = b"sg13cmos5l_decap_8"
POSITION = re.compile(rb"\+ PLACED \( (\d+) (\d+) \) (\w+) ;$")
SCALAR = r"-?[0-9]+(?:\.[0-9]+)?"


def capture(pattern, text, label):
    matches = re.findall(pattern, text, re.M)
    require(len(matches) == 1, f"Missing or repeated {label}")
    return matches[0]


def check_model_bytes(directory):
    """Optionally verify full local model cards against the observed resolved Git blobs."""
    text = {}
    for name, expected in MODEL_BLOBS.items():
        data = (directory / name).read_bytes()
        blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        require(blob == expected, f"Wrong pinned LV model blob: {name}")
        text[name] = data.decode("ascii")
    tt = capture(r"(?s)^\.LIB mos_tt\n(.*?)^\.ENDL mos_tt$", text["cornerMOSlv.lib"], "mos_tt")
    parameters = text["sg13g2_moslv_parm.lib"]
    for suffix, mos in (("nmos", "sg13_lv_nmos"), ("pmos", "sg13_lv_pmos")):
        multiplier = capture(rf"^\s*\.param sg13g2_lv_{suffix}_toxo\s*=\s*({SCALAR})\s*$", tt, "TOXO multiplier")
        model = capture(rf"(?s)^\.model sg13g2_lv_{suffix}_psp\s+psp103va\s+(.*?)(?=^\.model|\Z)",
                        parameters, f"PSP {suffix} model")
        value = capture(rf"^\+ toxo\s*=\s*'({SCALAR}e-09)\*sg13g2_lv_{suffix}_toxo'", model, "TOXO")
        require(Decimal(value) * Decimal(multiplier) * Decimal("1e9") == Decimal(TOXO_NM[mos]),
                f"Wrong nominal oxide parameter: {mos}")


def positions(row):
    match = POSITION.search(row[1])
    require(match is not None, f"Missing placed coordinate: {row[0]!r}")
    x, y, orient = match.groups()
    return int(x), int(y), orient.decode()


def replacement_census(workspace):
    _, before = def_components(workspace / BASE)
    _, after = def_components(workspace / ECO / "trial.def")
    partition = decode((workspace / ECO / "partition.json").read_bytes())
    removed, added = set(before) - set(after), set(after) - set(before)
    require(len(before) == len(after) == 98900 and len(removed) == len(added) == 5
            and all(after[name] == before[name] for name in before.keys() - removed),
            "Unexpected retained cell, placement or replacement count")
    require({item["new_instance"].encode() for item in partition["operations"]} == added
            and {cell.encode() for item in partition["operations"] for cell in item["site"][3]} == removed,
            "Partition and actual replacement membership differ")
    old_counts = Counter(row[0] for row in before.values())
    new_counts = Counter(row[0] for row in after.values())
    require(new_counts - old_counts == {BUFFER: 5} and old_counts - new_counts == {DECAP: 5},
            "Unexpected power-relevant master census delta")
    retained = {name: (row[0], positions(row)) for name, row in after.items() if row[0] in {DECAP, DECAP8}}
    placements = {}
    for item in partition["operations"]:
        x, y, orient, replaced = item["site"]
        old, = replaced
        new = item["new_instance"]
        require(before[old.encode()][0] == DECAP and after[new.encode()][0] == BUFFER
                and positions(before[old.encode()]) == positions(after[new.encode()])
                == (x, y, {"R0": "N", "MX": "FS"}[orient]), f"Wrong swap placement: {new}")
        distances = [(max(abs(px - x), abs(py - y)), name, master)
                     for name, (master, (px, py, _)) in retained.items()]
        closest, name, master = min(distances)
        placements[item["source_net"]] = dict(removed=old, added=new, location_dbu=[x, y], orientation=orient,
            nearest_decap=dict(instance=name.decode(), master=master.decode(), max_axis_dbu=closest),
            decaps_in_illustrative_10000_dbu_square=sum(distance <= 10000 for distance, *_ in distances))
    counts = {master.decode(): [old_counts[master], new_counts[master]] for master in (DECAP, DECAP8, BUFFER)}
    return counts, placements


def liberty_delta(text, count):
    require('  leakage_power_unit : "1pW";' in text and "  capacitive_load_unit (1,pf);" in text
            and '  voltage_unit : "1V";' in text, "Unexpected Liberty units")
    voltage = Decimal(capture(rf"^  nom_voltage : ({SCALAR});$", text, "nom_voltage"))
    temperature = int(capture(r"^  nom_temperature : (-?[0-9]+);$", text, "nom_temperature"))
    cells = {}
    for name in (BUFFER, DECAP, DECAP8):
        cells[name] = capture(rf"(?s)^  cell \({name.decode()}\) \{{\n(.*?)^  \}}$", text, name.decode())
    leakage = {name: Decimal(capture(rf"^    cell_leakage_power : ({SCALAR});$", cell, "cell leakage"))
               for name, cell in cells.items()}
    require("    is_decap_cell : true;" in cells[DECAP] and "    is_decap_cell : true;" in cells[DECAP8],
            "Liberty lacks the decap classification")
    buffer_states = [Decimal(value) for value in re.findall(rf"^      value : ({SCALAR});$", cells[BUFFER], re.M)]
    require(len(buffer_states) == 2, "Expected two Liberty buffer leakage states")
    pin = capture(r"(?s)^    pin \(A\) \{\n(.*?)^    \}$", cells[BUFFER], "buffer input A")
    cap_pf = Decimal(capture(rf"^      capacitance : ({SCALAR});$", pin, "input capacitance"))
    sum_ff = cap_pf * count * 1000
    return dict(voltage_v=str(voltage), temperature_c=temperature,
                buffer_cell_leakage_pw=str(leakage[BUFFER]), decap4_cell_leakage_pw=str(leakage[DECAP]),
                delta_nominal_cell_leakage_nw=str((leakage[BUFFER] - leakage[DECAP]) * count / 1000),
                delta_state_leakage_nw=[str((state - leakage[DECAP]) * count / 1000)
                                        for state in (min(buffer_states), max(buffer_states))],
                sum_added_signal_input_capacitance_ff=str(sum_ff),
                input_pin_charging_only_at_50mhz_1_rise_per_cycle_uw=str(
                    round(sum_ff * voltage**2 * Decimal("0.05"), 6)))


def oxide_scale(spice, count):
    cell = capture(r"(?s)^\.subckt sg13cmos5l_decap_4 VDD VSS\n(.*?)^\.ends$", spice, "decap_4 subckt")
    widths = {
        "sg13_lv_nmos": capture(r"^XN0 VSS VDD VSS VSS sg13_lv_nmos w=([0-9.]+)n l=1\.000u ng=1 .+ m=1$",
                               cell, "decap NMOS"),
        "sg13_lv_pmos": capture(r"^XP0 VDD VSS VDD VDD sg13_lv_pmos w=([0-9.]+)u l=1\.000u ng=1 .+ m=1$",
                               cell, "decap PMOS"),
    }
    areas = {"sg13_lv_nmos": Decimal(widths["sg13_lv_nmos"]) / 1000,
             "sg13_lv_pmos": Decimal(widths["sg13_lv_pmos"])}
    # F/m × square microns / nm gives fF after multiplying by 10^12.
    eps_ox = Decimal("8.8541878128e-12") * Decimal("3.9")
    value = sum(eps_ox * area * Decimal("1e12") / Decimal(TOXO_NM[mos]) for mos, area in areas.items())
    return dict(drawn_gate_area_um2={key: str(area) for key, area in areas.items()}, toxo_nm=TOXO_NM,
                oxide_scale_per_decap_ff=str(round(value, 1)), oxide_scale_removed_ff=str(round(value * count, 1)),
                scope="Parallel-plate drawn-area scale using nominal PSP TOXO. No effective pin capacitance "
                      "or bound. Bias, effective geometry, overlap, fringe, interconnect and replacement "
                      "buffer supply admittance require an electrical model.")


def report(workspace, pdk, model_directory):
    for path, expected in INPUTS.items():
        require(sha(workspace / path) == expected, f"Wrong frozen input: {path}")
    counts, placements = replacement_census(workspace)
    if model_directory is not None:
        check_model_bytes(model_directory)
    library = pdk / "libs.ref" / "sg13cmos5l_stdcell"
    spice = library / "spice" / "sg13cmos5l_stdcell.spice"
    require(sha(spice) == SPICE, "Wrong pinned standard-cell SPICE")
    count = len(placements)
    corners = {}
    for corner, expected in LIBERTY.items():
        path = library / "lib" / f"sg13cmos5l_stdcell_{corner}.lib"
        require(sha(path) == expected, f"Wrong pinned Liberty: {corner}")
        corners[corner] = liberty_delta(path.read_text(), count)
    return dict(schema="pinwheel.e982-eco-cell-power-observation.v1", inputs_sha256=INPUTS,
        liberty_sha256=LIBERTY, cell_spice_sha256=SPICE, pdk_revision=MODEL_REVISION,
        model_card_git_blobs=MODEL_BLOBS, local_model_cards_reopened=model_directory is not None,
        count_before_after=counts, placements=placements, liberty=corners,
        oxide_geometry=oxide_scale(spice.read_text(), count), spice_executed=False,
        dynamic_power_delta_qualified=False, transient_droop_qualified=False, power_qualified=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdk", type=Path, required=True, help="Path to the pinned ihp-sg13cmos5l directory")
    parser.add_argument("--workspace", type=Path, default=ROOT)
    parser.add_argument("--model-directory", type=Path, help="Optional full PDK ngspice models directory")
    args = parser.parse_args()
    try:
        result = report(args.workspace, args.pdk, args.model_directory)
    except (OSError, ValueError, KeyError) as error:
        print(f"Power observation rejected: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
