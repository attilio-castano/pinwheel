"""Measure the coverage of SRAM boundary abstraction, never internal LVS.

Inputs are the native abstract GDS extraction, supplied CDL and supplied LEF.
Only the declared macro interface is compared. The internal-width control is
deliberately invisible; this is a coverage limitation, not a successful check.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

MACRO = "RM_IHPSG13_1P_512x64_c2_bm_bist"
TOP = "SRAM_BOUNDARY"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(pin):
    if pin in ("VDD!", "VDDARRAY!", "VSS!"):
        return pin[:-1]
    m = re.fullmatch(r"(A_[A-Z_]+)<([0-9]+)>", pin)
    return f"{m[1]}[{m[2]}]" if m else pin


def boundary(text, expected, empty=False):
    joined = re.sub(r"\n\+\s*", " ", text)
    blocks = re.findall(r"(?ims)^\.subckt ([^\n]+)\n(.*?)^\.ends[^\n]*", joined)
    found = [(h.split()[1:], b) for h, b in blocks if h.split()[0] == MACRO]
    require(len(found) == 1, "Exactly one supplied macro definition required")
    pins, body = found[0]
    mapped = [canonical(p) for p in pins]
    require(len(pins) == len(set(pins)) == len(set(mapped)) == 351,
            "Missing, duplicate or colliding macro pins")
    require(set(mapped) == expected, "Macro interface differs from independent LEF")
    if empty:
        require(not any(s.strip() and not s.lstrip().startswith("*")
                        for s in body.splitlines()), "Native macro is not abstract")
    return mapped


def wrapper(pins, expected, fault=None):
    # Each external terminal is independent, so this fixture tests every name.
    # Actual chip ties and wiring are covered by the separate retained chip run.
    names = {p: "N" + str(i) for i, p in enumerate(sorted(expected))}
    terminals = [names[p] for p in pins]
    if fault:
        original, replacement = fault
        terminals[pins.index(original)] = names[replacement]
    return ("* Boundary-only diagnostic; no SRAM internal devices\n.subckt " +
            MACRO + " " + " ".join(pins) + "\n.ends\n.subckt " + TOP + " " +
            " ".join(names.values()) + "\nXmemory " + " ".join(terminals) +
            " " + MACRO + "\n.ends\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["abstract-spice", "cdl", "lef", "setup", "output"]:
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir()  # Never overwrite an executed comparison.
    expected = {canonical(p) for p in re.findall(r"^\s+PIN (\S+)", args.lef.read_text(), re.M)}
    require(len(expected) == 351, "Unexpected LEF interface")
    raw = args.abstract_spice.read_text()
    source = args.cdl.read_text()
    layout_pins = boundary(raw, expected, empty=True)
    source_pins = boundary(source, expected)
    # Change one internal parameter in a separate diagnostic source. The
    # projection must be blind to it; no device is read by this comparison.
    pattern = r"(?m)^(R1 BLC_BOT BLC_TOP lvsres w=)2\.6e-07( l=6e-07)$"
    mutant, count = re.subn(pattern, r"\g<1>2.0e-07\2", source)
    require(count == 1 and mutant != source, "Expected one source width token")
    mutant_path = out / "internal-width-counterfactual.cdl"
    mutant_path.write_text(mutant)
    mutant_pins = boundary(mutant, expected)
    require(mutant_pins == source_pins, "Internal control changed boundary")
    report = dict(status="running", macro_internal_qualified=False,
        chip_qualified=False, pins=351,
        boundary="One-instance interface fixture; actual chip wiring is separate",
        inputs_sha256={str(p): digest(p) for p in
            [args.abstract_spice, args.cdl, args.lef, args.setup, Path(__file__)]},
        internal_control=dict(changed_tokens=1, original_width_um=0.260,
            counterfactual_width_um=0.200, projected_interfaces_identical=True,
            original_cdl_sha256=digest(args.cdl), mutant_cdl_sha256=digest(mutant_path)),
        cases={})

    def save():
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    save()
    for label, pins, fault, want in [
        ("source-boundary", source_pins, None, True),
        ("internal-width-blind", mutant_pins, None, True),
        ("address-to-ground", source_pins, ("A_ADDR[0]", "VSS"), False),
        ("ground-to-power", source_pins, ("VSS", "VDD"), False),
    ]:
        case = out / label
        case.mkdir()
        left, right = case / "layout.spice", case / "source.spice"
        left.write_text(wrapper(layout_pins, expected, fault))
        right.write_text(wrapper(pins, expected))
        rpt = case / "lvs.rpt"
        cmd = ["netgen", "-batch", "lvs", f"{left} {TOP}", f"{right} {TOP}",
               str(args.setup), str(rpt), "-blackbox", "-json"]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        (case / "tool.log").write_text(result.stdout + result.stderr)
        native = rpt.read_text() if rpt.exists() else ""
        final = re.findall(r"^Final result: (.*)$", native, re.M)
        verdict = final[-1] if final else None
        passed = verdict == "Circuits match uniquely."
        report["cases"][label] = dict(returncode=result.returncode,
            native_final_result=verdict, expected_match=want,
            expected_behavior_observed=passed == want, fault=fault,
            command=cmd, layout_sha256=digest(left), source_sha256=digest(right))
        save()
        require(result.returncode == 0 and verdict is not None, "Native comparison failed to complete")
        require(passed == want, "Unexpected boundary sensitivity: " + label)
    require((out/"source-boundary/source.spice").read_bytes() ==
            (out/"internal-width-blind/source.spice").read_bytes(), "Projection differs")
    report["status"] = "coverage_demonstrated"
    save()
    print(json.dumps({k: report[k] for k in ["status", "pins", "macro_internal_qualified"]}))


if __name__ == "__main__":
    main()
