"""Native import-boundary fixtures; run only in the pinned, offline image."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path(sys.argv[1]).resolve()
out = Path(sys.argv[2]).resolve()
out.mkdir(exist_ok=False)
started = time.monotonic()
EXPECTED_ELF = "6ba87b45c762ee8c9670375c204cd03d801a6da98cd6e056a1c73027aad68a7c"

def definition(case):
    width = 140 if case in ("wide", "fixed") else 70
    plain = case in ("plain", "empty")
    use = "CLOCK" if not plain else "SIGNAL"
    assignment = "" if plain else " + NONDEFAULTRULE keepRule"
    routes = []
    if case != "empty":
        routes = ["metal1 ( 10000 10000 ) ( 20000 10000 )"]
        if not plain:
            routes += [
                "metal1 TAPER ( 20000 10000 ) ( 30000 10000 )",
                "metal2 ( 30000 10000 ) ( 30000 30000 )",
                "metal2 TAPER ( 20000 10000 ) ( 20000 30000 )",
                "metal1 TAPER ( 10000 14000 0 ) ( 20000 14000 120 )",
                "metal1 ( 10000 16000 100 ) ( 20000 16000 0 )",
                "metal1 ( 30000 10000 ) via1_0",
                "metal1 TAPER ( 20000 10000 ) via1_0",
                "metal1 TAPER ( 20000 10000 ) RECT ( -35 -35 35 35 )",
            ]
    if case == "distinct_rule":
        routes += ["metal1 TAPERRULE otherRule ( 30000 18000 ) ( 40000 18000 )"]
    if case == "ndr_rect":
        routes += ["metal1 ( 30000 18000 ) RECT ( -35 -35 35 35 )"]
    if case == "ambiguous":
        routes += ["metal1 TAPER ( 10000 10000 ) ( 20000 10000 )"]
    if case == "unmatched":
        routes = ["metal1 ( 10000 10000 ) ( 20000 10000 ) ( 30000 10000 )"]
    kind = "FIXED" if case == "fixed" else "ROUTED"
    route_text = ("\n  + " + kind + " " + "\n    NEW ".join(routes)) if routes else ""
    return f"""VERSION 5.8 ;
DIVIDERCHAR "/" ;
BUSBITCHARS "[]" ;
DESIGN taper_fixture ;
UNITS DISTANCE MICRONS 1000 ;
DIEAREA ( 0 0 ) ( 100000 100000 ) ;
TRACKS X 70 DO 716 STEP 140 LAYER metal1 ;
TRACKS Y 70 DO 716 STEP 140 LAYER metal1 ;
TRACKS X 95 DO 527 STEP 190 LAYER metal2 ;
TRACKS Y 95 DO 527 STEP 190 LAYER metal2 ;
NONDEFAULTRULES 2 ;
 - keepRule
  + LAYER metal1 WIDTH {width} SPACING 130
  + LAYER metal2 WIDTH {width} SPACING 160 ;
 - otherRule
  + LAYER metal1 WIDTH 210 SPACING 260
  + LAYER metal2 WIDTH 210 SPACING 320 ;
END NONDEFAULTRULES
COMPONENTS 0 ;
END COMPONENTS
PINS 2 ;
 - p0 + NET n + DIRECTION INPUT + USE {use}
  + LAYER metal1 ( -35 -35 ) ( 35 35 ) + FIXED ( 10000 10000 ) N ;
 - p1 + NET n + DIRECTION OUTPUT + USE {use}
  + LAYER metal1 ( -35 -35 ) ( 35 35 ) + FIXED ( 30000 10000 ) N ;
END PINS
NETS 1 ;
 - n ( PIN p0 ) ( PIN p1 ) + USE {use}{assignment}{route_text} ;
END NETS
END DESIGN
"""

def route_sections(path):
    text = path.read_text()
    result = {}
    for section in ["NETS", "SPECIALNETS", "NONDEFAULTRULES"]:
        match = re.search(r"(?ms)^" + section + r"\s+\d+\s*;\s*(.*?)^END " + section + r"\s*$", text)
        result[section] = " ".join(match[1].split()) if match else None
    return result

cases = [("plain", "original", True), ("plain", "patched", True),
         ("same_width", "original", False), ("same_width", "patched", True),
         ("wide", "original", False), ("wide", "patched", True),
         ("fixed", "patched", True),
         ("distinct_rule", "patched", False), ("ndr_rect", "patched", False),
         ("ambiguous", "patched", False), ("unmatched", "patched", False),
         ("empty", "patched", False)]
results = []
for case, variant, expected in cases:
    folder = out / (case + "-" + variant)
    folder.mkdir()
    (folder / "input.def").write_text(definition(case))
    commands = [
        f"read_lef {root}/fixtures/Nangate45.lef",
        f"read_def {folder}/input.def",
        f"write_def {folder}/before.def",
        f"write_db {folder}/before.odb",
        f"load {root}/native-03/{variant}/libpinwheel_drt_preservation.so Pinwheeldrtpreservation",
        "pinwheel_drt_preservation_roundtrip",
        f"write_def {folder}/after.def",
        f"write_db {folder}/after.odb",
    ]
    worker = """import hashlib,os
from pathlib import Path
from openroad import Tech,Design
assert hashlib.sha256(Path('/proc/self/exe').read_bytes()).hexdigest()==ELF
tech=Tech();design=Design(tech)
for command in COMMANDS:
 status=design.evalTclString('if {[catch {\\n'+command+'\\n} msg opts]} {set ::pw_error $msg;set ::pw_status ERROR} else {set ::pw_status OK}')
 if status!='OK':raise RuntimeError(design.evalTclString('set ::pw_error'))
print('PINWHEEL_FIXTURE_ROUNDTRIP_COMPLETED',flush=True)
""".replace("ELF", repr(EXPECTED_ELF)).replace("COMMANDS", repr(commands))
    (folder / "worker.py").write_text(worker)
    environment = dict(os.environ, PW_DRT_PRESERVATION_AUDIT=str(folder / "import-audit.json"), PYTHONDONTWRITEBYTECODE="1")
    assert time.monotonic() - started + 20 < 300, "Fixture aggregate native budget exhausted"
    begin = time.monotonic()
    with (folder / "native.log").open("x") as log:
        process = subprocess.run(["openroad", "-python", "-exit", "-threads", "1", "-no_splash", str(folder / "worker.py")], stdout=log, stderr=subprocess.STDOUT, env=environment, timeout=20)
    log = (folder / "native.log").read_text()
    audit = json.loads((folder / "import-audit.json").read_text()) if (folder / "import-audit.json").exists() else None
    actual = process.returncode == 0 and "PINWHEEL_FIXTURE_ROUNDTRIP_COMPLETED" in log
    record = {"case": case, "variant": variant, "expected_success": expected, "returncode": process.returncode,
              "native_seconds": round(time.monotonic() - begin, 3), "actual_success": actual,
              "input_def_sha256": hashlib.sha256((folder / "input.def").read_bytes()).hexdigest(),
              "audit": audit, "route_and_rule_sections_exact": False}
    if actual:
        record["route_and_rule_sections_exact"] = route_sections(folder / "before.def") == route_sections(folder / "after.def")
    expected_error = {
        "distinct_rule": "distinct per-path TAPERRULE is unsupported",
        "ndr_rect": "NDR RECT cannot be represented faithfully",
        "ambiguous": "unmatched or ambiguous imported geometry/per-path rules before GC",
        "unmatched": "unmatched or ambiguous imported geometry/per-path rules before GC",
        "empty": "unmatched or ambiguous imported geometry/per-path rules before GC",
    }.get(case, "unmatched or ambiguous imported geometry/per-path rules before GC")
    record["gate_passed"] = actual == expected and (
        record["route_and_rule_sections_exact"] and audit and audit["status"] == "passed" if expected
        else expected_error in log and "Start pin access" not in log and "Start detail routing" not in log)
    results.append(record)
    (out / "progress.json").write_text(json.dumps(results, indent=2) + "\n")
    print(case, variant, process.returncode, record["gate_passed"], flush=True)
report = {"schema": "pinwheel-drt-preservation-native-regression-v1", "status": "passed" if all(r["gate_passed"] for r in results) else "failed",
          "actual_elf_sha256_required": EXPECTED_ELF, "before_any_PA_GC_TA_DR": True,
          "fixture_count": len(results), "native_seconds": round(time.monotonic() - started, 3), "cases": results,
          "boundary": "Native import/writer regressions qualify supported per-path rules and geometry, not routing closure. Real P2 ordinary-main end0 identity is a separate mandatory gate."}
(out / "regression.json").write_text(json.dumps(report, indent=2) + "\n")
assert report["status"] == "passed", "Native preservation regression failed; inspect retained individual outputs"
print(report["status"], len(results), "native import fixtures", flush=True)
