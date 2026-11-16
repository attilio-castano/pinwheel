"""Collect the pinned PDNSim matrix, voltage and current vectors for one retained case."""

import argparse
from pathlib import Path
import time

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import IMAGE, read, require, run_native, write
from streaming_8x4_hold_cap_ir import OPENROAD, VOLTAGES
from streaming_8x4_hold_cap_physical import TARGET, TRIAL, setup


GOLDEN = TRIAL / "power-dc/i2c-sparse-r1-sheet105-01"
GOLDEN_SHA = "3211a5a5a569fabbf408abccd5f4ba36873c2844efb9e8762c803069f4f05f74"
VERIFIED_PARENT = TRIAL / "power-dc/ir-em-readback.json"
VERIFIED_PARENT_SHA = "d1bb974807b3caf1e1daa85cbddd314e06dede45980074f6d8c932d03c8de7e9"
SOURCE_REL = "build/campaigns/8x4-20261024-01/final24-PG-lifetime-01/inputs/psm-source"
DUMP_NAMES = ("psm_nodes.txt", "psm_G.txt", "psm_J.txt", "psm_V.txt", "psm_cond.txt")


def pinned_source(history):
    source = history / SOURCE_REL
    manifest = read(source / "manifest.json")
    require(manifest["commit"] == OPENROAD, "Wrong retained PSM implementation")
    entries = {entry["path"]: entry for entry in manifest["files"]}
    files = {name: bound(source / name) for name in ("src/psm/src/ir_solver.cpp", "src/psm/src/ir_network.cpp")}
    require(all(item["sha256"] == entries[name]["sha256"] for name, item in files.items()),
            "Retained PSM source bytes differ")
    return {"manifest": bound(source / "manifest.json"), **files}


def golden_case():
    native_pin, parent_pin = bound(GOLDEN / "readback.json"), bound(VERIFIED_PARENT)
    require(native_pin["sha256"] == GOLDEN_SHA and parent_pin["sha256"] == VERIFIED_PARENT_SHA,
            "Prior PSM readbacks changed")
    native, parent = read(native_pin["path"]), read(parent_pin["path"])
    case, = [row for row in parent["cases"] if row["case"] == GOLDEN.name]
    require(case["native"] == native_pin and case["request"] == native["request"]
            and native["status"] == "completed" and native["qualification"] is False,
            "Golden case did not close in the prior readback")
    bindings = [native["request"], *native["artifacts"]]
    require(all(bound(item["path"]) == item for item in bindings), "Golden PSM artifact changed")
    request = read(native["request"]["path"])
    require(request["inputs"]["/input/trial.odb"]["sha256"] == TARGET["odb_sha256"]
            and request["target_gds_sha256"] == TARGET["gds_sha256"] and request["image"] == IMAGE
            and request["openroad_commit"] == OPENROAD and request["external_ohm_per_source"] == 1
            and request["sheet_temperature_c"] == 105 and request["activity"]["kind"] == "functional_vcd",
            "Wrong golden PSM case assumptions")
    return request, native, [native_pin, parent_pin, *bindings]


def instrument(original):
    flag = "    set_debug_level PSM solve 3\n"
    rails = "        puts \"PINWHEEL_DC_BEGIN $rail\"\n"
    export = "        write_pg_spice -net $rail"
    require(all(original.count(line) == 1 for line in (flag, rails, export)), "Unexpected PSM Tcl shape")
    return (original.replace(flag, flag + "    set_debug_level PSM dump 2\n")
            .replace(rails, rails + "        cd /work/export/$rail\n")
            .replace(export, "        cd /work/export\n" + export))


def run(history, out):
    require(out.parent == TRIAL / "power-dc" and not out.exists(), "Use a fresh power-dc case directory")
    context = setup(history)
    golden, native, inherited = golden_case()
    source = pinned_source(history)
    for name, pin in golden["liberty"].items():
        require(name.startswith("/work/pdk/")
                and bound(context["pdk"] / name.removeprefix("/work/pdk/"))["sha256"] == pin,
                "Golden Liberty changed")
    inputs = golden["inputs"]
    original = golden["analysis_tcl"]
    inherited.extend([original, *inputs.values(), *source.values()])
    require(all(bound(item["path"]) == item for item in inherited), "Golden input bytes changed")
    out.mkdir(exist_ok=False)
    for rail in VOLTAGES:
        (out / rail).mkdir()
    tcl = out / "analysis.tcl"
    tcl.write_text(instrument(Path(original["path"]).read_text()))
    producer = bound(Path(__file__).resolve())
    request = out / "request.json"
    write(request, dict(schema="pinwheel.streaming-8x4-psm-dump-request.v1", golden=bound(GOLDEN / "request.json"),
                        retained_artifacts=inherited, producer=producer, analysis_tcl=bound(tcl)))
    sealed = [producer, bound(tcl), bound(request)]
    mounts = [(Path(item["path"]), name, False) for name, item in inputs.items()]
    mounts.append((tcl, "/input/analysis.tcl", False))
    execution = run_native(context, out, "openroad", ["-exit", "-threads", "1", "-metrics",
                           "/work/export/metrics.json", "/input/analysis.tcl"], mounts,
                           360, int(time.time()) + 540, memory="6g")
    require(all(bound(item["path"]) == item for item in sealed + inherited), "Sealed PSM input changed")
    log = (out / "container.log").read_text()
    require(OPENROAD in log and all(log.count(f"PINWHEEL_DC_END {rail}") == 1 for rail in VOLTAGES),
            "Native PSM dump did not finish both rails")
    exact = [Path(item["path"]).name for item in native["artifacts"]
             if Path(item["path"]).name not in {"container.log", "execution.json"}]
    require(all(bound(out / name)["sha256"] == bound(GOLDEN / name)["sha256"] for name in exact),
            "Instrumented native results differ from golden bytes")
    dumps = {rail: {name: bound(out / rail / name) for name in DUMP_NAMES} for rail in VOLTAGES}
    write(out / "dump-receipt.json", dict(schema="pinwheel.streaming-8x4-psm-dump.v1", status="completed",
          target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"], request=bound(request),
          golden_readback=bound(GOLDEN / "readback.json"), golden_equal={name: bound(out / name) for name in exact},
          execution=bound(out / "execution.json"), log=bound(out / "container.log"),
          solver_dumps=dumps, elapsed_seconds=execution["elapsed_seconds"], qualified_ir_drop=False, qualified_em=False))
    print(out / "dump-receipt.json")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.history.resolve(strict=True), args.out.resolve())


if __name__ == "__main__":
    main()
