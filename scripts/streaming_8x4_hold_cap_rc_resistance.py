"""Measure sourced sheet and cut resistance sensitivity on the frozen 8x4."""

import argparse
from decimal import Decimal
import fcntl
import math
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys

import streaming_8x4_draft_rc_timing as draft
import streaming_8x4_e982_eco_electrical as electrical
import streaming_8x4_e982_eco_timing_readback as sta
import streaming_8x4_e982_parasitics_preflight as preflight
import streaming_8x4_hold_cap_timing_coverage as coverage
from streaming_8x4_e982_native import IMAGE, TOP, read, require, run_native, sha, write
from streaming_8x4_hold_cap_physical import TARGET, TRIAL, setup
from streaming_8x4_hold_cap_timing_intake import COVERAGE, COVERAGE_SHA, retained, verified
from streaming_8x4_model24_process import G, ITF_SHA, METALS
from streaming_8x4_model24_via import token_replace
from streaming_8x4_rc_r_length_geometry import local_lef
from streaming_tt_quality import inventory_context


SCHEMA = "pinwheel.streaming-8x4-hold-cap-sourced-resistance.v1"
OUT = Path("/work/export")
DEF = "/work/views/design.def"
LEGACY_SHA = "ffda02d57a6ecb39b02268be9511d89ef072911f17bd2dcd095f3f3cbeb5a905"
CUTS = ("Via1", "Via2", "Via3", "TopVia1")
MODELS = (*draft.MODELS, "legacy")
PVT = draft.CORNERS[:2]
PDK_REV = "89d42ee6d2fd9b50b86a1aada6fee6673c3e6008"
PORTS = {"ui_in[3]", "ui_in[5]"}
BASE_ENV = {"_TCL_ENV_IN": "/dev/null", "LC_ALL": "C"}
RCX_KEYS = ("CELL_LEFS", "PAD_LEFS", "DESIGN_NAME", "SCRIPTS_DIR", "VDD_PIN", "GND_PIN",
            "PDN_CONNECT_MACROS_TO_GRID", "PDN_ENABLE_GLOBAL_CONNECTIONS", "SCL_POWER_PINS",
            "SCL_GROUND_PINS", "RCX_MERGE_VIA_WIRE_RES")
NATIVE_SECONDS = 330
GIB = 1024 ** 3
STOCK_SCHEMA = "pinwheel.streaming-8x4-tt-clean-run.v1"

TCL = electrical.TCL.split('    puts "PINWHEEL_ELECTRICAL_CORNER $corner"', 1)[0] + r"""
    puts "==================== $corner Corner ===================="
    puts "report_parasitic_annotation -report_unannotated"
    puts "========================================================================"
    report_parasitic_annotation -report_unannotated
    puts "========================================================================"
    foreach mode {min max} {
        puts "PINWHEEL_RC_WORST $mode [worst_slack -corner $corner -$mode]"
        puts "PINWHEEL_RC_TNS $mode [total_negative_slack -corner $corner -$mode]"
        foreach port [all_inputs] {
            set name [get_full_name $port]
            if {$name ni {{ui_in[3]} {ui_in[5]}}} { continue }
            set paths [find_timing_paths -corner $corner -path_delay $mode -from $port \
                -endpoint_path_count 1 -group_path_count 1]
            if {[llength $paths] != 1} { error "Expected one constrained path for $name/$mode" }
            set path [lindex $paths 0]
            set start [get_full_name [get_property $path startpoint]]
            if {[$path is_unconstrained] || $start ne $name} { error "Unexpected path source or constraint" }
            puts "PINWHEEL_RC_PORT\t$mode\t$name\t[get_full_name [get_property $path endpoint]]\t[get_property $path slack]"
        }
    }
    puts "PINWHEEL_RC_MAX slew [sta::max_slew_violation_count]"
    puts "PINWHEEL_RC_MAX fanout [sta::max_fanout_violation_count]"
    puts "PINWHEEL_RC_MAX capacitance [sta::max_capacitance_violation_count]"
    report_check_types -corner $corner -max_slew -max_capacitance -max_fanout -violators
    puts "PINWHEEL_RC_COMPLETE $corner"
} message]} {
    puts stderr "PINWHEEL_RC_ERROR $message"
    exit 1
}
"""


def aligned_lef(original, itf, model):
    require(model in draft.MODELS, "Unknown modeled RC corner")
    verified(itf, ITF_SHA["ITF_" + model])
    rows = G.parse_itf(itf.read_text())
    sheets = {metal: rows[metal]["RPSQ"] for metal in METALS}
    cuts = {cut: rows[cut]["RPV"] for cut in CUTS}
    lef, sheet_evidence = local_lef(original, sheets)
    fields = []
    for cut, value in cuts.items():
        header = rf"^LAYER[ \t]+{cut}[ \t]*\n(?:(?!^END[ \t]).)*?"
        field = r"^[ \t]*RESISTANCE[ \t]+([0-9.eE+-]+)[ \t]*;"
        match, = re.finditer(header + field, lef, re.M | re.S)
        # Keep the exact installed token for a numerically identical corner.
        fields.append((header + field, match[1] if Decimal(match[1]) == Decimal(value) else value, cut))
    lef, cut_evidence = token_replace(lef, fields)
    require((lef == original) == (model == "MAX"), "The MAX LEF must remain byte-identical")
    return lef, dict(itf=draft.bound(itf), sheets=sheet_evidence, cut_edits=cut_evidence)


def prepare(context):
    rows, layout, pins, _ = coverage.prepare(context)
    old_timing = read(TRIAL / "timing/inputs/request.json")
    official = TRIAL.parent / "verification-ciel/ihp-sg13cmos5l"
    require((official / "SOURCES").read_text().strip() == "IHP-Open-PDK " + PDK_REV,
            "Current IHP source revision changed")
    specs = {}
    for model in draft.MODELS:
        journal = TRIAL / "timing/run" / model / "native-journal.jsonl"
        call, = [row for row in draft.calls(journal) if row["step"] == "OpenROAD.RCX"]
        env = call["env"]
        rcx_script = "scripts/openroad/rcx.tcl"
        require(call["argv"][-1] == env["SCRIPTS_DIR"] + "/openroad/rcx.tcl" and env["CURRENT_DEF"] == DEF
                and env["RCX_RULESET"] == f"/work/diagnostic/rules/{model}.rules"
                and env["RCX_MERGE_VIA_WIRE_RES"] == "1" and env["DESIGN_NAME"] == TOP,
                "Retained RCX invocation differs")
        tech = context["pdk"] / env["RCX_LEF"].removeprefix("/work/pdk/")
        original = verified(tech, draft.TECH_SHA).read_text()
        itf = official / f"libs.tech/parasitics/itf/sg13cmos5l_{model.lower()}.itf"
        lef, evidence = aligned_lef(original, itf, model)
        rules = verified(TRIAL / "timing/inputs/rules" / (model + ".rules"), draft.RULE_SHA[model])
        specs[model] = dict(tech_lef=lef, rules=draft.bound(rules), resistance=evidence,
                            openroad_sha256=call["executable_sha256"],
                            scripts={env["SCRIPTS_DIR"] + "/" + name.removeprefix("scripts/"): digest
                                     for name, digest in old_timing["native_package_sha256"].items()
                                     if name in {rcx_script, "scripts/openroad/common/io.tcl",
                                                 "scripts/openroad/common/set_global_connections.tcl",
                                                 "scripts/openroad/common/set_power_nets.tcl"}},
                            env={key: env[key] for key in RCX_KEYS})
        require(len(specs[model]["scripts"]) == 4, "Retained RCX Tcl closure differs")
        for native_path in (*env["CELL_LEFS"].split(), *env["PAD_LEFS"].split()):
            role = native_path.removeprefix("/work/pdk/")
            path = context["pdk"] / role
            expected = context["prep"]["pdk_identity"]["complete_files_sha256"][role]
            pins[str(verified(path, expected))] = expected
            specs[model]["scripts"][native_path] = expected
        pins[str(verified(itf, ITF_SHA["ITF_" + model]))] = ITF_SHA["ITF_" + model]
        pins[str(tech)] = draft.TECH_SHA
        pins[str(rules)] = draft.RULE_SHA[model]
    legacy = verified(official / "libs.tech/librelane/IHP_rcx_patterns.rules", LEGACY_SHA)
    specs["legacy"] = dict(specs["MAX"], rules=draft.bound(legacy), resistance=None)
    pins[str(legacy)] = LEGACY_SHA
    require(sha(COVERAGE) == COVERAGE_SHA, "Retained timing coverage changed")
    pins[str(COVERAGE)] = COVERAGE_SHA
    return specs, rows, layout, pins


def stage(out, specs, rows, layout):
    out.mkdir()
    (out / "probe.tcl").write_text(TCL)
    cases = {}
    for model, spec in specs.items():
        owner = out / model
        owner.mkdir()
        (owner / "tech.lef").write_text(spec["tech_lef"])
        shutil.copyfile(spec["rules"]["path"], owner / "rules.txt")
        native = OUT / model
        env = dict(spec["env"], RCX_LEF=str(native / "tech.lef"), RCX_RULESET=str(native / "rules.txt"),
                   CURRENT_DEF=DEF, SAVE_SPEF=str(native / "design.spef"))
        rcx_tcl = env["SCRIPTS_DIR"] + "/openroad/rcx.tcl"
        inputs = {**spec["scripts"], DEF: layout["def"]["sha256"],
                  env["RCX_LEF"]: sha(owner / "tech.lef"), env["RCX_RULESET"]: spec["rules"]["sha256"]}
        timing = []
        for row in rows:
            if row["model"] == ("MAX" if model == "legacy" else model) and row["corner"] in PVT:
                old_spef = row["env"]["_CURRENT_SPEF_BY_CORNER"]
                inputs_sta = {k: v for k, v in row["input_sha256"].items() if k != old_spef}
                timing.append(dict(corner=row["corner"], sta_sha256=row["sta_sha256"], input_sha256=inputs_sta,
                                   env=dict(row["env"], _CURRENT_SPEF_BY_CORNER=env["SAVE_SPEF"])))
        require(len(timing) == len(PVT), "STA scenario matrix changed")
        cases[model] = dict(env=env, inputs=inputs, r_meta=spec["resistance"], rules=spec["rules"],
                            argv=["openroad", "-exit", "-threads", "2", "-no_splash", "-metrics",
                                  str(native / "rcx-metrics.json"), rcx_tcl],
                            openroad_sha256=spec["openroad_sha256"], timing=timing)
    info = dict(schema=SCHEMA, cases=cases, layout=layout)
    write(out / "request.json", info)
    return info


def check_files(pins):
    require(all(sha(path) == expected for path, expected in pins.items()), "Timing input changed")


def concurrent_admission(stock_receipt, out, lease, heavy_lock):
    stock = read(stock_receipt)
    require(stock["schema"] == STOCK_SCHEMA and stock["status"] == "running" and stock.get("mode", "stock") == "stock",
            "Concurrent timing requires the live stock hardening run")
    command = stock["command"]
    name = command[command.index("--name") + 1]
    require(name == "pinwheel-tt-clean-" + stock_receipt.parent.name, "Stock hardening name differs")
    with heavy_lock.open("rb") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            pass
        else:
            raise ValueError("Stock hardening must own the external heavy lease")
    def docker(*argv):
        return subprocess.check_output(["docker", *argv], text=True, timeout=10).strip()

    identity = ("{{.Id}} {{.Image}} {{.State.Running}} {{.HostConfig.NanoCpus}} {{.HostConfig.Memory}} "
                "{{.HostConfig.MemorySwap}} {{index .Config.Labels \"org.pinwheel.signoff_owner\"}}")
    ident, image, running, cpus, memory, swap, owner = docker(
        "inspect", "--type", "container", "--format", identity, name).split()
    require(running == "true" and (image, owner) == (stock["image"], stock["owner"])
            and (int(cpus), int(memory), int(swap)) == (4 * 10 ** 9, 6 * GIB, 6 * GIB),
            "Live stock identity, resource caps or status differ")
    total = int(docker("info", "--format", "{{.MemTotal}}"))
    require(docker("ps", "--no-trunc", "--format", "{{.ID}}").splitlines() == [ident] and total >= 7 * GIB,
            "Concurrent timing requires this stock container alone and a 7 GiB aggregate capacity")
    write(out / "admission.json", dict(mode="stock-concurrent", lease=str(lease), heavy_lease=str(heavy_lock),
          stock_execution=draft.bound(stock_receipt), stock=dict(container_id=ident, name=name, image=image,
          owner=owner, nano_cpus=int(cpus), memory_bytes=int(memory), memory_swap_bytes=int(swap)),
          docker_memory_bytes=total, timing=dict(cpus=1, memory_bytes=GIB, memory_swap_bytes=GIB,
          timeout_seconds=NATIVE_SECONDS)))


def native():
    request = read(OUT / "request.json")
    script = OUT / "probe.tcl"
    require(request["schema"] == SCHEMA and set(request["cases"]) == set(MODELS) and script.read_text() == TCL,
            "Native resistance request changed")
    env = {key: os.environ[key] for key in ("PATH", "HOME") if key in os.environ} | BASE_ENV
    rcx_bin = Path(shutil.which("openroad") or "/missing-openroad").resolve(strict=True)
    sta_bin = Path(shutil.which("sta") or "/missing-sta").resolve(strict=True)
    outputs = {}
    for model in MODELS:
        case = request["cases"][model]
        owner = OUT / model
        require(sha(rcx_bin) == case["openroad_sha256"], "Extraction binary changed")
        check_files(case["inputs"])
        with (owner / "rcx.log").open("x") as stream:
            subprocess.run([str(rcx_bin), *case["argv"][1:]], check=True, timeout=65,
                           stdin=subprocess.DEVNULL, stdout=stream, stderr=subprocess.STDOUT,
                           env=env | case["env"])
        spef = owner / "design.spef"
        spef_sha = sha(spef)
        for row in case["timing"]:
            require(sha(sta_bin) == row["sta_sha256"], "Timing binary changed")
            check_files(row["input_sha256"])
            with (owner / f"{row['corner']}.log").open("x") as stream:
                subprocess.run([sta_bin, "-no_splash", "-exit", script], check=True, timeout=20,
                               stdin=subprocess.DEVNULL, stdout=stream, stderr=subprocess.STDOUT,
                               env=env | row["env"])
        require(sha(spef) == spef_sha, "Extracted parasitics changed")
        outputs[model] = spef_sha
    write(OUT / "tool.json", dict(openroad_sha256=sha(rcx_bin), sta_sha256=sha(sta_bin),
                                 completed_models=list(MODELS), extracted_spef_sha256=outputs,
                                 children_peak_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss))


def parse_sta(log, corner, ctx, disconnected):
    require(not re.search(r"^(?:Error[: ]|\[ERROR\]|PINWHEEL_RC_ERROR)", log, re.M)
            and sta.exact_line(log, r"^PINWHEEL_RC_COMPLETE (\S+)$", "completion") == corner,
            "OpenSTA error or wrong corner")
    annotation = preflight.annotation_evidence(log, corner, ctx, disconnected)
    ports = {}
    for mode in ("min", "max"):
        ports[mode] = rows = {}
        for port, endpoint, slack in re.findall(rf"^PINWHEEL_RC_PORT\t{mode}\t([^\t\n]+)\t([^\t\n]+)"
                                                rf"\t({electrical.NUMBER})$", log, re.M):
            require(port not in rows and math.isfinite(float(slack)), "Duplicate or non-finite input path")
            rows[port] = dict(endpoint=endpoint, slack_ns=float(slack))
        require(set(rows) == PORTS, "Incomplete port coverage")
    slacks = {metric: {mode: float(sta.exact_line(log, rf"^PINWHEEL_RC_{metric} {mode} ({electrical.NUMBER})$",
                                                 f"{metric}/{mode}")) for mode in ("min", "max")}
              for metric in ("WORST", "TNS")}
    caps = {label: int(sta.exact_line(log, rf"^PINWHEEL_RC_MAX {label} ([0-9]+)$", label))
            for label in ("slew", "fanout", "capacitance")}
    return dict(ports=ports, global_slack_ns=slacks["WORST"], global_tns_ns=slacks["TNS"],
                electrical_violations=caps, annotation=annotation)


def readback(out, request, pins):
    timing, _ = retained()
    inventory = read(request["layout"]["inventory"]["path"])
    ctx, disconnected = inventory_context(inventory)
    layout = preflight.expected_nets(inventory, ctx)
    retained_coverage = {(r["model"], r["corner"]): r["coverage"]["constrained_path_coverage"]
                         for r in read(COVERAGE)["cases"]}
    results = {}
    for model, case in request["cases"].items():
        owner = out / model
        rcx_log = (owner / "rcx.log").read_text()
        require(not re.search(r"^\[ERROR ", rcx_log, re.M)
                and f"-ext_model_file /work/export/{model}/rules.txt -lef_res" in rcx_log
                and "Created 98904 components" in rcx_log
                and re.search(r"^\[INFO RCX-0443\] \d+ nets finished$", rcx_log, re.M),
                "Native RCX layout readback, invocation or completion differs")
        with (owner / "design.spef").open(encoding="ascii") as stream:
            graph = preflight.spef_evidence(stream, inventory, layout)
        comparisons = {}
        if model in draft.MODELS:
            base = timing["model_matrix"][model]["spef"]
            verified(Path(base["path"]), base["sha256"])
            reference = timing["model_matrix"][model]["spef_validation"]
            require(reference["status"] == "pass", "Retained SPEF validation is incomplete")
            same = graph["graph_sha256"] == reference["graph_sha256"]
            require(same == (model == "MAX"), "The retained control or sourced intervention did not reproduce")
            comparisons.update(same_model_original_spef=base, original_graph=reference)
        corners = {}
        for row in case["timing"]:
            corner = row["corner"]
            log = owner / f"{corner}.log"
            result = parse_sta(log.read_text(), corner, ctx, disconnected)
            if model in draft.MODELS:
                ref = timing["model_matrix"][model]["cases"][corner]
                cov = retained_coverage[model, corner]
                global_delta = {mode: result["global_slack_ns"][mode] - ref[key] for mode, key in
                                (("min", "hold_ws_ns"), ("max", "setup_ws_ns"))}
                port_delta = {mode: {port: entry["slack_ns"] - cov[mode]["input_paths"][port]["slack_ns"]
                                     for port, entry in result["ports"][mode].items()} for mode in ("min", "max")}
                if model == "MAX":
                    require(all(abs(delta) <= 3e-6 for delta in [*global_delta.values(),
                                                               *port_delta["min"].values(), *port_delta["max"].values()]),
                            "Identity control did not reproduce retained STA")
                result.update(original_global_delta_ns=global_delta, original_ports_delta_ns=port_delta)
            corners[corner] = dict(log=draft.bound(log), **result)
        results[model] = dict(graph=graph, spef=draft.bound(owner / "design.spef"),
                              extraction_log=draft.bound(owner / "rcx.log"),
                              extraction_warnings=re.findall(r"^\[WARN(?:ING)? [^\n]+", rcx_log, re.M),
                              corners=corners, **comparisons)
    check_files(pins)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--deadline", type=int, required=True)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--concurrent-stock-receipt", type=Path)
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.parent == TRIAL and not out.exists(), "Use a fresh directory beside retained timing evidence")
    context = setup(args.history.resolve(strict=True))
    specs, rows, layout, pins = prepare(context)
    request = stage(out, specs, rows, layout)
    check_files(pins)
    if args.prepare_only:
        print(out / "request.json")
        return
    for path in (out / "request.json", out / "probe.tcl", Path(__file__).resolve()):
        pins[str(path)] = sha(path)
    for model in MODELS:
        for name in ("tech.lef", "rules.txt"):
            path = out / model / name
            pins[str(path)] = sha(path)
    options = {}
    mode = "exclusive"
    if args.concurrent_stock_receipt:
        stock_receipt = args.concurrent_stock_receipt.resolve(strict=True)
        lease = TRIAL / ".timing-with-stock.lock"
        lease.touch(exist_ok=True)
        mode = "stock-concurrent"
        options = dict(memory="1g", resource_lease=lease,
                       admission=lambda heavy_lock: concurrent_admission(stock_receipt, out, lease, heavy_lock))
    execution = run_native(context, out, "python3", ["-B", f"/work/scripts/{Path(__file__).name}", "native"],
               [(Path(__file__).parent, "/work/scripts", False), (Path(layout["def"]["path"]), DEF, False),
                (Path(layout["netlist"]["path"]), coverage.NL, False),
                (Path(layout["sdc"]["path"]), coverage.SDC, False)],
               NATIVE_SECONDS, args.deadline, **options)
    admission = None
    if options:
        command = execution["argv"]
        require(execution["timeout_seconds"] <= NATIVE_SECONDS and all(command[command.index(flag) + 1] == val
                for flag, val in (("--cpus", "1"), ("--memory", "1g"), ("--memory-swap", "1g"))),
                "Concurrent timing execution did not retain admitted caps")
        admission = draft.bound(out / "admission.json")
    tools = read(out / "tool.json")
    require(tools["completed_models"] == list(MODELS)
            and all(sha(out / model / "design.spef") == tools["extracted_spef_sha256"][model] for model in MODELS),
            "Incomplete native results or changed SPEF output")
    results = readback(out, request, pins)
    write(out / "readback.json", dict(schema=SCHEMA, target=layout, results=results, status="diagnostic",
          execution_mode=mode, admission=admission,
          request=draft.bound(out / "request.json"), execution=draft.bound(out / "execution.json"),
          native_tools=draft.bound(out / "tool.json"), input_sha256=pins,
          itf_source_revision=PDK_REV, image=IMAGE, frozen_inputs_unchanged=True, qualified_timing=False,
          model_qualified=False, tapeout_ready=False))
    print(out / "readback.json")


if __name__ == "__main__":
    if sys.argv[1:] == ["native"]:
        native()
    else:
        main()
