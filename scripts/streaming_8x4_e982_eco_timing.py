"""Extract and time the exact fanout ECO with the retained five-layer draft models."""

import argparse
from pathlib import Path
import re
import shutil

import streaming_8x4_draft_rc_timing as draft
from streaming_8x4_draft_rc_timing_observe import observer
from streaming_8x4_e982_eco_signoff import ECO_ROOT, setup
from streaming_8x4_e982_native import (
    IMAGE, ROOT, TOP, active_layout, checked_views, local_inputs, read, require, run_native, sha, write,
)


HOLD_PROBE = """
# Record both delay checks on the same falling input and capture data pin.
set sources {}
foreach port [all_inputs] {
  if {[get_full_name $port] eq {ui_in[5]}} { lappend sources $port }
}
set sinks {}
foreach pin [get_pins -of_objects [dict get $observed {engine.frontend._0230_}]] {
  if {[get_full_name $pin] eq {engine.frontend._0230_/D}} { lappend sinks $pin }
}
if {[llength $sources] != 1 || [llength $sinks] != 1} { error "Exact hold probe pins missing" }
foreach delay {min max} {
  puts "PINWHEEL_ECO_TIMING_PATH_BEGIN $delay"
  report_checks -fall_from $sources -to $sinks -path_delay $delay -format full_clock_expanded -digits 6
  puts "PINWHEEL_ECO_TIMING_PATH_END $delay"
}
"""


def verified_layout(context):
    views, view = checked_views(context)
    target = active_layout(context)
    inventory = views / "actual-signal/inventory.json"
    receipt = inventory.with_name("receipt.json")
    export = read(receipt)
    require(export["database_sha256"] == target["odb_sha256"] and export["top"] == TOP
            and export["read_only_database"] is True
            and export["artifacts_sha256"]["inventory.json"] == sha(inventory),
            "Actual inventory differs from the selected ODB")
    source = views / "final-views-native.json"
    native = read(source)
    require(native["completed"] is True and native["source_odb_unchanged"] is True
            and native["source_odb_sha256"] == target["odb_sha256"]
            and native["canonical_boolean_report_sha256"] == sha(receipt),
            "Same-ODB view export did not close")
    paths = dict(odb=target["odb"], gds=target["gds"], inventory=inventory, inventory_receipt=receipt,
                 views_receipt=views / "rehearsal-view-readback.json",
                 sdc=context["prepared"] / "inputs/core.sdc", **{
                     "def": views / "design.def",
                     "netlist": views / "signoff-views/implemented.v",
                     "powered_netlist": views / "signoff-views/implemented.power.v",
                 })
    result = {role: draft.bound(path) for role, path in paths.items()}
    require(result["def"]["sha256"] == view["view_sha256"]["def"]
            and result["netlist"]["sha256"] == view["view_sha256"]["verilog"]
            and result["powered_netlist"]["sha256"] == view["view_sha256"]["powered_verilog"]
            and result["sdc"]["sha256"] == draft.SDC_SHA
            and result["odb"]["sha256"] == target["odb_sha256"]
            and result["gds"]["sha256"] == target["gds_sha256"], "Exact timing views differ")
    return views, result


def prepare(context, out, target_name):
    views, layout = verified_layout(context)
    campaign = context["prepared"].parent
    rules = campaign / "rc-consumer-preparation-02"
    plan = draft.bound(rules / "plan.json")
    require(plan["sha256"] == draft.PLAN_SHA, "Owned draft RC plan changed")
    source_manifest = campaign / "intake/librelane-native-source/manifest.json"
    native, package = draft.native_package(source_manifest)
    require(native["image_id"] == IMAGE, "Draft consumer source binds a different image")
    original_resolved = context["source"] / "flow/resolved.json"
    original = read(original_resolved)
    inputs = out / "inputs"
    inputs.mkdir(parents=True, exist_ok=False)
    head, sources, _ = draft.snapshot(inputs)
    (inputs / "rules").mkdir()
    for model, expected in draft.RULE_SHA.items():
        rule = rules / f"{model}-owned_explicit_via_rules.txt"
        dest = inputs / "rules" / f"{model}.rules"
        shutil.copyfile(rule, dest)
        require(sha(dest) == expected and re.findall(r"(?m)^LayerCount\s+(\d+)$", dest.read_text()) == ["5"],
                f"Draft {model} rules changed")
        write(inputs / f"{model}-config.json", draft.diagnostic_config(original, model))
    database = Path(layout["odb"]["path"])
    script, expected = observer(read(layout["inventory"]["path"]), layout["odb"]["sha256"],
                                layout["inventory"]["sha256"])
    script_path = inputs / "observe.tcl"
    script_path.write_text(script + HOLD_PROBE)
    request = draft.request_for({"actual_odb": layout["odb"]}, database.parent, views, package,
                                sha(script_path), expected)
    request["input_sha256"].update(draft.pdk_bindings(original, context["pdk"]))
    request.update(target_name=target_name, layout=layout, original_resolved=draft.bound(original_resolved),
                   rules_plan=plan, native_source_manifest=draft.bound(source_manifest),
                   producer_commit=head, producer_sha256=sources, adapter=draft.bound(__file__),
                   pdk_root=str(context["pdk"]), pdk_revision=context["prep"]["pdk_identity"]["base"]["revision"])
    write(inputs / "request.json", request)
    write(inputs / "seed.json", draft.seed_for({"actual_odb": layout["odb"]}, database.parent))
    return request


def execute(context, out, target_name, deadline):
    request = prepare(context, out, target_name)
    views = Path(request["layout"]["views_receipt"]["path"]).parent
    database = Path(request["layout"]["odb"]["path"])
    inputs = out / "inputs"
    staged = {path: sha(path) for path in inputs.rglob("*") if path.is_file()}
    run = out / "run"
    run.mkdir()
    run_native(context, run, "python3", [
        "-B", "/work/diagnostic/producer/" + draft.OWN, "native",
        "--inputs", "/work/diagnostic", "--output", "/work/result",
    ], [(inputs, "/work/diagnostic", False), (context["prepared"] / "inputs", "/work/inputs", False),
        (database.parent, "/work/source", False), (views, "/work/views", False), (run, "/work/result", True)],
        1080, deadline, environment=("_OPENLANE_MAX_CORES=1",
            "PYTHONPATH=/work/diagnostic:/work/diagnostic/producer/scripts:/work/inputs"))
    require(all(sha(path) == digest for path, digest in staged.items()), "Staged timing inputs changed")
    for item in (*request["layout"].values(), request["original_resolved"], request["rules_plan"],
                 request["native_source_manifest"], request["adapter"]):
        require(draft.bound(item["path"]) == item, "Timing input changed: " + item["path"])
    draft.checked_passes(run, {"request": request})
    write(out / "native-readback.json", dict(schema="pinwheel.e982-five-layer-timing-native.v1",
          status="completed", target_name=target_name, target_odb_sha256=request["layout"]["odb"]["sha256"],
          gds_sha256=request["layout"]["gds"]["sha256"], request=draft.bound(inputs / "request.json"),
          execution=draft.bound(run / "execution.json"), passes=draft.bound(run / "native-passes.json"),
          model_qualified=False, qualified_timing=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=("eco", "baseline"))
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--deadline", type=int, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.is_relative_to(ECO_ROOT) and out != ECO_ROOT and not out.exists(),
            "Use a fresh ignored ECO timing output path")
    history = args.history.resolve()
    if args.target == "eco":
        context = setup(history, ECO_ROOT / "signoff-01")
    else:
        context = local_inputs(history, ROOT / "build/tt-rehearsal-20261104")
    execute(context, out, args.target, args.deadline)


if __name__ == "__main__":
    main()
