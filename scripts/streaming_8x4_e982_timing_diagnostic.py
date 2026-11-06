"""Local nominal RCX/STA diagnostic on the frozen rehearsal target."""
import argparse
from pathlib import Path
import re

from streaming_8x4_e982_native import (
    GDS, ODB, ROOT, TOP, bind, checked_views, local_inputs, read, require, run_native, sha, write,
)


def run(context, deadline):
    views, view_receipt = checked_views(context)
    out = context["work"] / "timing-diagnostic"
    out.mkdir(exist_ok=False)
    source = context["odb"].parent
    inputs = context["prepared"] / "inputs"
    input_sdc = inputs / "core.sdc"
    input_config = inputs / "core.json"
    for item in (input_sdc, input_config):
        require(sha(item) == context["prep"]["input_sha256"][item.name], f"Prepared {item.name} changed")
    config_path = context["source"] / "flow/resolved.json"
    config = read(config_path)
    require(config["CLOCK_PERIOD"] == 20 and config["CLOCK_PORT"] == "clk",
            "Diagnostic clock contract changed")
    rules = config["RCX_RULESETS"]
    require(set(rules) == {"nom_*"}, "Unexpected RC corner setup")
    path = context["pdk"] / rules["nom_*"].removeprefix("/work/pdk/")
    text = path.read_text()
    layers = re.findall(r"(?m)^LayerCount\s+(\d+)\b", text)
    require(layers == ["7"], "Legacy nominal deck identity changed")
    ports = input_sdc.read_text()
    require("set_propagated_clock" in ports and "set_input_delay" in ports and
            "set_output_delay" in ports, "Missing integration clock/I/O constraints")
    source_inputs = {"odb": context["odb"], "def": source / f"{TOP}.def", "sdc": source / f"{TOP}.sdc",
                     "nl": source / f"{TOP}.nl.v", "pnl": source / f"{TOP}.pnl.v"}
    frozen = {str(file): sha(file) for file in (*source_inputs.values(), path, input_sdc, input_config, config_path)}
    require(frozen[str(source_inputs["odb"])] == ODB and
            frozen[str(source_inputs["def"])] == view_receipt["view_sha256"]["def"] and
            frozen[str(source_inputs["nl"])] == view_receipt["view_sha256"]["verilog"] and
            frozen[str(source_inputs["pnl"])] == view_receipt["view_sha256"]["powered_verilog"],
            "Initial timing view differs from canonical exports")
    seed = {role: "/work/seed/" + file.name for role, file in source_inputs.items()}
    write(out / "seed.json", {**seed, "metrics": {}})
    flow = out / "flow"
    flow.mkdir()
    run_native(context, out, "python3", [
        "-B", "-m", "librelane", "--manual-pdk", "--pdk-root", "/work/pdk",
        "--pdk", "ihp-sg13cmos5l", "--jobs", "1", "--flow", "Streaming8x4Certified",
        "--override-config", "OPENROAD_THREADS=1", "--run-tag", "e982-nominal-diagnostic",
        "--force-run-dir", "/work/export/flow", "--with-initial-state", "/work/export/seed.json",
        "--from", "OpenROAD.RCX", "--to", "OpenROAD.STAPostPNR", "/work/inputs/core.json",
    ], [(source, "/work/seed", False), (inputs, "/work/inputs", False)], 900, deadline,
       environment=("PYTHONPATH=/work/inputs",))
    actual_config = read(flow / "resolved.json")
    for field in ("CLOCK_PORT", "CLOCK_PERIOD", "RCX_RULESETS", "STA_CORNERS"):
        require(actual_config[field] == config[field], f"Timing flow changed {field}")
    rcx, = flow.glob("*-openroad-rcx")
    sta, = flow.glob("*-openroad-stapostpnr")
    spef, = rcx.rglob("*.spef")
    expected_spef = {"nom_*": "/work/export/flow/" + spef.relative_to(flow).as_posix()}
    rcx_state, sta_state = rcx / "state_out.json", sta / "state_out.json"
    extracted, observed = read(rcx_state), read(sta_state)
    for state in (extracted, observed):
        require(all(state[role] == value for role, value in seed.items()) and state["spef"] == expected_spef,
                "Diagnostic did not use the exact seed views and extracted nominal SPEF")
    metrics = observed["metrics"]
    corners = {}
    for corner in sorted(config["STA_CORNERS"]):
        root = sta / corner
        checks = (root / "checks.rpt").read_text()
        minimum = (root / "min.rpt").read_text()
        annotation = read(root / "filter_unannotated_metrics.json")
        raw = re.findall(r"Found (\d+) unannotated drivers", checks)
        require(len(raw) == 1, "Missing raw annotation count")
        keys = ("timing__hold__ws", "timing__setup__ws", "timing__hold_vio__count",
                "timing__setup_vio__count", "design__max_slew_violation__count",
                "design__max_cap_violation__count", "design__max_fanout_violation__count")
        corners[corner] = {
            "metrics": {key: metrics[key + "__corner:" + corner] for key in keys},
            "worst_hold_start": re.search(r"(?m)^Startpoint: (.*)$", minimum).group(1),
            "worst_hold_end": re.search(r"(?m)^Endpoint: (.*)$", minimum).group(1),
            "unannotated_raw": int(raw[0]), "filtered_annotation_metrics": annotation,
            "artifacts": [bind(root / name) for name in ("min.rpt", "max.rpt", "checks.rpt", "clock.rpt",
                                                           "filter_unannotated_metrics.json")],
        }
    require(all(sha(path) == digest for path, digest in frozen.items()), "Diagnostic input bytes changed")
    write(out / "diagnostic-readback.json", dict(schema="pinwheel.e982-nominal-timing-diagnostic.v1",
          status="diagnostic", target_odb_sha256=ODB, gds_sha256=GDS, qualified_timing=False,
          extraction_model_qualified=False, extracted_rule_layers=7, cmos5l_routing_layers=5,
          clock_period_ns=20, input_sdc_sha256=sha(input_sdc), rules_sha256=sha(path),
          corners=corners, artifacts=[bind(item) for item in (out / "execution.json", out / "seed.json",
              flow / "resolved.json", rcx_state, sta_state, spef)],
          scope="Unqualified legacy nominal SPEF reused across Liberty corners. Slack is diagnostic only."))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--deadline", type=int, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    require(work.is_relative_to(ROOT / "build"), "Use a fresh local ignored build path")
    run(local_inputs(args.history.resolve(), work), args.deadline)


if __name__ == "__main__":
    main()
