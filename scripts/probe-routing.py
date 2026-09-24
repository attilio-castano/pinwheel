#!/usr/bin/env python3
"""Bounded static DRC or pin-access check of a frozen OpenDB, without routing."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess
import time

from physical_checkpoint import sha
from routing_evidence import parse_report, pin_access_summary

ROOT = Path(__file__).resolve().parents[1]

TCL = """read_db $::env(PINWHEEL_PROBE_DB)
set_routing_layers -signal $::env(PINWHEEL_SIGNAL_LAYERS) -clock $::env(PINWHEEL_CLOCK_LAYERS)
if {$::env(PINWHEEL_PROBE_KIND) eq "drc"} {
    drt::check_drc -output_file /work/probe/drc.rpt -marker_name PinwheelFreshDiagnostic
} else {
    pin_access -min_access_points 1 -verbose 1
}
"""


def routing_layers(config):
    """Use resolved PDK limits; core.json does not contain all defaults."""
    low, high = config.get("RT_MIN_LAYER"), config.get("RT_MAX_LAYER")
    if not low or not high:
        raise ValueError("Resolved configuration must specify both routing layer limits")
    signal = f"{low}-{high}"
    clock = f'{config.get("RT_CLOCK_MIN_LAYER") or low}-{config.get("RT_CLOCK_MAX_LAYER") or high}'
    if not all(re.fullmatch(r"[A-Za-z0-9]+-[A-Za-z0-9]+", s) for s in [signal, clock]):
        raise ValueError("Unsupported routing layer names")
    return signal, clock


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--design", type=Path, required=True)
    p.add_argument("--database", type=Path, required=True)
    p.add_argument("--config", type=Path, required=True,
                   help="Resolved config.json from the corresponding physical step, including PDK defaults")
    p.add_argument("--kind", choices=["drc", "pin-access"], required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--timeout-seconds", type=int, default=180)
    args = p.parse_args()
    if not 1 <= args.timeout_seconds <= 300:
        p.error("Static probes must have a limit of 1 to 300 seconds")
    design, database, output = args.design.resolve(), args.database.resolve(), args.output.resolve()
    relative = database.relative_to(design)
    if not design.is_relative_to(ROOT / "build/physical") or not output.is_relative_to(ROOT / "build"):
        raise ValueError("Use a prepared design and a fresh output under build/")
    if not database.is_file() or output.exists():
        raise ValueError("Database must exist and output must be fresh")
    lock_path, config_path = ROOT / "tools/physical-toolchain.json", args.config.resolve()
    lock, config = json.loads(lock_path.read_text()), json.loads(config_path.read_text())
    if not config_path.is_relative_to(design) or not config.get("meta", {}).get("librelane_version"):
        raise ValueError("Use a resolved flow configuration from this prepared design")
    signal, clock = routing_layers(config)
    info = json.loads(subprocess.check_output(["docker", "image", "inspect", lock["container_tag"]], text=True))[0]
    runtime = {k: v for k, v in info["Config"].items() if v is not None}
    if (info["Architecture"] != "arm64" or info["Os"] != "linux" or
            info["RootFS"]["Layers"] != lock["container_rootfs_diff_ids"] or
            hashlib.sha256(json.dumps(runtime, sort_keys=True).encode()).hexdigest() != lock["container_runtime_config_sha256"]):
        raise ValueError("Local image differs from the pinned physical toolchain")
    source_digest = sha(database)
    output.mkdir(parents=True)
    script = output / "probe.tcl"
    script.write_text(TCL)
    name = "pinwheel-probe-" + hashlib.sha256(str(output).encode()).hexdigest()[:12]
    command = ["docker", "run", "--rm", "--pull", "never", "--network", "none", "--cpus", "4", "--memory", "6g", "--name", name,
        "--mount", f"type=bind,source={design},target=/work/core,readonly",
        "--mount", f"type=bind,source={output},target=/work/probe",
        "--env", f"PINWHEEL_PROBE_DB=/work/core/{relative.as_posix()}",
        "--env", f"PINWHEEL_SIGNAL_LAYERS={signal}", "--env", f"PINWHEEL_CLOCK_LAYERS={clock}",
        "--env", f"PINWHEEL_PROBE_KIND={args.kind}", info["Id"],
        "openroad", "-exit", "-threads", "4", "-no_splash", "/work/probe/probe.tcl"]
    runner = runpy.run_path(str(ROOT / "scripts/run-physical.py"))
    record = dict(schema=1, kind=args.kind, command=command, source_database=str(database),
                  source_database_sha256=source_digest, script_sha256=sha(script), image_id=info["Id"],
                  timeout_seconds=args.timeout_seconds, config_sha256=sha(config_path), toolchain_sha256=sha(lock_path),
                  config_path=str(config_path), signal_layers=signal, clock_layers=clock,
                  probe_sha256=sha(Path(__file__)), cleanup_helper_sha256=sha(ROOT / "scripts/run-physical.py"),
                  boundary="Static router DRC or minimum-one-access-point screen. No routing, repair, database write, foundry signoff, or extracted timing.")
    receipt = output / "report.json"
    runner["write_receipt"](receipt, record)
    start = time.monotonic()
    with (output / "probe.log").open("x") as log:
        try:
            record["exit_code"] = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT,
                                                 timeout=args.timeout_seconds).returncode
        except BaseException as error:
            record.update(exit_code=124 if isinstance(error, subprocess.TimeoutExpired) else 130,
                          stop_reason=type(error).__name__, container_termination={"status": "unconfirmed"})
            runner["write_receipt"](receipt, record)
            record["container_termination"] = runner["stop_container"](name, log)
    record["seconds"] = round(time.monotonic()-start, 3)
    try:
        query = subprocess.run(["docker", "container", "ls", "--all", "--filter", f"name=^/{name}$", "--format", "{{json .}}"],
                               capture_output=True, text=True, timeout=15)
        record["termination_query"] = dict(exit_code=query.returncode, stdout=query.stdout, stderr=query.stderr)
        record["settled"] = query.returncode == 0 and not query.stdout.strip()
    except (subprocess.TimeoutExpired, OSError) as error:
        record.update(termination_query=dict(error=str(error)), settled=False)
    record["source_unchanged"] = sha(database) == source_digest
    if record["exit_code"] == 0 and record["settled"] and record["source_unchanged"]:
        if args.kind == "drc":
            report = output / "drc.rpt"
            record.update(report_sha256=sha(report), marker_count=len(parse_report(report.read_text())))
        else:
            record["log_sha256"] = sha(output / "probe.log")
            record["pin_access"] = pin_access_summary((output / "probe.log").read_text())
    runner["write_receipt"](receipt, record)
    print(json.dumps({k: record.get(k) for k in ["kind", "exit_code", "seconds", "settled", "source_unchanged", "marker_count"]}))
    if record["exit_code"] or not record["settled"] or not record["source_unchanged"]:
        raise SystemExit(record["exit_code"] or 1)


if __name__ == "__main__":
    main()
