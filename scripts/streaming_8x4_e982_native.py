"""Run the local native checks for the frozen e982 Tiny Tapeout rehearsal."""
import argparse
import fcntl
import hashlib
import json
from pathlib import Path
import shutil
import struct
import subprocess
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
ODB = "b7e60eded5198fc53df7e5dd1e3ab0f5162720516ab0c1692a1cf7c7bb62602b"
GDS = "041ff30708e46be33db330e2f1dcafab889824b689499e931ec9d180a11c1689"
REF = "da19eccfaa31dca8836f40bd693b4f125759470959cb06a0ed9ee3df34a2d1a4"
IMAGE = "sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92"
TOP = "tt_um_pinwheel_streaming_ready_d2"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n")
    temporary.replace(path)


def normalized_gds(path):
    """Normalize the 24-byte GDSII library and structure timestamp payloads."""
    digest = hashlib.sha256()
    count = 0
    with Path(path).open("rb") as stream:
        while header := stream.read(4):
            require(len(header) == 4, "Truncated GDS header")
            size, kind, datatype = struct.unpack(">HBB", header)
            require(size >= 4 and size % 2 == 0, "Invalid GDS record size")
            data = stream.read(size - 4)
            require(len(data) == size - 4, "Truncated GDS record")
            if kind in (1, 5):
                require(datatype == 2 and len(data) == 24, "Invalid GDS timestamps")
                data = bytes(24)
                count += 1
            digest.update(header + data)
    require(count > 0, "No GDS library/structure timestamps")
    return digest.hexdigest()


def pdk_snapshot(pdk, prep):
    from streaming_tt_pdk import verify_complete_pdk

    lock = read(ROOT / "tools/streaming-tt-signoff.json")
    return verify_complete_pdk(pdk, read(ROOT / lock["physical_toolchain"]), lock,
                               tree_path=Path(prep["pdk_tree"]["path"]))


def local_inputs(history, work):
    base = history / "build/campaigns"
    source = ROOT / "build/e982-whole-route-20261104/native"
    prior = read(source / "execution.json")
    odb = Path(prior["postfill_odb"]["path"])
    gds = source / "design.gds"
    route = source.parent / "independent-readback.json"
    route_proof = read(route)
    require(prior["frozen_inputs_unchanged"] is True and
            all(item["container_absent"] and item["exit_code"] == 0 for item in prior["phases"]),
            "Frozen route custody did not close")
    require(sha(odb) == prior["postfill_odb"]["sha256"] == route_proof["postfill_odb_sha256"] == ODB and
            sha(gds) == prior["gds_sha256"] == route_proof["postfill_gds_sha256"] == GDS and
            route_proof["physical_checks_pass"] is True, "Exact routed candidate or readback changed")
    prepared = base / "8x4-20261022-01/prepared-8x4-02"
    prep = read(prepared / "preparation.json")
    reference = base / "8x4-20261024-01/final24-views-01/inputs/reference.json"
    require(sha(reference) == REF, "Flat source reference changed")
    pdk = Path(prep["pdk_root"])
    require(pdk_snapshot(pdk, prep) == prep["pdk_identity"], "Prepared PDK changed")
    require(prior["image"] == IMAGE, "Routed candidate image changed")
    return dict(work=work, source=source, odb=odb, gds=gds, route=route, prepared=prepared, prep=prep,
                reference=reference, pdk=pdk, history=history, base=base)


def bind(path):
    path = Path(path)
    return {"path": str(path.relative_to(ROOT)), "sha256": sha(path)}


def run_native(context, out, entrypoint, argv, mounts, timeout, deadline, *, memory="6g", environment=()):
    from streaming_8x4_signoff_execute import owned_native

    remaining = int(deadline - time.time()) - 90
    require(remaining >= 30, "Too close to campaign deadline for another native job")
    owner = str(uuid.uuid4())
    name = f"pinwheel-tt-rehearsal-{out.name}-{owner[:8]}"
    command = ["docker", "run", "--rm", "--pull", "never", "--name", name,
               "--label", f"org.pinwheel.streaming8_owner={owner}",
               "--network", "none", "--cpus", "1", "--memory", memory, "--memory-swap", memory,
               "--pids-limit", "256", "--read-only", "--tmpfs", "/tmp:rw,size=512m",
               "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
               "--env", "PYTHONDONTWRITEBYTECODE=1"]
    for item in environment:
        command.extend(["--env", item])
    for host, destination, writable in [(out, "/work/export", True),
                                        (context["pdk"], "/work/pdk", False), *mounts]:
        command.extend(["--mount", f"type=bind,source={host},target={destination}" +
                        ("" if writable else ",readonly")])
    command.extend(["--workdir", "/work/export", "--entrypoint", entrypoint, IMAGE, *argv])
    lock_dir = context["history"] / "build/streaming-tt-resources"
    with (lock_dir / "heavy.lock").open("rb") as lease:
        fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        require(not (lock_dir / "cleanup-unconfirmed.json").exists(), "Prior native cleanup is unconfirmed")
        receipt = owned_native(command, out, owner, min(timeout, remaining))
    require(receipt.get("status") == "completed" and receipt.get("exit_code") == 0 and
            receipt.get("container_termination", {}).get("status") == "absent",
            f"{out.name} native execution failed: {receipt.get('status')}/{receipt.get('exit_code')}")
    require(sha(context["odb"]) == ODB and sha(context["gds"]) == GDS,
            "Frozen ODB or GDS changed during native work")
    require(pdk_snapshot(context["pdk"], context["prep"]) == context["prep"]["pdk_identity"],
            "Prepared PDK changed during native work")
    return receipt


def views(context, deadline, output=None):
    from streaming_tt_lef_format import canonicalize, validate_equivalence

    work = context["work"]
    out = output or work / "views"
    inputs = out / "inputs"
    inputs.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(context["reference"], inputs / "reference.json")
    source = context["source"] / "flow"
    request = dict(schema="pinwheel.streaming-8x4-final-views-native-request.v1",
                   source_odb="/work/source/" + str(context["odb"].relative_to(source)), source_odb_sha256=ODB,
                   resolved_config="/work/source/resolved.json", resolved_config_sha256=sha(source / "resolved.json"),
                   input_sha256=context["prep"]["input_sha256"], reference_sha256=REF, top=TOP,
                   qualified=False, physical_acceptance=False)
    write(inputs / "request.json", request)
    shutil.copyfile(ROOT / "scripts/streaming_8x4_signoff_execute.py", inputs / "native-signoff.py")
    report = run_native(context, out, "python3",
                        ["-B", "/work/export/inputs/native-signoff.py", "native-views",
                         "--request", "/work/export/inputs/request.json"],
                        [(inputs, "/work/export/inputs", False),
                         (ROOT / "scripts", "/work/scripts", False),
                         (ROOT / "physical", "/work/physical", False),
                         (context["prepared"] / "inputs", "/work/inputs", False),
                         (source, "/work/source", False)],
                        900, deadline, memory="3g",
                        environment=("PYTHONPATH=/work/scripts:/work/inputs",))
    result = read(out / "final-views-native.json")
    require(result["completed"] is True and result["source_odb_sha256"] == ODB and
            result["source_odb_unchanged"] is True and
            result["resolved_config_sha256"] == request["resolved_config_sha256"], "Wrong native views identity")
    links = {"canonical_signoff_report_sha256": "signoff-views/report.json",
             "canonical_boolean_report_sha256": "actual-signal/receipt.json",
             "canonical_streamout_report_sha256": "native-report.json",
             "complete_cdl_sha256": "complete-reference.cdl", "cdl_context_sha256": "cdl-context.json"}
    for key, relative in links.items():
        require(sha(out / relative) == result[key], f"Changed view artifact {relative}")
    signoff = read(out / "signoff-views/report.json")
    connectivity = read(out / "actual-signal/receipt.json")
    stream = read(out / "native-report.json")
    require(signoff["completed"] is True and signoff["exit_code"] == 0 and
            signoff["actual_database_sha256"] == ODB and signoff["inputs_unchanged"] is True,
            "Canonical signoff views failed")
    require(connectivity["database_sha256"] == ODB and connectivity["reference_sha256"] == REF and
            connectivity["read_only_database"] is True and connectivity["top"] == TOP,
            "Canonical connectivity did not bind this ODB")
    require(stream["source_odb_sha256"] == ODB and stream["source_odb_unchanged"] is True,
            "Canonical streamout did not bind this ODB")
    for record, key, folder in ((signoff, "artifacts_sha256", "signoff-views"),
                                (connectivity, "artifacts_sha256", "actual-signal"),
                                (stream, "generated_files_sha256", ".")):
        for name, pin in record[key].items():
            require(sha(out / folder / name) == pin, f"Changed native view {folder}/{name}")
    require(normalized_gds(out / "design.gds") == normalized_gds(context["gds"]),
            "Independent streamout differs from frozen GDS beyond timestamps")
    original = (out / "signoff-views/implemented.lef").read_text()
    derived, _ = canonicalize(original)
    require(validate_equivalence(original, derived), "Official LEF canonicalization differs")
    (out / "official-format.lef").write_text(derived)
    write(out / "rehearsal-view-readback.json", dict(status="pass", target_odb_sha256=ODB,
          gds_sha256=GDS, normalized_gds_sha256=normalized_gds(context["gds"]),
          view_sha256={name: sha(out / path) for name, path in {
              "lef": "official-format.lef", "verilog": "signoff-views/implemented.v",
              "powered_verilog": "signoff-views/implemented.power.v", "cdl": "complete-reference.cdl",
              "def": "design.def"}.items()},
          artifacts=[bind(out / name) for name in (
              "execution.json", "final-views-native.json", "signoff-views/report.json",
              "actual-signal/receipt.json", "native-report.json", "cdl-context.json",
              "native-geometry.json", "official-format.lef", "signoff-views/implemented.v",
              "signoff-views/implemented.power.v", "complete-reference.cdl")],
          elapsed_seconds=report["elapsed_seconds"]))


def checked_views(context):
    root = context["work"] / "views"
    result = read(root / "rehearsal-view-readback.json")
    require(result["status"] == "pass" and result["target_odb_sha256"] == ODB and
            result["gds_sha256"] == GDS, "Views receipt refers to another target")
    for row in result["artifacts"]:
        require(sha(ROOT / row["path"]) == row["sha256"], f"Changed views input {row['path']}")
    return root, result


def pg(context, deadline):
    from streaming_8x4_closure24_pg_lifetime_context import native_module

    native = native_module()
    views_root, _ = checked_views(context)
    out = context["work"] / "pg"
    inputs = out / "inputs"
    inputs.mkdir(parents=True, exist_ok=False)
    inventory = views_root / "actual-signal/inventory.json"
    exporter = read(views_root / "actual-signal/receipt.json")
    require(sha(inventory) == exporter["artifacts_sha256"]["inventory.json"], "Inventory changed after export")
    rails = native.expected_rails(read(inventory))
    require(set(rails) == {"VGND", "VPWR"}, "Unexpected rails")
    request = dict(schema="pinwheel.streaming-8x4-power-grid-request.v1", source_odb="/work/target.odb",
                   source_odb_sha256=ODB, inventory_sha256=sha(inventory), reference_sha256=REF, top=TOP,
                   rails=rails, openroad_source_commit=native.COMMIT,
                   leaf_timeout_seconds=native.LEAF_SECONDS, outer_timeout_seconds=native.OUTER_SECONDS,
                   floorplanning=False, dont_require_terminals=False, qualified=False, physical_acceptance=False)
    write(inputs / "request.json", request)
    shutil.copyfile(inventory, inputs / "inventory.json")
    shutil.copyfile(context["reference"], inputs / "reference.json")
    (out / "launch.py").write_text(native.LAUNCHER)
    run_native(context, out, "python3",
               ["-B", "/work/scripts/streaming_8x4_closure24_pg_lifetime.py", "native-supervise"],
               [(out, "/work/pg", True), (inputs, "/work/pg/inputs", False),
                (context["odb"], "/work/target.odb", False),
                (ROOT / "scripts", "/work/scripts", False)],
               240, deadline, memory="3g", environment=("PYTHONPATH=/work/scripts",))
    native_result, stats = native.native_result(out, {"source_odb": {"sha256": ODB}})
    write(out / "rehearsal-pg-readback.json", dict(status="pass", target_odb_sha256=ODB, gds_sha256=GDS,
          rails={name: {"iterms": len(row["iterms"]), "bterms": len(row["bterms"]), "psm": stats[name]}
                 for name, row in rails.items()}, census_totals=native_result["inventory_totals"],
          shorts_checked=False, ir_drop_qualified=False,
          artifacts=[bind(out / name) for name in ("execution.json", "native.json", "openroad.log", "leaf.json",
                                                      "rail-0-errors.rpt", "rail-1-errors.rpt")]))


def layout(context, deadline):
    views_root, expected = checked_views(context)
    out = context["work"] / "layout"
    inputs = out / "inputs"
    inputs.mkdir(parents=True, exist_ok=False)
    cdl = views_root / "complete-reference.cdl"
    require(sha(cdl) == expected["view_sha256"]["cdl"], "Canonical CDL changed")
    decks = {kind: context["pdk"] / relative for kind, relative in {
        "antenna": "ihp-sg13cmos5l/libs.tech/klayout/tech/drc/rule_decks/antenna.drc",
        "lvs": "ihp-sg13cmos5l/libs.tech/klayout/tech/lvs/sg13cmos5l.lvs"}.items()}
    deck_sha256 = {kind: sha(path) for kind, path in decks.items()}
    require(deck_sha256 == {
        "antenna": "85f6d5a6ec9224cd78d3705835006e5741ea5a5d431cda692a96c0ac62437f38",
        "lvs": "6cf97a068d69abd590cc441f64ef69d34ef50aef113c00023f2a1a94ccbe6e18",
    }, "Frozen antenna/LVS deck changed")
    # KLayout uses NET_ONLY=false by default. Reuse the exact deck bytes and
    # unchanged canonical native command including transistor report parsing.
    source_files = ("scripts/streaming_8x4_signoff_execute.py", "scripts/streaming_tt_layout.py")
    req = dict(schema="pinwheel.streaming-8x4-layout-native-request.v1", timeout_each=900,
               source_odb_sha256=ODB, producer_sha256={name: sha(ROOT / name) for name in source_files},
               input_sha256={"/input/actual.gds": GDS, "/input/actual.cdl": sha(cdl), **{
                   "/work/pdk/" + str(path.relative_to(context["pdk"])): deck_sha256[kind]
                   for kind, path in decks.items()}},
               qualified=False)
    write(inputs / "request.json", req)
    run_native(context, out, "python3",
               ["-B", "/worker/scripts/streaming_8x4_signoff_execute.py", "native-layout",
                "--request", "/work/export/inputs/request.json"],
               [(inputs, "/work/export/inputs", False), (ROOT / "scripts", "/worker/scripts", False),
                (ROOT / "physical", "/worker/physical", False), (context["gds"], "/input/actual.gds", False),
                (cdl, "/input/actual.cdl", False)], 2100, deadline,
               environment=("PYTHONPATH=/worker/scripts",))
    receipt = read(out / "native-result.json")
    require(receipt["completed"] and receipt["inputs_unchanged"] and receipt["source_odb_sha256"] == ODB
            and [row["kind"] for row in receipt["events"]] == ["antenna", "lvs"], "Layout receipt changed")
    antenna, lvs = (read(out / f"{kind}-result.json") for kind in ("antenna", "lvs"))
    require(antenna["report_sha256"] == sha(out / "antenna.xml") and
            lvs["report_sha256"] == sha(out / "lvs.lvsdb"), "Layout reader report hashes differ")
    observed = lvs["result"]
    log = (out / "lvs.native.log").read_text()
    require("Selected NET_ONLY option: false" in log, "LVS did not run in transistor mode")
    if observed["passed"]:
        require("Congratulations! Netlists match." in log, "Missing LVS success context")
    write(out / "rehearsal-lvs-readback.json", dict(status="pass" if observed["passed"] else "fail",
          target_odb_sha256=ODB, gds_sha256=GDS, reference_cdl_sha256=sha(cdl),
          deck_sha256=sha(decks["lvs"]), top=observed["top"], circuit_pairs=len(observed["circuits"]),
          layout_devices=observed["layout_devices"], schematic_devices=observed["schematic_devices"],
          antenna_categories=antenna["result"]["category_count"], antenna_pass=antenna["result"]["passed"],
          artifacts=[bind(out / name) for name in ("execution.json", "native-result.json", "native-journal.json",
                    "lvs.lvsdb", "lvs-result.json", "lvs.native.log", "antenna.xml", "antenna-result.json")]))
    require(observed["passed"] and antenna["result"]["passed"], "LVS or antenna has violations")


def precheck_python(context):
    python = context["base"] / "8x4-20261022-01/precheck-venv/bin/python3"
    require(python.is_file(), "Pinned precheck interpreter is missing")
    return python


def pin_leaf(context, _deadline):
    from streaming_8x4_closure24_gds_geometry import certified_template, load_measurement, observe_runtime

    checked_views(context)
    out = context["work"] / "pins"
    out.mkdir(exist_ok=False)
    allocation, template, pins = certified_template(context["prepared"], context["prep"])
    before = observe_runtime()
    result = load_measurement(context["gds"], pins)
    require(observe_runtime() == before and sha(context["gds"]) == GDS, "Pin observation inputs changed")
    measured = result["geometry"]
    passed = all(measured[key] for key in ("exact_top_bbox_8x4", "exact_rectangular_prBoundary_189_4",
                 "all43_exact_Metal4_pin_rectangles_and_50_25_labels"))
    write(out / "rehearsal-pin-readback.json", dict(status="pass" if passed else "fail",
          target_odb_sha256=ODB, gds_sha256=GDS, allocation_sha256=sha(allocation),
          template_sha256=sha(template), gdstk_version=before["gdstk_version"], measurement=result))
    require(passed, "Final GDS pin/boundary measurement failed")


def official(context, deadline):
    import os
    import signal

    import process_group
    import streaming_tt_signoff as signoff
    import streaming_8x4_closure24_official_budget as resource

    views_root, checked = checked_views(context)
    out = context["work"] / "official"
    package = out / "design"
    package.mkdir(parents=True, exist_ok=False)
    support = out / "tt"
    historical = context["base"] / "8x4-20261024-01/final24-official-context-01/tt"
    lock = read(ROOT / "tools/streaming-tt-signoff.json")
    pdk_identity = context["prep"]["pdk_identity"]
    signoff.verify_support(historical, lock)
    template = read(ROOT / "physical/streaming_8x4/allocation.json")
    for name in (*lock["support_files"], template["template_path"]):
        dest = support / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(historical / name, dest)
    frozen = signoff.verify_support(support, lock)
    official_template = support / template["template_path"]
    require(sha(official_template) == template["template_sha256"], "Official 8x4 template changed")
    frozen[str(official_template)] = sha(official_template)
    gds = package / f"{TOP}.gds"
    lef = package / f"{TOP}.lef"
    info = ROOT / "info.yaml"
    for source, dest in ((context["gds"], gds), (views_root / "official-format.lef", lef),
                         (views_root / "signoff-views/implemented.power.v", package / f"{TOP}.v"),
                         (info, package / "info.yaml")):
        shutil.copyfile(source, dest)
        frozen[str(source)] = frozen[str(dest)] = sha(source)
    require(sha(gds) == GDS and sha(lef) == checked["view_sha256"]["lef"],
            "Precheck staged a different final view")
    python = precheck_python(context)
    frozen[str(python.resolve())] = sha(python.resolve())
    env = signoff.python_environment(os.environ)
    probe = "import json,sys,importlib.metadata as m;print(json.dumps([sys.version,sys.flags.optimize,sys.flags.no_user_site,{n:m.version(n) for n in "
    probe += repr(list(lock["precheck_python_packages"])) + "}]))"
    version, optimize, no_user_site, packages = json.loads(subprocess.check_output(
        [str(python), "-B", "-c", probe], env=env, text=True, timeout=30))
    require(version.startswith(lock["python_version_prefix"]) and packages == lock["precheck_python_packages"]
            and optimize == 0 and no_user_site == 1,
            "Pinned precheck runtime/packages changed")
    owner = str(uuid.uuid4())
    native_config = out / "native-config.json"
    write(native_config, dict(out=str(out), pdk=str(context["pdk"]), owner=owner, image_id=IMAGE,
          container_name=signoff.container_name(out), schema="pinwheel.closure24-official-budget-native-config.v1",
          resource_policy=resource.policy()))
    binary = out / "bin"
    binary.mkdir()
    wrapper = binary / "klayout"
    wrapper.write_text("#!" + str(python) + "\nimport sys\nsys.path.insert(0," + repr(str(ROOT / "scripts")) +
                       ")\nfrom streaming_8x4_closure24_official_budget import native_klayout\n"
                       + "raise SystemExit(native_klayout(" + repr(str(native_config)) + ",sys.argv[1:]))\n")
    wrapper.chmod(0o755)
    for item in (native_config, wrapper, ROOT / "scripts/streaming_8x4_closure24_official_budget.py",
                 ROOT / "scripts/streaming_tt_signoff.py"):
        frozen[str(item)] = sha(item)
    overrides = dict(PDK_ROOT=str(context["pdk"]), PDK="ihp-sg13cmos5l",
                     PATH=str(binary) + os.pathsep + env["PATH"], PYTHONDONTWRITEBYTECODE="1",
                     PYTHONNOUSERSITE="1", PYTHONPATH="")
    removed = sorted(key for key in os.environ if key.startswith("PYTHON") or key == "__PYVENV_LAUNCHER__")
    precheck = support / "precheck"
    expected = signoff.selected_checks((precheck / "precheck.py").read_text(), overrides["PDK"])
    argv = ["/usr/bin/env", *[item for key in removed for item in ("-u", key)],
            *[f"{name}={value}" for name, value in overrides.items()],
            str(python), "-B", "precheck.py", "--gds", str(gds), "--tech", overrides["PDK"]]
    result = dict(status="fail", target_odb_sha256=ODB, gds_sha256=GDS,
                  lef_sha256=sha(lef), info_yaml_sha256=sha(info),
                  support_revision=lock["support_commit"], action_revision=None,
                  argv=argv, expected_checks=expected, python_version=version, packages=packages,
                  pdk_revision=pdk_identity["base"]["revision"], pdk_tree_sha256=pdk_identity["base"]["tree_sha256"])

    def interrupt(_signum, _frame):
        raise KeyboardInterrupt

    remaining = int(deadline - time.time()) - 120
    require(remaining >= 60, "Too close to campaign deadline for pinned precheck")
    started = time.monotonic()
    lock_dir = context["history"] / "build/streaming-tt-resources"
    with (lock_dir / "heavy.lock").open("rb") as lease:
        fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        require(not (lock_dir / "cleanup-unconfirmed.json").exists(), "Prior native cleanup is unconfirmed")
        old_handler = signal.signal(signal.SIGTERM, interrupt)
        try:
            observed = process_group.run_captured(argv, cwd=precheck, timeout=min(3600, remaining),
                                                  log_path=out / "precheck.log")
            result["exit_code"] = observed.returncode
            result["result"] = signoff.precheck_result(precheck / "reports/results.xml", expected, observed.returncode)
            result["native"] = resource.native_journal(out / "native-klayout.jsonl", out=out, pdk=context["pdk"],
                                                       owner=owner, image_id=IMAGE, gds=gds)
            require(result["result"]["passed"] and result["native"]["passed"], "Official precheck failed")
        finally:
            signal.signal(signal.SIGTERM, old_handler)
            result["cleanup"] = signoff.cleanup(owner)
            result["frozen_inputs_unchanged"] = (all(sha(path) == pin for path, pin in frozen.items())
                and pdk_snapshot(context["pdk"], context["prep"]) == pdk_identity)
            result["elapsed_seconds"] = time.monotonic() - started
            result["artifacts"] = [bind(path) for path in (gds, lef, package / "info.yaml", package / f"{TOP}.v",
                out / "precheck.log", out / "native-klayout.jsonl", precheck / "reports/results.xml",
                *sorted((precheck / "reports").glob("drc_*.xml")))
                if path.is_file()]
            if result["frozen_inputs_unchanged"] and result.get("result", {}).get("passed") and result.get(
                    "native", {}).get("passed"):
                result["status"] = "pass"
            write(out / "rehearsal-tt-precheck-readback.json", result)
    require(result["status"] == "pass", "Official precheck custody failed")


def aggregate(context, _deadline):
    work = context["work"]
    mapping = {"views": "views/rehearsal-view-readback.json", "transistor_lvs": "layout/rehearsal-lvs-readback.json",
               "pg_connectivity": "pg/rehearsal-pg-readback.json", "pin_geometry": "pins/rehearsal-pin-readback.json",
               "tt_precheck": "official/rehearsal-tt-precheck-readback.json"}
    checks = {}
    for name, path in mapping.items():
        source = work / path
        if not source.exists():
            checks[name] = {"status": "missing", "artifacts": []}
            continue
        record = read(source)
        require(record["target_odb_sha256"] == ODB and record["gds_sha256"] == GDS,
                f"{name} belongs to a different target")
        artifacts = record.get("artifacts", [])
        for row in artifacts:
            require(sha(ROOT / row["path"]) == row["sha256"], f"{name} evidence changed")
        checks[name] = {**record, "artifacts": [bind(source), *artifacts]}
    write(work / "native-receipt.json", dict(schema="pinwheel.e982-tt-native-rehearsal.v1",
          target_odb_sha256=ODB, gds_sha256=GDS, checks=checks,
          view_sha256=checks["views"].get("view_sha256", {})))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["views", "pg", "layout", "pg-layout", "pin-leaf", "official", "aggregate"])
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--deadline", type=int, required=True, help="UTC Unix timestamp")
    args = parser.parse_args()
    work = args.work.resolve()
    require(work.is_relative_to(ROOT / "build"), "Use a fresh local ignored build path")
    context = local_inputs(args.history.resolve(), work)
    steps = {"views": (views,), "pg": (pg,), "layout": (layout,), "pg-layout": (pg, layout), "pin-leaf": (pin_leaf,), "official": (official,), "aggregate": (aggregate,)}
    for step in steps[args.phase]:
        step(context, args.deadline)


if __name__ == "__main__":
    main()
