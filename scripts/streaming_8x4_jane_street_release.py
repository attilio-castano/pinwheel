"""Stage frozen Pinwheel views and replay the current Tiny Tapeout precheck."""

import argparse
import fcntl
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tarfile
import tempfile
import time
import uuid
from zipfile import ZIP_DEFLATED, ZipFile

import process_group
import streaming_8x4_closure24_official_budget as native
import streaming_tt_signoff as signoff
from streaming_8x4_e982_native import ROOT, TOP, write
from streaming_8x4_hold_cap_rehearsal import GDS, ODB
from streaming_8x4_jane_street_source import RTL
from streaming_8x4_tt_rehearsal import digest, file_spec, read_json, require


BUILD = ROOT / "build/8x4-hold-cap-20261107"
BUNDLE = BUILD / "trial-02/rehearsal-01/bundle"
BUNDLE_SHA = "0533dfb6c6ddf203a43f8b2a5cd67a399e6deb1a3afa2911a1d0b00646b4158f"
BUNDLE_ARCHIVE_SHA = "07e8716279ca1458bcb12c3ed1f2f4c230d2961f799987fd02679cbab5b96632"
SOURCE_COMMIT = "a305a4b339767e80719c9720a12ced7345b0e814"
RELEASE_ROOT = ROOT / "build/8x4-jane-street-entry-20261114"
SUPPORT = "9d13ff3e3e6202090740110438c6a10c1d62ca0f"
ACTION = "e7a50f8f46f9f8df4b2c9935bfeb1cbc6b6ae4f6"
TEMPLATE = "4b1204ab387b5ab94db1d57067051d8d89a2f83c"
TEMPLATE_DEF = "tech/ihp-sg13cmos5l/def/tt_block_8x4_pgvdd.def"
TEMPLATE_SHA = "64b52f2150f699edc7fb500c2f486a51eca66fd91d3efb7347200bd2cf83a2ee"
PDK = "ihp-sg13cmos5l"
PDK_REVISION = "89d42ee6d2fd9b50b86a1aada6fee6673c3e6008"
PRECHECK_IMAGE = "pinwheel-ttihp27a-precheck-local:0.30.8"
CONVERTER_IMAGE = "pinwheel-ttihp27a-converter-local:0.30.12"
UPSTREAM_DEB_SHA = "23480767fec91bc9a15e075a9bd6906ba85cd7fdda8b4040dde4ffc95c26a742"
RELEASE_WORKFLOW = ROOT / "physical/streaming_8x4/ttihp27a-custom-gds.yml"
REVISION_FILES = {
    "custom_gds/action.yml": "558ce5b2e3a03331774fbbd850923fc921748a1f6cc3c48cf005c339fd1f0ee7",
    "precheck/action.yml": "688091ba49d0ea0930fdd1c171cafffab9fc1c02ae4e8f0e95e961d3b7697531",
}
ASSETS = {"gds": f"tt_submission/{TOP}.gds", "lef": f"tt_submission/{TOP}.lef",
          "nl": f"tt_submission/{TOP}.v", "pnl": f"views/{TOP}.power.v",
          "info_yaml": "info.yaml", "docs_info_md": "docs/info.md", "license": "LICENSE"}
RELEASE_INPUTS = {f"release/{Path(ASSETS[role]).name}": ASSETS[role] for role in ("gds", "lef", "nl")}
RELEASE_OVERLAY = {*RELEASE_INPUTS, "info.yaml", "LICENSE", "docs/info.md", "docs/jane-street-8x4-entry.md",
                   ".github/workflows/gds.yml", *(f"src/{name}" for name in RTL)}
PRECHECK_SOURCE = ("precheck", TEMPLATE_DEF, f"tech/{PDK}/tile_sizes.yaml", "project_checks.py", "project_info.py")


def record(root, path):
    return {"path": path.relative_to(root).as_posix(), "sha256": digest(path), "bytes": path.stat().st_size}


def frozen_bundle(bundle):
    require(digest(bundle / "manifest.json") == BUNDLE_SHA, "Frozen rehearsal manifest differs")
    manifest = read_json(bundle / "manifest.json")
    require((manifest["source_commit"], manifest["gds_sha256"], manifest["target_odb_sha256"]) ==
            (SOURCE_COMMIT, GDS, ODB), "Wrong frozen candidate")
    return manifest


def verify_archive(bundle):
    archive = bundle.parent / "pinwheel-8x4-hold-cap-rehearsal.tar.gz"
    require(digest(archive) == BUNDLE_ARCHIVE_SHA, "Frozen rehearsal archive differs")


def stage(out, bundle):
    manifest = frozen_bundle(bundle)
    files = {role: file_spec(bundle, manifest["payload"][role]) for role in ASSETS}
    out.mkdir(parents=True, exist_ok=False)
    for role, name in ASSETS.items():
        dest = out / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(bundle / files[role]["path"], dest)
        require(digest(dest) == files[role]["sha256"], f"Staged bytes changed for {role}")
    write(out / "tt_submission/pdk.json", {"PDK": PDK})
    names = (*ASSETS.values(), "tt_submission/pdk.json")
    write(out / "stage.json", dict(schema="pinwheel.streaming-8x4-jane-street-stage.v1",
        rehearsal_manifest_sha256=BUNDLE_SHA, target_gds_sha256=GDS, source_commit=SOURCE_COMMIT,
        action_revision=ACTION, support_revision=SUPPORT, template_revision=TEMPLATE,
        pdk_revision=PDK_REVISION, files=[record(out, out / name) for name in names],
        github_artifact_created=False, shuttle_acceptance=False))


def checked_stage(out, bundle):
    stage_receipt = read_json(out / "stage.json")
    manifest = frozen_bundle(bundle)
    files = [file_spec(out, entry) for entry in stage_receipt["files"]]
    require(stage_receipt["schema"] == "pinwheel.streaming-8x4-jane-street-stage.v1"
            and (stage_receipt["rehearsal_manifest_sha256"], stage_receipt["target_gds_sha256"],
                 stage_receipt["source_commit"], stage_receipt["action_revision"], stage_receipt["support_revision"],
                 stage_receipt["template_revision"], stage_receipt["pdk_revision"]) ==
                (BUNDLE_SHA, GDS, SOURCE_COMMIT, ACTION, SUPPORT, TEMPLATE, PDK_REVISION)
            and stage_receipt["github_artifact_created"] is False and stage_receipt["shuttle_acceptance"] is False
            and sorted(entry["path"] for entry in files) == sorted([*ASSETS.values(), "tt_submission/pdk.json"])
            and {entry["path"]: entry["sha256"] for entry in files if entry["path"] in ASSETS.values()} ==
            {name: manifest["payload"][role]["sha256"] for role, name in ASSETS.items()},
            "Staging and verified rehearsal bytes disagree")
    require(read_json(out / "tt_submission/pdk.json") == {"PDK": PDK}, "Wrong custom-GDS PDK metadata")
    return files


def checked_source(source):
    receipt = read_json(source / "receipt.json")
    require(receipt["schema"] == "pinwheel.streaming-8x4-jane-street-source.v1" and receipt["passed"] is True
            and receipt["source_commit"] == SOURCE_COMMIT and receipt["target_gds_sha256"] == GDS
            and {name: data["sha256"] for name, data in receipt["files"].items()} ==
                {f"src/{name}": sha for name, sha in RTL.items()}, "Wrong generated RTL receipt")
    return [file_spec(source, dict(path=name, **value)) for name, value in receipt["files"].items()]


def layouts_equal(gds, oasis):
    from collections import Counter
    import klayout.db as db

    left, right = db.Layout(), db.Layout()
    left.read(str(gds))
    right.read(str(oasis))
    require(left.dbu == right.dbu == 0.001 and left.top_cell().name == right.top_cell().name == TOP,
            "OASIS conversion changed DBU or top cell")
    flags = (db.LayoutDiff.NoLayerNames | db.LayoutDiff.BoxesAsPolygons | db.LayoutDiff.PathsAsPolygons |
             db.LayoutDiff.FlattenArrayInsts | db.LayoutDiff.NoProperties | db.LayoutDiff.IgnoreDuplicates |
             db.LayoutDiff.NoTextOrientation)
    require(db.LayoutDiff().compare(left, right, flags, 0), "OASIS conversion changed layout geometry")

    def labels(layout):
        result = Counter()
        for cell in layout.each_cell():
            for index in layout.layer_indexes():
                layer = layout.get_info(index)
                for shape in cell.shapes(index).each():
                    if shape.is_text():
                        label = shape.text
                        result[(cell.name, layer.layer, layer.datatype, label.string, str(label.trans))] += 1
        return result

    source_labels = labels(left)
    require(source_labels == labels(right), "OASIS conversion changed a label")
    return dict(cells=left.cells(), layers=left.layers(), labels=sum(source_labels.values()),
                geometry_tolerance_dbu=0, duplicate_shapes_and_format_properties_ignored=True)


def convert(out, bundle, deb):
    checked_stage(out, bundle)
    require(digest(deb) == UPSTREAM_DEB_SHA, "Wrong upstream Tiny Tapeout converter package")
    path = out / "tt_submission"
    oasis = path / f"{TOP}.oas"
    require(not oasis.exists() and not (out / "conversion.json").exists(), "Use a fresh conversion")
    image = subprocess.check_output(["docker", "image", "inspect", CONVERTER_IMAGE, "--format", "{{.Id}}"],
                                    text=True, timeout=20).strip()
    prefix = ["docker", "run", "--rm", "--pull", "never", "--platform", "linux/amd64", "--network", "none",
              "--read-only", "--tmpfs", "/tmp:rw,size=256m"]
    version = subprocess.check_output([*prefix, "--entrypoint", "klayout", image, "-v"], text=True, timeout=30).strip()
    require(version == "KLayout 0.30.12", "Wrong custom-GDS converter version")
    argv = [*prefix, "--mount", f"type=bind,source={path},target=/release", "--workdir", "/release",
            "--entrypoint", "strm2oas", image, f"{TOP}.gds", f"{TOP}.oas"]
    subprocess.run(argv, check=True, timeout=120)
    geometry = layouts_equal(path / f"{TOP}.gds", oasis)
    write(out / "conversion.json", dict(schema="pinwheel.streaming-8x4-jane-street-conversion.v1",
        argv=argv, target_gds_sha256=GDS, tiny_tapeout_deb_sha256=UPSTREAM_DEB_SHA,
        klayout=version, image=image, oasis=record(out, oasis), geometry=geometry))


def verified_precheck(out):
    receipt = read_json(out / "precheck.json")
    require((receipt["target_gds_sha256"], receipt["support_revision"], receipt["action_revision"],
             receipt["pdk_revision"]) == (GDS, SUPPORT, ACTION, PDK_REVISION)
            and receipt["checked_project_docs"] is True and receipt["cleanup"]["status"] == "absent",
            "Release precheck identity or custody differs")
    proofs = {file_spec(out, entry)["path"] for entry in receipt["artifacts"]}
    precheck_dir = out / "precheck-run/tt/precheck"
    xml = precheck_dir / "reports/results.xml"
    require(xml.relative_to(out).as_posix() in proofs, "Precheck XML is missing from receipt")
    expected = signoff.selected_checks((precheck_dir / "precheck.py").read_text(), PDK)
    require(expected == receipt["expected_checks"], "Precheck inventory differs from current source")
    confirmed = signoff.precheck_result(xml, expected, receipt["exit_code"])
    require(receipt["status"] == "pass" and confirmed == receipt["result"] and confirmed["passed"],
            "Current precheck failed")
    return confirmed


def package_release(out, bundle, source):
    stage_files = checked_stage(out, bundle)
    conversion = read_json(out / "conversion.json")
    oasis = file_spec(out, conversion["oasis"])
    require(conversion["target_gds_sha256"] == GDS and oasis["path"] == f"tt_submission/{TOP}.oas",
            "Wrong local OASIS conversion receipt")
    checks = verified_precheck(out)
    require(not (out / "handoff.json").exists(), "Local handoff already recorded")
    files = []
    for destination, staged in sorted(RELEASE_INPUTS.items()):
        dest = out / destination
        dest.parent.mkdir(parents=True, exist_ok=True)
        with (out / staged).open("rb") as stream, dest.open("xb") as output:
            shutil.copyfileobj(stream, output)
        binding = next(entry for entry in stage_files if entry["path"] == staged)
        files.append(file_spec(out, dict(binding, path=destination)))
    for entry in checked_source(source):
        dest = out / entry["path"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        with (source / entry["path"]).open("rb") as stream, dest.open("xb") as output:
            shutil.copyfileobj(stream, output)
        files.append(file_spec(out, entry))
    workflow = out / ".github/workflows/gds.yml"
    workflow.parent.mkdir(parents=True)
    shutil.copyfile(RELEASE_WORKFLOW, workflow)
    files.append(record(out, workflow))
    draft = out / "docs/jane-street-8x4-entry.md"
    shutil.copyfile(ROOT / "docs/jane-street-8x4-entry.md", draft)
    files.append(record(out, draft))
    metadata = out / "tt_submission/commit_id.json"
    write(metadata, {"app": "Pinwheel local preview", "commit": None, "repo": None, "workflow_url": None})
    files.extend([record(out, metadata), *stage_files, oasis])
    source_record = out / "source-receipt.json"
    shutil.copyfile(source / "receipt.json", source_record)
    require(digest(source_record) == digest(source / "receipt.json"), "Generated source receipt changed during copy")
    preview = out / "tt_submission-local-preview.zip"
    preview_paths = sorted(entry["path"] for entry in files if entry["path"].startswith(("tt_submission/", "docs/"))
                           or entry["path"] in {"LICENSE", "info.yaml"})
    with ZipFile(preview, "x", compression=ZIP_DEFLATED) as archive:
        for name in preview_paths:
            archive.write(out / name, name)
    overlay = out / "release-overlay.zip"
    with ZipFile(overlay, "x", compression=ZIP_DEFLATED) as archive:
        for name in sorted(RELEASE_OVERLAY):
            archive.write(out / name, name)
    write(out / "handoff.json", dict(schema="pinwheel.streaming-8x4-jane-street-handoff.v1", files=files,
        rehearsal_manifest_sha256=BUNDLE_SHA, source_receipt=record(out, source_record),
        target_gds_sha256=GDS, precheck_receipt=record(out, out / "precheck.json"),
        conversion_receipt=record(out, out / "conversion.json"), checks=checks["checks"],
        preview=record(out, preview), preview_paths=preview_paths, overlay=record(out, overlay),
        overlay_paths=sorted(RELEASE_OVERLAY), local_release_ready=True,
        github_artifact_created=False, submitted=False, shuttle_acceptance=False, fabrication="no-go"))


def verify_release(out, bundle, expected):
    import hashlib

    checked_stage(out, bundle)
    verify_archive(bundle)
    receipt_path = out / "handoff.json"
    require(digest(receipt_path) == expected, "Local handoff manifest SHA-256 differs")
    receipt = read_json(receipt_path)
    files = {entry["path"]: file_spec(out, entry) for entry in receipt["files"]}
    for name in ("precheck_receipt", "conversion_receipt", "source_receipt"):
        file_spec(out, receipt[name])
    source = read_json(out / receipt["source_receipt"]["path"])
    require(source["source_commit"] == SOURCE_COMMIT and source["target_gds_sha256"] == GDS
            and source["passed"] is True and {f"src/{name}": files[f"src/{name}"]["sha256"] for name in RTL} ==
                {name: row["sha256"] for name, row in source["files"].items()} ==
                {f"src/{name}": sha for name, sha in RTL.items()}, "Wrong source evidence in handoff")
    require(verified_precheck(out)["checks"] == receipt["checks"], "Wrong precheck result bound to handoff")
    for kind in ("preview", "overlay"):
        binding = file_spec(out, receipt[kind])
        with ZipFile(out / binding["path"]) as archive:
            require(archive.namelist() == receipt[f"{kind}_paths"], f"Unexpected local {kind} members")
            for name in archive.namelist():
                with archive.open(name) as stream:
                    require(hashlib.file_digest(stream, "sha256").hexdigest() == files[name]["sha256"],
                            f"Archived member differs from checked release: {name}")
    conversion = read_json(out / receipt["conversion_receipt"]["path"])
    require(layouts_equal(out / ASSETS["gds"], out / conversion["oasis"]["path"]) == conversion["geometry"],
            "OASIS geometry readback differs")
    print(f"Verified local release with {len(files)} staged files and {len(receipt['checks'])} current prechecks")


def install_support(support, dest):
    with tempfile.TemporaryFile() as archive:
        subprocess.run(["git", "-C", str(support), "archive", SUPPORT, *PRECHECK_SOURCE],
                       stdout=archive, check=True, timeout=30)
        archive.seek(0)
        with tarfile.open(fileobj=archive) as tar:
            tar.extractall(dest, filter="data")
    require(digest(dest / TEMPLATE_DEF) == TEMPLATE_SHA, "8×4 template differs from frozen geometry")
    return signoff.inventory(dest)


def check_action(action):
    commit = subprocess.check_output(["git", "-C", str(action), "rev-parse", "HEAD"], text=True, timeout=10)
    require(commit.strip() == ACTION, "Wrong Tiny Tapeout action checkout")
    for name, sha in REVISION_FILES.items():
        file_spec(action, {"path": name, "sha256": sha})


def precheck(out, bundle, support, action, pdk, python, lease, timeout):
    files = checked_stage(out, bundle)
    check_action(action)
    require((pdk / PDK).resolve().is_relative_to(pdk / f"ciel/ihp-sg13/versions/{PDK_REVISION}"),
            "Use the Ciel installation of the action's pinned CMOS5L revision")
    attempt = out / "precheck-run"
    attempt.mkdir(exist_ok=False)
    tools = attempt / "tt"
    frozen = install_support(support, tools)
    pdk_dir = (pdk / PDK / "libs.tech/klayout").resolve()
    require(pdk_dir.is_dir(), "Pinned Ciel PDK omits KLayout files")
    pdk_files = signoff.inventory(pdk_dir, aliases={})
    environment = signoff.python_environment(os.environ)
    environment.update(PDK=PDK, PDK_ROOT=str(pdk), PATH=str(python.parent) + os.pathsep + environment["PATH"],
        XDG_CACHE_HOME=str(attempt / "cache"))
    image = subprocess.check_output(["docker", "image", "inspect", PRECHECK_IMAGE, "--format", "{{.Id}}"],
                                    text=True, timeout=20).strip()
    version = subprocess.check_output(["docker", "run", "--rm", "--pull", "never", "--network", "none",
        "--entrypoint", "klayout", image, "-v"], text=True, timeout=30).strip()
    require(version == "KLayout 0.30.8", "Wrong Nix KLayout version")
    # Mount the release root for staged inputs and the official report directory.
    owner = str(uuid.uuid4())
    config = out / "native-config.json"
    write(config, dict(out=str(out), pdk=str(pdk), owner=owner, image_id=image,
        container_name=signoff.container_name(out), schema="pinwheel.closure24-official-budget-native-config.v1",
        resource_policy=native.policy()))
    binary = attempt / "bin"
    binary.mkdir()
    wrapper = binary / "klayout"
    wrapper.write_text(f"#!{python}\nimport sys\nsys.path.insert(0, {str(ROOT / 'scripts')!r})\n"
                       "from streaming_8x4_closure24_official_budget import native_klayout\n"
                       f"raise SystemExit(native_klayout({str(config)!r}, sys.argv[1:]))\n")
    wrapper.chmod(0o755)
    environment["PATH"] = str(binary) + os.pathsep + environment["PATH"]
    gds = out / ASSETS["gds"]
    precheck_dir = tools / "precheck"
    expected = signoff.selected_checks((precheck_dir / "precheck.py").read_text(), PDK)
    runtime = subprocess.check_output([str(python), "-B", "-c", "import sys,importlib.metadata as m;"
        "print(sys.version);print({n:m.version(n) for n in ('klayout','gdstk','yowasp-yosys','numpy','pyyaml')})"],
        env=environment, text=True, timeout=10)
    require("3.11." in runtime and "'klayout': '0.30.8'" in runtime, "Wrong precheck host runtime")
    metadata = subprocess.check_output([str(python), "-B", "-c",
        "import sys;sys.path.insert(0,sys.argv[1]);from project_checks import check_project_docs;"
        "check_project_docs(sys.argv[2],sys.argv[3])", str(tools), str(out), PDK],
        env=environment, text=True, timeout=20).strip()
    require(metadata == "Documentation check passed successfully.", "Current project documentation check failed")
    argv = [str(python), "-B", "precheck.py", "--gds", str(gds), "--tech", PDK]
    command = ["/usr/bin/env"]
    for name in os.environ:
        if name.startswith("PYTHON") or name == "__PYVENV_LAUNCHER__":
            command.extend(("-u", name))
    variables = ("PATH", "PDK", "PDK_ROOT", "XDG_CACHE_HOME", "PYTHONNOUSERSITE", "PYTHONDONTWRITEBYTECODE", "PYTHONPATH")
    command.extend(f"{name}={environment[name]}" for name in variables)
    command.extend(argv)
    receipt = dict(schema="pinwheel.streaming-8x4-jane-street-precheck.v1", status="incomplete",
        target_gds_sha256=GDS, action_revision=ACTION, support_revision=SUPPORT, pdk_revision=PDK_REVISION,
        template_sha256=TEMPLATE_SHA, expected_checks=expected, runtime=runtime, klayout_image=image,
        klayout=version, checked_project_docs=True, github_artifact_created=False, argv=command)
    started = time.monotonic()

    def interrupt(_signum, _frame):
        raise KeyboardInterrupt

    with lease.open("rb") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        require(not (lease.parent / "cleanup-unconfirmed.json").exists(), "Previous native cleanup unconfirmed")
        handler = signal.signal(signal.SIGTERM, interrupt)
        try:
            result = process_group.run_captured(command, cwd=precheck_dir, timeout=timeout,
                                                log_path=attempt / "precheck.log")
            receipt["exit_code"] = result.returncode
            receipt["result"] = signoff.precheck_result(precheck_dir / "reports/results.xml", expected,
                                                        result.returncode)
            journal = out / "native-klayout.jsonl"
            receipt["checks"] = checked_native(out, precheck_dir, pdk, gds, journal, config)
            if receipt["result"]["passed"]:
                require(all(entry["exit_code"] == 0 and entry["report"] for entry in receipt["checks"]),
                        "Passing precheck did not close all native deck calls")
            receipt["status"] = "pass" if receipt["result"]["passed"] else "fail"
        finally:
            signal.signal(signal.SIGTERM, handler)
            receipt["cleanup"] = signoff.cleanup(owner)
            receipt["elapsed_seconds"] = time.monotonic() - started
            signoff.unchanged(frozen)
            signoff.unchanged(pdk_files)
            require(checked_stage(out, bundle) == files, "Staged package changed during precheck")
            artifacts = (attempt / "precheck.log", out / "native-klayout.jsonl", config,
                         *sorted((precheck_dir / "reports").glob("*.xml")))
            receipt["artifacts"] = [record(out, item) for item in artifacts if item.is_file()]
            write(out / "precheck.json", receipt)
    require(receipt["status"] == "pass", "Current Tiny Tapeout precheck failed. See precheck.json")


def checked_native(out, cwd, pdk, gds, journal, config):
    events = [signoff.decode(line) for line in journal.read_text().splitlines()]
    checks = {"pin_label_purposes_overlapping_drawing": "tech-files/pin_label_purposes_overlapping_drawing.rb.drc",
        "sg13cmos5l": str(pdk / PDK / "libs.tech/klayout/tech/drc/ihp-sg13cmos5l.drc"),
        "zero_area": "tech-files/zeroarea.rb.drc"}
    require(len(events) == 2 * len(checks), "Missing current native deck calls")
    identity = read_json(config)
    reports = []
    for (name, deck), start, finish in zip(checks.items(), events[::2], events[1::2]):
        report = cwd / "reports" / f"drc_{name}.xml"
        expected = ["docker", "run", "--rm", "--pull", "never", "--name", identity["container_name"],
            "--network", "none", "--read-only", "--tmpfs", "/tmp:rw,size=256m", "--cpus", "1",
            "--memory", "6g", "--memory-swap", "6g", "--label", f"org.pinwheel.signoff_owner={identity['owner']}",
            "--mount", f"type=bind,source={out},target={out}",
            "--mount", f"type=bind,source={pdk},target={pdk},readonly", "--workdir", str(cwd),
            "--entrypoint", "klayout", identity["image_id"], "-b", "-r", deck, "-rd", f"{name}=true",
            "-rd", f"input={gds}", "-rd", "thr=1", "-rd", f"report={report}", "-rd", f"report_file={report}"]
        require(start["event"] == "intent" and finish["event"] == "result" and start["identity"] == finish["identity"]
                and start["argv"] == expected and isinstance(finish["exit_code"], int),
                f"Native call differs for {name}")
        reports.append(dict(name=name, exit_code=finish["exit_code"], seconds=finish["seconds"],
                            report=record(out, report) if report.is_file() else None))
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("stage", "convert", "precheck", "package", "verify"))
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--bundle", type=Path, default=BUNDLE)
    parser.add_argument("--support", type=Path, default=BUILD / "verification-support-9d13ff3")
    parser.add_argument("--action", type=Path, default=BUILD / "verification-action-e7a50f8")
    parser.add_argument("--pdk", type=Path, default=BUILD / "verification-ciel")
    parser.add_argument("--python", type=Path, default=BUILD / "verification-precheck-venv/bin/python")
    parser.add_argument("--lease", type=Path)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--converter-deb", type=Path,
        default=BUILD / "verification-runtime-cache/klayout_0.30.12-1_ubuntu24.04_amd64.deb")
    parser.add_argument("--handoff-sha")
    parser.add_argument("--timeout", type=int, default=4800)
    args = parser.parse_args()
    out, bundle = args.out.resolve(), args.bundle.resolve()
    require(out.parent == RELEASE_ROOT, "Use an ignored campaign release directory")
    if args.phase == "stage":
        stage(out, bundle)
    elif args.phase == "convert":
        convert(out, bundle, args.converter_deb.resolve())
    elif args.phase == "precheck":
        require(args.lease and args.timeout > 0, "Precheck requires the local native worker lease and a deadline")
        precheck(out, bundle, args.support.resolve(), args.action.resolve(), args.pdk.resolve(),
                 args.python.absolute(), args.lease.resolve(), args.timeout)
    elif args.phase == "package":
        require(args.source, "Provide the sealed generated RTL directory")
        package_release(out, bundle, args.source.resolve())
    else:
        require(args.handoff_sha, "Provide the independently recorded handoff SHA-256")
        verify_release(out, bundle, args.handoff_sha)


if __name__ == "__main__":
    main()
