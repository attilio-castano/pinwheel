"""Stage and run one immutable, routing-only experiment in the approved campaign.

The native import adapter must be qualified separately before a candidate run.
This entry point preserves producer receipts and applies independent host gates.
"""
from __future__ import annotations

import argparse
import ast
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import time

from drc import parse_native_log
from runner import JobSpec, run_owned_job
import drc
import runner

ROOT = Path(__file__).resolve().parents[2]
ORIGINAL = ROOT / "build/physical/tt-p2-drt-onepass-route-01"
CAMPAIGN_ID = "tt-overnight-20261015-000717"


def read(path: Path):
    return json.loads(path.read_text())


def write(path: Path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def settled_job(receipt_path: Path, image_id: str):
    receipt = read(receipt_path)
    assert receipt["status"] == "passed", receipt_path
    assert receipt["image_id"] == image_id, receipt_path
    assert receipt["inputs_unchanged"] is True, receipt_path
    assert receipt["container_termination"]["status"] == "absent", receipt_path
    assert receipt["within_absolute_and_job_deadlines"] is True, receipt_path
    return receipt


def retained_artifact(path: Path, receipt_path: Path, receipt):
    path, parent = path.resolve(), receipt_path.resolve().parent
    assert path.is_relative_to(parent), (path, parent)
    assert receipt["artifact_sha256"][str(path.relative_to(parent))] == sha(path), path


def adapter_admission(args, manifest):
    binary_hash = sha(args.adapter)
    build_job = settled_job(args.adapter_build_job_receipt, manifest["image_id"])
    retained_artifact(args.adapter, args.adapter_build_job_receipt, build_job)
    retained_artifact(args.adapter_build_receipt, args.adapter_build_job_receipt, build_job)
    build = read(args.adapter_build_receipt)
    assert build["status"] == "passed"
    variants = {v["variant"]: v for v in build["commands"]}
    assert set(variants) == {"original", "patched"}
    assert all(v["returncode"] == 0 for v in variants.values())
    assert variants["patched"]["binary_sha256"] == binary_hash
    fixtures_job = settled_job(args.adapter_fixture_job_receipt, manifest["image_id"])
    retained_artifact(args.adapter_fixture_receipt, args.adapter_fixture_job_receipt, fixtures_job)
    fixtures = read(args.adapter_fixture_receipt)
    assert fixtures["status"] == "passed" and fixtures["fixture_count"] >= 12
    assert fixtures["before_any_PA_GC_TA_DR"] is True
    assert fixtures["binary_sha256"]["patched"] == binary_hash
    assert fixtures["binary_sha256"]["original"] == variants["original"]["binary_sha256"]
    assert len(fixtures["cases"]) == fixtures["fixture_count"]
    required_cases = {(case, variant) for case, variant in (
        ("plain", "original"), ("plain", "patched"),
        ("same_width", "original"), ("same_width", "patched"),
        ("wide", "original"), ("wide", "patched"), ("fixed", "patched"),
        ("distinct_rule", "patched"), ("ndr_rect", "patched"),
        ("ambiguous", "patched"), ("unmatched", "patched"), ("empty", "patched"))}
    observed_cases = {(v["case"], v["variant"]) for v in fixtures["cases"]}
    assert len(observed_cases) == len(fixtures["cases"])
    assert required_cases <= observed_cases
    assert all(v["gate_passed"] for v in fixtures["cases"])
    return {"status": "admitted", "adapter_sha256": binary_hash,
            "build_receipt_sha256": sha(args.adapter_build_receipt),
            "build_job_receipt_sha256": sha(args.adapter_build_job_receipt),
            "fixture_receipt_sha256": sha(args.adapter_fixture_receipt),
            "fixture_job_receipt_sha256": sha(args.adapter_fixture_job_receipt)}


def control_admission(args, adapter_hash, source_hash, image_id):
    assert args.control_root is not None, "A candidate requires a passed exact no-edit control"
    control = args.control_root.resolve()
    receipt = settled_job(control / "report.json", image_id)
    for filename in ("stage-plan.json", "input.odb", "libpinwheel_drt_preservation.so"):
        retained_artifact(control / filename, control / "report.json", receipt)
    plan = read(control / "stage-plan.json")
    adjudication = read(control / "adjudication.json")
    assert plan["control"] and plan["end_iter"] == 0
    assert plan["source_odb_sha256"] == source_hash
    assert plan["adapter_sha256"] == adapter_hash
    assert plan["source_guides_sha256"] == sha(ORIGINAL / "input.guide")
    assert sha(control / "input.odb") == source_hash
    assert sha(control / "libpinwheel_drt_preservation.so") == adapter_hash
    assert adjudication["control"] and adjudication["stage_execution_and_scope_gate_passed"]
    # Post-run host adjudication is separately hashed in this admission record.
    retained_artifact(control / "control-wire-proof.json", control / "report.json", receipt)
    assert read(control / "control-wire-proof.json")["status"] == "passed"
    return {"root": str(control), "source_odb_sha256": source_hash,
            "receipt_sha256": sha(control / "report.json"),
            "adjudication_sha256": sha(control / "adjudication.json")}


def native_program(iteration: int, control: bool, snapshots: bool) -> str:
    source = (ORIGINAL / "native.py").read_text()
    old = "assert BOUNDS['native_end_iter']==0 and BOUNDS['maximum_actual_search_repair_passes']==1"
    assert source.count(old) == 1
    source = source.replace(old, f"assert BOUNDS['native_end_iter']=={iteration} and BOUNDS['maximum_actual_search_repair_passes']=={iteration + 1}")
    source = source.replace("detailed_route -droute_end_iter 0 ", f"detailed_route -droute_end_iter {iteration} ")
    source = source.replace("'maximum_end_iteration_option':0,'maximum_actual_search_repair_passes':1,'zero_based_iteration_indices':[0]", f"'maximum_end_iteration_option':{iteration},'maximum_actual_search_repair_passes':{iteration + 1},'zero_based_iteration_indices':{list(range(iteration + 1))}")
    source = source.replace("'droute_end_iter_option':0,'maximum_actual_search_repair_passes':1", f"'droute_end_iter_option':{iteration},'maximum_actual_search_repair_passes':{iteration + 1}")
    load = "tcl('source /work/diagnostic/load.tcl');B,BG,BW=inventory('before')"
    assert source.count(load) == 1
    adapter = """tcl('source /work/diagnostic/load.tcl')
tcl('load /work/diagnostic/libpinwheel_drt_preservation.so Pinwheeldrtpreservation\\nrename drt::detailed_route_cmd drt::detailed_route_cmd_original\\ninterp alias {} drt::detailed_route_cmd {} pinwheel_drt_preservation_detailed_route_cmd')
B,BG,BW=inventory('before')"""
    source = source.replace(load, adapter)
    if snapshots:
        anchor = "error=tcl(cmd,allow_error=True)"
        assert source.count(anchor) == 1
        source = source.replace(anchor, "(R/'checkpoints').mkdir()\ntcl('detailed_route_debug -snapshot_dir /work/diagnostic/checkpoints\\nset_debug_level DRT snapshot 1')\n" + anchor)
    if control:
        anchor = "tcl('check_placement -verbose\\ncheck_power_grid -net VPWR -error_file /work/diagnostic/after/VPWR-grid-errors.rpt"
        assert source.count(anchor) == 1
        gate = """def route_sections(path):
 text=path.read_text();out={}
 for section in ('NETS','SPECIALNETS'):
  m=re.search(r'(?ms)^'+section+r'\\s+\\d+\\s*;\\s*(.*?)^END '+section+r'\\s*$',text)
  assert m,section
  out[section]=' '.join(m[1].split())
 return out
control_wires_exact=route_sections(R/'before/checkpoint.def')==route_sections(R/'after/checkpoint.def')
write(R/'control-wire-proof.json',{'status':'passed' if control_wires_exact else 'failed','complete_NETS_SPECIALNETS_geometry_and_per_path_RULE_TAPER_tokens_exact':control_wires_exact})
assert control_wires_exact,'No-edit control changed detailed geometry or per-path routing rules'
"""
        source = source.replace(anchor, gate + anchor)
    ast.parse(source)
    return source


def main() -> int:
    stage_started_epoch, stage_started_mono = time.time(), time.monotonic()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--name", required=True)
    parser.add_argument("--adapter", type=Path, required=True)
    parser.add_argument("--adapter-build-receipt", type=Path, required=True)
    parser.add_argument("--adapter-build-job-receipt", type=Path, required=True)
    parser.add_argument("--adapter-fixture-receipt", type=Path, required=True)
    parser.add_argument("--adapter-fixture-job-receipt", type=Path, required=True)
    parser.add_argument("--control-root", type=Path)
    parser.add_argument("--source-root", type=Path, default=ORIGINAL / "after")
    parser.add_argument("--end-iter", type=int, required=True)
    parser.add_argument("--native-seconds", type=int, required=True)
    parser.add_argument("--control", action="store_true")
    parser.add_argument("--snapshots", action="store_true")
    args = parser.parse_args()
    assert not args.snapshots, "Resident debug snapshot writer is unqualified and mutates OpenDB with the old serializer"
    assert 0 <= args.end_iter <= 64
    assert (args.control and args.end_iter == 0) or (not args.control and args.end_iter >= 3)
    assert args.name and all(c.isalnum() or c in "-_" for c in args.name)
    manifest_path = args.manifest.resolve()
    campaign = manifest_path.parent
    manifest = read(manifest_path)
    admitted_adapter = adapter_admission(args, manifest)
    # Reserve the approved final hour for host closeout and the morning report.
    native_deadline = min(manifest["hard_stop_epoch"] - 3600, stage_started_epoch + 5400)
    allowed = min(args.native_seconds, 5400 - 60, int(native_deadline - time.time() - 60))
    assert allowed >= 60, "No native window remains before final-hour closeout"
    out = campaign / "runs" / args.name
    out.mkdir(parents=True, exist_ok=False)
    sources = dict(manifest["protected_sources_sha256"])
    sources.update(manifest["reference_files_sha256"])
    for name, expected in sources.items():
        assert sha(Path(name)) == expected, name
    source_root = args.source_root.resolve()
    assert source_root.is_relative_to(ROOT)
    for filename in ("checkpoint.odb", "checkpoint.def", "native-inventory.json", "master-OBS-signature.json", "via-definitions.json"):
        assert (source_root / filename).is_file(), filename
        sources[str(source_root / filename)] = sha(source_root / filename)
    admitted_control = None if args.control else control_admission(
        args, admitted_adapter["adapter_sha256"], sha(source_root / "checkpoint.odb"), manifest["image_id"])
    if admitted_control:
        for filename in ("report.json", "adjudication.json", "stage-plan.json", "input.odb",
                         "libpinwheel_drt_preservation.so", "control-wire-proof.json"):
            path = Path(admitted_control["root"]) / filename
            sources[str(path)] = sha(path)
    # Retain the exact host implementation used by this job. Later maintained
    # helper repairs must not invalidate historical job input custody.
    code = out / "host-code"
    code.mkdir()
    audit_origin = ROOT / "build/physical/tt-p2-drt-postroute-tools-03/audit.py"
    origins = [Path(__file__).resolve(), Path(drc.__file__).resolve(), Path(runner.__file__).resolve(), audit_origin]
    custody = {}
    for origin in origins:
        target = code / origin.name
        shutil.copyfile(origin, target)
        assert sha(origin) == sha(target)
        custody[str(origin)] = {"retained_path": str(target), "sha256": sha(target)}
    write(out / "host-code-custody.json", custody)
    for filename in ("native_inventory.py", "native-script-hashes.json", "load.tcl", "coordinator.py", "baseline-env.tcl", "corner-env.tcl", "capability-admission.json", "core.sdc", "input.guide"):
        shutil.copyfile(ORIGINAL / filename, out / filename)
    shutil.copytree(ORIGINAL / "lib", out / "lib")
    shutil.copyfile(source_root / "checkpoint.odb", out / "input.odb")
    shutil.copyfile(source_root / "native-inventory.json", out / "source-inventory.json")
    shutil.copyfile(args.adapter, out / "libpinwheel_drt_preservation.so")
    shutil.copyfile(args.adapter_build_receipt, out / "adapter-build-receipt.json")
    shutil.copyfile(args.adapter_fixture_receipt, out / "adapter-fixture-receipt.json")
    write(out / "adapter-admission.json", admitted_adapter)
    if admitted_control:
        write(out / "control-admission.json", admitted_control)
    (out / "native.py").write_text(native_program(args.end_iter, args.control, args.snapshots))
    # This is a conservative absolute upper bound; the owned runner publishes
    # the tighter actual native timeout after input recustody and launch.
    stop = min(stage_started_epoch + min(5400, allowed + 60), native_deadline)
    write(out / "runtime-bounds.json", {"started_epoch": time.time(), "hard_end_epoch": manifest["hard_stop_epoch"], "native_stop_epoch": stop, "native_end_iter": args.end_iter, "maximum_actual_search_repair_passes": args.end_iter + 1})
    write(out / "stage-plan.json", {"schema": "pinwheel-routing-stage-plan-v1", "control": args.control, "end_iter": args.end_iter, "source_root": str(source_root), "source_odb_sha256": sha(out / "input.odb"), "source_guides_sha256": sha(out / "input.guide"), "adapter_sha256": sha(out / "libpinwheel_drt_preservation.so"), "snapshots_requested": args.snapshots, "restart_is_not_restoration_of_transient_router_state": True})
    write(out / "phase-inputs.json", {str(Path("/work/diagnostic") / f.relative_to(out)): sha(f) for f in out.rglob("*") if f.is_file()})
    for f in out.rglob("*"):
        if f.is_file():
            sources[str(f.resolve())] = sha(f)
    for f in (manifest_path, args.adapter.resolve(), args.adapter_build_receipt.resolve(), args.adapter_build_job_receipt.resolve(), args.adapter_fixture_receipt.resolve(), args.adapter_fixture_job_receipt.resolve()):
        sources[str(f)] = sha(f)
    remaining_stage = min(5400, allowed + 60) - (time.monotonic() - stage_started_mono)
    assert remaining_stage >= 105, "Staging exhausted the all-in native/closeout budget"
    spec = JobSpec(output_dir=out, heavy_lock_path=campaign / "heavy.lock", image_id=manifest["image_id"], command=["python3", "-B", "/work/diagnostic/coordinator.py"], campaign_id=CAMPAIGN_ID, hard_end_epoch=native_deadline, input_sha256=sources, native_seconds=min(allowed, remaining_stage - 45), max_job_seconds=remaining_stage, closeout_reserve_seconds=45, minimum_native_seconds=60, cpus=4, memory="6g", readonly_mounts=[(ROOT / "build/physical/pdk", "/work/pdk")], environment={"PYTHONPATH": "/work/diagnostic", "PW_DRT_PRESERVATION_AUDIT": "/work/diagnostic/import-preservation.json"}, scope="Routing-only campaign stage; frozen RTL/ABI/cells/placement/SRAM/PG/clock topology/SDC/technology. Importer repair must precede checks; physical acceptance is separate.")
    receipt = run_owned_job(spec)
    log = (out / "native.log").read_text() if (out / "native.log").exists() else ""
    report = out / "drt/violations.rpt"
    observations = parse_native_log(log, report.read_text() if report.exists() else None, category_limit=10000, producer_status=receipt["status"])
    write(out / "native-observations.json", observations)
    scope = None
    audit_path = code / "audit.py"
    try:
        # Retain the actual new receipt; the read-only audit accepts its schema.
        loader = importlib.util.spec_from_file_location("pinwheel_scope_audit", audit_path)
        module = importlib.util.module_from_spec(loader)
        loader.loader.exec_module(module)
        scope = module.audit(out / "report.json")
        write(out / "independent-scope-audit.json", scope)
    except Exception as error:
        write(out / "independent-scope-audit-error.json", {"error": repr(error), "producer_status_retained": receipt["status"]})
    wire_proof = read(out / "control-wire-proof.json") if (out / "control-wire-proof.json").exists() else None
    importer = read(out / "import-preservation.json") if (out / "import-preservation.json").exists() else None
    complete = (observations["latest_native_route_completed"]
                and observations["completed_native_final_table"] is not None
                and isinstance(observations["completed_native_final_table"]["iteration"], int)
                and bool(observations["iteration_starts"]))
    importer_ok = bool(importer and importer.get("status") == "passed"
                       and importer.get("importer_variant") == "patched"
                       and importer.get("before_PA_GC_TA_DR") is True
                       and importer.get("audit_does_not_modify_imported_state") is True
                       and importer.get("geometry_and_per_object_path_rule_multisets_exact") is True)
    gate = (receipt["status"] == "passed" and complete and scope is not None
            and scope["status"] == "scope_verified" and importer_ok
            and not observations["native_modified_mapped_pin_checker_failure_lines"]
            and not observations["native_error_lines"]
            and all(v["iteration"] <= args.end_iter for v in observations["iteration_starts"]))
    if args.control:
        gate = (gate and wire_proof is not None and wire_proof.get("status") == "passed"
                and observations["completed_native_final_count"] > 0
                and [v["iteration"] for v in observations["iteration_starts"]] == [0])
    else:
        # The native scheduler may stop early after clearing every marker.
        # A positive ledger must reach the requested final stage. A completed
        # earlier DRC stage is not the result of a longer requested experiment.
        gate = (gate and observations["completed_native_final_table"]["iteration"] >= 3
                and (observations["completed_native_final_table"]["iteration"] == args.end_iter
                     or observations["completed_native_final_count"] == 0))
    adjudication = {"schema": "pinwheel-routing-stage-adjudication-v1", "producer_status_retained": receipt["status"], "stage_execution_and_scope_gate_passed": bool(gate), "control": args.control, "requested_end_iteration": args.end_iter, "completed_native_end_iteration": observations["completed_native_final_table"]["iteration"] if observations["completed_native_final_table"] else None, "control_wire_proof": wire_proof, "import_preservation_audit_present": importer is not None, "scope_status": scope["status"] if scope else None, "completed_native_final_count": observations["completed_native_final_count"], "completed_native_type_counts": observations["completed_native_type_counts"], "all_terminal_physical_connectivity_proven": False, "physical_acceptance_claim": False, "utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
    write(out / "adjudication.json", adjudication)
    print(json.dumps(adjudication, indent=2), flush=True)
    return 0 if gate else 1


if __name__ == "__main__":
    raise SystemExit(main())
