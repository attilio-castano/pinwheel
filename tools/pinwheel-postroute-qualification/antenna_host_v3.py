#!/usr/bin/env python3
"""Host-only antenna staging for an already admitted routed prepared.json.

Only an explicit --run on the copied staged helper launches root-owned CAD.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys

from audits import consumed_nets, sha, write
from antenna_results_v3 import parse_native, require

HERE = Path(__file__).resolve().parent
NATIVE_SHA256 = {
    'antenna_native_v2.py': 'a5c61003cfa173ca04c3d48ab6a28fef468951af8097f2de8cafa9d632fde588',
    'export_native.py': 'd1d082571a11709588d4d1ca18e0c8687d37853ff8b5db8667586771e4ba9543',
    'native_inventory.py': '27aad492757e79864d79e4e17d1a602a6da051000a343f9e95af3271acb53ada',
    'audits.py': '21af6fbe537fbd39a335e254bf40f4b78bcbf5c2449dd69a54a4f443b6c610c9',
}
NEW_HELPERS = ('antenna_host_v3.py', 'antenna_coordinator_v3.py', 'antenna_results_v3.py')
AFTER_FILES = {'checkpoint.odb': 'checkpoint.odb', 'checkpoint.def': 'checkpoint.def',
    'inventory.json': 'native-inventory.json', 'master-OBS.json': 'master-OBS-signature.json',
    'vias.json': 'via-definitions.json'}


def load(path):
    return json.loads(Path(path).read_text())


def merge(target, incoming):
    for path, digest in incoming.items():
        require(path not in target or target[path] == digest, 'Conflicting source identity: ' + path)
        target[path] = digest


def validate_campaign(request):
    campaign = load(request['campaign_path'])
    require(sha(request['campaign_path']) == request['campaign_sha256']
        and request['image_id'] == campaign['image_id'] and bool(request['campaign_id'])
        and request['hard_stop_epoch'] == campaign['hard_stop_epoch']
        and request['native_work_stop_epoch'] == campaign['hard_stop_epoch'] - campaign['budgets_seconds']['closeout']
        and campaign['single_heavy_CAD_process'] is True
        and campaign['native_cpus'] == 4 and campaign['native_memory'] == '6g', 'Campaign identity/absolute native stop differs')
    return campaign


def completed_producer(root):
    root = Path(root).resolve()
    receipt = load(root / 'report.json')
    require(receipt['status'] == 'passed' and receipt['exit_code'] == 0
        and receipt['inputs_unchanged'] is True and receipt['container_termination']['status'] == 'absent'
        and receipt['within_absolute_and_job_deadlines'] is True and not receipt['controller_must_stop'],
        'Producer is not completed, owner-absent and within custody/deadlines')
    bound = dict(receipt['input_sha256'])
    merge(bound, {str(root / path): digest for path, digest in receipt['artifact_sha256'].items()})
    bound[str(root / 'report.json')] = sha(root / 'report.json')
    for path, digest in bound.items():
        require(sha(path) == digest, 'Producer input/artifact changed: ' + path)
    return receipt, bound


def validate_prepared(prepared_path):
    prepared_path = Path(prepared_path).resolve()
    package, request = prepared_path.parent, load(prepared_path)
    require(request['schema'] == 'pinwheel-isolated-postroute-qualification-v1', 'Unsupported preparation contract')
    for relative, digest in request['staged_sha256'].items():
        require(sha(package / relative) == digest, 'Prepared input changed: ' + relative)
    for name, digest in NATIVE_SHA256.items():
        require(request['staged_sha256'].get(name) == digest, 'Native checker/export helper requires separate qualification: ' + name)
    sources = dict(request['source_sha256'])
    sources[str(prepared_path)] = sha(prepared_path)
    for path, digest in sources.items(): require(sha(path) == digest, 'Bound prepared source changed: ' + path)
    admission = request['route_admission']
    require(admission['producer_and_scope_admitted'] is True, 'No actual routed source admission')
    route_report, adjudication = Path(admission['route_receipt']), Path(admission['adjudication'])
    require(sha(route_report) == admission['route_receipt_sha256'] == sources[str(route_report)]
            and sha(adjudication) == admission['adjudication_sha256'] == sources[str(adjudication)], 'Changed route source gate')
    receipt, producer_sources = completed_producer(route_report.parent)
    require(receipt['image_id'] == request['image_id'] and receipt['campaign_id'] == request['campaign_id']
            and load(adjudication)['stage_execution_and_scope_gate_passed'] is True,
            'Actual route execution/scope gate failed')
    after = Path(admission['after_root'])
    require(after.is_relative_to(route_report.parent), 'Route after/source producer mismatch')
    for staged_name, source_name in AFTER_FILES.items():
        path = after / source_name
        require(sha(path) == sha(package / 'input' / staged_name)
                == receipt['artifact_sha256'][str(path.relative_to(route_report.parent))], 'Mixed/nonfinal routed source: ' + staged_name)
    merge(sources, producer_sources)
    return request, sources


def stage(prepared_path, out, reference=None):
    """No native execution; reject invalid/nonexistent sources before mkdir."""
    prepared_path, out = Path(prepared_path).resolve(), Path(out).resolve()
    require(not out.exists(), 'Immutable antenna stage already exists')
    request, sources = validate_prepared(prepared_path)
    package = prepared_path.parent
    inventory = load(package / 'input/inventory.json')
    consumed = consumed_nets(inventory)
    contacts = sum(direction == 'INPUT' and net in consumed for instance in inventory['instances'].values()
                   for pin, net, direction in instance['terminals'])
    require(contacts > 0, 'Empty source input/gate denominator')
    expected = {'schema': 'pinwheel-admitted-source-antenna-expected-v3',
        'source_ODB_sha256': sha(package / 'input/checkpoint.odb'),
        'consumed_net_count': len(consumed), 'INPUT_contact_count': contacts,
        'same_source_reference': None}
    if reference is not None:
        reference = Path(reference).resolve()
        reference_receipt, reference_sources = completed_producer(reference)
        require(reference_receipt['image_id'] == request['image_id']
            and reference_receipt['campaign_id'] == request['campaign_id'], 'Reference runtime/campaign differs')
        for name, digest in NATIVE_SHA256.items():
            require(sha(reference / name) == digest
                == reference_receipt['input_sha256'].get(str(reference / name)), 'Reference native body identity differs: ' + name)
        measured = load(reference / 'measurement.json')
        require(measured['status'] == 'measured' and measured['checker_called'] is True
            and measured['full_scope_and_DEF_TAPER_exact'] is True
            and measured['source_database_sha256'] == expected['source_ODB_sha256']
            == sha(reference / 'input/checkpoint.odb'), 'Reference is not a completed same-source antenna result')
        parsed = parse_native((reference / 'antenna-native.log').read_text(), load(reference / 'antenna-native-metrics.json'),
            measured['coverage'], load(reference / 'input/inventory.json'))
        require(measured['antenna_net_violation_count'] == parsed['native_net_violation_count']
            and measured['antenna_pin_violation_count'] == parsed['native_pin_violation_count']
            and measured['native_report_reconciliation']['semantic_violation_signature_sha256']
                == parsed['semantic_violation_signature_sha256'], 'Reference measurement/report disagrees')
        for key in ('native_net_violation_count', 'native_pin_violation_count', 'semantic_violation_signature_sha256'):
            expected[key] = parsed[key]
        expected['same_source_reference'] = str(reference)
        merge(sources, reference_sources)
    campaign = validate_campaign(request)
    for path, digest in {**campaign['protected_sources_sha256'], **campaign['reference_files_sha256']}.items():
        require(sources.get(path) == digest and sha(path) == digest, 'Protected campaign source missing/changed')
    for name in NEW_HELPERS:
        if name in request['staged_sha256']:
            require(sha(HERE / name) == request['staged_sha256'][name], 'New helper would overwrite a prepared hash: ' + name)
    # Every validation above is read-only. Copy only explicitly frozen inputs,
    # never a previous job's outputs or transient state.
    out.mkdir(parents=True)
    for relative in request['staged_sha256']:
        target = out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(package / relative, target)
    shutil.copyfile(prepared_path, out / 'prepared.json')
    for name in NEW_HELPERS:
        if not (out / name).exists(): shutil.copyfile(HERE / name, out / name)
    write(out / 'antenna-expected-v3.json', expected)
    write(out / 'antenna-plan-v3.json', {'schema': 'pinwheel-reusable-check-only-antenna-stage-v3',
        'prepared_origin': str(prepared_path), 'prepared_origin_sha256': sha(prepared_path),
        'source_sha256': sources, 'native_seconds': 300, 'all_in_seconds': 360,
        'native_bodies_sha256': NATIVE_SHA256, 'helper_origins_sha256': {str(HERE / n): sha(HERE / n) for n in NEW_HELPERS},
        'all_original_prepared_hashes_preserved': True,
        'root_independent_whole_custody_and_physical_scope_gate_remains_mandatory': True,
        'generic_reference_free_branch_native_qualification': 'First actual execution for each new source remains required; prior C14 capsule qualified the reconciliation mechanism.',
        'antenna_pass_qualified': False, 'physical_acceptance_claim': False})
    argv = ['python3', '-B', str(out / 'antenna_host_v3.py'), '--staged-root', str(out), '--run']
    write(out / 'antenna-ready-v3.json', {'status': 'host_staged_only_no_CAD', 'root_only_argv': argv,
        'native_seconds': 300, 'all_in_seconds': 360, 'source_ODB_sha256': expected['source_ODB_sha256'],
        'same_source_reference': expected['same_source_reference'], 'antenna_pass_qualified': False,
        'physical_acceptance_claim': False})
    write(out / 'antenna-staged-inputs.json', {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*')) if p.is_file()})
    return out


def job_spec(out):
    out = Path(out).resolve()
    request, plan, inputs = load(out / 'prepared.json'), load(out / 'antenna-plan-v3.json'), load(out / 'antenna-staged-inputs.json')
    require(plan['schema'] == 'pinwheel-reusable-check-only-antenna-stage-v3'
            and plan['native_seconds'] == 300 and plan['all_in_seconds'] == 360, 'Unknown antenna policy/bounds')
    require(sha(plan['prepared_origin']) == plan['prepared_origin_sha256'] == sha(out / 'prepared.json'), 'Changed prepared origin')
    sources = dict(plan['source_sha256'])
    for relative, digest in inputs.items():
        require(sha(out / relative) == digest, 'Changed staged antenna input: ' + relative)
        sources[str(out / relative)] = digest
    for relative, digest in request['staged_sha256'].items():
        require(inputs.get(relative) == digest, 'Original prepared hash not preserved: ' + relative)
    for name, digest in NATIVE_SHA256.items(): require(inputs[name] == digest, 'Native body changed')
    sources[str(out / 'antenna-staged-inputs.json')] = sha(out / 'antenna-staged-inputs.json')
    validate_campaign(request)
    for path, digest in sources.items(): require(sha(path) == digest, 'Changed antenna source: ' + path)
    spec = importlib.util.spec_from_file_location('immutable_antenna_v3_runner', out / 'campaign_runner.py')
    runner = importlib.util.module_from_spec(spec); sys.modules[spec.name] = runner; spec.loader.exec_module(runner)
    return runner, runner.JobSpec(output_dir=out, heavy_lock_path=Path(request['heavy_lock']), image_id=request['image_id'],
        command=['python3', '-B', '/work/diagnostic/antenna_coordinator_v3.py'], campaign_id=request['campaign_id'],
        hard_end_epoch=min(request['hard_stop_epoch'], request['native_work_stop_epoch'] + 60),
        input_sha256=sources, native_seconds=300, max_job_seconds=360, minimum_native_seconds=60,
        closeout_reserve_seconds=60, cpus=4, memory='6g', readonly_mounts=[(Path(request['PDK_root']), '/work/pdk')],
        environment={'PYTHONPATH': '/work/diagnostic'},
        scope='Actual detailed-wire check_antennas only; preserve cells/placement/SRAM/PG/clocks/routes/TAPER/rules; no repair or guide fallback; native diagnostic separate from acceptance')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepared', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--reference', type=Path, help='Optional completed same-ODB antenna producer; different checkpoint is rejected')
    parser.add_argument('--staged-root', type=Path)
    parser.add_argument('--run', action='store_true', help='Root-owned execution from the copied immutable helper only')
    args = parser.parse_args()
    if args.staged_root:
        require(args.prepared is None and args.out is None and args.reference is None, 'Cannot restage an existing capsule')
        out = args.staged_root.resolve()
        require(Path(__file__).resolve() == out / 'antenna_host_v3.py', 'Use the copied staged helper')
    else:
        require(args.prepared is not None and args.out is not None and not args.run, 'Host staging never launches native CAD')
        out = stage(args.prepared, args.out, args.reference)
    runner, spec = job_spec(out)
    if args.run:
        result = runner.run_owned_job(spec)
        print(json.dumps({'status': result['status'], 'receipt': str(out / 'report.json'), 'antenna_pass_qualified': False}))
        if result['status'] != 'passed': raise SystemExit(1)
    else:
        print(json.dumps({'status': 'host_staged_or_validated_no_CAD', 'ready': str(out / 'antenna-ready-v3.json'),
            'input_manifest_sha256': sha(out / 'antenna-staged-inputs.json'), 'native_seconds': 300, 'all_in_seconds': 360}))


if __name__ == '__main__': main()
