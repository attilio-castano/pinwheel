#!/usr/bin/env python3
"""Explicit bounded launch API; only the root campaign owner should invoke it."""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import sys

from audits import sha, write

PHASES = ('rcx-sta', 'streamout', 'lef-lvs', 'gds-lvs', 'drc')


def runner_module(package):
    path = Path(package) / 'campaign_runner.py'
    spec = importlib.util.spec_from_file_location('pinwheel_frozen_campaign_runner', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def fixture_admission(path, expected_sha, image_id):
    """Require independently reviewed native retained-macro sensitivity evidence."""
    assert path is not None and expected_sha is not None, 'Fixture semantic gate path and explicit SHA256 required'
    path = Path(path).resolve()
    assert sha(path) == expected_sha, 'Changed fixture semantic gate'
    gate = json.loads(path.read_text())
    assert gate['macro_connectivity_qualified'] is True
    assert gate['standardcell_sensitivity_qualified'] is True
    sources = dict(gate['source_sha256'])
    assert sources, 'Native gate evidence bindings required'
    for source, digest in sources.items():
        assert sha(source) == digest, 'Changed fixture semantic evidence: ' + source
    receipts = [Path(source) for source in sources if Path(source).name == 'report.json'
                and Path(source).parent.name == 'lvs-native-fixture-07']
    assert len(receipts) == 1, 'Exact fixture07 native producer receipt required'
    receipt_path = receipts[0]
    receipt = json.loads(receipt_path.read_text())
    assert receipt['status'] == 'passed' and receipt['inputs_unchanged'] is True
    assert receipt['container_termination']['status'] == 'absent'
    assert receipt['within_absolute_and_job_deadlines'] is True and receipt['image_id'] == image_id
    for case in ['positive', 'removed-terminal', 'bridged-nets', 'macro-detached-signal', 'macro-bridged-signals', 'macro-detached-VSS']:
        for name in ['lvs.json', 'lvs.rpt', 'native.log', 'reference.v', 'run.lvs']:
            source = receipt_path.parent / 'controls' / case / name
            assert str(source) in sources and sha(source) == sources[str(source)]
            assert receipt['artifact_sha256'][str(source.relative_to(receipt_path.parent))] == sha(source)
    sources[str(path)] = expected_sha
    return sources


def build_spec(prepared_path, *, phase, output_dir, native_seconds, minimum_native_seconds=30, prior=None,
               fixture_semantic_gate=None, fixture_semantic_sha256=None):
    """Stage one fresh phase and return JobSpec; no CAD is launched by this API."""
    prepared_path = Path(prepared_path).resolve()
    package = prepared_path.parent
    request = json.loads(prepared_path.read_text())
    assert request['schema'] == 'pinwheel-isolated-postroute-qualification-v1'
    assert sha(__file__) == sha(package / 'run.py'), 'Host launcher differs from prepared immutable helper'
    assert sha(Path(__file__).with_name('audits.py')) == sha(package / 'audits.py'), 'Host audit helper differs from immutable package'
    assert phase in PHASES
    assert 0 < minimum_native_seconds <= native_seconds <= 5355
    sources = dict(request['source_sha256'])
    sources[str(prepared_path)] = sha(prepared_path)
    for relative, digest in request['staged_sha256'].items():
        path = package / relative
        assert sha(path) == digest, 'Changed prepared package: ' + relative
    campaign_path = Path(request['campaign_path'])
    assert sha(campaign_path) == request['campaign_sha256']
    campaign = json.loads(campaign_path.read_text())
    protected = dict(campaign['protected_sources_sha256'])
    protected.update(campaign['reference_files_sha256'])
    assert all(sources.get(path) == digest for path, digest in protected.items())
    assert request['hard_stop_epoch'] == campaign['hard_stop_epoch']
    assert request['image_id'] == campaign['image_id']
    assert request['native_work_stop_epoch'] == campaign['hard_stop_epoch'] - campaign['budgets_seconds']['closeout']
    for path, digest in sources.items():
        assert sha(path) == digest, 'Changed bound source: ' + path
    if request.get('PDK_overlay'):
        from prepare import validate_overlay
        assert validate_overlay(request['PDK_root'], request['PDK_overlay']['path']) == request['PDK_overlay']
    fixture_sources = {}
    if phase in ('lef-lvs', 'gds-lvs'):
        fixture_sources = fixture_admission(fixture_semantic_gate, fixture_semantic_sha256, request['image_id'])
        sources.update(fixture_sources)
    else:
        assert fixture_semantic_gate is None and fixture_semantic_sha256 is None
    output_dir = Path(output_dir).resolve()
    if output_dir.exists():
        raise FileExistsError('Immutable phase output already exists: ' + str(output_dir))
    shutil.copytree(package, output_dir)
    if fixture_sources:
        shutil.copyfile(fixture_semantic_gate, output_dir / 'fixture-semantic-gate.json')
    prior_views = {}
    if phase in ('lef-lvs', 'gds-lvs', 'drc'):
        if prior is None:
            raise ValueError('A completed same-source streamout phase is required')
        prior = Path(prior).resolve()
        receipt = json.loads((prior / 'report.json').read_text())
        measured = json.loads((prior / 'measurement.json').read_text())
        assert receipt['status'] == 'passed' and receipt['inputs_unchanged']
        assert receipt['container_termination']['status'] == 'absent'
        assert measured['phase'] == 'streamout' and measured['status'] == 'measured'
        assert measured['source_database_sha256'] == sha(output_dir / 'input/checkpoint.odb')
        gds = Path(measured['views']['gds'])
        assert str(gds).startswith('/work/diagnostic/')
        local = prior / gds.relative_to('/work/diagnostic')
        assert sha(local) == measured['view_sha256']['gds']
        (output_dir / 'prior').mkdir()
        shutil.copyfile(local, output_dir / 'prior/layout.gds')
        prior_views['gds'] = '/work/diagnostic/prior/layout.gds'
        sources[str(prior / 'report.json')] = sha(prior / 'report.json')
        sources[str(prior / 'measurement.json')] = sha(prior / 'measurement.json')
        sources[str(local)] = sha(local)
    write(output_dir / 'phase.json', {'phase': phase, 'prior_views': prior_views,
        'native_work_stop_epoch': request['native_work_stop_epoch'],
        'campaign_hard_stop_epoch': request['hard_stop_epoch'],
        'fixture_semantic_gate_sha256': fixture_semantic_sha256})
    for path in output_dir.rglob('*'):
        if path.is_file():
            sources[str(path)] = sha(path)
    JobSpec = runner_module(output_dir).JobSpec
    return JobSpec(output_dir=output_dir, heavy_lock_path=Path(request['heavy_lock']),
        image_id=request['image_id'], command=['python3', '-B', '/work/diagnostic/worker.py'],
        campaign_id=request['campaign_id'],
        hard_end_epoch=min(request['hard_stop_epoch'], request['native_work_stop_epoch'] + 45),
        input_sha256=sources, native_seconds=native_seconds,
        max_job_seconds=min(5400, native_seconds + 45), closeout_reserve_seconds=45,
        minimum_native_seconds=minimum_native_seconds, cpus=4, memory='6g',
        readonly_mounts=[(Path(request['PDK_root']), '/work/pdk')],
        environment={'PYTHONPATH': '/work/diagnostic'},
        scope='Frozen-route isolated qualification ' + phase + '; no fill, route, cell, placement, PG, RTL or ABI edits; no automatic physical acceptance')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--prepared', type=Path, required=True)
    p.add_argument('--phase', choices=PHASES, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--native-seconds', type=int, required=True)
    p.add_argument('--minimum-native-seconds', type=int, default=30)
    p.add_argument('--prior', type=Path)
    p.add_argument('--fixture-semantic-gate', type=Path)
    p.add_argument('--fixture-semantic-sha256')
    p.add_argument('--prepare-only', action='store_true', help='Stage JobSpec without launching Docker')
    args = p.parse_args()
    assert Path(__file__).resolve() == args.prepared.resolve().parent / 'run.py', \
        'Run the immutable prepared/run.py snapshot, not the live source helper'
    spec = build_spec(args.prepared, phase=args.phase, output_dir=args.out,
        native_seconds=args.native_seconds, minimum_native_seconds=args.minimum_native_seconds, prior=args.prior,
        fixture_semantic_gate=args.fixture_semantic_gate, fixture_semantic_sha256=args.fixture_semantic_sha256)
    if args.prepare_only:
        print(json.dumps({'status': 'staged_only_no_CAD', 'output': str(spec.output_dir),
            'command': list(spec.command), 'native_seconds': spec.native_seconds,
            'all_in_seconds': spec.max_job_seconds, 'hard_end_epoch': spec.hard_end_epoch,
            'input_count': len(spec.input_sha256)}))
        return
    result = runner_module(spec.output_dir).run_owned_job(spec)
    print(json.dumps({'status': result['status'], 'receipt': str(spec.output_dir / 'report.json'),
                      'physical_acceptance_claim': False}))
    if result['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
