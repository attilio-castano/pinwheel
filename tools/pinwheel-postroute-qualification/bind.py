#!/usr/bin/env python3
"""Bind an accepted completed routing producer to an isolated qualification input."""
import argparse
import json
from pathlib import Path

from audits import sha, write

FILES = ['checkpoint.odb', 'checkpoint.def', 'native-inventory.json',
         'master-OBS-signature.json', 'via-definitions.json']


def admitted_sources(after, route_receipt, adjudication, core_config, sdc):
    after, route_receipt, adjudication, core_config, sdc = map(
        lambda p: Path(p).resolve(), (after, route_receipt, adjudication, core_config, sdc))
    receipt = json.loads(route_receipt.read_text())
    gate = json.loads(adjudication.read_text())
    assert receipt['status'] == 'passed' and receipt['inputs_unchanged'] is True
    assert receipt['container_termination']['status'] == 'absent'
    assert receipt['within_absolute_and_job_deadlines'] is True
    assert gate['stage_execution_and_scope_gate_passed'] is True
    assert after.is_relative_to(route_receipt.parent)
    for name in FILES:
        path = after / name
        relative = str(path.relative_to(route_receipt.parent))
        assert receipt['artifact_sha256'][relative] == sha(path), 'Unbound/changed native after artifact: ' + name
    files = [*(after / name for name in FILES), route_receipt, adjudication, core_config, sdc]
    return {'schema': 'pinwheel-explicit-routed-qualification-source-binding-v2',
        'source_sha256': {str(p): sha(p) for p in files},
        'route_admission': {'after_root': str(after), 'route_receipt': str(route_receipt),
            'adjudication': str(adjudication), 'route_receipt_sha256': sha(route_receipt),
            'adjudication_sha256': sha(adjudication),
            'producer_and_scope_admitted': True, 'physical_acceptance_claim': False},
        'boundary': 'Completed producer/source/scope admission only. Native DRC, extracted timing, LVS, GDS and official precheck are separate.'}


def verify_admission(bindings):
    admission = bindings['route_admission']
    assert admission['producer_and_scope_admitted'] is True
    paths = bindings['source_sha256']
    after = Path(admission['after_root'])
    receipt_path, gate_path = Path(admission['route_receipt']), Path(admission['adjudication'])
    assert paths[str(receipt_path)] == admission['route_receipt_sha256'] == sha(receipt_path)
    assert paths[str(gate_path)] == admission['adjudication_sha256'] == sha(gate_path)
    receipt = json.loads(receipt_path.read_text())
    gate = json.loads(gate_path.read_text())
    assert receipt['status'] == 'passed' and receipt['inputs_unchanged'] is True
    assert receipt['container_termination']['status'] == 'absent'
    assert receipt['within_absolute_and_job_deadlines'] is True
    assert gate['stage_execution_and_scope_gate_passed'] is True
    assert after.is_relative_to(receipt_path.parent)
    for name in FILES:
        path = after / name
        assert paths[str(path)] == sha(path) == receipt['artifact_sha256'][str(path.relative_to(receipt_path.parent))]
    return admission


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['after', 'route-receipt', 'adjudication', 'core-config', 'sdc', 'out']:
        p.add_argument('--' + name, type=Path, required=True)
    args = p.parse_args()
    assert not args.out.exists(), 'Immutable source binding output already exists'
    result = admitted_sources(args.after, args.route_receipt, args.adjudication, args.core_config, args.sdc)
    verify_admission(result)
    write(args.out, result)
    after = args.after.resolve()
    print(json.dumps({'status': 'source_and_scope_bound_only_no_CAD', 'bindings': str(args.out.resolve()),
        'bindings_sha256': sha(args.out), 'prepare_flags': ['--source-bindings', str(args.out.resolve()),
            '--odb', str(after / FILES[0]), '--def', str(after / FILES[1]),
            '--inventory', str(after / FILES[2]), '--master-obs', str(after / FILES[3]),
            '--via-definitions', str(after / FILES[4]), '--core-config', str(args.core_config.resolve()),
            '--sdc', str(args.sdc.resolve())]}))


if __name__ == '__main__':
    main()
