#!/usr/bin/env python3
"""Recover typed metrics from immutable native state files; no CAD or historical edits."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def recover(root):
    root = Path(root).resolve()
    report = json.loads((root / 'report.json').read_text())
    measurement = json.loads((root / 'measurement.json').read_text())
    request = json.loads((root / 'prepared.json').read_text())
    assert report['status'] == 'passed' and report['inputs_unchanged'] is True
    assert report['container_termination']['status'] == 'absent'
    assert report['within_absolute_and_job_deadlines'] is True
    for rel, expected in report['artifact_sha256'].items():
        assert sha(root / rel) == expected, 'Changed producer artifact: ' + rel
    assert measurement['status'] == 'measured' and measurement['phase'] == 'rcx-sta'
    assert measurement['export_scope']['status'] == 'passed'
    assert measurement['source_database_sha256'] == sha(root / 'input/checkpoint.odb')
    corners = request['expected_corners']
    assert len(corners) == len(set(corners)) == 3
    result = {'schema': 'pinwheel-native-state-metrics-recovery-v4', 'status': 'recovered_native_measurements',
        'producer_report_sha256': sha(root / 'report.json'), 'producer_measurement_sha256': sha(root / 'measurement.json'),
        'recovery_helper_sha256': sha(__file__), 'native_extraction_or_STA_rerun': False,
        'historical_files_edited': False, 'producer_artifact_count_verified': len(report['artifact_sha256']),
        'all_copied_native_artifacts_hash_bound': True, 'corners': {},
        'RC_model': measurement['RC_model'], 'FAST_qualification': request['FAST_qualification'],
        'serialization_defect': 'Native Metrics wrapper became a string in v3 measurement summary; original native typed state_out metrics retained and used here without parsing that string.',
        'physical_acceptance_claim': False, 'SPEF_is_physical_connectivity_proof': False,
        'boundary': 'One nominal RC model with three Liberty corners, FAST hybrid; no zero-DRC, timing-closure, internal SRAM, full LVS, antenna or official precheck acceptance.'}
    sources = {str(root / name): sha(root / name) for name in ['report.json', 'measurement.json', 'prepared.json', 'SPEF-coverage.json']}
    sys.path.insert(0, str(root))
    from audits import annotation_audit, audit_spef
    coverage_file = json.loads((root / 'SPEF-coverage.json').read_text())
    assert coverage_file['status'] == 'passed'
    inventory = json.loads((root / 'input/inventory.json').read_text())
    for model, native in measurement['SPEF'].items():
        relative = Path(native).relative_to('/work/diagnostic')
        path = root / relative
        coverage = json.loads(json.dumps(audit_spef(path.read_text(), inventory)))
        assert coverage == measurement['SPEF_coverage'][model] == coverage_file
        sources[str(path)] = sha(path)
    result['SPEF_coverage'] = coverage_file
    for corner in corners:
        path = root / 'sta' / corner / 'state_out.json'
        relative = str(path.relative_to(root))
        assert relative in report['artifact_sha256']
        state = json.loads(path.read_text())
        metrics = state['metrics']
        assert isinstance(metrics, dict) and metrics
        assert all('__corner:' not in key or key.endswith('__corner:' + corner) for key in metrics)
        keys = ['timing__setup__ws', 'timing__hold__ws', 'timing__setup__tns', 'timing__hold__tns',
            'timing__setup_vio__count', 'timing__hold_vio__count', 'design__max_slew_violation__count',
            'design__max_cap_violation__count', 'design__max_fanout_violation__count']
        summary = {}
        for key in keys:
            value = metrics[key + '__corner:' + corner]
            assert isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value)
            assert metrics[key] == value
            if key.endswith('__count'):
                assert isinstance(value, int) and value >= 0
            summary[key] = value
        captured = measurement['corner_results'][corner]
        check = root / Path(captured['checks_report']).relative_to('/work/diagnostic')
        assert sha(check) == captured['checks_sha256']
        assert annotation_audit(check.read_text(), inventory) == captured['annotation']
        assert captured['annotation']['status'] == 'passed'
        clock = root / Path(captured['clock_report']).relative_to('/work/diagnostic')
        assert sha(clock) == captured['clock_report_sha256']
        assert captured['single_20ns_propagated_clock_verified'] is True
        assert 'sta/' + corner in measurement['completed_stages']
        for artifact in [path, check, clock]:
            sources[str(artifact)] = sha(artifact)
        result['corners'][corner] = {'metrics': metrics, 'summary_native_ns_and_counts': summary,
            'state_out_sha256': sha(path), 'annotation': captured['annotation'],
            'single_20ns_propagated_clock_verified': True,
            'Liberty_temperature_qualification': captured['Liberty_temperature_qualification']}
    result['source_sha256'] = sources
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    assert not args.out.exists(), 'Immutable NEW recovery destination required'
    result = recover(args.run)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, allow_nan=False) + '\n')
    print(json.dumps({'status': result['status'], 'out': str(args.out.resolve()), 'sha256': sha(args.out)}))

if __name__ == '__main__': main()
