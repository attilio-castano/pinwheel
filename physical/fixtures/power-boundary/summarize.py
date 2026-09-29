"""Read-only evidence audit; write a new sensitivity report, never acceptance.

Usage: python3 -B physical/fixtures/power-boundary/summarize.py STUDY OUTPUT
"""
import hashlib
import json
from pathlib import Path
import re
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def coverage(text):
    annotated = re.search(r'^vcd\s+(\d+)$', text, re.M)
    missing = re.search(r'^unannotated\s+(\d+)$', text, re.M)
    require(annotated and int(annotated[1]) == 38497 and missing and int(missing[1]) == 0,
            'Incomplete activity annotation')
    return int(annotated[1])


def sources(lines, csv_text):
    # For the declared 1 um contacts, each CSV center must resolve to exactly
    # that top-metal node. This refuses the solver's silent nearest-node snap.
    expected = set()
    for line in csv_text.splitlines():
        x, y, size, voltage = map(float, line.split(','))
        require(size == 1, 'Unexpected contact size')
        expected.add((f'Node_TopMetal1_{round(x*1000)}_{round(y*1000)}', voltage))
    actual = {(s.split()[1], float(s.split()[4])) for s in lines}
    require(len(lines) == len(actual) == len(expected) == 4 and actual == expected,
            'Source locations do not match the declared contacts')
    return len(actual)


def build(base):
    req = json.loads((base / 'request.json').read_text())
    inputs = dict(req['inputs_sha256'])
    artifacts = {}
    runs = []
    for path in sorted(base.glob('*-receipt.json')):
        r = json.loads(path.read_text())
        require(r['status'] in ['failed', 'completed'] and r['sources_unchanged'], 'Unsettled run')
        require(r.get('container_state', 'absent') == 'absent' and r['full_flow_attempts'] == 0, 'Resource boundary')
        for p, h in r['inputs_sha256'].items():
            require(p not in inputs or inputs[p] == h, 'Conflicting input identities')
            inputs[p] = h
        for p, h in r['artifacts_sha256'].items():
            artifacts[str(base / p)] = h
        runs.append(dict(case=path.stem.removesuffix('-receipt'), status=r['status'], cad_seconds=r['cad_seconds']))
    for p, h in {**inputs, **artifacts}.items():
        require(sha(p) == h, 'Changed evidence: ' + p)
    used = round(sum(r['cad_seconds'] for r in runs), 3)
    require(used <= req['limits']['continuation_cad_seconds'], 'Continuation budget')
    total = round(req['prior_campaign_cad_seconds'] + used, 3)
    require(total <= req['limits']['campaign_cad_seconds'], 'Campaign budget')
    result = dict(schema=1, study='power-boundary-01', qualification=False,
                  A_accepted=False, B_admitted=False, complete_design_iteration=False,
                  remaining_blockers=['sram_qualification', 'timing_conditions', 'package_power'],
                  continuation_cad_seconds=used, campaign_cad_seconds=total,
                  full_flow_attempts_added=0, inputs_verified=len(inputs), artifacts_verified=len(artifacts), runs=runs)
    rows = []
    cases = ['baseline-03', 'contacts-ideal-01', 'contacts-r1-01', 'contacts-r10-01',
             'activity-idle-02', 'activity-replacement-02', 'activity-execution-02', 'combined-01']
    for name in cases:
        case = base / name
        spec = json.loads((case / 'case.json').read_text())
        p = json.loads((case / 'output/power.json').read_text())
        metrics = json.loads((case / 'output/metrics.json').read_text())
        row = dict(case=name, power_mw=p['Total']['total'] * 1000,
                   macro_power_mw=p['Macro']['total'] * 1000,
                   resistance_ohm_per_source_node=spec['external_resistance_ohm_per_node'])
        if spec.get('vcd'):
            row['annotated_signal_pins'] = coverage((case / 'output/activity.rpt').read_text())
        else:
            row['activity'] = 'default vectorless'
        drops = []
        for rail in ['VPWR', 'VGND']:
            lines = json.loads((case / 'output' / f'{rail}-sources.json').read_text())
            if spec.get('sources'):
                row[rail + '_source_nodes'] = sources(lines, (case / f'{rail}.csv').read_text())
            else:
                row[rail + '_source_nodes'] = len(lines)
            value = metrics[f'design_powergrid__drop__worst__net:{rail}__corner:nom_typ_1p20V_25C']
            drops.append(value)
            row[rail + '_worst_drop_mv'] = value * 1000
        row['conservative_rail_loss_mv'] = sum(drops) * 1000
        row['conservative_local_differential_v'] = 1.2 - sum(drops)
        rows.append(row)
    result['measurements'] = rows
    baseline = json.loads((Path(req['finalization_root']) / 'finalize-01/output/flow/05-openroad-irdropreport/or_metrics_out.json').read_text())
    fresh = json.loads((base / 'baseline-03/output/metrics.json').read_text())
    for rail in ['VPWR', 'VGND']:
        key = f'design_powergrid__drop__worst__net:{rail}__corner:nom_typ_1p20V_25C'
        require(baseline[key] == fresh[key], 'Retained baseline mismatch')
    result['baseline_worst_drops_exactly_reproduced'] = True
    # Rejected measurements remain part of the cost and evidence ledger.
    refused = []
    for name in ['activity-idle-01', 'activity-replacement-01', 'activity-execution-01']:
        try:
            coverage((base / name / 'output/activity.rpt').read_text())
        except ValueError as exc:
            refused.append(dict(case=name, reason=str(exc)))
        else:
            raise ValueError('Broken scope negative control unexpectedly admitted')
    result['rejected_activity_measurements'] = refused
    wave = json.loads((base / 'traces-03/waveform-audit.json').read_text())
    unknown = json.loads((base / 'traces-03/unknown-bit-audit.json').read_text())
    for name in ['idle', 'replacement', 'execution']:
        require(unknown[name]['connected_unknown_bits'] == 0, 'Connected unknown waveform bits')
        with (base / 'traces-03/output' / f'{name}.vcd').open() as f:
            prefix = f.read(1024)
        require(re.search(r'\$timescale\s+1ps\s+\$end', prefix), 'Unexpected VCD timescale')
        require(wave[name]['duration_ns'] > 0, 'Empty waveform')
    result['waveform_windows'] = {n: {k: v for k, v in w.items() if k != 'unknown_names'} for n, w in wave.items()}
    result['connected_unknown_waveform_bits'] = 0
    result['scope'] = 'Static nominal-grid sensitivity; finite zero-delay functional activity. No supply tolerance, package/transient model, universal activity bound or physical qualification.'
    return result


if __name__ == '__main__':
    base, target = map(Path, sys.argv[1:])
    require(not target.exists(), 'Preserve prior report')
    result = build(base)
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ['runs', 'measurements', 'waveform_windows']}, indent=2))
