"""Read-only claim and time boundaries for the October 22 8x4 campaign.

This module does not launch work, grant Root GO, or turn a resource receipt into
design acceptance. The resource supervisor can use job_window before launch and
must enforce its returned deadline while the job runs. All supervisor copies
must use shared_lease_paths with the campaign's one explicit workspace root.

The input claim packet has schema pinwheel.streaming-8x4-acceptance-input.v1,
candidate {allocation, semantic_state_bits, clock_period_ns, capacity,
source_artifact_sha256, template_sha256, final_odb_sha256}, and gates keyed by
GATES. An open gate is {status: not_run|incomplete|fail}. A pass must name its
scope, exact target_odb_sha256, complete: true, and an evidence list of regular
files with absolute path and sha256. Special pass fields are checked below.
Nominal timing and prephysical proofs may be retained separately as milestones;
they never substitute for final-target gates. Hash checking establishes custody,
not independent truth of a producer's engineering conclusions. Extraction-model
qualification is independent of the final ODB. It requires complete declared
reference/tolerance coverage below; a point pilot cannot substitute for it.
"""
import argparse
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import re


INPUT_SCHEMA = 'pinwheel.streaming-8x4-acceptance-input.v1'
OUTPUT_SCHEMA = 'pinwheel.streaming-8x4-acceptance-summary.v1'
SCHEDULE_KEYS = ('start', 'candidate_cutoff', 'rc_experiment_cutoff',
                 'heavy_cutoff', 'hard_deadline')
GATES = {
    'route': 'completed_detailed_route',
    'extraction_model': 'applicable_full_declared_cmos5l_extraction_model',
    'extracted_timing': 'qualified_extracted',
    'physical_drc': 'full_foundry_gds_drc',
    'lvs': 'transistor_top_comparison',
    'antenna': 'full_antenna_deck',
    'power': 'actual_physical_power_connectivity',
    'official_precheck': 'unchanged_applicable_official_precheck',
    'final_correspondence': 'all_actual_state_output_clock_packing',
    'final_wire': 'final_netlist_public_wire',
}
STATUSES = {'pass', 'fail', 'incomplete', 'not_run'}
HEAVY_KINDS = {'candidate_cad', 'fixed_cad', 'proof', 'rc_experiment', 'rc_validation'}
CAPACITY = dict(program_rows=64, program_word_bits=64, tx_queue_words=2, rx_queue_words=2)
MODEL_COVERAGE = {'resistance', 'ground_capacitance', 'coupling_capacitance',
                  'via_resistance', 'dielectric_interfaces', 'layer_coverage',
                  'width_spacing_range', 'consumer_units_and_semantics'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value):
    return type(value) is str and re.fullmatch('[0-9a-f]{64}', value) is not None


def timestamp(value):
    require(type(value) is str, 'Timestamp must be a timezone-qualified string')
    result = datetime.fromisoformat(value.replace('Z', '+00:00'))
    require(result.tzinfo is not None and result.utcoffset() is not None,
            'Timestamp requires timezone')
    return result.astimezone(timezone.utc)


def schedule_values(schedule):
    require(type(schedule) is dict and set(schedule) == set(SCHEDULE_KEYS),
            'Schedule must provide every explicit campaign boundary')
    values = {key: timestamp(schedule[key]) for key in SCHEDULE_KEYS}
    require(all(values[left] < values[right]
                for left, right in zip(SCHEDULE_KEYS, SCHEDULE_KEYS[1:])),
            'Campaign boundaries must be strictly increasing')
    require(values['hard_deadline'] - values['start'] <= timedelta(hours=12),
            'Campaign exceeds twelve-hour maximum')
    require(values['hard_deadline'] - values['heavy_cutoff'] >= timedelta(minutes=40),
            'Heavy cutoff must preserve at least forty minutes of closeout')
    return values


def shared_lease_paths(campaign_root):
    """Return the same lock/sentinel paths even from a copied producer runtime."""
    root = Path(campaign_root)
    require(root.is_absolute(), 'Campaign root must be explicit and absolute')
    root = root.resolve(strict=True)
    require(root.is_dir(), 'Campaign root is not a directory')
    base = root / 'build/streaming-tt-resources'
    return {'heavy_lock': str(base / 'heavy.lock'),
            'cleanup_sentinel': str(base / 'cleanup-unconfirmed.json')}


def job_window(kind, schedule, now, timeout_seconds, *, frozen_parent_sha256=None):
    """Bound actual execution, independently of earlier candidate admission."""
    values = schedule_values(schedule)
    now = timestamp(now)
    require(kind in HEAVY_KINDS | {'host_closeout'}, 'Unknown resource job kind')
    require(type(timeout_seconds) is int and 0 < timeout_seconds <= 12 * 3600,
            'Invalid requested wall-time allowance')
    require(now >= values['start'], 'Campaign has not started')
    if kind == 'candidate_cad':
        require(now < values['candidate_cutoff'], 'New physical candidate admission closed')
    if kind == 'rc_experiment':
        require(now < values['rc_experiment_cutoff'], 'New RC experiment admission closed')
    if kind in {'fixed_cad', 'rc_validation', 'proof'}:
        require(digest(frozen_parent_sha256), 'Fixed-target validation requires frozen parent SHA-256')
    else:
        require(frozen_parent_sha256 is None, 'New experiments cannot claim a frozen-validation parent')
    execution_end = {
        'candidate_cad': values['candidate_cutoff'],
        'rc_experiment': values['rc_experiment_cutoff'],
        'host_closeout': values['hard_deadline'],
    }.get(kind, values['heavy_cutoff'])
    seconds = min(timeout_seconds, (execution_end - now).total_seconds() - 20)
    require(seconds > 0, 'Execution cutoff reached; cleanup reserve is unavailable')
    return {'kind': kind, 'timeout_seconds': seconds,
            'execution_cutoff': execution_end.isoformat(),
            'cleanup_reserve_seconds': 20, 'root_go_required': True,
            'acceptance_claim': False}


def evidence_files(records):
    require(type(records) is list and records, 'Pass gate requires evidence files')
    seen = set()
    for record in records:
        require(type(record) is dict and set(record) == {'path', 'sha256'},
                'Evidence requires exactly path and sha256')
        path = Path(record['path'])
        require(path.is_absolute() and path.is_file() and not path.is_symlink(),
                'Evidence must be a regular absolute file')
        require(str(path) not in seen and digest(record['sha256']), 'Duplicate or invalid evidence identity')
        seen.add(str(path))
        with path.open('rb') as stream:
            actual = hashlib.file_digest(stream, 'sha256').hexdigest()
        require(actual == record['sha256'], 'Evidence bytes changed: ' + str(path))


def natural(value):
    return type(value) is int and value >= 0


def labels(value):
    require(type(value) is list and value and all(type(item) is str and item for item in value) and
            len(value) == len(set(value)), 'Expected unique nonempty declared labels')
    return set(value)


def model_qualification(record):
    for key in ('model_sha256', 'technology_lef_sha256', 'process_stack_sha256',
                'consumer_tool_sha256', 'qualification_report_sha256'):
        require(digest(record.get(key)), 'Extraction model lacks ' + key)
    require(record['qualification_report_sha256'] in {item['sha256'] for item in record['evidence']},
            'Extraction qualification report is not bound to evidence bytes')
    corners = labels(record.get('declared_corners'))
    definitions = record.get('corner_definitions')
    require(type(definitions) is dict and set(definitions) == corners and
            all(digest(value) for value in definitions.values()),
            'Extraction model lacks complete declared corner definitions')
    coverage = record.get('coverage')
    require(type(coverage) is dict and set(coverage) == MODEL_COVERAGE,
            'Point pilots do not cover the full declared extraction model')
    for name, item in coverage.items():
        require(type(item) is dict and item.get('coverage_complete') is True,
                'Extraction coverage incomplete: ' + name)
        require(labels(item.get('declared_cases')) == labels(item.get('executed_cases')),
                'Extraction model has missing reference cases: ' + name)
        require(digest(item.get('independent_reference_sha256')) and digest(item.get('protocol_sha256')),
                'Extraction reference/tolerance protocol is unidentified: ' + name)
        tolerance, measured = item.get('relative_tolerance'), item.get('max_relative_error')
        require(type(tolerance) in (int, float) and type(measured) in (int, float) and
                0 <= measured <= tolerance < float('inf'),
                'Extraction reference error exceeds predeclared tolerance: ' + name)
        require(item.get('protocol_predeclared') is True,
                'Extraction reference/tolerance protocol was not predeclared: ' + name)


def pass_gate(name, record, target):
    require(record.get('scope') == GATES[name], 'Wrong scope for ' + name)
    require(record.get('complete') is True, 'Pass gate is incomplete: ' + name)
    if name != 'extraction_model':
        require(digest(target) and record.get('target_odb_sha256') == target,
                'Pass gate does not bind the same final ODB: ' + name)
    evidence_files(record.get('evidence'))
    if name in {'route', 'physical_drc', 'antenna', 'power', 'official_precheck'}:
        require(type(record.get('violations')) is int and record['violations'] == 0,
                'Pass gate has missing/nonzero violations: ' + name)
    if name == 'extraction_model':
        model_qualification(record)
    elif name == 'route':
        require(record.get('connectivity_complete') is True, 'Route connectivity is incomplete')
    elif name == 'lvs':
        require(record.get('top_matched') is True and record.get('skipped_circuits') == 0 and
                type(record.get('skipped_circuits')) is int,
                'LVS top must match without skipped circuits')
    elif name == 'extracted_timing':
        require(digest(record.get('spef_sha256')) and digest(record.get('rc_model_sha256')) and
                digest(record.get('rc_qualification_sha256')),
                'Extracted timing requires SPEF/model/qualification identities')
        require(record.get('annotation_complete') is True, 'Incomplete parasitic annotation')
        corners = record.get('corners')
        require(type(corners) is list and corners, 'No declared extracted timing corners')
        labels = set()
        for corner in corners:
            label = corner.get('name')
            require(type(label) is str and label and label not in labels, 'Duplicate/unnamed timing corner')
            labels.add(label)
            require(corner.get('qualified_rc_corner') is True, 'Nominal RC is not a qualified extracted corner')
            for check in ('setup', 'hold', 'slew', 'capacitance', 'fanout'):
                count = corner.get(check + '_violations')
                require(type(count) is int and count == 0, 'Timing/electrical violation: ' + label + '/' + check)
        require(set(record.get('declared_corners', [])) == labels,
                'Declared timing corners do not match executed corner coverage')
    elif name == 'final_correspondence':
        require(record.get('semantic_state_bits') == 6039 and
                natural(record.get('actual_state_bits')) and record['actual_state_bits'] >= 6039 and
                record.get('all_actual_state_covered') is True and
                record.get('whole_axiom_audit_passed') is True and
                record.get('original_private_controls_rejected') is True,
                'Final correspondence lacks complete state/audit/private-control coverage')
    elif name == 'final_wire':
        require(record.get('declared_corpus_complete') is True and
                record.get('semantic_mutations_rejected') is True,
                'Final public-wire corpus/control coverage is incomplete')


def summarize(packet):
    require(type(packet) is dict and packet.get('schema') == INPUT_SCHEMA, 'Unknown acceptance packet schema')
    candidate = packet.get('candidate')
    require(type(candidate) is dict and candidate.get('allocation') == '8x4' and
            candidate.get('semantic_state_bits') == 6039 and candidate.get('clock_period_ns') == 20 and
            candidate.get('capacity') == CAPACITY and digest(candidate.get('source_artifact_sha256')) and
            digest(candidate.get('template_sha256')), 'Wrong/unbound candidate allocation/state/clock/capacity contract')
    gates = packet.get('gates')
    require(type(gates) is dict and set(gates) == set(GATES), 'Provide every final-target gate exactly once')
    target = candidate.get('final_odb_sha256')
    require(target is None or digest(target), 'Invalid final ODB identity')
    statuses = {}
    for name, record in gates.items():
        require(type(record) is dict and record.get('status') in STATUSES, 'Invalid gate status: ' + name)
        statuses[name] = record['status']
        if record['status'] == 'pass':
            pass_gate(name, record, target)
    if statuses['extracted_timing'] == 'pass':
        model, timing = gates['extraction_model'], gates['extracted_timing']
        require(model['status'] == 'pass' and timing['rc_model_sha256'] == model['model_sha256'] and
                timing['rc_qualification_sha256'] == model['qualification_report_sha256'] and
                set(timing['declared_corners']) == set(model['declared_corners']),
                'Extracted timing does not consume the qualified model/corners')
    ready = all(value == 'pass' for value in statuses.values())
    return {'schema': OUTPUT_SCHEMA, 'tapeout_ready': ready,
            'final_odb_sha256': target, 'gate_status': statuses,
            'remaining_gates': [name for name, value in statuses.items() if value != 'pass'],
            'boundary': 'Custody and claim-layer validation; original producer evidence remains authoritative.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('packet', type=Path)
    args = parser.parse_args()
    def unique(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    packet = json.loads(args.packet.read_bytes(), object_pairs_hook=unique)
    print(json.dumps(summarize(packet), indent=2))


if __name__ == '__main__':
    main()
