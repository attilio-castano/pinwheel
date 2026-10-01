"""Check a package-power analysis request without running CAD or accepting A.

All output goes to stdout. Missing evidence yields an incomplete request;
malformed or changed evidence is refused. Supplied provider claims are inputs
for a later scoped analysis, never qualifications certified by this checker.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[3]
RAILS = ('VPWR', 'VGND')
MODES = {'clocked_idle', 'replacement_upload', 'execution'}
REQUIREMENTS = {
    'parent_geometry': 'parent_chip_integrator',
    'source_voltage': 'parent_chip_or_package_integrator',
    'external_impedance': 'parent_chip_or_package_integrator',
    'operating_envelope': 'pinwheel_and_integrator',
    'activity_envelope': 'pinwheel_and_component_provider',
    'supported_local_supply': 'logic_and_sram_library_provider',
    'transient_allowance': 'parent_chip_or_package_integrator',
    'analysis_conditions': 'pinwheel_and_component_provider',
}
WORKLOADS = {
    'clocked_idle': ('activity-idle-02', 8192, 163840),
    'replacement_upload': ('activity-replacement-02', 63656, 1273120),
    'execution': ('activity-execution-02', 8192, 163840),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact(value, keys, label):
    require(isinstance(value, dict) and set(value) == set(keys),
            f'{label}: unexpected or missing fields')


def number(value, label, minimum=None):
    require(type(value) in (int, float) and math.isfinite(value),
            f'{label}: expected a finite number, not a boolean')
    if minimum is not None:
        require(value >= minimum, f'{label}: below {minimum}')
    return value


def words(value, label):
    require(isinstance(value, str) and bool(value.strip()), f'{label}: expected nonempty text')


def parse_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, f'Duplicate JSON key: {key}')
            result[key] = value
        return result

    def constant(value):
        raise ValueError(f'Nonfinite JSON number: {value}')

    return json.loads(data, object_pairs_hook=pairs, parse_constant=constant)


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def identity(entry, label):
    exact(entry, ('path', 'sha256'), label)
    path = Path(entry['path']) if isinstance(entry['path'], str) else None
    require(path is not None and str(path) not in ('', '.') and not path.is_absolute()
            and '..' not in path.parts, f'{label}: expected a repository-relative path')
    require(isinstance(entry['sha256'], str) and re.fullmatch(r'[0-9a-f]{64}', entry['sha256']),
            f'{label}: expected a SHA-256 identity')


def voltage_budget(source_min_v, vdd_drop_mv, ground_rise_mv, transient_loss_mv,
                   supported_local_min_v=None):
    """Dimensional arithmetic only; caller must establish result applicability."""
    source = number(source_min_v, 'source_min_v', 0)
    drops = [number(value, label, 0) for value, label in (
        (vdd_drop_mv, 'vdd_drop_mv'), (ground_rise_mv, 'ground_rise_mv'),
        (transient_loss_mv, 'transient_loss_mv'))]
    local = source - sum(drops) / 1000
    require(math.isfinite(sum(drops)) and math.isfinite(local), 'Voltage-budget arithmetic overflow')
    result = {'source_min_v': source, 'conservative_loss_mv': sum(drops),
              'conservative_local_min_v': local, 'qualification': False}
    if supported_local_min_v is not None:
        result['margin_v'] = local - number(supported_local_min_v, 'supported_local_min_v', 0)
    return result


def range_values(value, low, high, label, minimum=None):
    number(value[low], f'{label}.{low}', minimum)
    number(value[high], f'{label}.{high}', minimum)
    require(value[low] <= value[high], f'{label}: inverted range')


def validate_value(name, value):
    if name == 'parent_geometry':
        exact(value, ('ownership', 'contacts'), name)
        words(value['ownership'], name + '.ownership')
        require(isinstance(value['contacts'], list) and value['contacts'], 'No contacts declared')
        seen = set()
        for contact in value['contacts']:
            exact(contact, ('rail', 'layer', 'x_um', 'y_um', 'width_um', 'height_um'), 'contact')
            require(contact['rail'] in RAILS, 'Unexpected contact rail')
            words(contact['layer'], 'contact.layer')
            for key in ('x_um', 'y_um', 'width_um', 'height_um'):
                number(contact[key], 'contact.' + key, 0)
            require(contact['width_um'] > 0 and contact['height_um'] > 0, 'Empty contact')
            token = tuple(contact[key] for key in ('rail', 'layer', 'x_um', 'y_um'))
            require(token not in seen, 'Duplicate contact')
            seen.add(token)
        require({c['rail'] for c in value['contacts']} == set(RAILS), 'Contacts must cover both rails')
    elif name == 'source_voltage':
        exact(value, ('reference_point', 'minimum_v', 'maximum_v'), name)
        words(value['reference_point'], name + '.reference_point')
        range_values(value, 'minimum_v', 'maximum_v', name, 0)
        require(value['minimum_v'] > 0, 'Supply differential must be positive')
    elif name == 'external_impedance':
        exact(value, ('interpretation', 'vpwr_ohm', 'vgnd_ohm', 'return_path'), name)
        require(value['interpretation'] == 'ohm_per_resolved_source_node',
                'Saved evaluator requires resistance per resolved source node; RLC needs a separate analysis')
        number(value['vpwr_ohm'], name + '.vpwr_ohm', 0)
        number(value['vgnd_ohm'], name + '.vgnd_ohm', 0)
        words(value['return_path'], name + '.return_path')
    elif name == 'operating_envelope':
        exact(value, ('temperature_min_c', 'temperature_max_c', 'clock_period_ns', 'program_scope'), name)
        range_values(value, 'temperature_min_c', 'temperature_max_c', name)
        require(number(value['clock_period_ns'], name + '.clock_period_ns', 0) == 20,
                'This candidate request binds the retained 20 ns clock')
        words(value['program_scope'], name + '.program_scope')
    elif name == 'activity_envelope':
        exact(value, ('total_power_upper_bound_mw', 'method', 'program_scope',
                      'supported_modes', 'includes_physical_glitches', 'includes_macro_energy'), name)
        number(value['total_power_upper_bound_mw'], name + '.total_power_upper_bound_mw', 0)
        words(value['method'], name + '.method')
        words(value['program_scope'], name + '.program_scope')
        modes = value['supported_modes']
        require(isinstance(modes, list) and all(isinstance(m, str) for m in modes)
                and len(modes) == len(set(modes)) and set(modes) == MODES,
                'Activity envelope must cover each permitted mode exactly once')
        for key in ('includes_physical_glitches', 'includes_macro_energy'):
            require(type(value[key]) is bool, f'{name}.{key}: expected boolean')
    elif name == 'supported_local_supply':
        exact(value, ('minimum_v', 'maximum_v', 'temperature_min_c', 'temperature_max_c',
                      'fast_pair_compatibility'), name)
        range_values(value, 'minimum_v', 'maximum_v', name, 0)
        require(value['minimum_v'] > 0, 'Supported local supply must be positive')
        range_values(value, 'temperature_min_c', 'temperature_max_c', name)
        require(value['fast_pair_compatibility'] in ('supported_pair', 'supported_bound'),
                'Compatible component characterization or a supported bound is required')
    elif name == 'transient_allowance':
        exact(value, ('loss_mv', 'method', 'scope'), name)
        number(value['loss_mv'], name + '.loss_mv', 0)
        words(value['method'], name + '.method')
        words(value['scope'], name + '.scope')
    elif name == 'analysis_conditions':
        exact(value, ('model_voltage_v', 'logic_temperature_c', 'sram_temperature_c', 'parasitic_corner'), name)
        number(value['model_voltage_v'], name + '.model_voltage_v', 0)
        number(value['logic_temperature_c'], name + '.logic_temperature_c')
        number(value['sram_temperature_c'], name + '.sram_temperature_c')
        require(value['parasitic_corner'] in ('min', 'nom', 'max'), 'Unknown parasitic corner')


def assess(contract, repository=ROOT, artifact_root=None):
    exact(contract, ('schema', 'purpose', 'source_manifest', 'candidate', 'clock', 'rails',
                     'finite_workloads', 'requirements'), 'contract')
    require(type(contract['schema']) is int and contract['schema'] == 1, 'Unsupported contract schema')
    require(contract['purpose'] == 'analysis_request_only', 'This checker cannot qualify package power')
    exact(contract['clock'], ('period_ns',), 'clock')
    require(number(contract['clock']['period_ns'], 'clock.period_ns') == 20, 'Changed retained clock')
    require(contract['rails'] == list(RAILS), 'Changed retained rail identities')
    repository = Path(repository)
    artifact_root = Path(artifact_root) if artifact_root else repository
    missing = []
    verified = []

    def binding(entry, base, label, mandatory=False):
        identity(entry, label)
        path = base / entry['path']
        if not path.is_file():
            require(not mandatory, f'Missing evidence: {label}')
            missing.append({'id': label, 'owner': 'evidence_custodian', 'path': entry['path']})
            return False
        require(sha(path) == entry['sha256'], f'Changed evidence: {label}')
        verified.append((path, entry['sha256']))
        return True

    binding(contract['source_manifest'], repository, 'source_manifest', mandatory=True)
    manifest = parse_json((repository / contract['source_manifest']['path']).read_bytes())
    require(manifest['status'] == 'sensitivity_complete_qualification_open'
            and manifest['new_qualification_evidence'] is False, 'Unexpected source study scope')
    expected = dict(manifest['candidate'], readback=manifest['circuit_readback'],
                    readback_receipt=manifest['circuit_readback_receipt'])
    require(contract['candidate'] == expected, 'Candidate is disconnected from the frozen power study')
    for role, entry in expected.items():
        binding(entry, artifact_root, 'candidate.' + role)
    binding(manifest['report'], artifact_root, 'retained_power_report')
    waveform_present = binding(manifest['waveform_audit'], artifact_root, 'retained_waveform_audit')
    unknowns_present = binding(manifest['unknown_bit_audit'], artifact_root, 'retained_unknown_bit_audit')
    waveforms = parse_json((artifact_root / manifest['waveform_audit']['path']).read_bytes()) if waveform_present else None
    unknowns = parse_json((artifact_root / manifest['unknown_bit_audit']['path']).read_bytes()) if unknowns_present else None

    require(isinstance(contract['finite_workloads'], list), 'finite_workloads: expected list')
    require(len(contract['finite_workloads']) == len(WORKLOADS), 'Incomplete finite-workload inventory')
    modes = set()
    activity = []
    for workload in contract['finite_workloads']:
        exact(workload, ('mode', 'case', 'cycles', 'duration_ns', 'claim'), 'finite workload')
        mode = workload['mode']
        require(isinstance(mode, str) and mode in WORKLOADS and mode not in modes,
                'Unknown or duplicate finite workload')
        modes.add(mode)
        case, cycles, duration = WORKLOADS[mode]
        require(workload['case'] == case and type(workload['cycles']) is int
                and workload['cycles'] == cycles
                and number(workload['duration_ns'], 'workload.duration_ns') == duration,
                'Changed finite-workload window')
        require(workload['claim'] == 'finite_zero_delay_observation', 'Finite traces are not activity bounds')
        original_name = {'clocked_idle': 'idle', 'replacement_upload': 'replacement', 'execution': 'execution'}[mode]
        if waveforms is not None:
            window = waveforms[original_name]
            require(number(window['duration_ns'], 'retained duration_ns') == duration
                    and type(window['clock_transitions']) is int and window['clock_transitions'] == cycles * 2,
                    'Retained workload clock/window disagreement')
        if unknowns is not None:
            require(type(unknowns[original_name]['connected_unknown_bits']) is int
                    and unknowns[original_name]['connected_unknown_bits'] == 0,
                    'Unknown connected workload bit')
        rows = [r for r in manifest['measured_cases'] if r['case'] == case]
        require(len(rows) == 1 and rows[0]['annotated_signal_pins'] == 38497,
                'Source manifest lacks complete workload annotation')
        row = rows[0]
        activity.append({'mode': mode, 'case': case, 'cycles': cycles, 'duration_ns': duration,
                         'annotated_signal_pins': 38497, 'modeled_total_power_mw': row['power_mw'],
                         'claim': workload['claim']})

    exact(contract['requirements'], REQUIREMENTS, 'requirements')
    supplied = {}
    for name, owner in REQUIREMENTS.items():
        entry = contract['requirements'][name]
        exact(entry, ('owner', 'status', 'value', 'evidence', 'stop_condition'), name)
        require(entry['owner'] == owner, f'{name}: changed responsibility')
        words(entry['stop_condition'], name + '.stop_condition')
        require(entry['status'] in ('missing', 'supplied'), f'{name}: unknown status')
        if entry['status'] == 'missing':
            require(entry['value'] is None and entry['evidence'] is None,
                    f'{name}: missing input must remain null')
            missing.append({'id': name, 'owner': owner, 'stop_condition': entry['stop_condition']})
        else:
            validate_value(name, entry['value'])
            require(entry['evidence'] is not None, f'{name}: supplied value needs evidence')
            if binding(entry['evidence'], artifact_root, 'requirement.' + name):
                supplied[name] = entry['value']

    stops = []
    envelope = supplied.get('activity_envelope')
    if envelope:
        for key in ('includes_physical_glitches', 'includes_macro_energy'):
            if not envelope[key]:
                stops.append('activity_envelope.' + key)
    operating = supplied.get('operating_envelope')
    local = supplied.get('supported_local_supply')
    conditions = supplied.get('analysis_conditions')
    source = supplied.get('source_voltage')
    if envelope and operating:
        require(envelope['program_scope'] == operating['program_scope'], 'Program scopes disagree')
    if operating and local:
        require(local['temperature_min_c'] <= operating['temperature_min_c']
                and local['temperature_max_c'] >= operating['temperature_max_c'],
                'Component evidence does not cover the requested temperature envelope')
    if conditions and local:
        if conditions['logic_temperature_c'] != conditions['sram_temperature_c']:
            require(local['fast_pair_compatibility'] == 'supported_bound',
                    'Mixed-temperature analysis needs a supported bound')
        for key in ('logic_temperature_c', 'sram_temperature_c'):
            require(local['temperature_min_c'] <= conditions[key] <= local['temperature_max_c'],
                    'Analysis temperature outside supplied support')
    if conditions and source:
        # A nominal sensitivity cannot be relabeled as a source-minimum case.
        require(conditions['model_voltage_v'] == source['minimum_v'],
                'Analysis voltage must cover source minimum; nominal loss cannot qualify a lower supply')
    if source and local and source['maximum_v'] > local['maximum_v']:
        stops.append('source_maximum_exceeds_supported_local_supply')
    available = None
    if source and local and 'transient_allowance' in supplied:
        available = (source['minimum_v'] - local['minimum_v']) * 1000 - supplied['transient_allowance']['loss_mv']
        require(math.isfinite(available), 'Available voltage-budget arithmetic overflow')
        if available <= 0:
            stops.append('no_positive_static_rail_loss_budget')

    diagnostics = []
    for row in manifest['measured_cases']:
        budget = voltage_budget(1.2, row['VPWR_worst_drop_mv'], row['VGND_worst_drop_mv'], 0)
        diagnostics.append({'case': row['case'], 'conditions': {'voltage_v': 1.2, 'temperature_c': 25,
                            'parasitic_corner': 'nom'}, 'voltage_budget': budget,
                            'applicability': 'recorded_nominal_sensitivity_only'})
    for path, expected_hash in verified:
        require(sha(path) == expected_hash, f'Evidence changed during assessment: {path}')
    ready = not missing and not stops
    return {'schema': 1, 'status': 'ready_for_scoped_analysis' if ready else 'incomplete_request',
            'ready_for_scoped_analysis': ready, 'qualification': False, 'A_accepted': False,
            'readiness_scope': 'structural_request_only',
            'contact_containment_verified': False, 'provider_claims_validated': False,
            'existing_evidence': 'diagnostic', 'verified_file_count': len(verified),
            'missing_inputs': missing, 'stop_conditions': stops,
            'available_static_rail_loss_budget_mv': available, 'finite_workload_audit': activity,
            'activity_audit_scope': 'hash-bound retained window, annotation and connected-unknown summaries; simulations not rerun',
            'activity_gaps': ['all_program_power_bound', 'physical_glitch_activity',
                              'independent_macro_energy_qualification', 'transient_package_noise'],
            'diagnostic_voltage_budgets': diagnostics,
            'next_gate': 'Evaluate the saved candidate with bound parent/provider inputs; update acceptance through a new exact-identity intake.'}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--contract', type=Path, default=Path(__file__).with_name('contract.json'))
    parser.add_argument('--repository', type=Path, default=ROOT)
    parser.add_argument('--artifact-root', type=Path)
    parser.add_argument('--require-ready', action='store_true')
    args = parser.parse_args(argv)
    try:
        data = args.contract.read_bytes()
        result = assess(parse_json(data), args.repository, args.artifact_root)
        result['contract_sha256'] = hashlib.sha256(data).hexdigest()
        require(args.contract.read_bytes() == data, 'Contract changed during assessment')
    except (OSError, ValueError, TypeError, KeyError) as exc:
        print(json.dumps({'status': 'refused', 'error': str(exc), 'qualification': False}), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, allow_nan=False))
    return 2 if args.require_ready and not result['ready_for_scoped_analysis'] else 0


if __name__ == '__main__':
    sys.exit(main())
