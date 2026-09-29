"""Assemble the selected paired implementation's evidence without running CAD.

This is an assessment of a pinned experiment, not a production admission
override. Historical receipts remain historical; only explicitly replayed
checks are fresh. Identity does not upgrade a measured check to a Lean proof.
"""
from copy import deepcopy
import hashlib
import json
import math
from pathlib import Path
import re

from mapped_physical import connection_signature, signal_view
from paired_execution import compile_e64
from paired_image_certificate import render
from physical_buffer_repair import compare_buffer_repair
from physical_timing_acceptance import assess_timing
from pinwheel_host import PAIRED_FORMAT, Program


POLICY = 'pinwheel-paired-a-acceptance-v1'
READBACK_POLICY = 'pinwheel-paired-a-acceptance-v2-readback'
ROOT_ROLES = frozenset(('formal', 'mapping', 'balanced', 'host_campaign',
                        'transport', 'closure', 'finalization', 'interface', 'trust'))
PROGRAMS = ('uart-tx', 'spi-mode0', 'i2c-stretched-read', 'uart-rx',
            'uart-rx-bad-stop', 'trigger-captured-high', 'trigger-captured-low', 'trigger-timeout')
CORNERS = ('nom_fast_1p32V_m40C', 'nom_slow_1p08V_125C', 'nom_typ_1p20V_25C')
REQUIREMENTS = frozenset(('host_certificates', 'digital_refinement', 'emission_identity',
    'implementation_checks', 'layout_checks', 'sram_boundary', 'electrical_screen',
    'sram_qualification', 'timing_conditions', 'typed_circuit_to_rtl', 'package_power'))
POWER_ONLY = frozenset(('sg13cmos5l_fill_1', 'sg13cmos5l_fill_2',
                        'sg13cmos5l_decap_4', 'sg13cmos5l_decap_8'))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def parse_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON field: ' + key)
            result[key] = value
        return result

    def invalid(value):
        raise ValueError('Nonfinite JSON value: ' + value)

    return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid)


class Evidence:
    """Read/hash once for parsing; verify every consumed file again at closeout."""

    def __init__(self, root):
        self.root = Path(root).absolute()
        self.files = {}
        self.documents = {}
        self.joins = []

    def path(self, path):
        return (self.root / path).absolute()

    def name(self, path):
        path = self.path(path)
        return str(path.relative_to(self.root)) if path.is_relative_to(self.root) else str(path)

    def ref(self, path, expected=None, *, data=False):
        path = self.path(path)
        key = self.name(path)
        if expected is not None:
            require(isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected),
                    'Invalid SHA-256 for ' + key)
        if key in self.files:
            require(expected is None or self.files[key] == expected, 'Conflicting identity: ' + key)
        try:
            raw = path.read_bytes() if data else None
            actual = hashlib.sha256(raw).hexdigest() if data else digest(path)
        except OSError as error:
            raise ValueError('Missing or unreadable evidence: ' + key) from error
        require(expected is None or actual == expected, 'Changed evidence: ' + key)
        require(key not in self.files or self.files[key] == actual, 'Evidence changed during assessment: ' + key)
        self.files[key] = actual
        entry = dict(path=key, sha256=actual)
        return (entry, raw) if data else entry

    def load(self, entry):
        key = self.name(entry['path'])
        if key in self.documents:
            require(self.files[key] == entry['sha256'], 'Conflicting document identity: ' + key)
            return self.documents[key]
        _, raw = self.ref(entry['path'], entry['sha256'], data=True)
        document = parse_json(raw)
        require(isinstance(document, dict), 'Expected evidence object: ' + key)
        self.documents[key] = document
        return document

    def inventory(self, values, base='.'):
        require(isinstance(values, dict) and values, 'Missing evidence inventory')
        return {name: self.ref(Path(base) / name, sha) for name, sha in values.items()}

    def artifact(self, report_entry, report, name):
        folder = Path(report_entry['path']).parent
        if 'artifact_sha256' in report:
            path = folder / name
            sha = report['artifact_sha256'][str(path)]
        else:
            path = folder / name
            sha = report['artifacts_sha256'][name]
        return self.ref(path, sha)

    def receipt(self, entry, *, current_inputs=False):
        report = self.load(entry)
        passed_receipt(report)
        if current_inputs:
            self.inventory(report['inputs_sha256'])
        if 'artifact_sha256' in report:
            self.inventory(report['artifact_sha256'])
        else:
            self.inventory(report['artifacts_sha256'], Path(entry['path']).parent)
        return report

    def same(self, label, left, right, method='byte identity'):
        self.ref(left['path'], left['sha256'])
        self.ref(right['path'], right['sha256'])
        require(left['sha256'] == right['sha256'], 'Disconnected evidence: ' + label)
        self.joins.append(dict(label=label, left=left, right=right, method=method))

    def consumed(self, label, report_entry, report, artifact):
        frozen = report.get('inputs_sha256', report.get('source_sha256', {}))
        expected = {self.name(p): h for p, h in frozen.items()}
        require(expected.get(self.name(artifact['path'])) == artifact['sha256'],
                'Receipt does not consume selected artifact: ' + label)
        self.joins.append(dict(label=label, receipt=report_entry, input=artifact,
                               method='receipt input identity'))

    def close(self):
        for path, sha in self.files.items():
            require(digest(self.path(path)) == sha, 'Evidence changed during assessment: ' + path)


def passed_receipt(report):
    require(report.get('status') == 'passed', 'Expected passing scoped receipt')
    require(report.get('inputs_unchanged', report.get('sources_unchanged')) is True,
            'Receipt has no unchanged-input conclusion')
    commands = report.get('commands')
    require(isinstance(commands, list) and commands, 'Missing executed checks')
    labels = set()
    for command in commands:
        label = command['label']
        require(label not in labels, 'Duplicate executed check: ' + label)
        labels.add(label)
        code = command.get('exit_code')
        require(type(code) is int and (code != 0 if command.get('expected_failure') else code == 0),
                'Unsuccessful or incomplete executed check: ' + label)


def require_commands(report, labels):
    require(set(labels) <= {c['label'] for c in report['commands']}, 'Missing required executed checks')


def mapping_receipt(evidence, manifest):
    require(manifest.get('schema') == 1 and manifest.get('status') == 'passed', 'Invalid mapping selection')
    entry = dict(path=manifest['report'], sha256=manifest['report_sha256'])
    return entry, evidence.receipt(entry)


def check_readback_scope(report):
    """Require both complete interpreted modules and live certificate refusals."""
    passed_receipt(report)
    require(report.get('schema') == 1 and set(report.get('modules', {})) == {'core', 'chip'},
            'Incomplete paired interpretation')
    require(report.get('session_theorem') == 'Pinwheel.Artifact.Paired.Package.rtl_initialized_session',
            'Wrong interpreted session theorem')
    commands = {c['label']: c for c in report['commands']}
    require_commands(report, ('build', 'guards', 'guards-optimized', 'emit', 'hint-labels', 'chip.Session'))
    for kind, namespace, counts, defects in [
        ('core', 'Core', (81, 1469, 37, 157), ('upload-cursor', 'parameter-bank', 'sram-write')),
        ('chip', 'Package', (110, 1592, 7, 99), ('sampler', 'mailbox-valid', 'package-output'))]:
        module = report['modules'][kind]
        require(tuple(module.get(k) for k in ('registers', 'register_bits', 'outputs', 'output_bits')) == counts,
                'Incomplete interpreted interface: ' + kind)
        require(module['audit']['standard_axioms_only'] is True and module['shared_equations'] == 45 and
                module['local_equalities'] > 0 and module['component_theorem'] ==
                'Pinwheel.Artifact.Paired.' + namespace + '.component_correct', 'Wrong interpretation proof: ' + kind)
        require(module['mutation_controls'] == ['unchanged', *defects], 'Missing circuit fault controls')
        require_commands(report, [kind + '.' + name for name in
            ('import', 'Design', 'Hints', 'Graphs', 'HintEquations', 'Equations', 'Sources',
             'LocalProofs', 'Links', 'Model', 'Endpoints', 'Proof', 'Audit', 'RejectAxiom')])
        for defect in ['unchanged', *defects]:
            prefix = kind + '.mutations.' + defect + '.'
            require_commands(report, [prefix + name for name in ('import', 'MutantGraphs', 'MutantModel', 'Reject')])
            require(commands[prefix + 'Reject'].get('expected_failure') is (defect != 'unchanged'),
                    'Wrong circuit fault verdict')
        require(commands[kind + '.RejectAxiom'].get('expected_failure') is True,
                'Missing axiom refusal')


def certificate_bytes(name, program_bytes):
    source = Program.from_bytes(program_bytes)
    require(source.image_format == PAIRED_FORMAT, 'Host program has the wrong image format')
    image = compile_e64(source.words, (source.idle_levels, source.idle_enabled), source.last)
    words = source.upload_words()
    require(len(words) == 290, 'Paired upload must contain 290 words')
    return render(name.replace('-', '_'), source.words, source.last,
                  (source.idle_levels, source.idle_enabled), image, words).encode(), words


def bind_certificate(name, program_bytes, certificate):
    generated, words = certificate_bytes(name, program_bytes)
    require(generated == certificate, 'Host program and retained certificate disagree: ' + name)
    return words


def host_certificates(evidence, host_entry, host, out, run):
    require(host.get('backend') == 'paired' and host.get('image_format') == PAIRED_FORMAT,
            'Expected paired host receipt')
    entries = host['image_certificates']
    require([e['program'] for e in entries] == list(PROGRAMS), 'Missing, reordered or duplicate host certificate')
    require_commands(host, [p + '-certificate' for p in PROGRAMS])
    for name in ('pinwheel-host.py', 'pinwheel_host.py', 'host_demo.py', 'paired_execution.py',
                 'paired_image_certificate.py', 'pinwheel_sim.py', 'execution-vectors.py'):
        path = 'scripts/' + name
        evidence.ref(path, host['source_sha256'][path])
    folder = Path(host_entry['path']).parent
    evidence.ref(folder / host['compiled_images_snapshot'], host['compiled_images_sha256'])
    results = []
    for entry in entries:
        name = entry['program']
        require(entry['path'] == name + '-certificate.lean', 'Unexpected certificate path')
        cert_ref, certificate = evidence.ref(folder / entry['path'], entry['sha256'], data=True)
        program_ref, program = evidence.ref(folder / (name + '.json'), data=True)
        words = bind_certificate(name, program, certificate)
        # Recheck captured bytes; never execute the mutable original path.
        copy = out / entry['path']
        with copy.open('xb') as stream:
            stream.write(certificate)
        log = run(['lake', 'env', 'lean', '-DwarningAsError=true', copy], name + '-certificate')
        require('Paired image certificate: kernel checked; standard axioms only.' in log,
                'Missing fresh kernel certificate audit: ' + name)
        results.append(dict(program=name, source=program_ref, certificate=cert_ref,
            upload_words=len(words), upload_sha256=hashlib.sha256(
                b''.join(w.to_bytes(8, 'big') for w in words)).hexdigest(),
            kernel_rechecked=True))
    return results


def signal_circuit(data):
    module, rails = signal_view(data['modules']['tt_um_pinwheel'], ['VPWR', 'VGND'])
    module = deepcopy(module)
    removed = {}
    for name, cell in list(module['cells'].items()):
        if cell['type'] not in POWER_ONLY:
            continue
        require(not cell['connections'] and not cell['port_directions'] and
                not data['modules'][cell['type']]['ports'], 'Finishing cell has a signal terminal')
        removed[cell['type']] = removed.get(cell['type'], 0) + 1
        del module['cells'][name]
    return module, rails, removed


def same_signal(evidence, label, left, right):
    a, rails_a, removed_a = signal_circuit(evidence.load(left))
    b, rails_b, removed_b = signal_circuit(evidence.load(right))
    require(rails_a == rails_b and connection_signature(a) == connection_signature(b),
            'Signal circuit mismatch: ' + label)
    result = dict(label=label, left=left, right=right,
        method='fresh connection comparison of retained readbacks; only isolated power-only finishing cells removed',
        removed_left=removed_a, removed_right=removed_b)
    evidence.joins.append(result)
    return result


def protected_repair(before, after, protection, master):
    """Remove only the declared input-only diode, checking its receiver first."""
    name = protection['instance']
    require(name not in before['cells'] and name in after['cells'], 'Unexpected protection instance')
    require(protection['cell'] == 'sg13cmos5l_antennanp' and protection['pin'] == 'A',
            'Unexpected protection declaration')
    require(set(master['ports']) == {'A'} and master['ports']['A']['direction'] == 'input' and
            len(master['ports']['A']['bits']) == 1, 'Protection master is not input-only')
    diode = after['cells'][name]
    require(diode['type'] == protection['cell'] and not diode.get('parameters') and
            diode['port_directions'] == {'A': 'input'} and set(diode['connections']) == {'A'} and
            len(diode['connections']['A']) == 1, 'Malformed protection cell')
    receiver, pin = protection['protected_receiver'].rsplit('/', 1)
    require(diode['connections']['A'] == after['cells'][receiver]['connections'][pin],
            'Protection separated from its declared receiver')
    reduced = deepcopy(after)
    del reduced['cells'][name]
    return compare_buffer_repair(before, reduced)


def liberty_conditions(data):
    text = data.decode()
    name = re.search(r'default_operating_conditions\s*:\s*"?([\w.-]+)"?\s*;', text)
    require(name is not None, 'Missing default Liberty operating conditions')
    block = re.search(r'operating_conditions\s*\(\s*"?' + re.escape(name[1]) +
                      r'"?\s*\)\s*\{([^}]+)\}', text)
    require(block is not None, 'Missing Liberty operating-condition block')
    result = {}
    for field in ('process', 'voltage', 'temperature'):
        values = []
        for body, key in ((text, 'nom_' + field), (block[1], field)):
            found = re.search(r'\b' + key + r'\s*:\s*([-+\deE.]+)\s*;', body)
            require(found is not None, 'Missing Liberty condition: ' + key)
            value = float(found[1])
            require(math.isfinite(value), 'Nonfinite Liberty condition')
            values.append(value)
        require(values[0] == values[1], 'Nominal and operating conditions disagree')
        result[field] = values[0]
    return result


def row(name, title, verdict, detail, evidence):
    return dict(id=name, requirement=title, verdict=verdict, detail=detail, evidence=evidence)


def decision(rows):
    ids = [r['id'] for r in rows]
    require(len(ids) == len(set(ids)) and set(ids) == REQUIREMENTS, 'Incomplete acceptance requirements')
    require(all(r['verdict'] in ('passed', 'conditional', 'blocked', 'rejected') for r in rows),
            'Unknown acceptance verdict')
    blockers = [r['id'] for r in rows if r['verdict'] in ('blocked', 'rejected')]
    return dict(A_accepted=not blockers, blockers=blockers,
                B_admitted=False, complete_design_iteration=False)


def assess(evidence, selection, out, run):
    with_readback = selection.get('policy') == READBACK_POLICY
    require(selection.get('schema') == 1 and selection.get('policy') in (POLICY, READBACK_POLICY) and
            set(selection.get('roots', {})) == ROOT_ROLES | ({'readback'} if with_readback else set()),
            'Unsupported or incomplete evidence selection')
    refs = selection['roots']
    roots = {name: evidence.load(entry) for name, entry in refs.items()}
    formal = roots['formal']
    require(formal.get('status') == 'conditional_certified_upload_session_refinement_passed',
            'Require completed admission/session proof gate')
    proof_ref = formal['report']
    proof = evidence.receipt(proof_ref)
    require(proof['schema'] == 6 and proof['audit']['standard_axioms_only'] is True,
            'Require supported whole-library proof audit')
    require(proof['admission_refinement']['theorem'] ==
            'Pinwheel.Hardware.Storage.PairedSession.retained_initialized_session' and
            proof['admission_refinement']['admission_decisions_and_accepted_transcript_derived'] is True,
            'Admission proof has the wrong scope')
    require_commands(proof, ('build', 'axioms', 'reject-untrusted-axiom', 'admission-controls', 'emit'))
    evidence.inventory(proof['source_sha256'])
    evidence.inventory(formal['source_sha256'])
    contract_ref = formal['component_contract']
    contract = evidence.load(contract_ref)
    evidence.same('formal premise / SRAM proposal', contract_ref, roots['trust']['trust_contract'])

    mapping_ref, mapping = mapping_receipt(evidence, roots['mapping'])
    balanced_ref, balanced = mapping_receipt(evidence, roots['balanced'])
    require(roots['mapping']['implementation'] == 'PairedValidation', 'Wrong proved implementation')
    require_commands(mapping, ('core-equivalence', 'chip-equivalence', 'typical-proof', 'slow-proof'))
    for kind in ('core', 'chip'):
        require(mapping['cross_implementation'][kind]['status'] == 'equivalent', 'Failed RTL comparison')
    evidence.same('isolated RTL / balanced mapping', mapping_ref, balanced['source_mapping'])
    require_commands(balanced, ('typical-proof', 'slow-proof'))
    for name in ('core.mlir', 'chip.mlir', 'assembly.json'):
        retained = proof['retained_artifacts'][name]
        evidence.ref(retained['path'], retained['sha256'])
        emitted = evidence.artifact(proof_ref, proof, 'emitted/' + name)
        mapped = evidence.artifact(mapping_ref, mapping, name)
        evidence.same('proved emission / retained ' + name, emitted, retained)
        evidence.same('retained emission / mapping ' + name, retained, mapped)

    readback_ref = None
    if with_readback:
        interpreted = roots['readback']
        require(interpreted.get('schema') == 1 and interpreted.get('status') == 'passed',
                'Require completed paired interpretation')
        readback_ref = interpreted['report']
        readback = evidence.receipt(readback_ref)
        check_readback_scope(readback)
        evidence.inventory(readback['source_sha256'])
        evidence.inventory(readback['tools_sha256'])
        evidence.same('interpretation / formal admission gate', readback['previous_gate'], refs['formal'])
        evidence.consumed('interpretation / admission theorem source', readback_ref, readback, proof_ref)
        for name in ('core.mlir', 'chip.mlir', 'core.sv', 'chip.sv', 'assembly.json'):
            selected = evidence.artifact(mapping_ref, mapping, name)
            evidence.same('interpreted / selected ' + name, readback['retained_artifacts'][name], selected)
            evidence.same('interpreted frozen copy / selected ' + name,
                          evidence.artifact(readback_ref, readback, 'retained/' + name), selected)
            evidence.consumed('interpretation / selected ' + name, readback_ref, readback, selected)

    host_ref = roots['host_campaign']['reports']['paired_host_demo']
    host = evidence.load(host_ref)
    host_folder = Path(host_ref['path']).parent
    for filename, field, mapped_name in (('design.sv', 'rtl_sha256', 'baseline/chip.sv'),
                                        ('chip.mlir', 'mlir_sha256', 'baseline/chip.mlir')):
        observed = evidence.ref(host_folder / filename, host[field])
        baseline = evidence.artifact(mapping_ref, mapping, mapped_name)
        evidence.same('host demonstration / original paired ' + filename, observed, baseline)

    # The physical SAT receipt bypasses intermediate placement history and
    # compares its actual implemented netlist with the selected mapped source.
    transport = roots['transport']
    sat_ref = transport['coarse_reports']['candidate-implemented-check/report.json']
    sat = evidence.receipt(sat_ref, current_inputs=True)
    require(sat['equivalent'] is True and sat['hidden_state_rejected'] is True and
            sat['inverted_control_rejected'] is True, 'Missing physical SAT checks')
    require_commands(sat, ('implemented-equivalence', 'control-negative'))
    mapped_readback = evidence.artifact(balanced_ref, balanced, 'typical/readback.json')
    evidence.consumed('balanced mapping / physical SAT', sat_ref, sat, mapped_readback)
    routed_ref = transport['reports']['post-route-check/report.json']
    routed = evidence.receipt(routed_ref, current_inputs=True)
    require(routed['exact_original_signal_identity'] is True, 'Post-route signal identity failed')
    evidence.consumed('physical SAT / routed identity check', routed_ref, routed, sat_ref)
    common = {evidence.name(p): h for p, h in sat['inputs_sha256'].items() if p.endswith('/candidate/implemented.v')}
    require(len(common) == 1, 'Missing physical SAT endpoint')
    implemented = evidence.ref(*next(iter(common.items())))
    evidence.consumed('physical SAT endpoint / routing source', routed_ref, routed, implemented)

    closure = roots['closure']
    closure_ref = closure['reports']['candidate-05-check-report.json']
    closure_check = evidence.receipt(closure_ref, current_inputs=True)
    require(closure_check['identity']['buffer_contracted_connectivity'] is True,
            'Closure did not preserve signal function')
    routed_json = evidence.artifact(routed_ref, routed, 'final.json')
    closure_source = evidence.artifact(closure_ref, closure_check, 'source.json')
    same_signal(evidence, 'routed circuit / electrical-repair source', routed_json, closure_source)
    closure_final = evidence.artifact(closure_ref, closure_check, 'final.json')
    before, _, _ = signal_circuit(evidence.load(closure_source))
    after, _, _ = signal_circuit(evidence.load(closure_final))
    protection_inputs = [(p, h) for p, h in closure_check['inputs_sha256'].items()
                         if p.endswith('/protection-plan.json')]
    require(len(protection_inputs) == 1, 'Missing declared protection plan')
    protection_ref = evidence.ref(*protection_inputs[0])
    protection = evidence.load(protection_ref)
    master = evidence.load(closure_final)['modules']['sg13cmos5l_antennanp']
    require(protected_repair(before, after, protection, master) == closure_check['identity'] and
            closure_check['physical']['protection_receiver_binding_preserved'] is True,
            'Electrical repair identity changed')
    evidence.joins.append(dict(label='electrical repair', left=closure_source, right=closure_final,
        protection=protection_ref,
        method='fresh contraction of pinned buffers and checked declared input-only protection/receiver; physical geometry remains receipted'))

    final = roots['finalization']
    candidate = {k: evidence.ref(v['path'], v['sha256']) for k, v in final['candidate'].items()}
    final_ref = final['reports']['final-check/report.json']
    final_check = evidence.receipt(final_ref, current_inputs=True)
    require(final_check['exact_original_signal_identity'] is True, 'Finishing changed signal circuitry')
    evidence.consumed('electrical repair / finishing receipt', final_ref, final_check, closure_ref)
    evidence.consumed('selected final netlist / functional receipt', final_ref, final_check, candidate['nl'])
    final_source = evidence.artifact(final_ref, final_check, 'source.json')
    final_json = evidence.artifact(final_ref, final_check, 'final.json')
    same_signal(evidence, 'electrical repair / finishing source', closure_final, final_source)
    same_signal(evidence, 'finishing preserves signal circuit', final_source, final_json)

    analysis_ref = final['reports']['analysis.json']
    analysis = evidence.load(analysis_ref)
    require(analysis['evidence_validation'] == 'passed' and analysis['inputs_unchanged'] is True,
            'Missing final-layout evidence audit')
    for name, entry in candidate.items():
        evidence.same('layout audit / selected ' + name, entry, analysis['artifacts'][name])
    for key in ('all_existing_instances_and_connections_unchanged', 'all_existing_wire_encodings_unchanged',
                'power_geometry_and_all_terminal_bindings_preserved', 'all_98_antenna_bindings_preserved'):
        require(analysis[key] is True, 'Failed final-layout check: ' + key)
    for key in ('full_rule_magic_gds_drc', 'antenna_violations', 'critical_disconnected_pins', 'grid_overflow'):
        require(type(analysis[key]) is int and analysis[key] == 0, 'Failed final-layout check: ' + key)
    timing_ref = final['reports']['inspect-02/output/timing.json']
    timing = evidence.load(timing_ref)
    evidence.consumed('layout audit / timing', analysis_ref, analysis, timing_ref)
    require(timing['initial_metrics'] == {} and timing['status'] == 'completed', 'Stale or incomplete timing metrics')
    for key, field in (('odb', 'database_sha256'), ('nl', 'netlist_sha256'),
                       ('sdc', 'sdc_sha256'), ('spef', 'spef_sha256')):
        require(candidate[key]['sha256'] == timing[field], 'Timing refers to another ' + key)
        evidence.joins.append(dict(label='timing / selected ' + key, artifact=candidate[key],
            receipt=timing_ref, field=field, method='measured artifact identity'))
    timing_result = assess_timing(timing['metrics'], CORNERS)
    require(timing_result == analysis['acceptance'] == final['passed_checks']['acceptance'],
            'Final timing conclusion does not reproduce')
    power_ref = final['reports']['inspect-02/output/power.json']
    power = evidence.load(power_ref)
    evidence.consumed('layout audit / power continuity', analysis_ref, analysis, power_ref)
    require(power['status'] == 'passed' and power['terminals'] == analysis['power_terminals'],
            'Power connectivity evidence disagrees')

    interface = roots['interface']
    for name, entry in candidate.items():
        evidence.same('exported-layout interface / selected ' + name, entry, interface['candidate'][name])
    interface_ref = interface['reports']['interface-01/output/report.json']
    boundary = evidence.load(interface_ref)
    require(boundary['status'] == 'passed' and boundary['pins'] == 351 and
            boundary['cases']['adapted']['native_final_result'] == 'Circuits match uniquely.' and
            boundary['macro_internal_lvs'] is False, 'Unsupported SRAM boundary evidence')
    for name in ('address-to-ground', 'ground-to-power'):
        require(boundary['cases'][name]['native_final_result'] == 'Top level cell failed pin matching.',
                'Missing SRAM boundary fault rejection')
    interface_receipt_ref = interface['reports']['interface-01-receipt.json']
    interface_receipt = evidence.load(interface_receipt_ref)
    evidence.consumed('boundary LVS / final GDS', interface_receipt_ref, interface_receipt, candidate['gds'])
    for entry in [*contract['supplied_views'], contract['behavioral_dependency']]:
        evidence.ref(entry['path'], entry['sha256'])
    models = [v for v in contract['supplied_views'] if v['path'].endswith('.v')]
    models.append(contract['behavioral_dependency'])
    require({Path(v['path']).name for v in models} == set(host['macro_models_sha256']),
            'Host models do not cover the proposed SRAM contract')
    for entry in models:
        model = evidence.ref(Path('build/storage/macros') / Path(entry['path']).name,
                             host['macro_models_sha256'][Path(entry['path']).name])
        evidence.same('host model / SRAM proposal', model, entry)
        evidence.consumed('final pin replay / SRAM model', final_ref, final_check, model)

    audit_ref = roots['host_campaign']['reports']['audit']
    audit = evidence.load(audit_ref)
    inspection_ref = final['reports']['inspect-02-receipt.json']
    inspection = evidence.load(inspection_ref)
    require(inspection['status'] == 'completed' and inspection['sources_unchanged'] is True,
            'Incomplete final physical inspection')
    views = {Path(v['path']).name: v for v in contract['supplied_views']}
    conditions = {}
    for corner, pair in audit['corners'].items():
        conditions[corner] = {}
        for role in ('cells', 'sram'):
            entry = pair[role]
            reference, raw = evidence.ref(entry['path'], entry['sha256'], data=True)
            values = liberty_conditions(raw)
            require(values == entry['nominal'] == entry['operating'], 'Corner metadata changed')
            consumed = views[Path(entry['path']).name] if role == 'sram' else reference
            evidence.same('audited / consumed ' + corner + ' ' + role + ' library', reference, consumed)
            evidence.consumed('final inspection / ' + corner + ' ' + role, inspection_ref, inspection, consumed)
            conditions[corner][role] = dict(artifact=reference, **values)
        conditions[corner]['matching_voltage_temperature'] = all(
            conditions[corner]['cells'][f] == conditions[corner]['sram'][f] for f in ('voltage', 'temperature'))
    require(set(conditions) == {'typ', 'slow', 'fast'}, 'Missing required timing conditions')
    require(conditions['fast']['matching_voltage_temperature'] is False and
            final['limits']['fast_characterization_qualified'] is False, 'New corner qualification needs a reviewed policy')
    trust = roots['trust']
    require(trust['full_sram_qualification'] is False and contract['full_sram_qualification'] is False,
            'New SRAM qualification needs its own evidence intake')
    require(final['limits']['power_ir_drop_manufacturing_qualified'] is False,
            'New package power qualification needs its own evidence intake')

    # Finish identity/measurement intake before spending time on fresh proofs.
    certificates = host_certificates(evidence, host_ref, host, out, run)
    rows = [
        row('host_certificates', 'Canonical host image and 290-word upload', 'passed',
            'Eight retained programs reproduce their exact certificates and are freshly kernel checked.', [host_ref, proof_ref]),
        row('digital_refinement', 'Admission, storage, timed execution and package observations', 'conditional',
            'Universal Lean theorem under the explicit SRAM law, qualified digital delivery and execution-segment rule.', [proof_ref, contract_ref]),
        row('emission_identity', 'Proved typed package and retained emitted implementation', 'passed',
            'Fresh proof-gate core/package MLIR and assembly match the selected mapping bytes.', [proof_ref, mapping_ref]),
        row('implementation_checks', 'RTL, mapped logic and final signal circuit', 'passed',
            'Identity-connected scoped SAT receipts and fresh readback connectivity checks; pinned cell functions and tool interpretations remain trusted.', [mapping_ref, balanced_ref, sat_ref, routed_ref, closure_ref, final_ref]),
        row('layout_checks', 'Detailed wires, full-rule GDS DRC and antenna', 'passed',
            'Retained layout audit passes; disabled KLayout DRC/XOR and flow EQY remain disabled.', [analysis_ref]),
        row('sram_boundary', 'Exported-GDS SRAM interface', 'passed',
            '351-pin boundary comparison passes and two wiring faults reject; internals are abstracted.', [interface_ref]),
        row('electrical_screen', 'Extracted setup, hold and electrical limits', timing_result['status'],
            'All recorded corners pass numerically; fast operating-condition qualification is a separate requirement.', [timing_ref]),
        row('sram_qualification', 'Exact-version SRAM internal and behavioral qualification', 'blocked',
            '0.260/0.200 um source/layout width discrepancy and internal checking remain unresolved; the behavioral law is a premise.', [refs['trust'], contract_ref]),
        row('timing_conditions', 'Compatible logic/SRAM timing conditions', 'blocked',
            'Fast cells use -40 C, SRAM -55 C; no compatible delivered pair or justified conservative bound.', [audit_ref, timing_ref]),
        row('typed_circuit_to_rtl', 'Meaning preserved from typed circuit through RTL export',
            'passed' if with_readback else 'blocked',
            ('Kernel-checked interpretations of both exact retained RTL modules equal their typed components and inherit the session theorem; the restricted adapter and Yosys frontend/lowering remain trusted.'
             if with_readback else 'Byte identity and SAT between emitted variants do not prove the emitter/CIRCT interpretation. No paired artifact-interpretation theorem is supplied.'),
            [proof_ref, mapping_ref, readback_ref] if with_readback else [proof_ref, mapping_ref]),
        row('package_power', 'Qualified power delivery for the declared package', 'blocked',
            'Continuity passes; IR-drop uses default source locations and modeled activity without qualified package assumptions.', [power_ref, analysis_ref]),
    ]
    # No inherited A_accepted/status field can promote a missing requirement.
    result = decision(rows)
    result.update(scope=selection['scope'], requirements=rows, candidate=candidate,
        certificates=certificates, proof=dict(report=proof_ref, audit=proof['audit'],
            theorem=proof['admission_refinement']['theorem'], premises=proof['admission_refinement']['premises']),
        implementation_joins=evidence.joins, timing=timing_result, timing_conditions=conditions,
        host_observations=dict(report=host_ref, edges=host['edges'], frames=host['frames'], replayed_now=False),
        final_pin_observations=dict(report=final_ref, **final_check['pin_coverage'], replayed_now=False),
        physical_limits=final['limits'],
        iteration_gates=[dict(id='capacity_B', verdict='blocked', detail='Accept A before the 64-record B change.'),
                         dict(id='clean_replay', verdict='blocked', detail='Retained worktree artifacts are dependencies; no clean-source physical replay.')],
        campaign=trust['resource_ledger'], cad_seconds=0,
        boundary='Evidence consolidation and eight fresh kernel certificate checks. No CAD, host/physical simulation replay, hardware modification, external qualification or production admission change.')
    if readback_ref:
        result['artifact_interpretation'] = dict(report=readback_ref,
            session_theorem=readback['session_theorem'], modules=readback['modules'], replayed_now=False)
    return result


def markdown(report, root):
    lines = ['# Design A acceptance report', '',
        '**A accepted: ' + ('yes' if report['A_accepted'] else 'no') + '.** Assessment: ' + report['status'] + '.', '']
    if report['status'] != 'assessed':
        return '\n'.join(lines + ['Evidence could not be validated: ' + report.get('error', 'unknown error'), ''])
    lines += [report['scope'], '', '| Requirement | Verdict | Evidence and meaning |', '| --- | --- | --- |']
    for r in report['requirements']:
        links = ', '.join(f"[{Path(e['path']).name}]({Path(root) / e['path']})" for e in r['evidence'])
        lines.append(f"| {r['requirement']} | {r['verdict']} | {r['detail']} {links} |")
    lines += ['', 'Links refer to this checkout. Exact hashes, '
              'implementation joins, observed results and premises are in `report.json`.', '',
              'The assessment keeps source-to-RTL correspondence, SRAM qualification, compatible fast conditions '
              'and package power qualification open. B and clean-source physical replay remain separate.', '',
              report['boundary'], '']
    return '\n'.join(lines)
