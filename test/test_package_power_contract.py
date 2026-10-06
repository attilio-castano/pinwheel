"""Controls for power-request custody, scope, units and unsafe admission claims."""
from copy import deepcopy
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'physical/fixtures/package-power-contract'
SPEC = importlib.util.spec_from_file_location('package_power_contract', DIRECTORY / 'validate.py')
power = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(power)


class PackagePowerContractTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.contract = power.parse_json((DIRECTORY / 'contract.json').read_bytes())
        self.manifest = power.parse_json((ROOT / self.contract['source_manifest']['path']).read_bytes())
        # These are synthetic custody fixtures, never physical qualification.
        for role in self.manifest['candidate']:
            entry = self.manifest['candidate'][role]
            self.manifest['candidate'][role] = self.file(entry['path'], {'synthetic_candidate_role': role})
        for key in ('circuit_readback', 'circuit_readback_receipt', 'report'):
            self.manifest[key] = self.file(self.manifest[key]['path'], {'synthetic_role': key})
        windows = {old: {'duration_ns': duration, 'clock_transitions': cycles * 2}
                   for new, old in (('clocked_idle', 'idle'), ('replacement_upload', 'replacement'), ('execution', 'execution'))
                   for case, cycles, duration in [power.WORKLOADS[new]]}
        self.manifest['waveform_audit'] = self.file(self.manifest['waveform_audit']['path'], windows)
        self.manifest['unknown_bit_audit'] = self.file(self.manifest['unknown_bit_audit']['path'],
                                                     {key: {'connected_unknown_bits': 0} for key in windows})
        self.rebind()

    def file(self, path, value):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        data = json.dumps(value).encode()
        target.write_bytes(data)
        return {'path': path, 'sha256': hashlib.sha256(data).hexdigest()}

    def rebind(self):
        self.contract['source_manifest'] = self.file(self.contract['source_manifest']['path'], self.manifest)
        self.contract['candidate'] = dict(self.manifest['candidate'], readback=self.manifest['circuit_readback'],
                                          readback_receipt=self.manifest['circuit_readback_receipt'])

    def result(self):
        return power.assess(self.contract, self.root)

    def supplied_request(self):
        values = {
            'parent_geometry': {'ownership': 'synthetic parent', 'contacts': [
                {'rail': rail, 'layer': 'TopMetal1', 'x_um': 10, 'y_um': y,
                 'width_um': 1, 'height_um': 1} for rail, y in [('VPWR', 10), ('VGND', 20)]]},
            'source_voltage': {'reference_point': 'synthetic contact boundary', 'minimum_v': 1.2, 'maximum_v': 1.25},
            'external_impedance': {'interpretation': 'ohm_per_resolved_source_node',
                                   'vpwr_ohm': 1, 'vgnd_ohm': 1, 'return_path': 'synthetic return'},
            'operating_envelope': {'temperature_min_c': 25, 'temperature_max_c': 25,
                                   'clock_period_ns': 20, 'program_scope': 'synthetic bounded domain'},
            'activity_envelope': {'total_power_upper_bound_mw': 10, 'method': 'synthetic bound',
                                  'program_scope': 'synthetic bounded domain', 'supported_modes': sorted(power.MODES),
                                  'includes_physical_glitches': True, 'includes_macro_energy': True},
            'supported_local_supply': {'minimum_v': 1.08, 'maximum_v': 1.32,
                                       'temperature_min_c': 25, 'temperature_max_c': 25,
                                       'fast_pair_compatibility': 'supported_pair'},
            'transient_allowance': {'loss_mv': 5, 'method': 'synthetic bound', 'scope': 'synthetic operating domain'},
            'analysis_conditions': {'model_voltage_v': 1.2, 'logic_temperature_c': 25,
                                    'sram_temperature_c': 25, 'parasitic_corner': 'nom'},
        }
        for name, value in values.items():
            self.contract['requirements'][name].update(status='supplied', value=value,
                evidence=self.file('external/' + name + '.json', {'synthetic_input': value}))

    def value(self, name):
        return self.contract['requirements'][name]['value']

    def test_missing_inputs_are_incomplete_not_zero(self):
        result = self.result()
        self.assertEqual(result['status'], 'incomplete_request')
        self.assertEqual({row['id'] for row in result['missing_inputs']}, set(power.REQUIREMENTS))
        self.assertIsNone(result['available_static_rail_loss_budget_mv'])
        self.assertFalse(result['qualification'])

    def test_supplied_inputs_make_request_ready_but_never_qualified(self):
        self.supplied_request()
        result = self.result()
        self.assertTrue(result['ready_for_scoped_analysis'])
        self.assertAlmostEqual(result['available_static_rail_loss_budget_mv'], 115)
        self.assertFalse(result['qualification'])
        self.assertFalse(result['A_accepted'])
        self.assertEqual(result['existing_evidence'], 'diagnostic')

    def test_voltage_arithmetic_subtracts_both_rails_and_transient_in_mv(self):
        result = power.voltage_budget(1.2, 18.2947, 18.3254, 5, 1.08)
        self.assertAlmostEqual(result['conservative_loss_mv'], 41.6201)
        self.assertAlmostEqual(result['conservative_local_min_v'], 1.1583799)
        self.assertAlmostEqual(result['margin_v'], 0.0783799)
        self.assertFalse(result['qualification'])

    def test_source_at_library_minimum_has_no_positive_drop_budget(self):
        self.supplied_request()
        self.value('source_voltage')['minimum_v'] = 1.08
        self.value('analysis_conditions')['model_voltage_v'] = 1.08
        self.value('transient_allowance')['loss_mv'] = 0
        result = self.result()
        self.assertFalse(result['ready_for_scoped_analysis'])
        self.assertIn('no_positive_static_rail_loss_budget', result['stop_conditions'])
        self.assertAlmostEqual(result['available_static_rail_loss_budget_mv'], 0)

    def test_source_oversupply_cannot_rely_on_rail_drop(self):
        self.supplied_request()
        self.value('source_voltage')['maximum_v'] = 1.33
        result = self.result()
        self.assertFalse(result['ready_for_scoped_analysis'])
        self.assertIn('source_maximum_exceeds_supported_local_supply', result['stop_conditions'])
        self.assertGreater(result['available_static_rail_loss_budget_mv'], 0)

    def test_nominal_voltage_cannot_cover_a_lower_source_minimum(self):
        self.supplied_request()
        self.value('source_voltage')['minimum_v'] = 1.08
        with self.assertRaisesRegex(ValueError, 'nominal loss cannot qualify'):
            self.result()

    def test_mixed_temperature_pair_requires_supported_bound(self):
        self.supplied_request()
        self.value('operating_envelope').update(temperature_min_c=-55, temperature_max_c=-40)
        self.value('supported_local_supply').update(temperature_min_c=-55, temperature_max_c=-40)
        self.value('analysis_conditions').update(logic_temperature_c=-40, sram_temperature_c=-55)
        with self.assertRaisesRegex(ValueError, 'Mixed-temperature'):
            self.result()
        self.value('supported_local_supply')['fast_pair_compatibility'] = 'supported_bound'
        self.assertTrue(self.result()['ready_for_scoped_analysis'])
        self.assertFalse(self.result()['qualification'])

    def test_temperature_and_program_envelopes_must_be_covered(self):
        self.supplied_request()
        self.value('operating_envelope')['temperature_max_c'] = 125
        with self.assertRaisesRegex(ValueError, 'temperature envelope'):
            self.result()
        self.value('operating_envelope')['temperature_max_c'] = 25
        self.value('activity_envelope')['program_scope'] = 'different domain'
        with self.assertRaisesRegex(ValueError, 'Program scopes disagree'):
            self.result()

    def test_missing_glitch_or_macro_energy_bound_blocks_analysis_readiness(self):
        self.supplied_request()
        self.value('activity_envelope')['includes_physical_glitches'] = False
        self.value('activity_envelope')['includes_macro_energy'] = False
        result = self.result()
        self.assertFalse(result['ready_for_scoped_analysis'])
        self.assertEqual(set(result['stop_conditions']), {
            'activity_envelope.includes_physical_glitches', 'activity_envelope.includes_macro_energy'})

    def test_required_mode_and_both_supply_rails_cannot_be_omitted(self):
        self.supplied_request()
        self.value('parent_geometry')['contacts'].pop()
        with self.assertRaisesRegex(ValueError, 'both rails'):
            self.result()
        self.supplied_request()
        self.value('activity_envelope')['supported_modes'].pop()
        with self.assertRaisesRegex(ValueError, 'each permitted mode'):
            self.result()

    def test_source_evidence_and_candidate_identity_cannot_be_rewritten(self):
        self.contract['candidate']['odb']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'disconnected'):
            self.result()
        self.rebind()
        (self.root / self.contract['source_manifest']['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError, 'Changed evidence'):
            self.result()

    def test_missing_retained_artifact_is_reported_changed_artifact_refuses(self):
        target = self.root / self.contract['candidate']['odb']['path']
        original = target.read_bytes()
        target.unlink()
        result = self.result()
        self.assertFalse(result['ready_for_scoped_analysis'])
        self.assertIn('candidate.odb', {row['id'] for row in result['missing_inputs']})
        target.write_bytes(original + b'changed')
        with self.assertRaisesRegex(ValueError, 'Changed evidence'):
            self.result()

    def test_supplied_values_require_present_unchanged_evidence(self):
        self.supplied_request()
        evidence = self.contract['requirements']['source_voltage']['evidence']
        target = self.root / evidence['path']
        target.unlink()
        self.assertFalse(self.result()['ready_for_scoped_analysis'])
        target.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'Changed evidence'):
            self.result()

    def test_incomplete_annotation_and_unknown_connected_bits_refuse(self):
        self.manifest['measured_cases'][4]['annotated_signal_pins'] = 0
        self.rebind()
        with self.assertRaisesRegex(ValueError, 'complete workload annotation'):
            self.result()
        self.manifest['measured_cases'][4]['annotated_signal_pins'] = 38497
        self.manifest['unknown_bit_audit'] = self.file(self.manifest['unknown_bit_audit']['path'],
            {key: {'connected_unknown_bits': 1 if key == 'idle' else 0} for key in ['idle', 'replacement', 'execution']})
        self.rebind()
        with self.assertRaisesRegex(ValueError, 'Unknown connected'):
            self.result()

    def test_duplicate_nonfinite_boolean_negative_and_overflow_numbers_refuse(self):
        for data in ('{"schema":1,"schema":1}', '{"v":NaN}', '{"v":Infinity}'):
            with self.subTest(data=data), self.assertRaises(ValueError):
                power.parse_json(data)
        for value in (True, -1, float('nan'), float('inf')):
            with self.subTest(value=value), self.assertRaises(ValueError):
                power.voltage_budget(1.2, value, 0, 0)
        with self.assertRaisesRegex(ValueError, 'overflow'):
            power.voltage_budget(1.2, 1e308, 1e308, 0)

    def test_missing_fields_implicit_zero_and_unreviewed_impedance_semantics_refuse(self):
        entry = self.contract['requirements']['source_voltage']
        entry['value'] = {'minimum_v': 0}
        with self.assertRaisesRegex(ValueError, 'must remain null'):
            self.result()
        self.supplied_request()
        self.value('external_impedance')['interpretation'] = 'lumped_package_ohm'
        with self.assertRaisesRegex(ValueError, 'per resolved source node'):
            self.result()

    def test_claim_escalation_and_path_traversal_refuse(self):
        self.contract['finite_workloads'][0]['claim'] = 'all_program_bound'
        with self.assertRaisesRegex(ValueError, 'not activity bounds'):
            self.result()
        self.contract['finite_workloads'][0]['claim'] = 'finite_zero_delay_observation'
        self.contract['source_manifest']['path'] = '../escape.json'
        with self.assertRaisesRegex(ValueError, 'repository-relative'):
            self.result()

    def test_cli_readiness_exit_and_read_only_outputs(self):
        path = self.root / 'request.json'
        path.write_text(json.dumps(self.contract))
        before = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob('*') if p.is_file()}
        with contextlib.redirect_stdout(io.StringIO()) as output:
            exit_code = power.main(['--contract', str(path), '--repository', str(self.root), '--require-ready'])
        self.assertEqual(exit_code, 2)
        self.assertEqual(json.loads(output.getvalue())['status'], 'incomplete_request')
        after = {p.relative_to(self.root): p.read_bytes() for p in self.root.rglob('*') if p.is_file()}
        self.assertEqual(before, after)


if __name__ == '__main__':
    unittest.main()
