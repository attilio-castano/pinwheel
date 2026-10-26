"""Negative controls for final-artifact claims and campaign time boundaries."""
import copy
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('streaming_8x4_acceptance', ROOT / 'scripts/streaming_8x4_acceptance.py')
A = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(A)
TARGET = 'a' * 64
SCHEDULE = dict(start='2026-10-22T21:00:35Z', candidate_cutoff='2026-10-23T03:00:35Z',
                rc_experiment_cutoff='2026-10-23T05:00:35Z', heavy_cutoff='2026-10-23T08:00:35Z',
                hard_deadline='2026-10-23T09:00:35Z')


class AcceptanceTests(unittest.TestCase):
    def packet(self):
        return dict(schema=A.INPUT_SCHEMA, candidate=dict(allocation='8x4', semantic_state_bits=6039,
                    clock_period_ns=20, capacity=copy.deepcopy(A.CAPACITY), source_artifact_sha256='e' * 64,
                    template_sha256='f' * 64,
                    final_odb_sha256=TARGET), gates={name: dict(status='not_run') for name in A.GATES})

    def record(self, name, evidence):
        return dict(status='pass', scope=A.GATES[name], complete=True, target_odb_sha256=TARGET,
                    evidence=evidence, violations=0)

    def evidence(self, temporary):
        path = Path(temporary) / 'receipt.json'
        path.write_bytes(b'closed evidence fixture')
        return [dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())]

    def model(self, evidence):
        result = self.record('extraction_model', evidence)
        result.update(model_sha256='c' * 64, technology_lef_sha256='e' * 64,
                      process_stack_sha256='f' * 64, consumer_tool_sha256='a' * 64,
                      qualification_report_sha256=evidence[0]['sha256'], declared_corners=['slow'],
                      corner_definitions={'slow': 'b' * 64}, coverage={})
        for name in A.MODEL_COVERAGE:
            result['coverage'][name] = dict(coverage_complete=True, declared_cases=['case-1'],
                executed_cases=['case-1'], independent_reference_sha256='f' * 64, protocol_sha256='e' * 64,
                relative_tolerance=.1, max_relative_error=.02, protocol_predeclared=True)
        return result

    def test_open_packet_cannot_inherit_prephysical_proof_or_nominal_timing(self):
        packet = self.packet()
        packet['milestones'] = dict(prephysical_correspondence=True, nominal_timing=True, source_tests=True)
        result = A.summarize(packet)
        self.assertFalse(result['tapeout_ready'])
        self.assertEqual(len(result['remaining_gates']), len(A.GATES))

    def test_final_route_requires_complete_connectivity_same_target_and_unchanged_evidence(self):
        with tempfile.TemporaryDirectory() as temporary:
            packet = self.packet()
            record = self.record('route', self.evidence(temporary))
            record['connectivity_complete'] = True
            packet['gates']['route'] = record
            self.assertEqual(A.summarize(packet)['gate_status']['route'], 'pass')
            for key, value in [('target_odb_sha256', 'b' * 64), ('complete', False),
                               ('violations', 1), ('violations', False), ('connectivity_complete', False)]:
                altered = copy.deepcopy(packet)
                altered['gates']['route'][key] = value
                with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                    A.summarize(altered)
            Path(record['evidence'][0]['path']).write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'Evidence bytes changed'):
                A.summarize(packet)

    def test_nominal_scope_cannot_be_promoted_to_extracted_timing(self):
        with tempfile.TemporaryDirectory() as temporary:
            packet = self.packet()
            evidence = self.evidence(temporary)
            record = self.record('extracted_timing', evidence)
            record.update(spef_sha256='b' * 64, rc_model_sha256='c' * 64,
                          rc_qualification_sha256=evidence[0]['sha256'], annotation_complete=True,
                          declared_corners=['slow'], corners=[dict(name='slow', qualified_rc_corner=True,
                            setup_violations=0, hold_violations=0, slew_violations=0,
                            capacitance_violations=0, fanout_violations=0)])
            packet['gates']['extracted_timing'] = record
            packet['gates']['extraction_model'] = self.model(evidence)
            A.summarize(packet)
            for alter in ('nominal_scope', 'unqualified_corner', 'missing_corner', 'fanout_violation'):
                changed = copy.deepcopy(packet)
                r = changed['gates']['extracted_timing']
                if alter == 'nominal_scope': r['scope'] = 'nominal_rc_estimate'
                if alter == 'unqualified_corner': r['corners'][0]['qualified_rc_corner'] = False
                if alter == 'missing_corner': r['declared_corners'].append('fast')
                if alter == 'fanout_violation': r['corners'][0]['fanout_violations'] = 1
                with self.subTest(alter=alter), self.assertRaises(ValueError): A.summarize(changed)

    def test_point_pilot_and_missing_reference_or_corner_cannot_qualify_full_model(self):
        with tempfile.TemporaryDirectory() as temporary:
            packet = self.packet()
            packet['gates']['extraction_model'] = self.model(self.evidence(temporary))
            A.summarize(packet)
            for mutation in ('pilot', 'reference', 'tolerance', 'corner', 'qualification_hash', 'missing_case'):
                altered = copy.deepcopy(packet)
                r = altered['gates']['extraction_model']
                if mutation == 'pilot': r['coverage'] = {'ground_capacitance': r['coverage']['ground_capacitance']}
                if mutation == 'reference': r['coverage']['via_resistance']['independent_reference_sha256'] = None
                if mutation == 'tolerance': r['coverage']['resistance']['max_relative_error'] = .2
                if mutation == 'corner': r['corner_definitions'] = {}
                if mutation == 'qualification_hash': r['qualification_report_sha256'] = 'b' * 64
                if mutation == 'missing_case': r['coverage']['layer_coverage']['declared_cases'].append('unexecuted')
                with self.subTest(mutation=mutation), self.assertRaises(ValueError): A.summarize(altered)

    def test_full_state_count_alone_and_skipped_lvs_are_insufficient(self):
        with tempfile.TemporaryDirectory() as temporary:
            packet = self.packet()
            record = self.record('final_correspondence', self.evidence(temporary))
            record.update(semantic_state_bits=6039, actual_state_bits=6039)
            packet['gates']['final_correspondence'] = record
            with self.assertRaisesRegex(ValueError, 'coverage'): A.summarize(packet)
            packet = self.packet()
            record = self.record('lvs', self.evidence(temporary))
            record.update(top_matched=True, skipped_circuits=1)
            packet['gates']['lvs'] = record
            with self.assertRaisesRegex(ValueError, 'skipped'): A.summarize(packet)

    def test_boundaries_close_admission_but_preserve_frozen_validation_only_to_heavy_cut(self):
        self.assertEqual(A.job_window('candidate_cad', SCHEDULE, '2026-10-23T02:59:35Z', 120)['timeout_seconds'], 40)
        for kind, now in [('candidate_cad', '2026-10-23T03:00:35Z'),
                          ('rc_experiment', '2026-10-23T05:00:35Z')]:
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, 'admission closed'):
                A.job_window(kind, SCHEDULE, now, 120)
        result = A.job_window('fixed_cad', SCHEDULE, '2026-10-23T07:59:35Z', 600,
                              frozen_parent_sha256=TARGET)
        self.assertEqual(result['timeout_seconds'], 40)
        with self.assertRaisesRegex(ValueError, 'cutoff'):
            A.job_window('fixed_cad', SCHEDULE, '2026-10-23T08:00:35Z', 600, frozen_parent_sha256=TARGET)
        with self.assertRaisesRegex(ValueError, 'frozen parent'):
            A.job_window('proof', SCHEDULE, '2026-10-23T06:00:00Z', 120)
        self.assertTrue(A.job_window('host_closeout', SCHEDULE, '2026-10-23T08:30:00Z', 120)['root_go_required'])

    def test_schedule_refuses_implicit_boundaries_naive_time_and_overlong_campaign(self):
        for changed in (dict(SCHEDULE, hard_deadline='2026-10-23T10:00:35Z'),
                        dict(SCHEDULE, heavy_cutoff='2026-10-23T08:50:00Z'),
                        dict(SCHEDULE, candidate_cutoff='2026-10-23T03:00:00')):
            with self.subTest(changed=changed), self.assertRaises(ValueError): A.schedule_values(changed)
        with self.assertRaises(ValueError): A.schedule_values({'hard_deadline': SCHEDULE['hard_deadline']})

    def test_shared_lock_uses_explicit_root_and_never_module_runtime_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            self.assertEqual(A.shared_lease_paths(temporary)['heavy_lock'],
                             str(Path(temporary).resolve() / 'build/streaming-tt-resources/heavy.lock'))
        with self.assertRaisesRegex(ValueError, 'explicit and absolute'): A.shared_lease_paths('.')


if __name__ == '__main__':
    unittest.main()
