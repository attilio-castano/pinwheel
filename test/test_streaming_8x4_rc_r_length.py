"""HOST controls for the fixed R26 geometry/policies/raw rounding and failures."""
import copy
from historical_evidence import historical_evidence
import streaming_8x4_consumer_fixtures as F
from decimal import Decimal as D
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_rc_r_length as W
import streaming_8x4_rc_r_length_readback as R
G, M, C = W.G, W.M, W.C
B = ROOT / 'build/campaigns/8x4-20261022-01'
BASE = B / 'rc-consumer-semantic-preparation-01/consumer-inputs'


def synthetic():
    old = F.consumer_plan(); plan = W.math_plan(dict(old, fixture_rows=G.rows()))
    jobs = []
    for corner, policy in M.JOBS:
        values = {}; intervals = {}
        for row in G.rows():
            if row['via'] is not None: continue
            layer, length, width = row['segments'][0]; sheet = D(plan['corners'][corner]['wire_sheet_R'][layer])
            divisor = C.WIDTHS[layer] if policy == 'baseline_rules' else D(width)
            slope = sheet / divisor; total = slope * (D(length) + D(width))
            values[row['name']] = dict(R_ohm=str(total))
            intervals[row['name']] = dict(lower_ohm=str(total - D('.000001')), upper_ohm=str(total + D('.000001')))
        for row in G.rows():
            if row['via'] is None: continue
            value = sum(D(values[layer + '_L50']['R_ohm']) for layer, _, _ in row['segments'])
            value += D(plan['LEF_inventory']['explicit_vias'][row['name']]['resistance_ohm'])
            values[row['name']] = dict(R_ohm=str(value))
        absolute = C.analyze_values(plan, corner, 'retained_rules', values)
        jobs.append(dict(corner=corner, policy=policy, values=values, rounding_intervals=intervals, absolute_audit=absolute))
    return plan, jobs


class RLengthControls(unittest.TestCase):
    def setUp(self):
        self.tech = F.tech(); self.widths = F.widths()
        self.fixture, self.ndr = G.fixture(self.tech, self.widths)

    def test_exact26_geometry_and_via_exit_normalization(self):
        before, canonical = G.parse(self.fixture, self.tech, self.ndr, G.rows())
        result = G.compare(self.fixture, canonical, self.tech, self.ndr, G.rows())
        self.assertEqual((len(before['routes']), len(before['ports'])), (26, 52))
        self.assertEqual((result['segment_count'], result['named_via_count']), (31, 5))
        self.assertEqual(len(before['removed_NEW_clauses']), 5)
        self.assertFalse(result['byte_identical']); self.assertTrue(result['non_normalized_bytes_identical'])

    def test_initial_headers_ports_ndr_route_via_membership_fail_closed(self):
        for text in (self.fixture.replace('NETS 26', 'NETS 25'), self.fixture.replace('PINS 52', 'PINS 51'),
            self.fixture.replace('200000 600000', '200000 600001'), self.fixture.replace('rc_R_length', 'foreign'),
            self.fixture.replace('WIDTH 320 SPACING 210', 'WIDTH 321 SPACING 210'),
            self.fixture.replace('NEW Metal2', 'NEW Metal3', 1),
            self.fixture.replace('( 160000 60000 )', '( 160001 60000 )'),
            self.fixture.replace('DIRECTION INPUT', 'DIRECTION OUTPUT', 1), self.fixture + 'VIAS 0 ;\nEND VIAS\n'):
            with self.assertRaises(ValueError): G.compare(text, text, self.tech, self.ndr, G.rows())

    def test_local_corner_lef_changes_only_five_selected_routing_R_values(self):
        plan = F.consumer_plan()
        for corner in ('MIN', 'TYP', 'MAX'):
            sheets = plan['corners'][corner]['wire_sheet_R']; local, witness = G.local_lef(self.tech, sheets)
            self.assertEqual(G.restore_original(local), self.tech)
            self.assertEqual({n: D(r['value']) for n, r in G.resistance_fields(local).items()}, {n: D(v) for n, v in sheets.items()})
            self.assertFalse(witness['shared_PDK_modified']); self.assertTrue(witness['explicit_via_and_cut_layer_resistances_unchanged'])
            for bad in (local.replace('RESISTANCE 4.0', 'RESISTANCE 4.1'), local.replace('WIDTH\t\t0.20', 'WIDTH\t\t0.21', 1)):
                with self.assertRaises(ValueError): G.restore_original(bad)

    @historical_evidence
    def test_raw_percent_g_intervals_reopen_actual_frozen_seventeen_net_SPEF(self):
        path = B / 'rc-native-outputs/rc-consumer-semantic-01/native/MIN-retained_rules/result.spef'
        text = path.read_text(); names = {r['name'] for r in C.fixtures({'explicit_vias':{n: {'cut_layer':l} for n,l in zip(C.VIA_FIXTURES,('Via1','Via1','Via2','Via3','TopVia1'))}})}
        values = C.parse_spef(text, names); result = M.intervals(text, values)
        self.assertEqual(len(result), 17); self.assertEqual(D(result['Metal1_L100']['half_width_ohm']), D('.00005'))
        self.assertFalse(result['Metal1_L100']['physical_error_enclosure'])
        bad = copy.deepcopy(values); bad['Metal1_L100']['R_ohm'] = '1'
        with self.assertRaises(ValueError): M.intervals(text, bad)

    def test_explicit_six_digit_resistor_rounding_intervals(self):
        raw = '*D_NET wire 0\n*RES\n1 a b 100.25\n2 b c 50\n*END\n'
        values = dict(wire=dict(R_ohm='150.25', R_unit_ohm='1', edges=2))
        row = M.intervals(raw, values)['wire']
        self.assertEqual(D(row['center_ohm']), D('150.25'))
        self.assertEqual(D(row['half_width_ohm']), D('.00055'))
        self.assertTrue(row['serialization_rounding_only'])
        self.assertFalse(row['physical_error_enclosure'])
        with self.assertRaises(ValueError):
            M.intervals(raw, dict(wire=dict(R_ohm='1', R_unit_ohm='1', edges=2)))

    def test_six_call_diagnostic_can_pass_while_original_absolute_audits_fail(self):
        plan, jobs = synthetic(); result = M.measurements(plan, jobs)
        self.assertTrue(result['length_width_diagnostic_controls_passed']); self.assertFalse(result['original_17net_experiment_passed'])
        self.assertGreater(result['new_absolute_wire_failures'], 0); self.assertEqual(result['new_absolute_wire_controls'], 126)
        self.assertEqual((result['original_17net_absolute_wire_failures'], result['original_17net_via_difference_passes']), (72, 30))
        self.assertTrue(all(v['passed'] for v in result['measured_named_vias']))
        self.assertTrue(all(not w['ITF_width_aware_slope_gate_passed'] for r in result['per_job'] if r['policy'] == 'baseline_rules' for w in r['widths'] if '_wide' in w['family']))

    def test_heldout150_length_and_actual_width_scaling_fail_without_retuning(self):
        plan, jobs = synthetic(); wrong = copy.deepcopy(jobs)
        wrong[-1]['values']['Metal1_wide_L150']['R_ohm'] = str(D(wrong[-1]['values']['Metal1_wide_L150']['R_ohm']) + 1)
        result = M.measurements(plan, wrong); self.assertFalse(result['length_width_diagnostic_controls_passed'])
        rows = result['per_job'][-1]['widths']; wide = next(r for r in rows if r['family'] == 'Metal1_wide')
        self.assertFalse(wide['linearity_gate_passed'])
        wrong = copy.deepcopy(jobs)
        # The heldout interval itself must reject even when the printed centers stay linear.
        wrong[0]['rounding_intervals']['Metal1_L150'] = dict(lower_ohm='1000000', upper_ohm='1000001')
        self.assertFalse(M.measurements(plan, wrong)['per_job'][0]['widths'][0]['heldout_150um_rounding_gate_passed'])

    def test_named_via_failure_and_missing_or_reordered_call_remain_failed(self):
        plan, jobs = synthetic()
        for wrong in (jobs[:-1], list(reversed(jobs))):
            with self.assertRaises(ValueError): M.measurements(plan, wrong)
        wrong = copy.deepcopy(jobs); wrong[-1]['absolute_audit']['vias'][0]['passed'] = False
        self.assertFalse(M.measurements(plan, wrong)['length_width_diagnostic_controls_passed'])

    def test_exact_resources_and_new_policy_have_no_C_or_fullmodel_promotion(self):
        protocol = W.protocol(); self.assertEqual(protocol['seconds_per_leaf'], 30); self.assertEqual(protocol['outer_seconds'], 300)
        self.assertEqual(protocol['memory_bytes'], 2147483648); self.assertFalse(protocol['model_qualified']); self.assertFalse(protocol['capacitance_qualified'])
        self.assertEqual(protocol['jobs'], [dict(corner=c, policy=p) for c,p in M.JOBS])

    def test_raw_prefix_failure_preserves_resource_custody_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); report = dict(schema='pinwheel.streaming-8x4-rc-R-length-width-execution.v1', plan_sha256='seal', passed=False, model_qualified=False)
            (root / 'report.json').write_text(json.dumps(report)); proposal = dict(parent_semantic_proposal=dict(path='old'), output_directory=str(root))
            path = root / 'proposal.json'; path.write_text(json.dumps(proposal))
            with patch.object(W, 'verify', return_value={}), patch.object(W, 'proposal', return_value=proposal), \
                patch.object(R, 'resource_join', return_value=dict(status='failed', resource_custody_closed=True)), \
                patch.object(R, 'raw_readback', side_effect=ValueError('incomplete actual packet')):
                result = R.closeout(root, 'seal', root, root, path)
            self.assertTrue(result['resource_custody_closed']); self.assertFalse(result['measurement_packet_completed'])
            self.assertFalse(result['length_width_diagnostic_controls_passed']); self.assertFalse(result['original_17net_experiment_passed'])
            self.assertIn('incomplete', result['raw_readback']['error'])

    @historical_evidence
    def test_actual_preparation_reopens_and_generated_LEF_tamper_rejects(self):
        original = B / 'rc-r-length-width-preparation-01'; digest = W.P.sha(original / 'plan.json')
        self.assertEqual(len(W.verify(original, digest)['fixture_rows']), 26)
        with tempfile.TemporaryDirectory() as temporary:
            copied = Path(temporary) / 'prepared'; shutil.copytree(original, copied)
            self.assertTrue(W.verify(copied, digest))
            path = copied / 'MIN-local.lef'; path.write_text(path.read_text().replace('RESISTANCE RPERSQ 0.085', 'RESISTANCE RPERSQ 0.086', 1))
            with self.assertRaises(ValueError): W.verify(copied, digest)

    def test_exact_resource_failure_contract_and_input_seals(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            prep = root / 'plan.json'; prep.write_text('{"fixture": "R-resource-input"}')
            parent = root / 'parent.json'; parent.write_text('{"fixture": "parent-input"}')
            digest = W.P.sha(prep)
            producer = 'streaming_8x4_rc_r_length.py'
            plan = dict(producer_sha256={producer: W.P.sha(ROOT / 'scripts' / producer)})
            proposal = dict(argv=['fixture-worker', '--fixed-six-calls'], plan_path=str(prep), plan_sha256=digest,
                parent_semantic_proposal=dict(path=str(parent), sha256=W.P.sha(parent)))
            path = root / 'proposal.json'; path.write_text(json.dumps(proposal)); resource_path = root / 'resource.json'
            seals = {str(path.resolve()): W.P.sha(path), proposal['plan_path']: digest,
                proposal['parent_semantic_proposal']['path']: proposal['parent_semantic_proposal']['sha256']}
            seals.update({str(ROOT / 'scripts' / n): h for n,h in plan['producer_sha256'].items()})
            supervisor = W.P.sha(ROOT / 'scripts/streaming_tt_resources.py')
            resource = dict(schema='pinwheel.streaming-tt-resource-job.v1', status='failed', exit_code=2,
                argv=proposal['argv'], timeout_seconds=300, cleanup_confirmed=True, inputs_unchanged=True,
                owned_processes_remaining=[], containers_remaining=[], cleanup_errors=[], input_sha256=seals,
                supervisor_sha256=supervisor, campaign_boundary=dict(schema='pinwheel.streaming-8x4-resource-boundary.v1',
                    campaign_root=str(ROOT), campaign_kind='rc_experiment', shared_lease=dict(heavy_lock=str(ROOT / 'build/streaming-tt-resources/heavy.lock')),
                    wrapper_sha256=W.P.sha(ROOT / 'scripts/streaming_8x4_acceptance_resources.py'), inherited_supervisor_sha256=supervisor))
            for changes in ({}, {'cleanup_confirmed':False}, {'argv':['foreign']}, {'exit_code':1}, {'input_sha256':{}}):
                row = dict(resource, **changes); resource_path.write_text(json.dumps(row))
                if changes:
                    with self.assertRaises(ValueError): R.resource_join(resource_path, path, proposal, plan, dict(passed=False))
                else:
                    result = R.resource_join(resource_path, path, proposal, plan, dict(passed=False))
                    self.assertTrue(result['resource_custody_closed']); self.assertFalse(result['diagnostic_pass_claim'])


if __name__ == '__main__': unittest.main()
