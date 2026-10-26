"""HOST controls using exact captured Native before/after serialization bytes."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_rc_route_semantics as S

B = ROOT / 'build/campaigns/8x4-20261022-01'


class RouteSemanticsControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.before = (ROOT / 'test/fixtures/streaming-8x4-rc-ndr-before-20261023.def').read_text()
        cls.after = (ROOT / 'test/fixtures/streaming-8x4-rc-ndr-after-20261023.def').read_text()
        inputs = B / 'rc-consumer-ndr-preparation-01/consumer-inputs'
        cls.tech = (inputs / 'tech.lef').read_text()
        cls.rows = json.loads((inputs / 'plan.json').read_text())['fixture_rows']
        cls.witness = json.loads((inputs.parent / 'NDR-witness.json').read_text())

    def compare(self, before=None, after=None):
        return S.compare(self.before if before is None else before, self.after if after is None else after,
            self.tech, self.witness, self.rows)

    def test_actual_capture_only_five_redundant_NEWs_change(self):
        result = self.compare()
        self.assertFalse(result['byte_identical']); self.assertTrue(result['non_normalized_bytes_identical'])
        self.assertEqual(result['segment_count'], 22); self.assertEqual(result['named_via_count'], 5)
        self.assertEqual(len(result['before']['removed_NEW_clauses']), 5)
        self.assertEqual(result['after']['removed_NEW_clauses'], [])
        self.assertEqual(len(result['before']['routes']), 17); self.assertEqual(len(result['before']['ports']), 34)
        self.assertEqual(self.compare(after=self.before)['before'], self.compare(after=self.before)['after'])
        self.assertFalse(result['qualified']); self.assertTrue(result['numerical_tolerances_unchanged'])

    def test_capture_bytes_have_only_exact_artifact_exceptions(self):
        policy = json.loads((ROOT / 'tools/artifact-policy.json').read_text())
        for name in ('before', 'after'):
            path = ROOT / ('test/fixtures/streaming-8x4-rc-ndr-' + name + '-20261023.def')
            row = policy['exceptions'][str(path.relative_to(ROOT))]; data = path.read_bytes()
            self.assertEqual(row['bytes'], len(data)); self.assertEqual(row['sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(row['git_mode'], '100644')

    def test_pinned_reader_writer_sources_and_via_exit_semantics(self):
        row = S.source_evidence(B / 'rc-route-source-intake-01', B / 'rc-ndr-source-intake-01')
        self.assertEqual(row['openroad_commit'], S.N.COMMIT)
        reader = (B / 'rc-ndr-source-intake-01/definNet.cpp').read_text()
        self.assertIn('_wire_encoder.addTechVia(tech_via);', reader)
        self.assertIn('if (top == _cur_layer)', reader); self.assertIn('_cur_layer = bot;', reader)
        writer = (B / 'rc-route-source-intake-01/defout_impl.cpp').read_text()
        self.assertIn('case dbWireDecoder::TECH_VIA:', writer); self.assertIn('decode.getTechVia()', writer)
        self.assertEqual(S.via_layers(self.tech)['Via1_XX'], dict(bottom='Metal1', top='Metal2', cut_layer='Via1'))

    def test_wrong_NEW_layer_shifted_junction_or_nonvia_NEW_reject(self):
        for before in (self.before.replace('NEW Metal2 ( 60000 260000 )', 'NEW Metal3 ( 60000 260000 )'),
            self.before.replace('NEW Metal2 ( 60000 260000 )', 'NEW Metal2 ( 60001 260000 )'),
            self.before.replace('NEW Metal2 ( 60000 260000 )', 'NEW Metal2 ( * 260000 )'),
            self.before.replace('( 110000 * ) ;', 'NEW Metal1 ( 10000 40000 ) ( 110000 * ) ;', 1)):
            with self.assertRaises(ValueError): self.compare(before=before)

    def test_segment_layer_width_via_and_NDR_changes_reject_even_if_both_match(self):
        mutations = [lambda x:x.replace('( 110000 * ) ;', '( 110001 * ) ;', 1),
            lambda x:x.replace('Via1_XX ( 110000 * )', 'Via1_DC1B ( 110000 * )'),
            lambda x:x.replace('Metal1 WIDTH 320 SPACING 210', 'Metal1 WIDTH 321 SPACING 210'),
            lambda x:x.replace('Metal1 WIDTH 320 SPACING 210', 'Metal1 WIDTH 320 SPACING 211'),
            lambda x:x.replace('+ NONDEFAULTRULE WIDE_Metal1', '+ NONDEFAULTRULE WIDE_Metal2'),
            lambda x:x.replace('+ ROUTED Metal3', '+ ROUTED Metal4', 1)]
        for mutation in mutations:
            wrong = mutation(self.after)
            with self.assertRaises(ValueError): self.compare(before=wrong, after=wrong)

    def test_all_nonroute_bytes_and_ports_are_fixed(self):
        for after in (self.after.replace('DESIGN rc_consumer', 'DESIGN other'),
            self.after.replace('DIEAREA ( 0 0 )', 'DIEAREA ( 1 0 )'),
            self.after.replace('DIRECTION INPUT', 'DIRECTION OUTPUT', 1),
            self.after.replace('( 10000 40000 ) N', '( 10001 40000 ) N', 1),
            self.after.replace('VERSION 5.8 ;', 'VERSION  5.8 ;')):
            with self.assertRaises(ValueError): self.compare(after=after)

    def test_missing_duplicate_or_unsupported_routes_reject(self):
        for after in (self.after.replace('    - Metal1_L50 ', '    - Metal1_L100 '),
            self.after.replace('NETS 17 ;', 'NETS 16 ;'),
            self.after.replace('Via1_XX ( 110000 * )', 'Via1_XX N ( 110000 * )'),
            self.after.replace('Via1_XX ( 110000 * )', 'Via1_XX Via1_XX ( 110000 * )'),
            self.after.replace('( 60000 * ) Via2_XX', '( 60000 * 100 ) Via2_XX')):
            with self.assertRaises(ValueError): self.compare(after=after)

    def test_changed_technology_or_selected_fixture_authority_reject(self):
        with self.assertRaises(ValueError): S.compare(self.before, self.after, self.tech + '\n', self.witness, self.rows)
        wrong = copy.deepcopy(self.rows); wrong[0]['segments'][0][1] = '51'
        with self.assertRaises(ValueError): S.compare(self.before, self.after, self.tech, self.witness, wrong)


if __name__ == '__main__': unittest.main()
