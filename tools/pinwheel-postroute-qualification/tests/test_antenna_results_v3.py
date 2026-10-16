"""Meaningful host negatives using immutable actual native01 output, no CAD."""
from pathlib import Path
import copy
import json
import unittest
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from antenna_results_v3 import parse_native, validate_reference

REPOSITORY = next(p for p in Path(__file__).resolve().parents if (p / 'tools/physical-toolchain.json').is_file())
SOURCE = REPOSITORY / 'build/physical/tt-overnight-qualification-plan-01/p2-C14-v1-antenna-01'


class ActualNativeControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not (SOURCE / 'antenna-native.log').exists():
            raise unittest.SkipTest('Retained actual C14 diagnostic is not available in this checkout')
        cls.text = (SOURCE / 'antenna-native.log').read_text()
        cls.metrics = json.loads((SOURCE / 'antenna-native-metrics.json').read_text())
        cls.coverage = json.loads((SOURCE / 'antenna-model-coverage.json').read_text())
        cls.inventory = json.loads((SOURCE / 'input/inventory.json').read_text())

    def call(self, text=None, metrics=None, coverage=None):
        return parse_native(text if text is not None else self.text,
            metrics if metrics is not None else self.metrics,
            coverage if coverage is not None else self.coverage, self.inventory)

    def test_actual_missing_optional_metrics_recovered(self):
        result = self.call()
        self.assertEqual((result['native_net_violation_count'], result['native_pin_violation_count']), (124, 135))
        self.assertEqual(result['violated_input_contacts_by_class'], {'standard_cell_input': 126, 'SRAM_input': 9})
        self.assertEqual(result['events_by_layer'], {'Metal3': 135})
        self.assertIn('absent', result['optional_metric_telemetry'])

    def test_present_metrics_must_agree(self):
        metrics = dict(self.metrics, antenna__violating__nets=124, antenna__violating__pins=135)
        self.assertIn('present', self.call(metrics=metrics)['optional_metric_telemetry'])

    def test_missing_final_count(self):
        with self.assertRaises(ValueError): self.call(text=self.text.replace('[INFO ANT-0002] Found 124 net violations.', ''))

    def test_duplicate_final_count(self):
        with self.assertRaises(ValueError): self.call(text=self.text + '\n[INFO ANT-0002] Found 124 net violations.\n')

    def test_partial_report_body(self):
        with self.assertRaises(ValueError): self.call(text=self.text.replace('(VIOLATED)', '', 1))

    def test_incorrect_summary(self):
        with self.assertRaises(ValueError): self.call(text=self.text.replace('Found 135 pin violations.', 'Found 134 pin violations.'))

    def test_metric_disagreement(self):
        with self.assertRaises(ValueError): self.call(metrics=dict(self.metrics, antenna__violating__nets=124, antenna__violating__pins=0))

    def test_partial_metric_telemetry(self):
        with self.assertRaises(ValueError): self.call(metrics=dict(self.metrics, antenna__violating__nets=124))

    def test_wrong_metric_type(self):
        with self.assertRaises(ValueError): self.call(metrics=dict(self.metrics, antenna__violating__nets='124', antenna__violating__pins=135))

    def test_native_error(self):
        with self.assertRaises(ValueError): self.call(text=self.text + '\n[ERROR ANT-0099] source error\n')

    def test_unknown_source_net(self):
        with self.assertRaises(ValueError): self.call(text=self.text.replace('Net: _03605_', 'Net: PW_FAKE_NET', 1))

    def test_unknown_input_pin(self):
        with self.assertRaises(ValueError): self.call(text=self.text.replace('_20161_/B1', '_20161_/PW_FAKE_PIN', 1))

    def test_empty_route_coverage(self):
        coverage=copy.deepcopy(self.coverage);coverage['relevant_consumed_net_count']=0
        with self.assertRaises(ValueError):self.call(coverage=coverage)

    def test_empty_gate_coverage(self):
        coverage=copy.deepcopy(self.coverage);coverage['relevant_connected_INPUT_ITerm_count']=0;coverage['native_positive_gate_area_contact_count']=0
        with self.assertRaises(ValueError):self.call(coverage=coverage)

    def test_missing_input_model(self):
        coverage=copy.deepcopy(self.coverage);next(iter(coverage['master_gate_models'].values()))['gate_areas']=[]
        with self.assertRaises(ValueError):self.call(coverage=coverage)

    def test_missing_layer_rules(self):
        coverage=copy.deepcopy(self.coverage);coverage['used_layers_without_positive_native_scalar_rule']=['Via3']
        with self.assertRaises(ValueError):self.call(coverage=coverage)

    def test_nondetailed_route(self):
        coverage=copy.deepcopy(self.coverage);coverage['all_have_actual_ROUTED_detailed_wires']=False
        with self.assertRaises(ValueError):self.call(coverage=coverage)

    def test_missing_whole_model_map_rejected(self):
        coverage=copy.deepcopy(self.coverage);coverage['master_gate_models']={}
        with self.assertRaises(ValueError): self.call(coverage=coverage)

    def test_model_map_must_cover_actual_input(self):
        coverage=copy.deepcopy(self.coverage);coverage['master_gate_models'].pop(next(iter(coverage['master_gate_models'])))
        with self.assertRaises(ValueError): self.call(coverage=coverage)

    def test_forged_contact_denominator_rejected(self):
        coverage=copy.deepcopy(self.coverage)
        coverage['relevant_connected_INPUT_ITerm_count']-=1
        coverage['native_positive_gate_area_contact_count']-=1
        with self.assertRaises(ValueError): self.call(coverage=coverage)

    def test_forged_consumed_net_denominator_rejected(self):
        coverage=copy.deepcopy(self.coverage);coverage['relevant_consumed_net_count']-=1
        with self.assertRaises(ValueError): self.call(coverage=coverage)

    def test_empty_used_layer_denominator_rejected(self):
        coverage=copy.deepcopy(self.coverage);coverage['used_metal_and_via_cut_layers']=[]
        with self.assertRaises(ValueError): self.call(coverage=coverage)

    def test_claimed_rule_coverage_requires_actual_rule(self):
        coverage=copy.deepcopy(self.coverage);coverage['native_technology_rules'].pop('Metal3')
        with self.assertRaises(ValueError): self.call(coverage=coverage)

    def test_claimed_rule_coverage_rejects_empty_scalar_model(self):
        coverage=copy.deepcopy(self.coverage);coverage['native_technology_rules']['Metal3']['scalar_ratios']={}
        with self.assertRaises(ValueError): self.call(coverage=coverage)

    def test_reference_free_new_source_is_explicit(self):
        self.assertFalse(validate_reference(self.call(), {}))

    def test_reference_same_complete_result_passes(self):
        result=self.call()
        keys=('native_net_violation_count','native_pin_violation_count','semantic_violation_signature_sha256')
        self.assertTrue(validate_reference(result, {k:result[k] for k in keys}))

    def test_partial_reference_rejected(self):
        with self.assertRaises(ValueError): validate_reference(self.call(), {'native_net_violation_count':124})

    def test_same_count_different_violation_set_rejected(self):
        result=self.call()
        expected={k:result[k] for k in ('native_net_violation_count','native_pin_violation_count','semantic_violation_signature_sha256')}
        expected['semantic_violation_signature_sha256']='0'*64
        with self.assertRaises(ValueError): validate_reference(result, expected)

    def test_exact_actual_semantic_signature_retained(self):
        self.assertEqual(self.call()['semantic_violation_signature_sha256'],
            '93a282fee7b195b9e201aaf10f8b282302b8bf70d750337d0c8b589b30222229')

    def test_nonviolating_load_sections_are_not_violations(self):
        result=self.call()
        self.assertEqual(result['all_reported_INPUT_pin_sections'],418)
        self.assertEqual(result['reported_nonviolating_INPUT_pin_sections'],283)

    def test_missing_nonviolating_input_section_rejected(self):
        with self.assertRaises(ValueError):
            self.call(text=self.text.replace('fanout2911/A', 'PW_UNKNOWN/A',1))


class FiniteNativeContract(unittest.TestCase):
    """Always available even when ignored historical build outputs are absent."""
    def setUp(self):
        self.inventory={'nets':{'n':{'sig_type':'SIGNAL','ports':['in'],
            'terminals':[['U','A','INPUT'],['V','A','INPUT']]}},
            'instances':{name:{'master':'BUF','macro':False,'terminals':[['A','n','INPUT']]} for name in ['U','V']}}
        self.coverage={'all_have_actual_ROUTED_detailed_wires':True,'relevant_consumed_net_count':1,
            'all_input_gate_area_and_used_layer_rule_coverage_complete':True,
            'relevant_connected_INPUT_ITerm_count':2,'native_positive_gate_area_contact_count':2,
            'uncovered_INPUT_contacts':[],'used_layers_without_positive_native_scalar_rule':[],
            'used_metal_and_via_cut_layers':['Metal3'],
            'native_technology_rules':{'Metal3':{'has_native_rule':True,'positive_scalar_rule':True,
                'query_errors':[],'scalar_ratios':{'getCAR':200.0}}},
            'master_gate_models':{'BUF/A':{'has_native_model':True,'positive_gate_area':True,
                'query_error':None,'gate_areas':[[0.25,None]]}}}
        self.text='''Net: n
 Pin: U/A (BUF)
 Layer: Metal3
 Cumulative area ratio: 300.0
 Required ratio: 200.0 (Cumulative area) (VIOLATED)
 Pin: V/A (BUF)
 Layer: Metal3
 Cumulative area ratio: 100.0
 Required ratio: 200.0 (Cumulative area)
[INFO ANT-0002] Found 1 net violations.
[INFO ANT-0001] Found 1 pin violations.
'''

    def call(self,text=None):
        return parse_native(self.text if text is None else text,{'flow__errors__count':0},self.coverage,self.inventory)

    def test_positive_violation_with_nonviolating_load(self):
        result=self.call()
        self.assertEqual(result['native_pin_violation_count'],1)
        self.assertEqual(result['reported_nonviolating_INPUT_pin_sections'],1)

    def test_complete_zero_count_is_numeric_only(self):
        result=self.call('[INFO ANT-0002] Found 0 net violations.\n[INFO ANT-0001] Found 0 pin violations.\n')
        self.assertEqual(result['native_pin_violation_count'],0)
        self.assertEqual(result['events'],[])
        self.assertNotIn('antenna_pass_qualified',result)

    def test_missing_nonviolating_load_rejected(self):
        with self.assertRaisesRegex(ValueError,'INPUT-pin sections'):
            self.call(self.text.replace(' Pin: V/A (BUF)\n',''))

    def test_nonfinite_native_rule_rejected(self):
        self.coverage['native_technology_rules']['Metal3']['scalar_ratios']={'getCAR':float('nan')}
        with self.assertRaises(ValueError):self.call()

    def test_duplicate_report_pin_rejected(self):
        with self.assertRaises(ValueError):self.call(self.text.replace(' Pin: V/A (BUF)',' Pin: U/A (BUF)'))

    def test_unscoped_violation_rejected(self):
        with self.assertRaises(ValueError):self.call(self.text.replace(' Layer: Metal3\n','',1))

    def test_multiple_layers_and_ratio_events_count_one_native_input(self):
        self.coverage['used_metal_and_via_cut_layers'].append('Metal2')
        self.coverage['native_technology_rules']['Metal2']=copy.deepcopy(self.coverage['native_technology_rules']['Metal3'])
        text=self.text.replace(' Layer: Metal3\n Cumulative area ratio: 300.0\n Required ratio: 200.0 (Cumulative area) (VIOLATED)',
            ''' Layer: Metal2
 Cumulative area ratio: 300.0
 Required ratio: 200.0 (Cumulative area) (VIOLATED)
 Layer: Metal3
 Partial area ratio: 300.0
 Required ratio: 200.0 (Gate area) (VIOLATED)
 Partial area ratio: 400.0
 Required ratio: 200.0 (Side area) (VIOLATED)
 Cumulative area ratio: 500.0
 Required ratio: 200.0 (Cumulative side area) (VIOLATED)''',1)
        result=self.call(text)
        self.assertEqual(result['detailed_ratio_violation_events'],4)
        self.assertEqual(result['distinct_detailed_violated_net_pin_pairs'],1)
        self.assertEqual(result['native_pin_violation_count'],1)
        self.assertEqual(result['events_by_layer'],{'Metal2':1,'Metal3':3})

    def test_native_strict_violation_can_round_to_equal_displayed_ratio(self):
        result=self.call(self.text.replace('Cumulative area ratio: 300.0','Cumulative area ratio: 200.0',1))
        self.assertEqual(result['native_violations_with_equal_rounded_ratio_and_limit'],1)

    def test_printed_below_limit_violation_is_not_admitted(self):
        with self.assertRaises(ValueError):
            self.call(self.text.replace('Cumulative area ratio: 300.0','Cumulative area ratio: 199.0',1))


if __name__ == '__main__': unittest.main()

