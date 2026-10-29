import copy
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('consumer_readback', Path(__file__).resolve().parents[1] / 'scripts/streaming_8x4_rc_consumer_readback.py')
R = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(R)


def fixture():
    rows = [{'name': metal + '_L' + length, 'via': None} for metal in R.C.P.METALS for length in ('50', '100')]
    rows += [{'name': m + '_wide_L100', 'via': None} for m in ('Metal1', 'Metal2')]
    rows += [{'name': n, 'via': n} for n in R.C.VIA_FIXTURES]
    jobs = []
    for corner in ('MIN', 'TYP', 'MAX'):
        for policy in R.C.POLICIES:
            jobs.append({'corner': corner, 'policy': policy, 'analysis': {
                'wires': [{'name': r['name'], 'passed': '_wide_' not in r['name']} for r in rows if r['via'] is None],
                'vias': [{'name': n, 'passed': True} for n in R.C.VIA_FIXTURES]}})
    return {'fixture_rows': rows}, jobs


class ReadbackTests(unittest.TestCase):
    def test_width_failure_remains_visible_when_via_component_passes(self):
        plan, jobs = fixture(); result = R.component_summary(plan, jobs)
        self.assertTrue(result['via_corner_consumer_arithmetic_passed'])
        self.assertFalse(result['full_consumer_experiment_passed'])
        self.assertFalse(result['all_width_wire_controls_passed'])
        self.assertFalse(result['model_qualified'])

    def test_via_claim_requires_default_width_wire_controls(self):
        plan, jobs = fixture(); jobs[0]['analysis']['wires'][0]['passed'] = False
        self.assertFalse(R.component_summary(plan, jobs)['via_corner_consumer_arithmetic_passed'])

    def test_missing_policy_or_via_name_cannot_form_component_pass(self):
        plan, jobs = fixture()
        with self.assertRaises(ValueError):
            R.component_summary(plan, jobs[:-1])
        jobs[0]['analysis']['vias'].pop()
        with self.assertRaises(ValueError):
            R.component_summary(plan, jobs)

    def test_full_numeric_pass_still_does_not_qualify_model(self):
        plan, jobs = fixture()
        for j in jobs:
            for r in j['analysis']['wires']:
                r['passed'] = True
        result = R.component_summary(plan, jobs)
        self.assertTrue(result['full_consumer_experiment_passed'])
        self.assertFalse(result['model_qualified'])
        self.assertFalse(result['generated_dbVia_coverage'])


if __name__ == '__main__':
    unittest.main()
