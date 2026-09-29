from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_distribution_acceptance import COUNTS, qualify_candidate


def fixture():
    record = lambda n,d:dict(net=n, driver=d, consumers=['q/D'], ports=[], families=['data'])
    before = dict(source_database_sha256='source', scope={'owner':'q'}, connections=[record('n','d/X')])
    after = dict(source_database_sha256='candidate', scope=before['scope'],
                 connections=[record('n','b/X'),record('branch','d/X')])
    plan = dict(source_database={'sha256':'source'}, operations=[dict(net='n',new_net='branch')])
    contract = dict(source_database_sha256='source', scope=before['scope'], selected_nets=['n'],
        reserve_fraction=.2, max_added_area_fraction=.003,
        timing_floors_ns={c:dict(setup=.9,hold=.09) for c in ['fast','slow']})
    def measured(r):
        return dict(drivers=1,loads=1,capacitance=dict(pin=r['driver'],limit=.4,actual=.1,slack=.3,verdict='MET'),
            slew=dict(pin='q/D',limit=.5,actual=.2,slack=.3,verdict='MET'),
            fanout=dict(pin=r['driver'],limit=10.,actual=1.,slack=9.,verdict='MET'),
            paths={k:dict(slack_ns=.1,verdict='MET') for k in ['min','max']})
    measurements={c:{r['net']:measured(r) for r in after['connections']} for c in ['fast','slow']}
    timing={c:dict({k:0 for k in COUNTS},timing__setup__ws=1.,timing__hold__ws=.1) for c in ['fast','slow']}
    return [contract,before,after,plan,measurements,timing,1000.,1002.]


class Acceptance(unittest.TestCase):
    def test_new_branch_is_included_in_every_corner(self):
        r=qualify_candidate(*fixture())
        self.assertTrue(r['quantitative_gates_passed'])
        self.assertEqual(r['counts'],{'within_trial_reserve':2})
        self.assertEqual(r['connection_corner_records'],4)
        self.assertEqual(r['min_max_path_summaries'],8)

    def test_missing_or_duplicate_inventory_is_rejected(self):
        changes=[lambda a:a[2]['connections'].pop(),lambda a:a[1]['connections'].append(a[1]['connections'][0]),
                 lambda a:a[4]['slow'].pop('branch'),lambda a:a[4].pop('fast'),
                 lambda a:a[5].pop('slow'),lambda a:a[3]['operations'].append(a[3]['operations'][0])]
        for change in changes:
            a=fixture();change(a)
            with self.subTest(change=change),self.assertRaises(ValueError):qualify_candidate(*a)

    def test_changed_source_scope_driver_or_load_is_rejected(self):
        for change in [lambda a:a[2].update(scope={}),lambda a:a[1].update(source_database_sha256='wrong'),
                       lambda a:a[4]['fast']['n'].update(loads=2),
                       lambda a:a[4]['slow']['branch']['capacitance'].update(pin='wrong/X'),
                       lambda a:a[4]['slow']['branch']['slew'].update(pin='wrong/D')]:
            a=fixture();change(a)
            with self.subTest(change=change),self.assertRaises(ValueError):qualify_candidate(*a)

    def test_passing_added_branch_below_reserve_fails_saved_budget(self):
        a=fixture();a[4]['slow']['branch']['slew'].update(actual=.45,slack=.05)
        r=qualify_candidate(*a)
        self.assertFalse(r['quantitative_gates_passed'])
        self.assertEqual(r['counts'],{'below_trial_reserve':1,'within_trial_reserve':1})
        self.assertTrue(r['gates']['measured_electrical_limits_met'])

    def test_timing_floor_area_and_chipwide_electrical_fail_independently(self):
        for change,gate in [(lambda a:a[5]['slow'].update(timing__setup__ws=.85),'whole_chip_timing_floors'),
                            (lambda a:a.__setitem__(7,1004.),'added_area_within_budget'),
                            (lambda a:a[5]['fast'].update(design__max_cap_violation__count=1),'whole_chip_violation_counts_zero')]:
            a=fixture();change(a);r=qualify_candidate(*a)
            self.assertEqual([k for k,v in r['gates'].items() if not v],[gate])

    def test_invalid_numeric_evidence_never_passes(self):
        for change in [lambda a:a[4]['slow']['n']['slew'].update(actual=float('nan')),
                       lambda a:a[5]['fast'].update(timing__hold__ws=float('inf')),
                       lambda a:a[5]['fast'].update(design__max_cap_violation__count=-1),
                       lambda a:a[0].update(reserve_fraction=0),
                       lambda a:a.__setitem__(7,float('nan'))]:
            a=fixture();change(a)
            with self.subTest(change=change),self.assertRaises(ValueError):qualify_candidate(*a)

    def test_absent_fanout_bound_cannot_qualify_a_candidate(self):
        a=fixture();a[4]['slow']['n']['fanout']=None
        with self.assertRaisesRegex(ValueError,'Missing required electrical bound: n slow fanout'):
            qualify_candidate(*a)

    def test_reported_violation_and_bad_path_cannot_be_hidden_by_global_counts(self):
        a=fixture();a[4]['fast']['n']['slew'].update(verdict='VIOLATED')
        self.assertEqual(qualify_candidate(*a)['counts'],{'failing':1,'within_trial_reserve':1})
        a=fixture();a[4]['slow']['branch']['paths']['min'].update(slack_ns=-.001,verdict='VIOLATED')
        self.assertFalse(qualify_candidate(*a)['gates']['measured_paths_positive'])


if __name__ == '__main__':
    unittest.main()
