from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_distribution import inventory, assess, validate_contract
from physical_connections import parse_measurements
from test_physical_connections import fixture, REPORT
from test_physical_repair_plan import plan_fixture


def sample():
    context, ownership = fixture()
    scope = dict(source_owner='serial', sink_owner='state', sink_owner_prefix='state',
                 macro_inputs=['memory/A_DIN[0]'])
    return context, ownership, scope


class Distribution(unittest.TestCase):
    def test_covers_passing_siblings_and_retains_shared_owners(self):
        c, o, s = sample()
        result = inventory(c, o, {}, s)
        self.assertEqual({r['net'] for r in result['connections']}, {'src', 'n', 'u'})
        self.assertEqual(len(result['components']), 1)
        self.assertEqual(result['components'][0]['root'], 'src')
        self.assertIn('sram_write_input', result['connections'][0]['families'])
        n = next(r for r in result['connections'] if r['net'] == 'n')
        self.assertIn('output', n['ports'])
        self.assertTrue(n['shared'])
        self.assertEqual(n['source_owners'], ['serial'])

    def test_single_load_buffer_and_hold_neighbors_are_not_dropped(self):
        c, o, s = sample()
        result = inventory(c, o, {}, s)
        self.assertEqual(result['seed_nets'], 2)
        self.assertEqual(next(r for r in result['connections'] if r['net'] == 'n')['seed_families'], [])
        self.assertIn('hold/X', {r['driver'] for r in result['connections']})

    def test_requires_resolved_owners_and_exact_macro_inputs(self):
        for change in [dict(source_owner='absent'), dict(sink_owner_prefix='absent'),
                       dict(macro_inputs=[]), dict(macro_inputs=['q/D']),
                       dict(macro_inputs=['memory/A_DIN[9]']),
                       dict(macro_inputs=['memory/A_DIN[0]'] * 2)]:
            c, o, s = sample()
            with self.subTest(change=change), self.assertRaises(ValueError):
                inventory(c, o, {}, dict(s, **change))

    def test_clock_is_not_a_repair_family(self):
        c, o, s = sample()
        c['nets']['clock'] = dict(type='CLOCK', ports=['clk'], terminals=[])
        result = inventory(c, o, {}, s)
        self.assertNotIn('clock', {r['net'] for r in result['connections']})

    def measured(self):
        row = parse_measurements(REPORT, {'n'})['n']
        row['capacitance'] = dict(pin='d/X', limit=.4, actual=.1, slack=.3, verdict='MET')
        row['slew'] = dict(pin='d/X', limit=.5, actual=.2, slack=.3, verdict='MET')
        rows = {'n': row}
        return [dict(net='n', families=['serial_data'], distribution_root='src',
                     consumers=['q/D'], ports=[])], {
            label:{corner:deepcopy(rows) for corner in ['fast','slow']}
            for label in ['local','route']}

    def test_passing_but_low_margin_neighbor_is_selected_across_corners(self):
        records, measurements = self.measured()
        measurements['route']['slow']['n']['capacitance'].update(actual=.35, slack=.05)
        result = assess(records, measurements, ['fast','slow'], .2)
        self.assertEqual(result['counts'], {'below_trial_reserve':1})
        self.assertAlmostEqual(result['connections'][0]['corners'][1]['capacitance']['reserve_fraction'], .125)

    def test_failure_is_distinct_from_trial_reserve(self):
        records, measurements = self.measured()
        measurements['route']['fast']['n']['slew'].update(actual=.6, slack=-.1, verdict='VIOLATED')
        self.assertEqual(assess(records, measurements, ['fast','slow'], .2)['counts'], {'failing':1})

    def test_missing_corner_net_or_changed_pin_load_is_rejected(self):
        for change in [lambda d:d['route'].pop('slow'), lambda d:d['route']['slow'].pop('n'),
                       lambda d:d['route']['slow']['n'].update(loads=2),
                       lambda d:d['route']['slow']['n'].update(pin_cap_pf=[.01,.01]),
                       lambda d:d['route']['slow']['n']['slew'].update(actual=float('nan'))]:
            records, measurements = self.measured()
            change(measurements)
            with self.assertRaises(ValueError):
                assess(records, measurements, ['fast','slow'], .2)

    def test_trial_reserve_is_explicit_and_not_a_wire_multiplier(self):
        records, measurements = self.measured()
        measurements['route']['slow']['n']['wire_cap_pf'] = [.9,.9]
        result = assess(records, measurements, ['fast','slow'], .2)
        self.assertEqual(result['connections'][0]['measured_wire_ratio_range'], [1.,3.])
        self.assertEqual(result['counts'], {'within_trial_reserve':1})
        for reserve in [0,1,-.1,float('nan')]:
            with self.assertRaises(ValueError):
                assess(records, measurements, ['fast','slow'], reserve)
        for corners in [[], ['fast','fast']]:
            with self.assertRaises(ValueError):
                assess(records, measurements, corners, .2)


def contract_sample():
    context, plan = plan_fixture()
    context['die'] = [0,0,100,250]
    context['instances']['memory']['bbox'] = [60,10,90,200]
    context['instances']['memory']['bbox_dbu'] = [60,10,90,200]
    coverage = dict(source_database_sha256='frozen',scope={'explicit':'family'},
                    connections=[dict(net=n) for n in ['src','n','u']])
    assessment = dict(reserve_fraction=.2,connections=[
        dict(net='src',verdict='within_trial_reserve'),
        dict(net='n',verdict='below_trial_reserve'),dict(net='u',verdict='failing')])
    timing = {'slow':dict(timing__setup__ws=1.,timing__hold__ws=.1)}
    contract = dict(schema=1,status='checked-plan-only',source_database_sha256='frozen',
        scope=coverage['scope'],reserve_fraction=.2,selected_nets=['n','u'],
        max_added_area_fraction=.01,max_timing_regression_fraction=.1,
        timing_floors_ns={'slow':dict(setup=.9,hold=.1*.9)},
        acceptance=dict(all_covered_and_added_connections_measured=True,
            all_corner_capacitance_and_slew_reserve=True,all_corner_setup_hold_floors=True,
            all_chip_electrical_zero=True,buffer_contracted_identity=True,
            original_cells_clocks_and_hold_retained=True,added_cells_legal_and_power_bound=True,
            whole_chip_routing_revalidation_required=True,congestion_and_effective_clock_rules_reported=True,
            repair_executed=False,new_route_admitted=False,detailed_route_admitted=False),boundary='test')
    return contract, coverage, assessment, plan, context, timing


class Contract(unittest.TestCase):
    def test_checked_plan_keeps_passing_neighbor_and_explicit_cost(self):
        args = contract_sample()
        result = validate_contract(*args)
        self.assertEqual(result['covered_connections'],3)
        self.assertEqual(result['selected_connections'],2)
        self.assertEqual(result['added_area_um2'],48)
        self.assertFalse(args[0]['acceptance']['repair_executed'])

    def test_cannot_drop_passing_neighbor_or_low_margin_target(self):
        for change in [lambda a:a[2]['connections'].pop(0),
                       lambda a:a[0]['selected_nets'].remove('n'),
                       lambda a:a[3]['operations'].pop()]:
            args = contract_sample()
            change(args)
            with self.assertRaises(ValueError):validate_contract(*args)

    def test_cannot_weaken_or_omit_budget_checks(self):
        for change in [lambda c:c.update(reserve_fraction=.1),
                       lambda c:c['timing_floors_ns']['slow'].update(hold=.001),
                       lambda c:c.update(max_added_area_fraction=.0001),
                       lambda c:c['acceptance'].update(all_covered_and_added_connections_measured=False),
                       lambda c:c['acceptance'].update(new_route_admitted=True),
                       lambda c:c['acceptance'].update(repair_executed=True)]:
            args = contract_sample()
            change(args[0])
            with self.assertRaises(ValueError):validate_contract(*args)

    def test_stale_source_changed_scope_and_unknown_verdict_are_rejected(self):
        for change in [lambda a:a[0].update(source_database_sha256='stale'),
                       lambda a:a[0].update(scope={'partial':'family'}),
                       lambda a:a[2]['connections'][0].update(verdict='ignore')]:
            args = contract_sample()
            change(args)
            with self.assertRaises(ValueError):validate_contract(*args)


if __name__ == '__main__':
    unittest.main()
