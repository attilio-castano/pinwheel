from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_connections import Connectivity
from physical_path_contract import declared_roles, path_inventory, validate_preserved_budgets
from physical_route_intake import validate_repair_route
from test_physical_path_repair import explicit_fixture
import test_physical_added_route_chain as chain


def fixture():
    source, plan, _, _ = explicit_fixture()
    ownership = dict(registers={'serial':[dict(cell='s', bit=0)], 'state':[dict(cell='q', bit=3)]})
    scope = dict(distribution=dict(source_owner='serial', sink_owner='state',
        sink_owner_prefix='state', macro_inputs=['memory/A_DIN[0]']), explicit_connections=['control', 'n'])
    roles = dict(rejection_status=dict(sources=['s/Q'], sinks=['output']))
    for name, cell, box in [('control_logic', 'sg13cmos5l_inv_1', [44,4,48,8]),
                          ('tie', 'sg13cmos5l_tielo', [49,4,51,8])]:
        source['instances'][name] = dict(cell=cell, macro=False, bbox=box, bbox_dbu=box[:])
    source['nets']['src']['terminals'].append(dict(instance='control_logic', pin='A', direction='INPUT'))
    for name, driver, pin, kind in [('control','control_logic/Y','A_REN','SIGNAL'),
                                  ('constant','tie/L','TEST','SIGNAL'),
                                  ('clock','clockbuf/X','A_CLK','CLOCK')]:
        inst, output = driver.split('/')
        source['nets'][name] = dict(type=kind, ports=[], terminals=[
            dict(instance=inst, pin=output, direction='OUTPUT'),
            dict(instance='memory', pin=pin, direction='INPUT')])
    graph = Connectivity(source, ownership)
    watch = dict(source_database=dict(sha256='frozen'), status_net='n', hold_endpoints=['q/D'],
        additional_connections=[graph.record(n, roles) for n in scope['explicit_connections']],
        macro_inputs=[dict(pin='memory/'+pin, net=net, kind=kind) for pin,net,kind in [
            ('A_REN','control','timed_control'), ('TEST','constant','static_tie'), ('A_CLK','clock','clock')]])
    after = deepcopy(source)
    after['database_sha256'] = 'candidate'
    for op in plan['operations']:
        for index, stage in enumerate(op['stages']):
            name, box = stage['instance'], stage['footprint_dbu']
            after['instances'][name] = dict(cell=stage['cell'], macro=False, bbox=box[:], bbox_dbu=box[:])
            net = after['nets'][op['net'] if index == 0 else op['stages'][index-1]['new_net']]
            sink = next(t for t in net['terminals'] if t['instance']+'/'+t['pin'] == op['receiver'])
            net['terminals'].remove(sink)
            net['terminals'].append(dict(instance=name, pin='A', direction='INPUT'))
            after['nets'][stage['new_net']] = dict(type='SIGNAL', ports=[], terminals=[
                dict(instance=name, pin='X', direction='OUTPUT'), sink])
    return source, after, ownership, roles, scope, watch, plan


class PathContract(unittest.TestCase):
    def test_roles_survive_both_hold_stages_and_keep_family_coverage(self):
        source, after, ownership, roles, scope, watch, plan = fixture()
        before = path_inventory(source, source, ownership, roles, scope, watch)
        candidate = path_inventory(source, after, ownership, roles, scope, watch, plan)
        rows = {r['net']:r for r in candidate['connections']}
        self.assertEqual(set(rows), {r['net'] for r in before['connections']} |
            {s['new_net'] for op in plan['operations'] for s in op['stages']})
        for net in ['n', 'path_0_0_net', 'path_0_1_net']:
            self.assertIn('input_hold', rows[net]['families'])
            self.assertIn('status_path', rows[net]['families'])
        self.assertEqual(rows['n']['ports'], ['output'])
        self.assertEqual(rows['control']['families'], ['sram_control'])
        self.assertNotIn('constant', rows)
        self.assertNotIn('clock', rows)

    def test_cannot_drop_dynamic_macro_control_even_with_matching_scope(self):
        s, _, o, r, scope, w, _ = fixture()
        scope['explicit_connections'].remove('control')
        w['additional_connections'] = [row for row in w['additional_connections'] if row['net'] != 'control']
        with self.assertRaisesRegex(ValueError, 'declared path connection'):
            declared_roles(s, o, r, scope, w)

    def test_macro_census_cannot_reclassify_dynamic_pin_as_static(self):
        s, _, o, r, scope, w, _ = fixture()
        w['macro_inputs'][0]['kind'] = 'static_tie'
        with self.assertRaisesRegex(ValueError, 'macro input census'):
            declared_roles(s, o, r, scope, w)

    def test_missing_static_or_clock_pin_is_not_silently_ignored(self):
        for index in [1, 2]:
            s, _, o, r, scope, w, _ = fixture()
            w['macro_inputs'].pop(index)
            with self.assertRaisesRegex(ValueError, 'macro input census'):
                declared_roles(s, o, r, scope, w)

    def test_stale_consumers_or_wrong_source_fail(self):
        for change in [lambda w:w['additional_connections'][1]['ports'].clear(),
                       lambda w:w['source_database'].update(sha256='other')]:
            s, _, o, r, scope, w, _ = fixture()
            change(w)
            with self.assertRaises(ValueError): declared_roles(s, o, r, scope, w)

    def test_hold_anchor_cannot_be_changed_to_a_clock_pin(self):
        s, _, o, r, scope, w, _ = fixture()
        w['hold_endpoints'] = ['q/CLK']
        with self.assertRaisesRegex(ValueError, 'state data input'):
            declared_roles(s, o, r, scope, w)

    def test_plan_cannot_omit_a_declared_hold_anchor(self):
        s, a, o, r, scope, w, plan = fixture()
        plan['operations'][0]['purpose'] = 'electrical'
        with self.assertRaisesRegex(ValueError, 'hold endpoints'):
            path_inventory(s, a, o, r, scope, w, plan)

    def budgets(self):
        original = dict(scope={'families':'fixed'}, reserve_fraction=.2, max_added_area_fraction=.003,
            timing_floors_ns={'slow':dict(setup=.4, hold=.08)}, source_database_sha256='budget-origin')
        reference = dict(source_database_sha256='budget-origin', placed_instance_area_um2=100)
        contract = dict(schema=1, status='checked-plan-only',
            scope=dict(distribution=original['scope'], explicit_connections=['extra']),
            reserve_fraction=.2, max_added_area_fraction=.003, timing_floors_ns=deepcopy(original['timing_floors_ns']),
            area_reference=dict(area_um2=100), acceptance=dict(all_connections_including_added_branches=True,
                all_chip_electrical_zero=True, unchanged_timing_floors=True, unchanged_cumulative_area_cap=True,
                original_cells_clocks_and_hold_retained=True, independent_identity_placement_power=True,
                whole_chip_routing_revalidation_required=True))
        return contract, original, reference

    def test_original_area_origin_is_preserved(self):
        self.assertEqual(validate_preserved_budgets(*self.budgets()), 100)
        c, o, r = self.budgets()
        c['area_reference']['area_um2'] = 100.25
        with self.assertRaisesRegex(ValueError, 'preserved budgets'): validate_preserved_budgets(c, o, r)
        c['area_reference']['area_um2'] = r['placed_instance_area_um2'] = 100.25
        r['source_database_sha256'] = 'recent-parent'
        with self.assertRaisesRegex(ValueError, 'preserved budgets'): validate_preserved_budgets(c, o, r)

    def test_reserve_timing_and_area_limits_cannot_be_relaxed(self):
        for change in [lambda c:c.update(reserve_fraction=.19), lambda c:c.update(max_added_area_fraction=.004),
                       lambda c:c['timing_floors_ns']['slow'].update(hold=.04),
                       lambda c:c['acceptance'].update(all_connections_including_added_branches=False)]:
            c, o, r = self.budgets(); change(c)
            with self.assertRaisesRegex(ValueError, 'preserved budgets'): validate_preserved_budgets(c, o, r)

    def test_new_receipt_cannot_bypass_path_contract(self):
        with tempfile.TemporaryDirectory() as folder:
            f = chain.ChainedRoute(); args = f.fixture(Path(folder))
            f.edit(args, 'validation/report.json', lambda d:d.update(
                decision='retain-locally-qualified-path-repair-bind-expanded-intake-before-whole-chip-route',
                local_path_contract_pass=False))
            with self.assertRaisesRegex(ValueError, 'local contract pass'):
                validate_repair_route(**args)


if __name__ == '__main__': unittest.main()
