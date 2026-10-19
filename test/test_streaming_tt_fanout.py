from copy import deepcopy
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_fanout as F


BUFFER = 'sg13cmos5l_buf_8'
LIBRARY = SimpleNamespace(cells={BUFFER: SimpleNamespace(sequential=False,
    directions={'A': 'input', 'X': 'output'}, output='X', function=('variable', 'A'))})


def fixture(leaves=1, sinks=16):
    power = dict(VPWR=dict(direction='INOUT', signal_type='POWER'), VGND=dict(direction='INOUT', signal_type='GROUND'))
    buffer = dict(A=dict(direction='INPUT', signal_type='SIGNAL'), X=dict(direction='OUTPUT', signal_type='SIGNAL'), **power)
    load = dict(A=dict(direction='INPUT', signal_type='SIGNAL'), **power)
    result = dict(schema='pinwheel.streaming-tt-odb-inventory.v1', top='example', nets={}, instances={},
        masters={BUFFER: buffer, 'diode': load}, public_bterms=dict(clk=dict(port='clk', index=0, direction='input', net='clk')),
        power_bterms=dict(VPWR=dict(direction='INOUT', signal_type='POWER', net='VPWR'),
            VGND=dict(direction='INOUT', signal_type='GROUND', net='VGND')),
        unconnected_signal_outputs={}, physical_only_instances={}, signal_model_instances=0, instance_counts={})
    def net(name, kind='CLOCK'):
        result['nets'][name] = dict(wire=len(result['nets'])+2, signal_type=kind)
    net('VPWR', 'POWER'); net('VGND', 'GROUND'); net('clk'); net('root')
    def instance(name, master, connections):
        terms = {pin: dict(row, net=connections.get(pin, pin if pin in power else None))
            for pin, row in result['masters'][master].items()}
        result['instances'][name] = dict(master=master, master_type='CORE', terminals=terms)
    instance('root_buffer', BUFFER, dict(A='clk', X='root'))
    for leaf in range(leaves):
        name = 'leaf'+str(leaf); net(name)
        instance(name+'_buffer', BUFFER, dict(A='root', X=name))
        for sink in range(sinks): instance(name+'_sink'+str(sink), 'diode', dict(A=name))
    result['signal_model_instances'] = len(result['instances'])
    from collections import Counter
    result['instance_counts'] = dict(sorted(Counter(row['master'] for row in result['instances'].values()).items()))
    return result


class PositiveClonePlan(unittest.TestCase):
    def test_all_actual_diode_loads_are_partitioned(self):
        original = fixture(); plan, actual = F.build_plan(original, LIBRARY)
        self.assertEqual(plan['projected_added_cells'], 1)
        self.assertEqual(plan['initial_over_limit'], {'leaf0': 16})
        self.assertTrue(F.verify_result(original, actual, plan, LIBRARY)['passed'])
        self.assertEqual(len(original['instances']), 18)

    def test_recursive_parent_input_loads_also_close(self):
        original = fixture(leaves=8); plan, actual = F.build_plan(original, LIBRARY)
        self.assertEqual(plan['projected_added_cells'], 9)
        self.assertFalse(any(len(row['loads']) > 8 for row in F.loads(actual).values()))

    def test_ancestor_clones_wait_until_all_descendant_loads_are_final(self):
        original = fixture(leaves=8, sinks=17); plan, _ = F.build_plan(original, LIBRARY)
        self.assertEqual(plan['projected_added_cells'], 18)
        self.assertTrue(all(op['source_net'].startswith('leaf') for op in plan['operations'][:16]))
        self.assertEqual([op['source_net'] for op in plan['operations'][16:]], ['root', 'root'])

    def test_public_clock_overload_gets_one_explicit_balanced_prefix(self):
        original = fixture(leaves=8)
        for number in range(7):
            net = 'unused'+str(number)
            original['nets'][net] = dict(wire=1000+number, signal_type='CLOCK')
            original['instances'][net] = deepcopy(original['instances']['root_buffer'])
            original['instances'][net]['terminals']['X']['net'] = net
        original['signal_model_instances'] += 7; original['instance_counts'][BUFFER] += 7
        plan, actual = F.build_plan(original, LIBRARY)
        self.assertEqual(plan['balanced_public_clock_prefix_levels'], 1)
        prefixes = [op for op in plan['operations'] if op['kind'] == 'clock_root_prefix']
        self.assertEqual(len(prefixes), 2)
        self.assertEqual(sum(len(op['loads']) for op in prefixes), 9)
        changed = deepcopy(plan); changed['balanced_public_clock_prefix_levels'] = 0
        with self.assertRaisesRegex(ValueError, 'Hidden'): F.verify_result(original, actual, changed, LIBRARY)
        changed = deepcopy(plan)
        prior = next(op for op in changed['operations'] if op['kind'] == 'clone')
        changed['operations'].append(deepcopy(prior))
        with self.assertRaisesRegex(ValueError, 'may follow'): F.verify_result(original, actual, changed, LIBRARY)
        changed_actual = deepcopy(actual)
        moved = prefixes[0]['loads'][0]
        changed_actual['instances'][moved[1]]['terminals'][moved[2]]['net'] = 'clk'
        with self.assertRaisesRegex(ValueError, 'bypass'): F.verify_result(original, changed_actual, plan, LIBRARY)

    def test_nonbuffer_signal_driver_gets_explicit_positive_branches(self):
        original = fixture(); original['nets']['leaf0']['signal_type'] = 'SIGNAL'
        original['instances']['leaf0_buffer']['master'] = 'sg13cmos5l_inv_1'
        original['masters']['sg13cmos5l_inv_1'] = original['masters'][BUFFER]
        original['instance_counts'][BUFFER] -= 1; original['instance_counts']['sg13cmos5l_inv_1'] = 1
        plan, _ = F.build_plan(original, LIBRARY)
        self.assertEqual(plan['signal_nets_with_new_positive_buffer_level'], ['leaf0'])
        self.assertEqual([op['kind'] for op in plan['operations']], ['signal_buffer', 'signal_buffer'])

    def test_missing_load_and_original_cell_mutations_are_rejected(self):
        original = fixture(); plan, actual = F.build_plan(original, LIBRARY)
        controls = []
        changed = deepcopy(actual); changed['instances']['leaf0_sink0']['terminals']['A']['net'] = 'clk'; controls.append(changed)
        changed = deepcopy(actual); changed['instances']['root_buffer']['master'] = 'diode'; controls.append(changed)
        changed = deepcopy(actual); changed['instances'][plan['operations'][0]['new_instance']]['terminals']['VPWR']['net'] = 'VGND'; controls.append(changed)
        for changed in controls:
            with self.assertRaisesRegex(ValueError, 'unadmitted'): F.verify_result(original, changed, plan, LIBRARY)

    def test_dropped_partition_member_is_rejected(self):
        original = fixture(); plan, actual = F.build_plan(original, LIBRARY)
        changed = deepcopy(plan); changed['operations'][0]['loads'].pop()
        with self.assertRaisesRegex(ValueError, 'unadmitted'): F.verify_result(original, actual, changed, LIBRARY)

    def test_inverted_buffer_contract_cannot_authorize_cloning(self):
        bad = deepcopy(LIBRARY); bad.cells[BUFFER].function = ('not', ('variable', 'A'))
        with self.assertRaisesRegex(ValueError, 'No actual positive'): F.build_plan(fixture(), bad)

    def test_cell_budget_and_name_collisions_are_not_silently_truncated(self):
        with self.assertRaisesRegex(ValueError, 'cell budget'): F.build_plan(fixture(leaves=8), LIBRARY, maximum_added=1)
        original = fixture(); original['nets']['streaming_tt_fanout_branch_0'] = dict(wire=999, signal_type='CLOCK')
        with self.assertRaisesRegex(ValueError, 'collide'): F.build_plan(original, LIBRARY)

    def test_exporter_local_wire_numbering_can_change_but_never_alias(self):
        original = fixture(); plan, actual = F.build_plan(original, LIBRARY)
        for row in actual['nets'].values(): row['wire'] += 10000
        self.assertTrue(F.verify_result(original, actual, plan, LIBRARY)['passed'])
        values = list(actual['nets'].values()); values[1]['wire'] = values[0]['wire']
        with self.assertRaisesRegex(ValueError, 'Aliased'): F.verify_result(original, actual, plan, LIBRARY)

    def test_incremental_pin_cache_equals_independent_full_inventory(self):
        original = fixture(leaves=8); plan, _ = F.build_plan(original, LIBRARY)
        projected = deepcopy(original); context = F.loads(projected)
        for operation in plan['operations']:
            F.apply_operation(projected, operation, F.positive_buffers(LIBRARY), context=context)
        def canonical(table):
            return {name: dict(row, loads=sorted(row['loads']), drivers=sorted(row['drivers'])) for name, row in table.items()}
        self.assertEqual(canonical(context), canonical(F.loads(projected)))


if __name__ == '__main__': unittest.main()
