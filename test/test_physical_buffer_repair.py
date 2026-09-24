from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_buffer_repair import compare_buffer_repair


def cell(kind, connections, output):
    return dict(type=kind, connections=connections,
                port_directions={p: 'output' if p == output else 'input' for p in connections})


def fixture():
    original = dict(ports={'clk': dict(direction='input', bits=[2]),
                           'in': dict(direction='input', bits=[3]),
                           'out': dict(direction='output', bits=[6])},
                    cells={'clock': cell('sg13cmos5l_buf_8', {'A': [2], 'X': [4]}, 'X'),
                           'reg': cell('ff', {'CLK': [4], 'D': [3], 'Q': [5]}, 'Q'),
                           'memory': cell('sram', {'CLK': [4], 'A': [5], 'Q': [6]}, 'Q')})
    repaired = deepcopy(original)
    repaired['cells']['clock_copy'] = cell('sg13cmos5l_buf_8', {'A': [2], 'X': [7]}, 'X')
    repaired['cells']['memory']['connections']['CLK'] = [7]
    repaired['cells']['sram_buffer'] = cell('sg13cmos5l_buf_4', {'A': [6], 'X': [8]}, 'X')
    repaired['ports']['out']['bits'] = [8]
    return original, repaired


class BufferRepair(unittest.TestCase):
    def test_resizing_requires_explicit_mode_and_preserves_every_logical_connection(self):
        before, _ = fixture()
        after = deepcopy(before)
        after['cells']['clock']['type'] = 'sg13cmos5l_buf_4'
        with self.assertRaisesRegex(ValueError, 'Changed original cell'):
            compare_buffer_repair(before, after)
        result = compare_buffer_repair(before, after, allow_resizing=True)
        self.assertEqual(result['added_buffers'], {})
        self.assertEqual(result['resized_buffers']['clock']['after'], 'sg13cmos5l_buf_4')
        for mode in ['inverter', 'state', 'wire', 'noop']:
            bad = deepcopy(after)
            if mode == 'inverter': bad['cells']['clock']['type'] = 'sg13cmos5l_inv_4'
            elif mode == 'state': bad['cells']['reg']['type'] = 'other_ff'
            elif mode == 'wire': bad['cells']['clock']['connections']['A'] = [3]
            else: bad = deepcopy(before)
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                compare_buffer_repair(before, bad, allow_resizing=True)

    def test_original_cts_dummy_output_can_be_unconnected(self):
        before, after = fixture()
        dummy = cell('sg13cmos5l_buf_8', {'A': [4]}, 'X')
        before['cells']['dummy'] = deepcopy(dummy)
        after['cells']['dummy'] = deepcopy(dummy)
        self.assertTrue(compare_buffer_repair(before, after)['buffer_contracted_connectivity'])
        after['cells']['dummy']['connections']['A'] = [999]
        with self.assertRaisesRegex(ValueError, 'undriven'):
            compare_buffer_repair(before, after)

    def test_clock_replication_and_data_buffering_preserve_connections(self):
        before, after = fixture()
        result = compare_buffer_repair(before, after)
        self.assertEqual(sum(result['added_buffers'].values()), 2)
        # Wire-number renaming cannot substitute for terminal identity.
        for p in after['ports'].values():
            p['bits'] = [b + 100 for b in p['bits']]
        for c in after['cells'].values():
            c['connections'] = {p: [b + 100 for b in bits] for p, bits in c['connections'].items()}
        self.assertEqual(compare_buffer_repair(before, after), result)

    def test_rejects_wrong_clock_data_output_and_cell_changes(self):
        for name, mutate in [
            ('clock', lambda m: m['cells']['clock_copy']['connections']['A'].__setitem__(0, 3)),
            ('address', lambda m: m['cells']['memory']['connections']['A'].__setitem__(0, 3)),
            ('output', lambda m: m['ports']['out']['bits'].__setitem__(0, 5)),
            ('inverter', lambda m: m['cells']['sram_buffer'].__setitem__('type', 'sg13cmos5l_inv_4')),
            ('state', lambda m: m['cells']['reg'].__setitem__('type', 'different_ff')),
            ('parameter', lambda m: m['cells']['memory'].__setitem__('parameters', {'INIT': '1'})),
            ('removed', lambda m: m['cells'].pop('reg')),
        ]:
            before, after = fixture()
            mutate(after)
            with self.subTest(name=name), self.assertRaises(ValueError):
                compare_buffer_repair(before, after)

    def test_rejects_cycles_floating_inputs_shorts_and_noop(self):
        for value in [7, 999, 'x']:
            before, after = fixture()
            after['cells']['clock_copy']['connections']['A'] = [value]
            with self.subTest(value=value), self.assertRaises(ValueError):
                compare_buffer_repair(before, after)
        before, after = fixture()
        after['cells']['clock_copy']['connections']['X'] = [5]
        with self.assertRaisesRegex(ValueError, 'multiply driven'):
            compare_buffer_repair(before, after)
        with self.assertRaisesRegex(ValueError, 'actual edit'):
            compare_buffer_repair(before, before)


if __name__ == '__main__':
    unittest.main()
