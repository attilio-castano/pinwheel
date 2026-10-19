"""Constant clustering partitions and connection-preservation refusal controls."""
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_tt_ties as T


LIB = '''library(test) {
default_input_pin_cap:0.006; default_max_capacitance:0.3; default_max_fanout:8;
cell(sg13cmos5l_tielo) { pin(L_LO) { direction:output; function:"0"; } }
cell(sg13cmos5l_tiehi) { pin(L_HI) { direction:output; function:"1"; } }
cell(ff) { ff(IQ,IQN) { next_state:"D"; } pin(D) { direction:input; capacitance:0.009; } }
}'''


class TieTests(unittest.TestCase):
    def test_actual_liberty_constant_function_and_inherited_limits(self):
        with tempfile.TemporaryDirectory() as temporary:
            p = Path(temporary)/'cells.lib'; p.write_text(LIB)
            result = T.tie_contract([p])
            self.assertEqual(result['max_fanout'], 8)
            self.assertEqual(result['max_capacitance_pf'], 0.3)
            self.assertEqual(result['input_caps'][('ff','D')], 0.009)
            self.assertEqual(result['ff_masters'], {'ff'})
            for text in [LIB.replace('function:"1"','function:"0"'), LIB.replace('function:"0"','function:"D"'),
                    LIB.replace('default_max_fanout:8','default_max_fanout:0')]:
                p.write_text(text)
                with self.assertRaises(ValueError): T.tie_contract([p])

    def test_all_corners_use_strictest_load_limit_and_largest_pin_load(self):
        with tempfile.TemporaryDirectory() as temporary:
            p, q = Path(temporary)/'a.lib', Path(temporary)/'b.lib'
            p.write_text(LIB); q.write_text(LIB.replace('default_max_capacitance:0.3','default_max_capacitance:0.2')
                .replace('capacitance:0.009','capacitance:0.012'))
            result = T.tie_contract([p,q])
            self.assertEqual(result['max_capacitance_pf'], 0.2)
            self.assertEqual(result['input_caps'][('ff','D')], 0.012)

    def test_partition_has_actual_fanout_distance_and_pin_cap_bounds(self):
        sinks = [T.Sink(('i',str(i)), bool(i%2), i%4, i//4, 0.006) for i in range(101)]
        groups = T.cluster(sinks, max_fanout=8, max_distance=10, max_capacitance_pf=0.03,
            anchor=lambda value,index,point: point)
        actual = [sink.key for group in groups for sink in group['sinks']]
        self.assertEqual(set(actual), {sink.key for sink in sinks})
        self.assertEqual(len(actual), len(sinks))
        for group in groups:
            self.assertLessEqual(len(group['sinks']), 5)  # capacitance, not just fanout
            self.assertLessEqual(group['capacitance_pf'], 0.03)
            self.assertLessEqual(group['max_distance'], 10)
            self.assertTrue(all(s.value == group['value'] for s in group['sinks']))

    def test_invalid_load_duplicate_sink_and_far_actual_anchor_refuse(self):
        sink = T.Sink(('i','a'), True, 0, 0, 0.006)
        options = dict(max_fanout=8, max_distance=10, max_capacitance_pf=0.3,
            anchor=lambda value,index,point: point)
        with self.assertRaisesRegex(ValueError, 'Duplicate'): T.cluster([sink,sink], **options)
        with self.assertRaisesRegex(ValueError, 'load'):
            T.cluster([T.Sink(('i','a'), True, 0, 0, 0.4)], **options)
        options['anchor'] = lambda value,index,point: (100,100)
        with self.assertRaisesRegex(ValueError, 'too far'): T.cluster([sink], **options)

    def test_native_inventory_accepts_only_same_literal_constant_rebinding(self):
        before = ({'ff':{'master':'ff','location':[3,4]},'old':{'master':'tie'}},
            {('iterm','ff','D'):'zero', ('iterm','ff','Q'):'q', ('bterm','out'):'zero'})
        after = ({'ff':{'master':'ff','location':[3,4]},'new':{'master':'tie'}},
            {('iterm','ff','D'):'cluster0', ('iterm','ff','Q'):'q', ('bterm','out'):'cluster0'})
        T.verify_transform(before,after,{'zero':False},{'cluster0':False},{'old'},{'new'})
        for mode in ['value','location','connection','terminal','instance']:
            changed = deepcopy(after); constants = {'cluster0':False}
            if mode == 'value': constants['cluster0'] = True
            elif mode == 'location': changed[0]['ff']['location'] = [4,4]
            elif mode == 'connection': changed[1][('iterm','ff','Q')] = 'another'
            elif mode == 'terminal': del changed[1][('bterm','out')]
            else: changed[0]['unexpected'] = {'master':'ff'}
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                T.verify_transform(before,changed,{'zero':False},constants,{'old'},{'new'})


if __name__ == '__main__': unittest.main()
