import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lvs_mutants_v2 import native_verdict, reference_faults, standard_connections

TEXT = '''module tt_um_pinwheel_buffered (clk, VPWR, VGND);
 input clk;
 inout VPWR, VGND;
 wire net8042, net8046;
 sg13cmos5l_buf_1 hold0 (.A(data0), .X(net8042), .VDD(VPWR), .VSS(VGND));
 sg13cmos5l_buf_1 hold1 (.A(data1), .X(net8046), .VDD(VPWR), .VSS(VGND));
 sg13cmos5l_dfrbpq_1 _30759_ (.D(net8042), .CLK(clk), .Q(q0), .VDD(VPWR), .VSS(VGND));
 sg13cmos5l_dfrbpq_1 _30606_ (.D(net8046), .CLK(clk), .Q(q1), .VDD(VPWR), .VSS(VGND));
endmodule
'''
INV = {'instances': {
    'hold0': {'master': 'sg13cmos5l_buf_1', 'terminals': [['X', 'net8042', 'OUTPUT']]},
    'hold1': {'master': 'sg13cmos5l_buf_1', 'terminals': [['X', 'net8046', 'OUTPUT']]},
    '_30759_': {'master': 'sg13cmos5l_dfrbpq_1', 'terminals': [['D', 'net8042', 'INPUT']]},
    '_30606_': {'master': 'sg13cmos5l_dfrbpq_1', 'terminals': [['D', 'net8046', 'INPUT']]}},
    'nets': {'net8042': {'sig_type': 'SIGNAL', 'ports': [], 'terminals': [['hold0', 'X', 'OUTPUT'], ['_30759_', 'D', 'INPUT']]},
             'net8046': {'sig_type': 'SIGNAL', 'ports': [], 'terminals': [['hold1', 'X', 'OUTPUT'], ['_30606_', 'D', 'INPUT']]}}}


class Controls(unittest.TestCase):
    def test_exact_positive_and_single_contact_removal(self):
        variants, facts = reference_faults(TEXT, INV)
        self.assertEqual(variants['positive'], TEXT)
        self.assertEqual(facts['removed-terminal']['changed_terminal_count'], 1)
        self.assertEqual(facts['removed-terminal']['changed_terminals'][0]['before'], 'net8042')
        self.assertIn('wire PW_LVS_NEG_OPEN_30759_D;', variants['removed-terminal'])
        self.assertEqual(standard_connections(variants['positive'])[1], standard_connections(variants['removed-terminal'])[1])
        self.assertEqual(TEXT, variants['positive'])

    def test_exact_two_contact_bridge(self):
        variants, facts = reference_faults(TEXT, INV)
        self.assertEqual(facts['bridged-nets']['changed_terminal_count'], 2)
        _, _, connections = standard_connections(variants['bridged-nets'])
        self.assertEqual(connections[('hold1', 'X')]['expression'], 'net8042')
        self.assertEqual(connections[('_30606_', 'D')]['expression'], 'net8042')
        self.assertEqual(connections[('_30759_', 'D')]['expression'], 'net8042')
        self.assertEqual(facts['bridged-nets']['distinct_consumed_nets'], ['net8042', 'net8046'])

    def test_wrong_or_unconsumed_source_terminal_rejected(self):
        for text in [TEXT.replace('.D(net8042)', '.D(other)'), TEXT.replace('_30759_', 'different')]:
            with self.assertRaises(AssertionError):
                reference_faults(text, INV)
        inv = copy.deepcopy(INV)
        inv['nets']['net8042']['terminals'] = [['hold0', 'X', 'OUTPUT']]
        with self.assertRaises(AssertionError):
            reference_faults(TEXT, inv)

    def test_alias_assignment_rejected(self):
        text = TEXT.replace('endmodule', 'assign net8046 = something;\nendmodule')
        with self.assertRaises(AssertionError):
            reference_faults(text, INV)

    def test_same_or_clock_bridge_rejected(self):
        with self.assertRaises(AssertionError):
            reference_faults(TEXT, INV, bridge_nets=('net8042', 'net8042'))
        inv = copy.deepcopy(INV)
        inv['nets']['net8046']['sig_type'] = 'CLOCK'
        with self.assertRaises(AssertionError):
            reference_faults(TEXT, inv)

    def test_complete_native_positive_and_mismatch(self):
        self.assertTrue(native_verdict('Final result: Circuits match uniquely.\n')['match_uniquely'])
        self.assertFalse(native_verdict('Final result: Netlists do not match.\n')['match_uniquely'])

    def test_unknown_or_missing_native_verdict_rejected(self):
        for report in ['', 'Final result: Could not load inputs.\n',
                       'Final result: Circuits match uniquely.\nFinal result: Netlists do not match.\n']:
            with self.assertRaises(ValueError):
                native_verdict(report)


if __name__ == '__main__':
    unittest.main()
