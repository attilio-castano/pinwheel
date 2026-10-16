import re
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lvs_fixture_host_v4 import fixture, MASTER
from lvs_mutants_v2 import reference_faults

MODELS = {'sg13cmos5l_buf_1': ['X', 'A', 'VDD', 'VSS'],
          'sg13cmos5l_dfrbpq_1': ['Q', 'CLK', 'D', 'RESET_B', 'VDD', 'VSS']}
PORTS = ['A_ADDR[' + str(i) + ']' for i in range(342)] + ['VDD!', 'VDDARRAY!', 'VSS!']

class FixtureMapping(unittest.TestCase):
    def test_positional_345_exact_model_order_and_intended_rails(self):
        spice, verilog, native = fixture(MODELS, PORTS)
        macro = re.search(re.escape(MASTER) + r' memory \((.*?)\);', verilog)[1].split(', ')
        extracted = next(line for line in spice.splitlines() if line.startswith('Xmemory ')).split()[1:-1]
        self.assertEqual(macro, extracted)
        self.assertEqual(len(macro), 345)
        self.assertEqual(len(set(macro)), 344)
        self.assertEqual(macro[-3:], ['VPWR', 'VPWR', 'VGND'])
        self.assertNotIn('.\\A_ADDR', verilog)
        variants, changes = reference_faults(verilog, native)
        for text in variants.values():
            self.assertEqual(re.search(re.escape(MASTER) + r' memory \((.*?)\);', text)[1].split(', '), macro)
        self.assertEqual(changes['removed-terminal']['changed_terminal_count'], 1)
        self.assertEqual(changes['bridged-nets']['changed_terminal_count'], 2)
    def test_bad_macro_count_or_alias_rejected(self):
        for ports in [PORTS[:-1], PORTS[:-1] + [PORTS[0]]]:
            with self.assertRaises(AssertionError): fixture(MODELS, ports)

if __name__ == '__main__': unittest.main()
