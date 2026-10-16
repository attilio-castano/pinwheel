import copy
import re
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from boundary_adapter_v5 import MASTER, RAILS, canonical_pin, positional_reference, normalized_extracted_header

PORTS = ['DATA[' + str(i) + ']' for i in range(341, -1, -1)] + list(RAILS)
ORDER = [canonical_pin(pin) for pin in PORTS]
NODES = ['net\\[' + str(i) + '\\]' for i in range(341, -1, -1)]
TERMS = [[pin, net, 'INPUT'] for pin, net in zip(PORTS, NODES + ['VPWR', 'VPWR', 'VGND'])]
INV = {'instances': {name: {'master': MASTER, 'terminals': TERMS} for name in ['memory0', 'memory1']},
       'nets': {net: {} for net in NODES + ['VPWR', 'VGND']}}
PREFIX = 'module top;\nsg13cmos5l_buf_1 sentinel (.A(a), .X(x), .VDD(VPWR), .VSS(VGND));\n'
TEXT = PREFIX + '\n'.join(MASTER + ' ' + name + ' (.DATA({' + ', '.join('\\net[' + str(i) + '] ' for i in range(341, -1, -1)) + '}), .\\VDD! (VPWR), .\\VDDARRAY! (VPWR), .\\VSS! (VGND));' for name in ['memory0', 'memory1']) + '\nendmodule\n'
SPICE = '.subckt ' + MASTER + ' ' + ' '.join(pin.replace('[', '<').replace(']', '>').rstrip('!') for pin in PORTS) + '\n.ends ' + MASTER + '\n'

class BoundaryAdapter(unittest.TestCase):
    def test_positive_exact690contacts_and_other_text(self):
        adapted, audit = positional_reference(TEXT, INV, ORDER)
        self.assertTrue(adapted.startswith(PREFIX))
        self.assertTrue(adapted.endswith('\nendmodule\n'))
        self.assertEqual(audit['native_macro_contacts_checked'], 690)
        self.assertTrue(audit['native_net_spelling_map_bijective_over_all_nets'])
        self.assertEqual(len(audit['native_net_spelling_nonidentity_map']), 342)
        for statement in re.findall(re.escape(MASTER) + r' memory[01] \((.*?)\);', adapted):
            self.assertEqual(len(statement.split(', ')), 345)
            self.assertTrue(statement.endswith('VPWR, VPWR, VGND'))
    def test_reference_pin_net_mismatch_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'pin-to-net mismatch'):
            positional_reference(TEXT.replace('\\net[341] ', 'other', 1), INV, ORDER)
    def test_native_spelling_alias_rejected(self):
        inventory = copy.deepcopy(INV)
        inventory['nets']['net[0]'] = {}
        with self.assertRaisesRegex(AssertionError, 'aliases identities'):
            positional_reference(TEXT, inventory, ORDER)
    def test_extracted_header_bijection_and_no_body(self):
        adapted, audit = normalized_extracted_header(SPICE, PORTS)
        self.assertTrue(adapted.startswith('.subckt ' + MASTER + ' ' + ' '.join(ORDER)))
        self.assertEqual(audit['port_count'], 345)
        self.assertTrue(audit['rails_are_not_merged'])
    def test_unexpected_extracted_pin_or_model_body_rejected(self):
        for text in [SPICE.replace('DATA<341>', 'UNKNOWN'), SPICE.replace('\n.ends', '\nXillegal a b model\n.ends')]:
            with self.assertRaises(AssertionError): normalized_extracted_header(text, PORTS)

if __name__ == '__main__': unittest.main()
