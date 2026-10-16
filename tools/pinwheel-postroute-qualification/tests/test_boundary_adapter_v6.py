from pathlib import Path
import re
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_boundary_adapter_v5 import TEXT, INV, ORDER, PORTS, SPICE, PREFIX
from boundary_adapter_v6 import named_reference, aliased_extracted_header, pin_aliases
from boundary_adapter_v5 import MASTER

class SafeNames(unittest.TestCase):
    def test_named690_contacts_and_unique_aliases(self):
        adapted, audit = named_reference(TEXT, INV, ORDER)
        self.assertTrue(adapted.startswith(PREFIX))
        self.assertEqual(audit['native_macro_contacts_checked'], 690)
        self.assertEqual(len(set(audit['canonical_to_safe_pin_aliases'].values())), 345)
        for clause in re.findall(re.escape(MASTER) + r' memory[01] \((.*?)\);', adapted):
            associations = re.findall(r'\.(PW_SRAM_PIN_\d+)\(([^()]*)\)', clause)
            self.assertEqual([pin for pin, net in associations], list(pin_aliases(ORDER).values()))
            self.assertEqual(len(associations), 345)
            self.assertEqual([net for pin, net in associations][-3:], ['VPWR', 'VPWR', 'VGND'])
    def test_extracted_header_same_aliases_preserves_instance_nodes(self):
        instance = 'Xmemory n0 n1 original-physical-node-list ' + MASTER + '\n'
        adapted, audit = aliased_extracted_header(SPICE + instance, PORTS, ORDER)
        self.assertTrue(adapted.endswith(instance))
        self.assertEqual(adapted.splitlines()[0].split()[2:], list(pin_aliases(ORDER).values()))
        self.assertTrue(audit['no_interior_conductive_model_added'])

if __name__ == '__main__': unittest.main()
