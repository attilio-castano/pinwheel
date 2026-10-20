"""Strict input boundary checks for the frontend artifact adapter.

These exercise rejection of changed interpreter inputs, not proof of frontend
behavior; the universal Lean endpoint certificate supplies that evidence.
"""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import buffered_serial_readback as sr


class BufferedSerialReadbackTests(unittest.TestCase):
    def setUp(self):
        self.rb = sr.backend()
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / 'assembly.json'
        self.interface = {'schema': 1, 'module': self.rb.TOP}
        for category, contract in [('inputs', self.rb.INPUTS), ('registers', self.rb.REGISTERS),
                                   ('outputs', self.rb.OUTPUTS)]:
            self.interface[category] = [dict(name=n, width=w, **({'reference': n}
                if category == 'registers' else {})) for n, (w, _) in contract.items()]

    def check(self, interface):
        self.path.write_text(json.dumps(interface))
        sr.check_interface(self.rb, self.path)

    def test_exact_contract_and_private_import(self):
        self.check(self.interface)
        self.assertEqual((len(self.rb.INPUTS), len(self.rb.REGISTERS), len(self.rb.OUTPUTS)), (31, 13, 19))
        self.assertEqual(sum(w for w, _ in self.rb.REGISTERS.values()), 389)
        import backend_readback
        self.assertNotEqual(backend_readback.TOP, self.rb.TOP)
        self.assertNotIn('r_response', backend_readback.REGISTERS)

    def test_state_and_port_changes_rejected(self):
        for category in ('inputs', 'registers', 'outputs'):
            changed = copy.deepcopy(self.interface)
            changed[category][0]['width'] += 1
            with self.subTest(category=category), self.assertRaises(ValueError):
                self.check(changed)
            changed = copy.deepcopy(self.interface)
            changed[category].append(changed[category][0])
            with self.subTest(duplicate=category), self.assertRaises(ValueError):
                self.check(changed)

    def test_response_alias_and_duplicate_json_rejected(self):
        changed = copy.deepcopy(self.interface)
        response = next(e for e in changed['registers'] if e['name'] == 'r_response')
        response['reference'] = 'r_request'
        with self.assertRaises(ValueError):
            self.check(changed)
        self.path.write_text('{"schema":1,"schema":1}')
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON key'):
            sr.check_interface(self.rb, self.path)


if __name__ == '__main__':
    unittest.main()
