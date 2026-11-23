"""Lean-emitted read-back descriptors must configure the importer exactly as the
hand-typed tables do, and any drift in names, widths, terms or order must show.

The descriptors are emitted fresh with `lake env lean --run`; the test is
skipped when `lake` is not available.
"""
import copy
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import readback_descriptor as D
import streaming_ready_readback as adapter

MODULES = (('core', 1, 'core-d2'), ('core', 2, 'core-d4'), ('frontend', 1, 'frontend'))


@unittest.skipUnless(shutil.which('lake'), 'needs lake to emit the descriptors')
class ReadbackDescriptor(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = ROOT / 'build' / f'readback-descriptors-test-{os.getpid()}'
        subprocess.run(['lake', 'build', 'Pinwheel.Hardware.StreamingReady.CoreEmit',
                        'Pinwheel.Hardware.StreamingReady.Wiring', 'Pinwheel.Hardware.Streaming.FrontendEmit'],
                       cwd=ROOT, check=True, capture_output=True)
        subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run',
                        'test/StreamingReadyReadbackDescriptor.lean', str(cls.out)],
                       cwd=ROOT, check=True, capture_output=True)
        cls.descriptors = {name: D.load(cls.out / f'{name}.json') for _, _, name in MODULES}

    def test_descriptors_reproduce_hand_tables(self):
        for kind, addr_bits, name in MODULES:
            with self.subTest(module=name):
                legacy = D.configuration(adapter.backend(kind, addr_bits))
                built = D.configuration(adapter.backend(kind, addr_bits, descriptor=self.descriptors[name]))
                self.assertEqual(D.differences(legacy, built), [])

    def test_changed_term_is_caught(self):
        changed = copy.deepcopy(self.descriptors['core-d2'])
        changed['registers'][3]['term'] = '.word 4#6'
        legacy = D.configuration(adapter.backend('core', 1))
        built = D.configuration(adapter.backend('core', 1, descriptor=changed))
        self.assertEqual(D.differences(legacy, built), ['REGISTERS'])

    def test_reordered_ports_are_caught(self):
        changed = copy.deepcopy(self.descriptors['frontend'])
        changed['outputs'][0], changed['outputs'][1] = changed['outputs'][1], changed['outputs'][0]
        legacy = D.configuration(adapter.backend('frontend'))
        built = D.configuration(adapter.backend('frontend', descriptor=changed))
        self.assertEqual(D.differences(legacy, built), ['OUTPUTS'])

    def test_families_follow_indexed_registers(self):
        self.assertEqual(D.families(self.descriptors['core-d4']['registers']),
                         [('word', 'word', 64, 6), ('tx_word', 'txWord', 4, 2), ('tx_bits', 'txBits', 4, 2),
                          ('rx_word', 'rxWord', 4, 2), ('rx_bits', 'rxBits', 4, 2)])

    def test_shift_layout_is_rejected(self):
        with self.assertRaises(ValueError):
            adapter.backend('core', 1, tx_layout='shift', descriptor=self.descriptors['core-d2'])


class DescriptorFormat(unittest.TestCase):
    def test_duplicate_names_are_rejected(self):
        path = ROOT / 'build' / f'readback-descriptor-duplicate-{os.getpid()}.json'
        path.parent.mkdir(exist_ok=True)
        path.write_text('{"schema": "%s", "inputs": [{"name": "a", "width": 1, "term": ".a"},'
                        ' {"name": "a", "width": 1, "term": ".b"}], "registers": [], "outputs": []}' % D.SCHEMA)
        try:
            with self.assertRaises(ValueError):
                D.load(path)
        finally:
            path.unlink()


if __name__ == '__main__':
    unittest.main()
