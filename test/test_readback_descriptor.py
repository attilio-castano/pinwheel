"""Lean-emitted read-back descriptors configure the Streaming and Buffered importers.

The importer reads checked-in copies (scripts/readback_descriptors); they must
equal a fresh `lake env lean --run` emission byte for byte. The emission tests
are skipped when `lake` is not available.
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

READY = (('core', 1), ('core', 2), ('frontend', 1))


@unittest.skipUnless(shutil.which('lake'), 'needs lake to emit the descriptors')
class FreshEmission(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = ROOT / 'build' / f'readback-descriptors-test-{os.getpid()}'
        for emitter in D.EMITTERS:
            subprocess.run(['lake', 'build', *D.emitter_imports(emitter)],
                           cwd=ROOT, check=True, capture_output=True)
            subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '--run', emitter,
                            str(cls.out / Path(emitter).stem)],
                           cwd=ROOT, check=True, capture_output=True)

    def emitted(self, name):
        return self.out / Path(D.emitter_for(name)).stem / f'{name}.json'

    def test_each_emitter_writes_only_its_descriptors(self):
        for emitter, names in D.EMITTERS.items():
            with self.subTest(emitter=emitter):
                self.assertEqual(sorted(p.name for p in (self.out / Path(emitter).stem).iterdir()),
                                 sorted(n + '.json' for n in names))

    def test_checked_in_copies_are_current(self):
        self.assertEqual(sorted(p.name for p in D.DIRECTORY.iterdir()), sorted(n + '.json' for n in D.NAMES))
        for name in D.NAMES:
            with self.subTest(descriptor=name):
                self.assertEqual(self.emitted(name).read_bytes(),
                                 (D.DIRECTORY / f'{name}.json').read_bytes(),
                                 'stale checked-in descriptor; regenerate it (see docs/development.md)')

    def test_fresh_descriptor_configures_like_checked_in(self):
        for kind, addr_bits in READY:
            with self.subTest(kind=kind, addr_bits=addr_bits):
                fresh = self.emitted(adapter.descriptor_name(kind, addr_bits))
                self.assertEqual(D.configuration(adapter.backend(kind, addr_bits, descriptor=fresh)),
                                 D.configuration(adapter.backend(kind, addr_bits)))


class Emitters(unittest.TestCase):
    def test_emitters_split_the_names(self):
        names = [name for names in D.EMITTERS.values() for name in names]
        self.assertEqual(len(names), len(set(names)))

    def test_streaming_emitter_does_not_import_buffered_modules(self):
        imports = D.emitter_imports('test/StreamingReadyReadbackDescriptor.lean')
        self.assertIn('Pinwheel.Hardware.StreamingReady.CoreEmit', imports)
        self.assertFalse([m for m in imports if '.Buffered.' in m])

    def test_buffered_emitter_imports_its_modules(self):
        self.assertEqual(D.emitter_imports('test/BufferedReadbackDescriptor.lean'),
                         ['Pinwheel.Hardware.Buffered.Sram', 'Pinwheel.Hardware.Buffered.Serial',
                          'Pinwheel.Hardware.Readback.Descriptor'])


class CheckedIn(unittest.TestCase):
    def test_release_state_bits(self):
        """The depth-two core and the frontend hold the chip's 6,039 state bits."""
        bits = {name: sum(port['width'] for port in D.checked_in(name)['registers'])
                for name in ('ready-core-d2', 'frontend')}
        self.assertEqual(bits, {'ready-core-d2': 4636, 'frontend': 1403})

    def test_changed_term_reaches_the_importer(self):
        changed = copy.deepcopy(D.checked_in('ready-core-d2'))
        changed['registers'][3]['term'] = '.word 4#6'
        built = D.configuration(adapter.backend('core', 1, descriptor=changed))
        self.assertEqual(D.differences(D.configuration(adapter.backend('core', 1)), built), ['REGISTERS'])

    def test_reordered_ports_reach_the_importer(self):
        changed = copy.deepcopy(D.checked_in('frontend'))
        changed['outputs'][0], changed['outputs'][1] = changed['outputs'][1], changed['outputs'][0]
        built = D.configuration(adapter.backend('frontend', descriptor=changed))
        self.assertEqual(D.differences(D.configuration(adapter.backend('frontend')), built), ['OUTPUTS'])

    def test_families_follow_indexed_registers(self):
        self.assertEqual(D.families(D.checked_in('ready-core-d4')['registers']),
                         [('word', 'word', 64, 6), ('tx_word', 'txWord', 4, 2), ('tx_bits', 'txBits', 4, 2),
                          ('rx_word', 'rxWord', 4, 2), ('rx_bits', 'rxBits', 4, 2)])

    def test_cores_differ_only_in_module_and_circuit(self):
        for depth in ('d2', 'd4'):
            plain, ready = D.checked_in('streaming-core-' + depth), D.checked_in('ready-core-' + depth)
            self.assertEqual({key for key in plain if plain[key] != ready[key]}, {'module', 'circuit'})

    def test_descriptor_for_another_module_is_rejected(self):
        with self.assertRaises(ValueError):
            adapter.backend('core', 1, descriptor=D.checked_in('ready-core-d4'))
        with self.assertRaises(ValueError):
            adapter.backend('core', 1, tx_layout='shift', descriptor=D.checked_in('ready-core-d2'))

    def test_shift_layout_starts_from_the_streaming_core(self):
        self.assertEqual(adapter.descriptor_name('core', 1, 'shift'), 'streaming-core-d2')
        explicit = adapter.backend('core', 1, tx_layout='shift', descriptor=D.DIRECTORY / 'streaming-core-d2.json')
        self.assertEqual(D.configuration(explicit), D.configuration(adapter.backend('core', 1, tx_layout='shift')))
        self.assertNotIn('r_tx_head', explicit.REGISTERS)

    def test_buffered_tables_cover_every_port(self):
        """The Buffered adapters' constructor tables leave no descriptor field out."""
        import buffered_serial_readback as serial
        import buffered_sram_readback as sram
        counts = lambda d: [len(d[key]) for key in ('inputs', 'registers', 'outputs')]
        self.assertEqual(counts(serial.DESCRIPTOR), [len(serial.RAW_INPUTS) + len(serial.STATUS),
                                                    len(serial.REGISTERS), len(serial.CORE_OUTPUTS) + 2])
        # Two memory data inputs; 64 metadata, 16 branch, branch_written and start_word
        # registers; five memory port outputs.
        self.assertEqual(counts(sram.DESCRIPTOR), [len(sram.BASE_INPUTS) + 2, len(sram.CORE_REGISTERS) + 82,
                                                  len(sram.BASE_OUTPUTS) + 5])

    def test_nested_terms_keep_their_parentheses(self):
        outputs = D.table(D.checked_in('buffered-sram')['outputs'])
        self.assertEqual(outputs['mem_addr1'], (6, '.port (.address true)'))
        self.assertEqual(outputs['mem_data'], (64, '.port .data'))

    def test_unknown_name_is_rejected(self):
        with self.assertRaises(ValueError):
            D.checked_in('core-d2')


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
