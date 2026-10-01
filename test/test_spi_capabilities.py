"""Capability gate accepts only complete, retained, decoded protocol results."""
from dataclasses import replace
import contextlib
import hashlib
import io
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from pinwheel_host import Program, Result, PAIRED_FORMAT
from test_resolved_pads import exercise_peer

spec = importlib.util.spec_from_file_location('spi_capabilities', ROOT / 'scripts/check-spi-capabilities.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def metadata(name='spi-mode0-1byte'):
    return dict(name=name, mode=0, byte_count=1, half_cycles=4, tx_payload=0xa6,
                rx_payload=0x96, sample_slots=8, transfer_cycles=68)


class MetadataChecks(unittest.TestCase):
    def test_metadata_must_agree_with_captured_image_names_and_capacity(self):
        images = {'spi-mode0-1byte': Program((4,), 0)}
        item = metadata()
        self.assertEqual(gate.fixture_metadata(json.dumps([item]), images), [item])
        for changes in [dict(byte_count=True), dict(mode=4), dict(half_cycles=257),
                        dict(sample_slots=16), dict(transfer_cycles=64), dict(rx_payload=256),
                        dict(name='unbound')]:
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                gate.fixture_metadata(json.dumps([dict(item, **changes)]), images)
        with self.assertRaises(ValueError):
            gate.fixture_metadata(json.dumps([item, item]), images)

    def test_capture_slot_corruption_stays_canonical_but_changes_source(self):
        # Capture input0 into slot7; corruption redirects that observation to0.
        source = Program((7 << 6 | 3 << 9 | (1 | 7 << 2) << 29, 4), 1,
                         image_format=PAIRED_FORMAT)
        corrupt = gate.collapse_capture_slots(source)
        self.assertNotEqual(corrupt.words, source.words)
        self.assertEqual((corrupt.words[0] >> 29) & 63, 1)
        self.assertEqual(len(corrupt.upload_words()), 290)
        with self.assertRaisesRegex(RuntimeError, 'no nonzero'):
            gate.collapse_capture_slots(Program((4,), 0))


class CapabilityResultChecks(unittest.TestCase):
    def run_case(self, fault=None):
        events = []
        simulation = SimpleNamespace(device=None)
        class Host:
            def __init__(self, sim, *, image_format):
                self.edges = self.frames = 0
                self.reads = 0
            def reset(self):
                events.append('reset')
            def upload(self, program):
                events.append('upload')
                program.upload_words()
            def start(self):
                events.append('start')
                exercise_peer(simulation.device)
            def read_result(self, **kwargs):
                events.append('read')
                self.reads += 1
                result = Result(0x69, 5, False, False)
                if fault == 'reply':
                    result = replace(result, samples=0x65)
                if fault == 'retention' and self.reads == 2:
                    result = replace(result, samples=0)
                if fault in ('overrun', 'rejected'):
                    result = replace(result, **{fault: True})
                return result
            def consume(self):
                events.append('consume')
            def result_status(self):
                events.append('status')
                return int(fault == 'consume')
        with tempfile.TemporaryDirectory() as directory, patch.object(gate, 'Host', Host):
            result = gate.run_spi_cases(simulation, {'spi-mode0-1byte': Program((4,), 0)},
                [metadata()], Path(directory), lambda name, program: events.append('certify'))
        return result, events

    def test_reply_is_decoded_retained_and_consumed_after_certificate(self):
        result, events = self.run_case()
        self.assertEqual(events, ['reset', 'certify', 'upload', 'start', 'read', 'read', 'consume', 'status'])
        self.assertEqual(result['cases'][0]['decoded_wire_bytes'], [0x96])
        self.assertTrue(result['cases'][0]['retained_twice'])

    def test_wrong_reply_error_carries_actual_observation(self):
        with self.assertRaises(gate.SPIReplyMismatch) as error:
            self.run_case('reply')
        self.assertEqual(error.exception.case['decoded_wire_bytes'], [0xa6])
        self.assertEqual(error.exception.expected, [0x96])
        self.assertTrue(error.exception.case['consumed'])

    def test_flags_retention_and_consumption_fail_closed(self):
        for fault, message in [('overrun', 'outcome/flags'), ('rejected', 'outcome/flags'),
                               ('retention', 'retained result'), ('consume', 'consumption')]:
            with self.subTest(fault=fault), self.assertRaisesRegex(RuntimeError, message):
                self.run_case(fault)


class CapabilityReceiptChecks(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        files = ['Pinwheel.lean', 'Pinwheel/Fixture.lean', 'lakefile.toml', 'lake-manifest.json',
                 'lean-toolchain', *['test/' + name for name in ('Loader.lean', 'SPITransactions.lean',
                 'PairedValidationEmit.lean', 'paired_chip.sv', 'host_bridge.sv')],
                 *['scripts/' + name for name in ('check-spi-capabilities.py', 'pinwheel_host.py',
                 'pinwheel_sim.py', 'host_demo.py', 'pad_io.py', 'pad_peers.py', 'paired_execution.py',
                 'paired_image_certificate.py', 'execution-vectors.py', 'validation_run.py', 'process_group.py')],
                 'build/tools/firtool-1.159.0/bin/circt-opt',
                 'build/tools/oss-cad-suite/bin/iverilog', 'build/tools/oss-cad-suite/bin/vvp']
        for name in files:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Fixture ' + name)
        hashes = {}
        for name in ('RM_IHPSG13_1P_512x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v'):
            path = self.root / 'build/storage/macros' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Fixture model ' + name)
            hashes['verilog/' + name] = hashlib.sha256(path.read_bytes()).hexdigest()
        lock = self.root / 'tools/storage-macros.json'
        lock.parent.mkdir()
        lock.write_text(json.dumps(dict(files_sha256=hashes)))
        self.sequence = 0
        self.on_event = lambda event: None

    def run_cli(self):
        self.sequence += 1
        self.out = self.root / 'build/host' / ('fixture-' + str(self.sequence))
        test = self
        class Commands:
            def __init__(self, *args, **kwargs):
                self.records = []
            def __call__(self, command, label):
                self.records.append(dict(label=label, stubbed=True))
                if label == 'compile-spi-programs':
                    entries, lines = [], []
                    for mode in range(4):
                        for count in (1, 2):
                            name = f'spi-mode{mode}-{count}byte' + ('s' if count == 2 else '')
                            entries.append(dict(metadata(name), mode=mode, byte_count=count,
                                tx_payload=0xa6 if count == 1 else 0xa653,
                                rx_payload=0x96 if count == 1 else 0x963c,
                                sample_slots=8 * count, transfer_cycles=(16 * count + 1) * 4))
                            word = 7 << 6 | 3 << 9 | (1 | 7 << 2) << 29
                            lines.append(name + ' 1 0 0 ' + str(word) + ' 4')
                    (test.out / 'images.txt').write_text('\n'.join(lines) + '\n')
                    (test.out / 'metadata.json').write_text(json.dumps(entries))
                if label == 'compile-legacy-programs':
                    path = test.root / 'build/loader/images.txt'
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text('uart 0 0 0 4\n')
                if label == 'emit':
                    (test.out / 'chip.mlir').write_text('Generated MLIR')
                if label == 'compile-simulation':
                    (test.out / 'host.vvp').write_text('Generated executable')
                test.on_event(label)
                if label == 'export':
                    return 'Generated RTL'
                return 'Paired image certificate: kernel checked; standard axioms only.'
        class Simulation:
            def __init__(self, *args):
                self.device = None
            def __enter__(self):
                return self
            def __exit__(self, *args):
                test.on_event('closed')
        def run_cases(sim, images, entries, out, certify, **kwargs):
            for item in entries:
                certify(item['name'], replace(images[item['name']], image_format=PAIRED_FORMAT))
            test.on_event('spi-consumed')
            if entries[0]['name'].endswith(('-collapsed-capture-slots', '-late-peer')):
                case = dict(name=entries[0]['name'], decoded_wire_bytes=[0],
                            result=dict(samples=0, outcome=5), retained_twice=True, consumed=True)
                raise gate.SPIReplyMismatch(case, [0x96])
            return dict(cases=[dict(name=item['name']) for item in entries], edges=1, frames=1)
        with patch.object(gate, 'ROOT', self.root), patch.object(gate, 'Commands', Commands), \
                patch.object(gate, 'Simulation', Simulation), patch.object(gate, 'run_spi_cases', run_cases), \
                patch.object(gate, 'reset_active_spi', return_value=dict(boundary='stubbed control')), \
                patch.object(gate, 'demonstrate', return_value=dict(cases=[])), \
                patch.object(sys, 'argv', ['check-spi-capabilities.py', '--tag', 'fixture-' + str(self.sequence)]), \
                contextlib.redirect_stdout(io.StringIO()):
            gate.main()
        return json.loads((self.out / 'report.json').read_text())

    def test_receipt_binds_generated_bytes_before_consumption(self):
        report = self.run_cli()
        self.assertEqual(report['executable_sha256'], hashlib.sha256(b'Generated executable').hexdigest())
        self.assertEqual(report['rtl_sha256'], hashlib.sha256(b'Generated RTL').hexdigest())
        self.assertEqual(report['mlir_sha256'], hashlib.sha256(b'Generated MLIR').hexdigest())

    def test_changed_generated_bytes_cannot_publish_success(self):
        for name in ('chip.mlir', 'design.sv', 'host.vvp'):
            def mutate(event, name=name):
                if event == 'closed':
                    (self.out / name).write_text('Changed after consumption')
            self.on_event = mutate
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'Generated artifact changed'):
                self.run_cli()
            self.assertFalse((self.out / 'report.json').exists())

    def test_changed_certificate_cannot_rebind_kernel_check(self):
        name = 'spi-mode0-1byte-certificate.lean'
        for event_name, message in [('spi-mode0-1byte-certificate', 'during kernel check'),
                                     ('closed', 'after kernel check')]:
            def mutate(event, event_name=event_name):
                if event == event_name:
                    (self.out / name).write_text('Changed proof bytes after kernel consumption')
            self.on_event = mutate
            with self.subTest(event=event_name), self.assertRaisesRegex(RuntimeError, message):
                self.run_cli()
            self.assertFalse((self.out / 'report.json').exists())

    def test_changed_captured_fixture_copies_cannot_publish_success(self):
        for name in ('spi-images.txt', 'spi-metadata.json', 'legacy-images.txt'):
            def mutate(event, name=name):
                if event == 'closed':
                    (self.out / name).write_text('Changed captured bytes after consumption')
            self.on_event = mutate
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'Captured input changed'):
                self.run_cli()
            self.assertFalse((self.out / 'report.json').exists())


if __name__ == '__main__':
    unittest.main()
