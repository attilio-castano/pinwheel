"""Independent I2C wire/result checks and fail-closed capability byte custody."""
from dataclasses import replace
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from capability_receipt import CapabilityEvidence
from i2c_peers import I2CBusClearPeer, I2CWritePeer
from pad_io import PadObservation
from pinwheel_host import Program, Result, PAIRED_FORMAT
from protocol_tool_closure import CIRCT_SEEDS, ICARUS_SEEDS, ProtocolToolClosure, VPI_NAMES

spec = importlib.util.spec_from_file_location('i2c_capabilities', ROOT / 'scripts/check-i2c-capabilities.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def fixture_tools(root):
    packages = {'circt': {'directory': 'firtool-1.159.0'},
                'oss-cad-suite': {'directory': 'oss-cad-suite'}}
    config = root / 'tools/hardware-toolchain.json'
    config.parent.mkdir(parents=True, exist_ok=True)
    config.write_text(json.dumps(dict(platform='darwin-arm64', packages=packages)))
    for package, names in [('firtool-1.159.0', CIRCT_SEEDS),
            ('oss-cad-suite', (*ICARUS_SEEDS, *('lib/ivl/' + n for n in VPI_NAMES)))]:
        for name in names:
            path = root / 'build/tools' / package / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Fixture ' + package + '/' + name)
    return (root / 'build/tools/firtool-1.159.0/bin/circt-opt',
            root / 'build/tools/oss-cad-suite/bin/iverilog',
            root / 'build/tools/oss-cad-suite/bin/vvp')


def fixture_vvp(root):
    backend = root / 'build/tools/oss-cad-suite/lib/ivl'
    return ''.join(':vpi_module "' + str(backend / n) + '";\n' for n in sorted(VPI_NAMES)) + 'Generated executable\n'


def write_metadata(name='write', count=2, acks=None, **changes):
    acks = [0] * (count + 1) if acks is None else acks
    done = next((k + 1 for k, bit in enumerate(acks) if bit), len(acks))
    item = dict(name=name, address=0x53, payload_bytes=[0xa6, 0x53][:count], ack_bits=acks,
        phase_cycles=4, wait_cycles=32, stretch_cycles=0, scl_stuck=False,
        expected_samples=sum(bit << index for index, bit in enumerate(acks[:done])),
        expected_outcome=5, expected_clock_count=9 * done)
    item.update(changes)
    return item


def clear_metadata(name='clear', release=9, **changes):
    item = dict(name=name, phase_cycles=4, timeout_cycles=32,
        recovery_policy='nine_rises_release_only', capture_slot=0,
        release_after_pulses=release, stretch_cycles=0, scl_stuck=False,
        expected_pulses=9, expected_sda_sample=release is not None, expected_outcome=5)
    item.update(changes)
    return item


def resolved(enabled, drive):
    # Independent low/release resolution of the two declared joined wire pairs.
    wires = 255
    for sense, output in ((0, 2), (1, 3)):
        if enabled & (1 << (output - 2)) or drive.enabled & (1 << sense):
            wires &= ~((1 << sense) | (1 << output))
    return PadObservation(0, 0, enabled << 2, wires, 255)


class WireFixture:
    def __init__(self, peer):
        self.peer, self.cycle = peer, 0
        self.observation = PadObservation(0, 0, 0, 255, 255)

    def tick(self, enabled, cycles):
        for _ in range(cycles):
            drive = self.peer.drive(self.cycle, self.observation, 0)
            self.observation = resolved(enabled, drive)
            self.cycle += 1


def exercise_write(peer, corrupt=False):
    fixture, h = WireFixture(peer), peer.phase_cycles
    fixture.tick(0, h)
    fixture.tick(2, h)
    outgoing = list(peer.expected_bytes[:peer.completed_bytes])
    if corrupt:
        outgoing[0] ^= 128
    for index, byte in enumerate(outgoing):
        for bit in [*((byte >> k) & 1 for k in range(7, -1, -1)), 1]:
            data = 0 if bit else 2
            fixture.tick(1 | data, h)
            fixture.tick(data, h + peer.stretch_cycles + 2)
    fixture.tick(1, h)
    fixture.tick(3, h)
    fixture.tick(2, h + peer.stretch_cycles + 2)
    fixture.tick(0, h + 2)
    return fixture


class IndependentWireChecks(unittest.TestCase):
    def test_both_lengths_every_first_nack_and_stretched_ack(self):
        for count in (1, 2):
            for nack in (None, *range(count + 1)):
                for stretch in (0, 1, 3):
                    acks = [int(index == nack) for index in range(count + 1)]
                    with self.subTest(count=count, nack=nack, stretch=stretch):
                        peer = I2CWritePeer(0x53, [0xa6, 0x53][:count], acks, stretch_cycles=stretch)
                        exercise_write(peer)
                        report = peer.check()
                        self.assertEqual(report['clock_count'], 9 * (count + 1 if nack is None else nack + 1))
                        self.assertEqual(report['observed_ack_bits'], acks[:peer.completed_bytes])
                        self.assertTrue(report['stopped'])

    def test_wrong_address_is_rejected_by_wire_bytes_not_mailbox(self):
        peer = I2CWritePeer(0x53, [0xa6, 0x53], [0, 0, 0])
        exercise_write(peer, corrupt=True)
        with self.assertRaisesRegex(RuntimeError, 'byte/ACK order'):
            peer.check()

    def test_ack_ownership_and_early_stop_fail(self):
        peer = I2CWritePeer(0x53, [0xa6], [0, 0])
        peer.started, peer.bits, peer.previous, peer.sda_sink = True, [0] * 8, (0, 0), True
        with self.assertRaisesRegex(RuntimeError, 'drives SDA during peer ACK'):
            peer.drive(20, PadObservation(0, 0, 8, 245, 255), 0)
        peer = I2CWritePeer(0x53, [0xa6], [0, 0])
        peer.started, peer.previous = True, (1, 0)
        with self.assertRaisesRegex(RuntimeError, 'STOP before complete'):
            peer.drive(20, PadObservation(0, 0, 0, 255, 255), 0)

    def test_bus_clear_all_releases_and_still_stuck_have_nine_rises(self):
        for release in (*range(1, 10), None):
            with self.subTest(release=release):
                peer = I2CBusClearPeer(release)
                fixture = WireFixture(peer)
                fixture.tick(0, 4)
                for _ in range(9):
                    fixture.tick(1, 4)
                    fixture.tick(0, 6)
                fixture.tick(0, 4)
                report = peer.check()
                self.assertEqual(report['pulse_rises'], 9)
                self.assertFalse(report['controller_stop_claimed'])
                self.assertEqual(report['sda_released_at'] is not None, release is not None)
                self.assertEqual(report['natural_stop'], release == 9)

    def test_bus_clear_tenth_pulse_sda_drive_and_stuck_clock_controls(self):
        peer = I2CBusClearPeer(None)
        fixture = WireFixture(peer)
        fixture.tick(0, 4)
        for _ in range(9):
            fixture.tick(1, 4)
            fixture.tick(0, 6)
        fixture.tick(1, 4)
        with self.assertRaisesRegex(RuntimeError, 'more than nine'):
            fixture.tick(0, 6)
        peer = I2CBusClearPeer(1)
        with self.assertRaisesRegex(RuntimeError, 'always release SDA'):
            peer.drive(0, PadObservation(0, 0, 8, 255, 255), 0)
        for peer in (I2CBusClearPeer(9, scl_stuck=True), I2CWritePeer(0x53, [0xa6], [0, 0], scl_stuck=True)):
            fixture = WireFixture(peer)
            fixture.tick(0, 40)
            peer.check(timeout=True)

    def test_guard_loss_is_explicit_and_keeps_a_partial_wire_trace(self):
        for peer in (I2CWritePeer(0x53, [0xa6], [0, 0], fault_after_rises=1),
                     I2CBusClearPeer(9, fault_after_rises=1)):
            with self.subTest(peer=type(peer).__name__):
                fixture = WireFixture(peer)
                fixture.tick(0, 4)
                if isinstance(peer, I2CWritePeer):
                    fixture.tick(2, 4)
                fixture.tick(1, 4)
                fixture.tick(0, 12)
                report = peer.check(fault=True)
                self.assertTrue(report['guard_clock_lost'])

    def test_guard_loss_allows_high_to_reach_sampler_before_forcing_low(self):
        for peer in (I2CWritePeer(0x53, [0xa6], [0, 0], fault_after_rises=1), I2CBusClearPeer(9, fault_after_rises=1)):
            peer.previous, peer.fall_cycle = (0, 1), 10
            if isinstance(peer, I2CWritePeer):
                peer.started, peer.start_cycle = True, 0
            high = PadObservation(0, 0, 0, 255, 255)
            enabled = [peer.drive(cycle, high, 0).enabled & 1 for cycle in (14, 15, 16)]
            self.assertEqual(enabled, [0, 0, 1])


class FixtureChecks(unittest.TestCase):
    def test_metadata_is_exact_and_peer_configuration_drives_expectations(self):
        images = {'write': Program((4,), 0)}
        good = write_metadata()
        self.assertEqual(gate.metadata('write', json.dumps([good]), images), [good])
        for change in (dict(address=128), dict(address=True), dict(ack_bits=[0, 1]),
                       dict(expected_samples=4), dict(expected_clock_count=18), dict(scl_stuck=1),
                       dict(expected_outcome=6), dict(name='../escape'), dict(extra=1)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                gate.metadata('write', json.dumps([dict(good, **change)]), images)
        images = {'clear': Program((4,), 0)}
        good = clear_metadata()
        self.assertEqual(gate.metadata('clear', json.dumps([good]), images), [good])
        for change in (dict(expected_sda_sample=1), dict(expected_pulses=10),
                       dict(recovery_policy='automatic-retry'), dict(capture_slot=1),
                       dict(release_after_pulses=0), dict(expected_sda_sample=False)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                gate.metadata('clear', json.dumps([dict(good, **change)]), images)

    def test_mutants_are_canonical_and_change_distinct_contracts(self):
        words = [3, 2 | 2 << 6, *([0] * 111), 2 | 11 << 35, 4]
        for bit in range(8):
            for phase in range(4):
                words[2 + 4 * bit + phase] = (2 if phase == 2 else 0) | 1 << 6
                words[2 + 4 * (18 + bit) + phase] = (2 if phase == 2 else 0) | 3 << 6
        program = Program(tuple(words), len(words) - 1, image_format=PAIRED_FORMAT)
        for mutate in (gate.wrong_ack_slot, gate.wrong_status, gate.push_pull_sda, gate.swap_address_data):
            with self.subTest(mutate=mutate.__name__):
                corrupted = mutate(program)
                self.assertNotEqual(corrupted.words, program.words)
                self.assertEqual(len(corrupted.upload_words()), 290)


class ByteCustodyChecks(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.out = self.root / 'out'
        self.out.mkdir()
        self.source, self.tool, self.model = [self.root / name for name in ('source', 'tool', 'model')]
        for path in (self.source, self.tool, self.model):
            path.write_text(path.name)
        self.evidence = CapabilityEvidence(self.root, self.out, [self.source], [self.tool], [self.model])

    def test_capture_uses_exact_bytes_and_does_not_reopen_original(self):
        data = self.evidence.capture(self.source, 'captured.txt')
        self.source.write_text('Atomically replaced original')
        self.assertEqual(data, b'source')
        self.assertEqual(self.evidence.captured_inputs_sha256['captured.txt'], hashlib.sha256(data).hexdigest())
        self.source.write_text('source')
        self.evidence.closeout()

    def test_source_tool_model_generated_and_captured_mutations_fail(self):
        generated = self.out / 'generated'
        generated.write_text('generated')
        self.evidence.freeze_generated(generated)
        self.evidence.capture(self.source, 'captured.txt')
        for path, expected in ((self.source, 'Source'), (self.tool, 'Tool'), (self.model, 'SRAM'),
                               (generated, 'Generated'), (self.out / 'captured.txt', 'Captured')):
            original = path.read_bytes()
            path.write_text('Different after consumption')
            with self.subTest(path=path.name), self.assertRaisesRegex(RuntimeError, expected):
                self.evidence.closeout()
            path.write_bytes(original)
        self.evidence.closeout()

    def test_certificate_cannot_change_during_or_after_kernel_consumption(self):
        source = Program((4,), 0, image_format=PAIRED_FORMAT)
        def corrupt(command, label):
            (self.out / 'during-certificate.lean').write_text('Different proof bytes')
            return 'Paired image certificate: kernel checked; standard axioms only.'
        with self.assertRaisesRegex(RuntimeError, 'during kernel check'):
            self.evidence.certify('during', source, corrupt)
        self.assertFalse(self.evidence.image_certificates)
        self.evidence = CapabilityEvidence(self.root, self.out, [self.source], [self.tool], [self.model])
        self.evidence.certify('after', source, lambda *args: 'Paired image certificate: kernel checked; standard axioms only.')
        (self.out / 'after-certificate.lean').write_text('Different later proof')
        with self.assertRaisesRegex(RuntimeError, 'Generated artifact changed'):
            self.evidence.closeout()


class BundledToolClosureChecks(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.tools = fixture_tools(self.root)
        self.closure = ProtocolToolClosure(self.root, *self.tools, environment={})

    def test_backend_runtime_plugin_and_shared_library_mutations_refuse(self):
        out = self.root / 'out'
        out.mkdir()
        evidence = CapabilityEvidence(self.root, out, [], self.closure.files, [])
        wrapper = self.tools[2].read_bytes()
        for name in ('oss-cad-suite/libexec/vvp', 'oss-cad-suite/libexec/ivlpp',
                     'oss-cad-suite/lib/ivl/system.vpi', 'oss-cad-suite/lib/libvvp.1.14.0.dylib',
                     'firtool-1.159.0/lib/libCIRCTHW.dylib'):
            path = self.root / 'build/tools' / name
            original = path.read_bytes()
            path.write_text('Different actual executable/plugin bytes; launcher unchanged')
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'Tool changed'):
                evidence.closeout()
            self.assertEqual(self.tools[2].read_bytes(), wrapper)
            path.write_bytes(original)
        self.closure.closeout()
        evidence.closeout()

    def test_inventory_additions_and_missing_seed_fail(self):
        extra = self.root / 'build/tools/firtool-1.159.0/lib/extra.dylib'
        extra.write_text('New search-path dependency')
        with self.assertRaisesRegex(RuntimeError, 'inventory changed'):
            self.closure.closeout()
        extra.unlink()
        (self.root / 'build/tools/oss-cad-suite/libexec/ivl').unlink()
        with self.assertRaisesRegex(RuntimeError, 'Missing bundled tool'):
            ProtocolToolClosure(self.root, *self.tools, environment={})

    def test_compiled_vpi_references_must_be_exactly_indexed(self):
        executable = self.root / 'host.vvp'
        executable.write_text(fixture_vvp(self.root))
        self.closure.check_executable(executable)
        self.assertEqual(len(self.closure.identity()['vpi_modules']), 6)
        for data in (fixture_vvp(self.root).replace('system.vpi', 'external.vpi'),
                     fixture_vvp(self.root) + ':vpi_module "/outside/system.vpi";\n',
                     'Generated executable without plugin references'):
            executable.write_text(data)
            with self.subTest(data=data), self.assertRaisesRegex(RuntimeError, 'frozen bundled VPI'):
                self.closure.check_executable(executable)

    def test_dependency_symlink_escape_and_loader_overrides_refuse(self):
        external = self.root / 'external.dylib'
        external.write_text('Not bundled')
        link = self.root / 'build/tools/firtool-1.159.0/lib/external.dylib'
        link.symlink_to(external)
        with self.assertRaisesRegex(RuntimeError, 'escapes its package'):
            ProtocolToolClosure(self.root, *self.tools, environment={})
        link.unlink()
        with self.assertRaisesRegex(RuntimeError, 'loader environment overrides'):
            ProtocolToolClosure(self.root, *self.tools, environment={'DYLD_LIBRARY_PATH': '/unbound'})
        for name in ('IVERILOG_ICONFIG', 'IVERILOG_VPI_MODULE_PATH'):
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'compiler overrides'):
                ProtocolToolClosure(self.root, *self.tools, environment={name: '/unbound'})
        self.closure.environment['DYLD_INSERT_LIBRARIES'] = '/unbound'
        with self.assertRaisesRegex(RuntimeError, 'loader environment overrides'):
            self.closure.closeout()


class ResultLifecycleChecks(unittest.TestCase):
    def run_case(self, fault=None):
        events = []
        simulation = SimpleNamespace(device=None, pins=SimpleNamespace(enabled=int(fault == 'outputs')))
        class Host:
            def __init__(self, *args, **kwargs):
                self.edges = self.frames = self.reads = 0
            def reset(self):
                events.append('reset')
            def upload(self, source):
                events.append('upload')
            def start(self):
                events.append('start')
                exercise_write(simulation.device)
            def read_result(self, **kwargs):
                self.reads += 1
                events.append('read')
                result = Result(4, 5, False, False)
                if fault == 'capture' or fault == 'retention' and self.reads == 2:
                    result = replace(result, samples=1)
                if fault == 'status':
                    result = replace(result, outcome=6)
                if fault in ('overrun', 'rejected'):
                    result = replace(result, **{fault: True})
                return result
            def consume(self):
                events.append('consume')
            def result_status(self):
                events.append('status')
                return int(fault == 'consume')
        class Peer(I2CWritePeer):
            def check(self, **kwargs):
                events.append('wire')
                return super().check(**kwargs)
        peer = Peer(0x53, [0xa6, 0x53], [0, 0, 1])
        with tempfile.TemporaryDirectory() as directory, patch.object(gate, 'Host', Host), \
                patch.object(gate, 'peer_for', return_value=peer):
            result = gate.run_cases(simulation, 'write', {'write': Program((4,), 0)},
                [write_metadata(acks=[0, 0, 1])], Path(directory), lambda *args: events.append('certify'))
        return result, events

    def test_results_are_independently_decoded_retained_consumed_and_wire_checked(self):
        result, events = self.run_case()
        self.assertEqual(events, ['reset', 'certify', 'upload', 'start', 'read', 'read', 'consume', 'status', 'wire'])
        self.assertEqual(result['cases'][0]['decoded_ack_bits'], [0, 0, 1])
        self.assertEqual(result['cases'][0]['protocol_result'], 'data2-nack')

    def test_semantic_negatives_include_clean_wire_and_consumption(self):
        for fault in ('capture', 'status', 'overrun', 'rejected'):
            with self.subTest(fault=fault), self.assertRaises(gate.I2CCheckError) as error:
                self.run_case(fault)
            case = error.exception.case
            self.assertTrue(case['wire']['stopped'])
            self.assertEqual(case['wire']['clock_count'], 27)
            self.assertTrue(case['retained_twice'] and case['consumed'] and case['outputs_released'])

    def test_retention_consume_and_release_faults_fail_closed(self):
        for fault, diagnostic in (('retention', 'retained result'), ('consume', 'consumption'), ('outputs', 'not released')):
            with self.subTest(fault=fault), self.assertRaisesRegex(RuntimeError, diagnostic):
                self.run_case(fault)

    def test_recovery_to_write_reuses_same_host_without_intervening_reset(self):
        calls = []
        simulation = SimpleNamespace(device=None)
        host = SimpleNamespace(reset=lambda: calls.append('reset'))
        def run(sim, kind, images, entries, out, certify, **kwargs):
            self.assertIs(kwargs['host'], host)
            self.assertFalse(kwargs['reset'])
            calls.extend([kind, 'consume'])
            return dict(cases=[dict(protocol_result='recovered' if kind == 'clear' else 'success')])
        with patch.object(gate, 'Host', return_value=host), patch.object(gate, 'run_cases', side_effect=run):
            result = gate.recovery_then_write(simulation, {'clear': Program((4,), 0)}, [clear_metadata()],
                {'write': Program((4,), 0)}, [write_metadata()], Path('.'), lambda *args: None)
        self.assertEqual(calls, ['reset', 'clear', 'consume', 'write', 'consume'])
        self.assertEqual(result['intervening_chip_resets'], 0)


class CapabilityCLIReceiptChecks(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        files = ['Pinwheel.lean', 'Pinwheel/Fixture.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
            *['test/' + n for n in ('I2CWriteTransactions.lean', 'I2CRecovery.lean', 'PairedValidationEmit.lean', 'paired_chip.sv', 'host_bridge.sv')],
            *['scripts/' + n for n in ('check-i2c-capabilities.py', 'capability_receipt.py', 'i2c_peers.py',
                'pad_io.py', 'pad_peers.py', 'pinwheel_host.py', 'pinwheel_sim.py', 'host_demo.py',
                'paired_execution.py', 'paired_image_certificate.py', 'execution-vectors.py', 'validation_run.py',
                'process_group.py', 'protocol_tool_closure.py')]]
        for name in files:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Fixture ' + name)
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        fixture_tools(self.root)
        hashes = {}
        for name in ('RM_IHPSG13_1P_512x64_c2_bm_bist.v', 'RM_IHPSG13_1P_core_behavioral_bm_bist.v'):
            path = self.root / 'build/storage/macros' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Fixture ' + name)
            hashes['verilog/' + name] = hashlib.sha256(path.read_bytes()).hexdigest()
        lock = self.root / 'tools/storage-macros.json'
        lock.parent.mkdir(exist_ok=True)
        lock.write_text(json.dumps(dict(files_sha256=hashes)))
        self.writes = [write_metadata('w' + str(count) + '-' + str(nack), count,
                        [int(k == nack) for k in range(count + 1)])
                       for count in (1, 2) for nack in (None, *range(count + 1))]
        self.writes.extend([write_metadata('ws', stretch_cycles=3),
            write_metadata('wt', scl_stuck=True, expected_outcome=6, expected_clock_count=0, expected_samples=0)])
        self.clears = [clear_metadata('c' + str(release), release) for release in (*range(1, 10), None)]
        self.clears.extend([clear_metadata('cs', 5, stretch_cycles=3),
            clear_metadata('ct', None, scl_stuck=True, expected_outcome=6, expected_pulses=0, expected_sda_sample=False)])
        self.sequence, self.on_event = 0, lambda label: None

    def run_cli(self):
        self.sequence += 1
        self.out = self.root / 'build/host' / ('fixture-' + str(self.sequence))
        test = self
        class Commands:
            def __init__(self, *args, **kwargs):
                self.records = []
            def __call__(self, command, label):
                self.records.append(dict(label=label, stubbed=True))
                if label in ('compile-write', 'compile-clear'):
                    kind = label.removeprefix('compile-')
                    entries = test.writes if kind == 'write' else test.clears
                    destination = Path(command[-1])
                    destination.mkdir()
                    (destination / 'images.txt').write_text(''.join(x['name'] + ' 0 0 0 4\n' for x in entries))
                    (destination / 'metadata.json').write_text(json.dumps(entries))
                if label == 'emit':
                    (test.out / 'chip.mlir').write_text('Generated MLIR')
                if label == 'compile-simulation':
                    test.assertEqual(command[1:3], ['-B', test.root / 'build/tools/oss-cad-suite/lib/ivl'])
                    (test.out / 'host.vvp').write_text(fixture_vvp(test.root))
                test.on_event(label)
                if label.startswith('lean-version'):
                    return test.lean_version(label)
                return 'Generated RTL' if label == 'export' else 'Paired image certificate: kernel checked; standard axioms only.'
        class Simulation:
            def __init__(self, *args):
                pass
            def __enter__(self):
                return self
            def __exit__(self, *args):
                test.on_event('closed')
        def cases(sim, kind, images, entries, out, certify):
            for item in entries:
                certify(item['name'], replace(images[item['name']], image_format=PAIRED_FORMAT))
            categories = {'i2c-wrong-ack-slot': 'capture', 'i2c-wrong-terminal-status': 'status', 'i2c-swapped-address-data': 'wire-order'}
            name = entries[0]['name']
            if name in categories:
                raise gate.I2CCheckError(categories[name], 'Expected semantic refusal', dict(name=name))
            if name == 'i2c-push-pull-sda':
                raise RuntimeError('I2C board links require open-drain low/release drivers')
            return dict(cases=[dict(name=x['name']) for x in entries])
        with patch.object(gate, 'ROOT', self.root), patch.object(gate, 'Commands', Commands), \
                patch.object(gate, 'Simulation', Simulation), patch.object(gate, 'run_cases', side_effect=cases), \
                patch.object(gate, 'reset_control', return_value={}), patch.object(gate, 'recovery_then_write', return_value={}), \
                patch.object(gate, 'wrong_ack_slot', side_effect=lambda x: x), patch.object(gate, 'wrong_status', side_effect=lambda x: x), \
                patch.object(gate, 'push_pull_sda', side_effect=lambda x: x), patch.object(gate, 'swap_address_data', side_effect=lambda x: x), \
                patch.object(sys, 'argv', ['check-i2c-capabilities.py', '--tag', 'fixture-' + str(self.sequence)]), \
                contextlib.redirect_stdout(io.StringIO()):
            gate.main()
        return json.loads((self.out / 'report.json').read_text())

    def test_receipt_binds_before_use_digests_and_refused_controls(self):
        report = self.run_cli()
        self.assertEqual(report['rtl_sha256'], hashlib.sha256(b'Generated RTL').hexdigest())
        self.assertEqual(report['mlir_sha256'], hashlib.sha256(b'Generated MLIR').hexdigest())
        self.assertEqual(report['executable_sha256'], hashlib.sha256(fixture_vvp(self.root).encode()).hexdigest())
        self.assertEqual(len(report['negatives']), 4)
        self.assertTrue(report['lean_version_unchanged'])
        self.assertEqual(len(report['bundled_tool_closure']['vpi_modules']), 6)
        self.assertIn('tools/hardware-toolchain.json', report['source_sha256'])
        self.assertIn('build/tools/oss-cad-suite/libexec/vvp', report['tools_sha256'])

    def test_consumed_artifact_and_metadata_changes_prevent_success_receipt(self):
        for name in ('chip.mlir', 'design.sv', 'host.vvp', 'write-images.txt', 'write-metadata.json', 'clear-images.txt', 'clear-metadata.json'):
            def mutate(label, name=name):
                if label == 'closed':
                    (self.out / name).write_text('Different consumed bytes')
            self.on_event = mutate
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'changed after consumption'):
                self.run_cli()
            self.assertFalse((self.out / 'report.json').exists())

    def test_source_and_certificate_changes_prevent_success_receipt(self):
        for name, expected in (('Pinwheel.lean', 'Source changed'), ('w1-None-certificate.lean', 'Generated artifact changed')):
            path = self.root / name
            original = path.read_bytes() if path.exists() else None
            def mutate(label, name=name):
                if label == 'closed':
                    destination = self.root / name if name == 'Pinwheel.lean' else self.out / name
                    destination.write_text('Different bound bytes')
            self.on_event = mutate
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, expected):
                self.run_cli()
            self.assertFalse((self.out / 'report.json').exists())
            if original is not None:
                path.write_bytes(original)

    def test_actual_runtime_plugin_config_and_inventory_mutations_prevent_receipt(self):
        for name in ('build/tools/oss-cad-suite/libexec/vvp',
                     'build/tools/oss-cad-suite/lib/ivl/system.vpi',
                     'tools/hardware-toolchain.json',
                     'build/tools/firtool-1.159.0/lib/new.dylib'):
            path = self.root / name
            original = path.read_bytes() if path.exists() else None
            def mutate(label, path=path):
                if label == 'closed':
                    path.write_text('Changed consumed runtime/config/dependency')
            self.on_event = mutate
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'changed during capability run'):
                self.run_cli()
            self.assertFalse((self.out / 'report.json').exists())
            if original is None:
                path.unlink()
            else:
                path.write_bytes(original)

    def lean_version(self, label):
        return 'Lean (version 4.33.1, fixture, Release)'

    def test_wrong_or_changed_lean_version_prevents_success(self):
        self.lean_version = lambda label: 'Lean (version 4.33.2, fixture, Release)'
        with self.assertRaisesRegex(RuntimeError, 'does not match lean-toolchain'):
            self.run_cli()
        self.assertFalse((self.out / 'report.json').exists())
        self.lean_version = lambda label: ('Lean (version 4.33.1, fixture, Release)' if label == 'lean-version'
                                         else 'Lean (version 4.33.1, changed, Release)')
        with self.assertRaisesRegex(RuntimeError, 'version changed'):
            self.run_cli()
        self.assertFalse((self.out / 'report.json').exists())


if __name__ == '__main__':
    unittest.main()
