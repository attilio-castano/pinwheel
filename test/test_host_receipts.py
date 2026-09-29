"""Exercise real CLI receipts with stubbed CAD commands and chip observations."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import host_demo
from pinwheel_host import Program, Result
from test_host_demo import ScriptedHost


class HostReceiptTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        spec = importlib.util.spec_from_file_location('host_cli', ROOT / 'scripts/pinwheel-host.py')
        self.cli = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.cli)
        self.cli.ROOT = self.root
        sources = ['Pinwheel/Fixture.lean', 'lakefile.toml', 'lean-toolchain',
                   'test/Loader.lean', 'test/ChipEmit.lean', 'test/SramChipEmit.lean',
                   'test/sram_chip.sv', 'test/host_bridge.sv',
                   'test/PairedChipEmit.lean', 'test/paired_chip.sv',
                   *['scripts/' + name for name in ('pinwheel-host.py', 'pinwheel_host.py',
                     'pinwheel_sim.py', 'host_demo.py', 'validation_run.py', 'process_group.py',
                     'paired_execution.py', 'paired_image_certificate.py', 'execution-vectors.py')],
                   'build/tools/firtool-1.159.0/bin/circt-opt',
                   'build/tools/oss-cad-suite/bin/iverilog', 'build/tools/oss-cad-suite/bin/vvp']
        for name in sources:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Fixture for ' + name)
        self.program_path = self.root / 'input.json'
        # Preserve deliberately noncanonical whitespace and field order.
        self.program_bytes = (b'{ "last":0, "words":[4], "idle_enabled":0, '
                              b'"format":"pinwheel-e64-v1", "idle_levels":0 }\n\n')
        self.program_path.write_bytes(self.program_bytes)
        self.images_path = self.root / 'build/loader/images.txt'
        self.images_bytes = b'\n'.join(name + b' 0 0 0 4' for name in
                                      (b'uart', b'spi', b'i2c-read', b'uart-rx')) + b'\n'
        self.events = []
        self.programs = []
        self.sequence = 0
        self.demo_fault = None
        self.on_event = lambda event: None

    def event(self, name):
        self.events.append(name)
        self.on_event(name)

    def run_cli(self, action='run'):
        test = self
        self.sequence += 1
        tag = 'case-' + str(self.sequence)
        self.out = self.root / 'build/host' / tag

        class Commands:
            def __init__(self, *args, **kwargs):
                self.records = []

            def __call__(self, command, label):
                self.records.append(dict(label=label, stubbed=True))
                if label == 'compile-programs':
                    test.images_path.parent.mkdir(parents=True, exist_ok=True)
                    test.images_path.write_bytes(test.images_bytes)
                if label == 'emit':
                    (test.out / 'chip-twoport-result.mlir').write_text('Fixture MLIR')
                test.event(label)
                return 'Fixture RTL' if label == 'export' else ''

        class Simulation:
            def __init__(self, *args):
                self.device = None

            def __enter__(self):
                test.event('simulation')
                return self

            def __exit__(self, *args):
                test.event('closed')

        class Host:
            def __init__(self, simulation, *, image_format):
                self.edges = self.frames = 0

            def reset(self):
                pass

            def upload(self, program):
                program.upload_words()
                test.programs.append(program)

            def start(self):
                test.event('start')

            def read_result(self, **kwargs):
                test.event('read-result')
                return Result(0, 5, False, False)

        class DemoHost(ScriptedHost):
            def __init__(self, simulation, *, image_format):
                super().__init__(simulation, test.demo_fault)

            def upload(self, program):
                test.programs.append(program)
                super().upload(program)

        argv = ['pinwheel-host.py', action, '--tag', tag, '--backend', 'reference']
        if action == 'run':
            argv += ['--program', str(self.program_path)]
        with patch.object(self.cli, 'Commands', Commands), patch.object(self.cli, 'Simulation', Simulation), \
                patch.object(self.cli, 'Host', Host), patch.object(host_demo, 'Host', DemoHost), \
                patch.object(sys, 'argv', argv), contextlib.redirect_stdout(io.StringIO()):
            self.cli.main()
        return json.loads((self.out / 'report.json').read_text())

    def check_custom_input(self, report):
        self.assertEqual(self.programs[-1], Program((4,), 0))
        self.assertEqual(report['program_sha256'], hashlib.sha256(self.program_bytes).hexdigest())
        self.assertEqual((self.out / report['program_snapshot']).read_bytes(), self.program_bytes)

    def test_program_is_captured_before_building(self):
        def mutate(event):
            if event == 'build':
                Program((0, 4), 1).write(self.program_path)
        self.on_event = mutate
        self.check_custom_input(self.run_cli())
        self.assertEqual(Program.read(self.program_path).words, (0, 4))

    def test_atomic_replacement_during_execution_cannot_rebind_receipt(self):
        def mutate(event):
            if event == 'read-result':
                replacement = self.root / 'replacement.json'
                Program((0, 4), 1).write(replacement)
                replacement.replace(self.program_path)
        self.on_event = mutate
        self.check_custom_input(self.run_cli())

    def test_original_file_can_disappear_after_capture(self):
        self.on_event = lambda event: self.program_path.unlink() if event == 'start' else None
        self.check_custom_input(self.run_cli())
        self.assertFalse(self.program_path.exists())

    def test_input_validation_precedes_cad_and_transport(self):
        self.program_path.write_text('{"format":"unsupported"}')
        with self.assertRaisesRegex(ValueError, 'schema'):
            self.run_cli()
        self.assertEqual(self.events, [])
        self.assertFalse((self.out / 'report.json').exists())

    def test_compiler_images_use_captured_bytes_and_digest(self):
        def mutate(event):
            if event == 'simulation':
                self.images_path.write_bytes(self.images_bytes.replace(b' 0 0 0 4', b' 1 0 0 0 4'))
        self.on_event = mutate
        report = self.run_cli('demo')
        self.assertEqual(len(report['cases']), 9)
        self.assertEqual(self.programs[0], Program((4,), 0))
        self.assertEqual(report['compiled_images_sha256'], hashlib.sha256(self.images_bytes).hexdigest())
        self.assertEqual((self.out / report['compiled_images_snapshot']).read_bytes(), self.images_bytes)
        self.assertNotEqual(self.images_path.read_bytes(), self.images_bytes)

    def test_failed_demo_checks_never_publish_success_receipt(self):
        for fault, message in [('samples', 'expected samples'), ('retention', 'retained result changed'),
                               ('consumption', 'consumption did not release'),
                               ('wrong-rejection', 'Unexpected malformed-upload failure')]:
            self.demo_fault = fault
            with self.subTest(fault=fault), self.assertRaisesRegex(RuntimeError, message):
                self.run_cli('demo')
            self.assertEqual(self.events[-1], 'closed')
            self.assertFalse((self.out / 'report.json').exists())


class ReceiptOptimizationModes(unittest.TestCase):
    def test_receipt_boundaries_under_optimization(self):
        for flag in ('-O', '-OO'):
            env = dict(os.environ)
            env.pop('PYTHONOPTIMIZE', None)
            with self.subTest(flag=flag):
                result = subprocess.run([sys.executable, '-B', flag, str(Path(__file__).resolve()),
                                         'HostReceiptTests'], env=env,
                                        capture_output=True, text=True, timeout=15)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
