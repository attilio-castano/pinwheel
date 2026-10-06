"""Provider-free custody and admission checks for the shared package runner."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import transaction_package as package
from capability_receipt import CapabilityEvidence
from pinwheel_host import PAIRED_FORMAT, Program
from pinwheel_transactions import Transaction, compile_transaction, i2c_register_read, uart_tx
from validation_run import sha


class PackageAdmissionTests(unittest.TestCase):
    def test_input_capability_errors_precede_package_creation(self):
        resident = compile_transaction(uart_tx())
        fixed = Transaction(i2c_register_read(45, 113, byte_count=2),
                            Program((4,), 0, image_format=PAIRED_FORMAT))
        with patch.object(package, 'paired_package') as create:
            for transaction, kwargs in [(resident, dict(payload=256)), (fixed, dict(payload=1)),
                                        (resident, dict(incoming=4)), (resident, dict(timeout_cycles=-1))]:
                with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                    package.run_transaction('unused', transaction, **kwargs)
            create.assert_not_called()

    def test_failed_setup_preserves_attempt_without_an_accepted_report(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(package, 'ROOT', Path(directory)), \
             patch.object(package, 'ProtocolToolClosure', side_effect=RuntimeError('refuse tool override')):
            with self.assertRaisesRegex(RuntimeError, 'refuse tool override'):
                with package.paired_package('failed-01'):
                    self.fail('Failed setup yielded a package')
            out = Path(directory) / 'build/host/failed-01'
            attempt = json.loads((out / 'failed-attempt.json').read_bytes())
            self.assertEqual((attempt['status'], attempt['accepted']), ('failed', False))
            self.assertEqual(json.loads((out / 'commands.json').read_bytes()), [])
            self.assertFalse((out / 'report.json').exists())
            original = (out / 'failed-attempt.json').read_bytes()
            with self.assertRaises(FileExistsError):
                with package.paired_package('failed-01'):
                    self.fail('Reused a failed attempt directory')
            self.assertEqual((out / 'failed-attempt.json').read_bytes(), original)

    def test_constant_i2c_inputs_are_low_or_release_on_declared_links(self):
        for incoming in range(4):
            fixture = package.ConstantInputFixture(incoming, True)
            drive = fixture.drive(0, None, 0)
            self.assertEqual(drive.levels & drive.enabled, 0)
            self.assertEqual((drive.enabled, drive.links), (3 - incoming, 3))
            ordinary = package.ConstantInputFixture(incoming).drive(0, None, 0)
            self.assertEqual((ordinary.levels, ordinary.enabled, ordinary.links), (incoming, 3, 0))
        for incoming in (-1, 4, True):
            with self.assertRaises(ValueError):
                package.ConstantInputFixture(incoming)


class CompilationCustodyTests(unittest.TestCase):
    def runtime(self, root, run):
        out = root / 'output'
        out.mkdir()
        source = root / 'source.py'
        source.write_text('frozen source')
        evidence = CapabilityEvidence(root, out, [source], [], [])
        evidence.certify = Mock()
        return package.PackageRuntime(Mock(), Mock(), evidence, run, out)

    def test_resident_compile_captures_identity_and_certifies_exact_program(self):
        with tempfile.TemporaryDirectory() as directory:
            run = Mock(side_effect=AssertionError('Resident compilation must not call fixed frontend'))
            runtime = self.runtime(Path(directory), run)
            transaction = runtime.compile(uart_tx(bit_cycles=7), 'uart')
            self.assertEqual(json.loads((runtime.out / 'uart-request.json').read_bytes()), transaction.spec.request)
            self.assertEqual(json.loads((runtime.out / 'uart-transaction.json').read_bytes()), transaction.artifact())
            entry = runtime.compiled[0]
            self.assertEqual(entry['request_sha256'], sha(runtime.out / entry['request']))
            self.assertEqual(entry['artifact_sha256'], sha(runtime.out / entry['artifact']))
            runtime.evidence.certify.assert_called_once_with('uart', transaction.program, run)
            runtime.evidence.closeout()
            with self.assertRaises(FileExistsError):
                runtime.compile(uart_tx(), 'uart')
            runtime._active = False
            with self.assertRaisesRegex(RuntimeError, 'already closed'):
                runtime.compile(uart_tx(), 'other')

    def test_fixed_compile_records_static_frontend_and_checks_echoed_request(self):
        spec = i2c_register_read(45, 113, byte_count=2, phase_cycles=7, wait_cycles=19)
        def frontend(command, label):
            self.assertEqual(command[:2], [sys.executable, package.ROOT / 'scripts/export-program.py'])
            self.assertEqual(label, 'read-frontend')
            request = json.loads(Path(command[2]).read_bytes())
            self.assertEqual(request, spec.request)
            return json.dumps(dict(schema='pinwheel-compiled-program-v1', request=request,
                program=dict(format=PAIRED_FORMAT, words=[4], last=0, idle_levels=0, idle_enabled=0)))
        with tempfile.TemporaryDirectory() as directory:
            run = Mock(side_effect=frontend)
            runtime = self.runtime(Path(directory), run)
            transaction = runtime.compile(spec, 'read')
            self.assertEqual(transaction.spec, spec)
            run.assert_called_once()
            self.assertIn('read-frontend.json', runtime.evidence.generated_sha256)
            runtime.evidence.certify.assert_called_once_with('read', transaction.program, run)
            response = json.loads((runtime.out / 'read-frontend.json').read_bytes())
            response['request']['register'] = 114
            run.side_effect = lambda command, label: json.dumps(response)
            with self.assertRaisesRegex(ValueError, 'differs from the requested transaction'):
                runtime.compile(spec, 'wrong')
            self.assertFalse((runtime.out / 'wrong-transaction.json').exists())


if __name__ == '__main__':
    unittest.main()
