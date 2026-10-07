"""Provider-free transaction CLI admission, binding and dispatch checks."""
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import runpy
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
CLI = runpy.run_path(str(ROOT / 'scripts/pinwheel-transaction.py'))
from pinwheel_transactions import compile_transaction, uart_tx


class ParserTests(unittest.TestCase):
    def parse(self, *arguments):
        return CLI['build_parser']().parse_args(arguments)

    def test_compile_and_inspect_need_paths_without_a_tag(self):
        args = self.parse('compile', '--request', 'request.json', '--output', 'artifact.json')
        self.assertEqual((args.request, args.output), (Path('request.json'), Path('artifact.json')))
        self.assertEqual(self.parse('inspect', '--transaction', 'artifact.json').transaction, Path('artifact.json'))

    def test_run_defaults_and_hexadecimal_bounds(self):
        args = self.parse('run', '--transaction', 'a.json', '--tag', 'local_01')
        self.assertEqual((args.payload, args.incoming, args.timeout_cycles), (0, 3, 100_000))
        args = self.parse('run', '--transaction', 'a.json', '--tag', 'local-01',
                          '--payload', '0xff', '--incoming', '0x0', '--timeout-cycles', '0')
        self.assertEqual((args.payload, args.incoming, args.timeout_cycles), (255, 0, 0))

    def test_invalid_ranges_and_tags_reject_before_dispatch(self):
        base = ['run', '--transaction', 'a.json', '--tag', 'safe']
        for field, value in [('--payload', '-1'), ('--payload', '256'), ('--payload', '1.0'),
                             ('--incoming', '-1'), ('--incoming', '4'), ('--timeout-cycles', '-1'),
                             ('--tag', '../escape'), ('--tag', '')]:
            with self.subTest(field=field, value=value), redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as error:
                    self.parse(*base, field, value)
                self.assertEqual(error.exception.code, 2)

    def test_required_action_arguments(self):
        for args in [(), ('compile',), ('inspect',), ('run', '--transaction', 'a.json'), ('demo',)]:
            with self.subTest(args=args), redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    self.parse(*args)


class CommandTests(unittest.TestCase):
    def invoke(self, *arguments):
        output, errors = io.StringIO(), io.StringIO()
        with redirect_stdout(output), redirect_stderr(errors):
            code = CLI['main'](list(arguments))
        return code, output.getvalue(), errors.getvalue()

    def test_real_resident_compile_inspect_and_rebinding_rejection(self):
        with tempfile.TemporaryDirectory() as folder:
            request, artifact = Path(folder) / 'request.json', Path(folder) / 'artifact.json'
            request.write_text(json.dumps(uart_tx(bit_cycles=7).request))
            code, output, errors = self.invoke('compile', '--request', str(request), '--output', str(artifact))
            self.assertEqual((code, errors), (0, ''))
            self.assertEqual(json.loads(output)['payload_bits'], 8)
            code, output, errors = self.invoke('inspect', '--transaction', str(artifact))
            self.assertEqual((code, errors), (0, ''))
            self.assertEqual(json.loads(output)['request'], uart_tx(bit_cycles=7).request)
            saved = json.loads(artifact.read_bytes())
            saved['request']['bit_cycles'] = 8
            artifact.write_text(json.dumps(saved))
            code, output, errors = self.invoke('inspect', '--transaction', str(artifact))
            self.assertEqual((code, output), (1, ''))
            self.assertIn('differs from its compiled request', errors)

    def test_duplicate_request_keys_do_not_compile_or_write(self):
        with tempfile.TemporaryDirectory() as folder:
            request, artifact = Path(folder) / 'request.json', Path(folder) / 'artifact.json'
            request.write_text('{"schema":"pinwheel-protocol-request-v1","protocol":"uart-tx","bit_cycles":4,"bit_cycles":8}')
            compiler = Mock(side_effect=AssertionError('Must reject before compiling'))
            with patch.dict(CLI['main'].__globals__, compile_transaction=compiler):
                code, output, errors = self.invoke('compile', '--request', str(request), '--output', str(artifact))
            self.assertEqual((code, output), (1, ''))
            self.assertIn('Duplicate JSON field', errors)
            compiler.assert_not_called()
            self.assertFalse(artifact.exists())

    def test_fixed_payload_rejects_before_runtime_creation(self):
        transaction = SimpleNamespace(validate_payload=Mock(side_effect=ValueError('fixed payload must be zero')))
        runtime = Mock(side_effect=AssertionError('Must reject before package creation'))
        with tempfile.TemporaryDirectory() as folder:
            artifact = Path(folder) / 'artifact.json'
            artifact.write_bytes(b'captured artifact')
            with patch.object(CLI['Transaction'], 'from_bytes', return_value=transaction), \
                 patch.dict(sys.modules, transaction_package=SimpleNamespace(run_transaction=runtime)):
                code, output, errors = self.invoke('run', '--transaction', str(artifact), '--tag', 'test', '--payload', '1')
        self.assertEqual((code, output), (1, ''))
        self.assertIn('fixed payload must be zero', errors)
        transaction.validate_payload.assert_called_once_with(1)
        runtime.assert_not_called()

    def test_run_dispatches_the_validated_bound_transaction(self):
        transaction = compile_transaction(uart_tx())
        runtime = Mock()
        with tempfile.TemporaryDirectory() as folder:
            artifact = Path(folder) / 'artifact.json'
            transaction.write(artifact)
            with patch.dict(sys.modules, transaction_package=SimpleNamespace(run_transaction=runtime)):
                code, output, errors = self.invoke('run', '--transaction', str(artifact), '--tag', 'test',
                    '--payload', '0xa6', '--incoming', '1', '--timeout-cycles', '0')
        self.assertEqual((code, output, errors), (0, '', ''))
        runtime.assert_called_once()
        args, kwargs = runtime.call_args
        self.assertEqual(args, ('test', transaction))
        self.assertEqual(kwargs, dict(payload=166, incoming=1, timeout_cycles=0))

    def test_demo_dispatches_requested_tag(self):
        gate = Mock()
        with patch.object(CLI['runpy'], 'run_path', return_value={'run_gate': gate}):
            self.assertEqual(self.invoke('demo', '--tag', 'demo-01'), (0, '', ''))
        gate.assert_called_once_with('demo-01')


if __name__ == '__main__':
    unittest.main()
