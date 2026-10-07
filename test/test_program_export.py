"""Real static Lean-export entrypoint and host-format integration checks."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from pinwheel_host import PAIRED_FORMAT, Program


class ExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if shutil.which('lake') is None or shutil.which('lean') is None:
            raise unittest.SkipTest('Production Lean export integration requires local lake and lean')
        if not (ROOT / '.lake/build/lib/lean/Pinwheel/Program/Requests.olean').is_file():
            raise unittest.SkipTest('Build Pinwheel.Program.Requests before running Lean export integration')

    def export(self, request, *, path=None, cwd=ROOT):
        command = [sys.executable, str(ROOT / 'scripts/export-program.py')]
        if path is not None:
            command.append(str(path))
        return subprocess.run(command, input=json.dumps(request, indent=2).encode(),
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              cwd=cwd, timeout=30)

    def response(self, process, request):
        self.assertEqual(process.returncode, 0, process.stderr.decode())
        self.assertEqual(process.stderr, b'')
        result = json.loads(process.stdout)
        self.assertEqual(set(result), {'schema', 'request', 'program'})
        self.assertEqual(result['schema'], 'pinwheel-compiled-program-v1')
        self.assertEqual(result['request'], request)
        program = Program.from_bytes(json.dumps(result['program']).encode())
        self.assertEqual(program.image_format, PAIRED_FORMAT)
        self.assertEqual(len(program.words), 256)
        self.assertEqual(len(program.upload_words()), 290)
        return program

    def test_nonfixture_read_is_a_host_program(self):
        request = dict(schema='pinwheel-protocol-request-v1', protocol='i2c-register-read',
                       address=45, register=113, byte_count=2, phase_cycles=7, wait_cycles=19)
        program = self.response(self.export(request), request)
        self.assertEqual((program.last, program.idle_levels, program.idle_enabled), (195, 0, 0))

    def test_spi_payload_is_in_wire_order(self):
        for mode in range(4):
            with self.subTest(mode=mode):
                request = dict(schema='pinwheel-protocol-request-v1', protocol='spi-transaction',
                               mode=mode, payload=[0x3b, 0xc9], half_cycles=5)
                program = self.response(self.export(request), request)
                phases = [2 * bit + (mode & 1) for bit in range(16)]
                bits = [(program.words[phase] >> 3) & 1 for phase in phases]
                self.assertEqual(bits, [(0x3bc9 >> bit) & 1 for bit in range(15, -1, -1)])
                self.assertEqual(program.last, 33)

    def test_rejected_request_has_no_response_or_modulo_program(self):
        request = dict(schema='pinwheel-protocol-request-v1', protocol='i2c-register-read',
                       address=128, register=113, byte_count=2, phase_cycles=7, wait_cycles=19)
        process = self.export(request)
        self.assertEqual(process.returncode, 1)
        self.assertEqual(process.stdout, b'')
        self.assertIn(b'address must be in 0..127', process.stderr)

    def test_file_request_works_outside_repository(self):
        request = dict(schema='pinwheel-protocol-request-v1', protocol='spi-transaction',
                       mode=0, payload=[255], half_cycles=256)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'request.json'
            path.write_text(json.dumps(request))
            program = self.response(self.export(request, path=path, cwd=directory), request)
        self.assertEqual(program.last, 17)


if __name__ == '__main__':
    unittest.main()
