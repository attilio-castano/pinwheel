"""Pinned functional-model replay and meaningful two-copy negative controls."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
CAD = ROOT / 'build/tools/oss-cad-suite/bin'
VIEWS = ROOT / 'build/storage/macros'
MACRO = 'RM_IHPSG13_1P_64x64_c2_bm_bist'
CORE = 'RM_IHPSG13_1P_core_behavioral_bm_bist.v'


class BufferedSramMemoryChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        required = [CAD / 'iverilog', CAD / 'vvp', VIEWS / (MACRO + '.v'), VIEWS / CORE]
        if not all(path.is_file() for path in required):
            raise unittest.SkipTest('Pinned Icarus and SRAM functional models are required')
        lock = json.loads((ROOT / 'tools/storage-macros.json').read_text())
        for path in required[2:]:
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual != lock['files_sha256']['verilog/' + path.name]:
                raise AssertionError('Mismatched pinned SRAM model: ' + path.name)

    def replay(self, memory):
        with tempfile.TemporaryDirectory(prefix='pinwheel-buffered-sram-') as folder:
            out = Path(folder)
            source = out / 'memory.sv'
            source.write_text(memory)
            executable = out / 'memory.vvp'
            compile_result = subprocess.run([str(CAD / 'iverilog'), '-g2012', '-DFUNCTIONAL',
                '-s', 'buffered_sram_memory_tb', '-o', str(executable), str(source),
                str(ROOT / 'test/buffered_sram_memory_tb.sv'),
                str(VIEWS / (MACRO + '.v')), str(VIEWS / CORE)],
                capture_output=True, text=True, timeout=20)
            self.assertEqual(compile_result.returncode, 0, compile_result.stdout + compile_result.stderr)
            return subprocess.run([str(CAD / 'vvp'), str(executable)],
                capture_output=True, text=True, timeout=20)

    def memory(self):
        return (ROOT / 'physical/buffered_sram_memory.sv').read_text()

    def second_copy(self, old, new):
        memory = self.memory()
        marker = MACRO + ' storage1 ('
        first, second = memory.split(marker)
        self.assertEqual(second.count(old), 1)
        return first + marker + second.replace(old, new, 1)

    def rejected(self, memory):
        result = self.replay(memory)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Buffered SRAM', result.stdout)
        self.assertIn('mismatch', result.stdout)

    def test_pinned_memory_preserves_latency_broadcast_and_response_holds(self):
        result = self.replay(self.memory())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Buffered SRAM memory passed: 197 edges, 128 independent read pairs', result.stdout)

    def test_missing_second_write_is_rejected(self):
        self.rejected(self.second_copy('.A_WEN(mem_write)', ".A_WEN(1'b0)"))

    def test_shared_read_address_is_rejected(self):
        self.rejected(self.second_copy('.A_ADDR(mem_addr1)', '.A_ADDR(mem_addr0)'))

    def test_write_through_response_is_rejected(self):
        self.rejected(self.second_copy('.A_REN(mem_read)', ".A_REN(1'b1)"))

    def test_partial_word_initialization_is_rejected(self):
        self.rejected(self.second_copy(".A_BM(64'hffffffffffffffff)",
            ".A_BM(64'h7fffffffffffffff)"))

    def test_swapped_responses_are_rejected(self):
        memory = self.memory().replace('.A_DOUT(mem_q0)', '.A_DOUT(swapped)').replace(
            '.A_DOUT(mem_q1)', '.A_DOUT(mem_q0)').replace('.A_DOUT(swapped)', '.A_DOUT(mem_q1)')
        self.rejected(memory)


if __name__ == '__main__':
    unittest.main()
