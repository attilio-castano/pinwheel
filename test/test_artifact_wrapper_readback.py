"""Refusal and actual-source extraction controls for the wrapper decoder."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import artifact_wrapper_readback as aw


class ArtifactWrapperReadback(unittest.TestCase):
    def setUp(self):
        self.files = [ROOT / 'physical' / name for name in (
            'buffered_sram_serial_wrapper.sv', 'buffered_sram_memory.sv', 'tt_um_pinwheel_buffered.sv')]
        self.text = [path.read_text() for path in self.files]

    def decode(self, change=None):
        if change is None:
            return aw.read_wrappers(*self.files)
        index, old, new = change
        with tempfile.TemporaryDirectory() as directory:
            files = []
            for position, original in enumerate(self.text):
                path = Path(directory) / self.files[position].name
                if position == index:
                    self.assertIn(old, original)
                    original = original.replace(old, new, 1)
                path.write_text(original)
                files.append(path)
            return aw.read_wrappers(*files)

    def test_source_bytes_and_complete_extraction(self):
        bundle = self.decode()
        for name, path in zip(('package', 'memory', 'tiny'), self.files):
            self.assertEqual(bundle[name].sha256, hashlib.sha256(path.read_bytes()).hexdigest())
        self.assertEqual(len(bundle['frontend']), 31)
        self.assertEqual(len(bundle['controller']), 19)
        self.assertEqual(len(bundle['macros']), 2)
        self.assertEqual([len(macro['constants']) for macro in bundle['macros']], [11, 11])
        proof = aw.lean_source(bundle)
        for theorem in ('package_correct', 'memory_correct', 'tiny_correct'):
            self.assertIn('theorem '+theorem, proof)
        self.assertEqual(bundle['controller']['mem_q0'], ('memory', False))
        self.assertEqual(bundle['controller']['mem_q1'], ('memory', True))

    def test_noncanonical_connections_are_extracted_not_replaced(self):
        changed = self.decode((0, '.mem_q0(mem_q0), .mem_q1(mem_q1)',
            '.mem_q0(mem_q1), .mem_q1(mem_q0)'))
        self.assertEqual(changed['controller']['mem_q0'], ('memory', True))
        self.assertEqual(changed['controller']['mem_q1'], ('memory', False))
        changed = self.decode((0, '.mem_q0(mem_q0), .mem_q1(mem_q1)',
            '.mem_q0(mem_q0), .mem_q1(mem_q0)'))
        self.assertEqual(changed['controller']['mem_q1'], ('memory', False))
        changed = self.decode((1, '.A_ADDR(mem_addr0)', '.A_ADDR(mem_addr1)'))
        self.assertEqual(changed['macros'][0]['address'], '(Sram.Port.address true)')
        changed = self.decode((2, '.raw_inputs(ui_in[4:3])', '.raw_inputs(ui_in[5:4])'))
        proof = aw.lean_source(changed)
        self.assertIn('(.slice 4 2 (by decide +kernel)', proof)
        changed = self.decode((1, ".A_BM(64'hffffffffffffffff)", ".A_BM(64'hfffffffffffffffe)"))
        mask = next(v for n, _, v in changed['macros'][0]['constants'] if n == 'A_BM')
        self.assertEqual(mask, 2**64-2)

    def test_reject_state_extra_logic_duplicate_or_missing_drivers(self):
        cases = [
            (0, '  wire core_initialize;', '  reg core_initialize;'),
            (0, 'endmodule', 'always @(posedge clk) begin end\nendmodule'),
            (0, '  assign busy = status_busy;',
                '  assign busy = status_busy;\n  assign busy = status_busy;'),
            (0, '.mem_q0(mem_q0)', '.mem_q0(mem_q0), .mem_q0(mem_q0)'),
            (0, '.read_index(core_read_index)', '.read_index(missing_wire)'),
            (1, '.A_DOUT(mem_q1)', '.A_DOUT(mem_q0)'),
            (1, 'endmodule', 'module hidden(); endmodule\nendmodule'),
            (1, ".A_BIST_EN(1'b0)", '.A_BIST_EN(mem_write)'),
            (2, '  wire active = ena && rst_n;', '  wire active = ena || rst_n;'),
            (2, 'wire _unused =', 'wire _unused = undeclared &&'),
        ]
        for mutation in cases:
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.decode(mutation)

    def test_refuse_unknown_widths_and_source_forms(self):
        for text in (
            "module m(input [1:0] x, output y); assign y=x; endmodule",
            "module m(input x, output y); assign y=1'bx; endmodule",
            "module m(input x, output y); assign y=1; endmodule",
            "module m(input x, output y); assign y=x[2]; endmodule",
            "module m(input x, input x); endmodule",
            "`include \"other.sv\"\nmodule m(input x); endmodule",
        ):
            with self.subTest(text=text), self.assertRaises(ValueError):
                aw.Parser(text).module('fixture.sv', 'fixture')


if __name__ == '__main__':
    unittest.main()
