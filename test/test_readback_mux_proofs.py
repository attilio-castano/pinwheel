"""Proof-search rewriting must preserve all original statements and fail closed."""
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import readback_mux_proofs as m

class MuxProofTests(unittest.TestCase):
    def text(self):
        return 'import Design\nnamespace X\ntheorem local_0 (x0 : BitVec 1) :\n    x0 = x0 := by\n  all_goals first\n  | rfl\n\nend X\n'

    def test_same_header_and_all_goals_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'LocalProofs000.lean';p.write_text(self.text())
            before=[d[3] for d in m.declarations(p.read_text())]
            self.assertEqual(m.add_mux_algebra(Path(tmp),['LocalProofs000']),1)
            self.assertEqual([d[3] for d in m.declarations(p.read_text())],before)
            self.assertIn('     done)',p.read_text());self.assertEqual(p.read_text().count(m.IMPORT),1)
            with self.assertRaises(ValueError):m.add_mux_algebra(Path(tmp),['LocalProofs000'])

    def test_bad_headers_and_boundaries_rejected(self):
        variants=[self.text().replace(' :\n',' broken\n',1),self.text().replace('\nend X','\ndef surprising := 1\nend X'),
                  self.text().replace('\nend X\n',''),self.text().replace('  | rfl','  | rfl\n  all_goals first\n  | rfl'),
                  self.text().replace('\nend X','\n'+self.text().split('namespace X\n')[1])]
        for value in variants:
            with tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp)/'LocalProofs000.lean';p.write_text(value)
                with self.subTest(value=value),self.assertRaises(ValueError):m.add_mux_algebra(Path(tmp),['LocalProofs000'])
                self.assertEqual(p.read_text(),value)

    def test_empty_aggregator_untouched(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'LocalProofs.lean';p.write_text('import LocalProofs000\n')
            self.assertEqual(m.add_mux_algebra(Path(tmp),['LocalProofs']),0)
            self.assertEqual(p.read_text(),'import LocalProofs000\n')

    def test_no_rewriting_other_modules(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'Graphs.lean';p.write_text(self.text())
            self.assertEqual(m.add_mux_algebra(Path(tmp),['Graphs']),0);self.assertEqual(p.read_text(),self.text())

if __name__=='__main__':unittest.main()
