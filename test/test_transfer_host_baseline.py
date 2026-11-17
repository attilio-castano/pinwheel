import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import transfer_host_baseline as baseline

SPEC = importlib.util.spec_from_file_location("baseline_checks", ROOT / "scripts/check-memory-transfer-host-baseline.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)


class BaselineTests(unittest.TestCase):
    def test_invalid_configuration_and_module_rejected(self):
        for args in ((0, 1, 1, "top"), (1, 0, 1, "top"), (1, 1, 0, "top"),
                     (True, 1, 1, "top"), (1, 1, 1, "top; endmodule")):
            with self.subTest(arguments=args), self.assertRaises(ValueError):
                baseline.generate(*args)

    def test_register_map_complete_unique(self):
        for a in (1, 2, 3):
            refs = baseline.register_references(a)
            self.assertEqual(len(refs), 7+2*((1 << a)+2))
            self.assertEqual(len(set(refs)), len(refs))
            self.assertEqual(refs[7], "source_words[0]")
            self.assertEqual(refs[-1], "destination_pending")

    def test_mutations_are_distinct_and_fail_closed(self):
        text = baseline.generate(2, 8, 8, "baseline")
        mutants = list(baseline.mutations(text, 8, 8))
        self.assertEqual(len(mutants), 3)
        self.assertEqual(len({value for _, value in mutants}), 3)
        self.assertTrue(all(value != text for _, value in mutants))
        with self.assertRaises(ValueError):
            list(baseline.mutations("module unrelated; endmodule", 8, 8))

    def test_receipt_path_escape_rejected(self):
        with self.assertRaises(ValueError):
            checks.contained(ROOT / "build", "../outside")


if __name__ == "__main__":
    unittest.main()
