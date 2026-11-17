import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location("transfer_checks", ROOT / "scripts/check-memory-transfer.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)


class NegativeEvidenceTests(unittest.TestCase):
    expected = [("PRE", 0, 0, 1), ("POST", 0, 1, 0), ("REG", 0, 2)]
    semantic = "PRE,0,0,1\nPOST,0,1,1\nREG,0,2\nMEMORY_DONE\n"

    def test_aligned_value_change(self):
        checks.concrete_mismatch(self.semantic, self.expected)

    def test_no_value_change(self):
        with self.assertRaises(AssertionError):
            checks.concrete_mismatch(self.semantic.replace("POST,0,1,1", "POST,0,1,0"), self.expected)

    def test_incomplete_or_malformed_trace(self):
        corruptions = [
            self.semantic.replace("MEMORY_DONE\n", ""),
            self.semantic + "MEMORY_DONE\n",
            self.semantic + "unexpected diagnostic\n",
            self.semantic.replace("POST,0", "POST,1"),
            self.semantic.replace("POST,0", "PRE,0"),
            self.semantic.replace("POST,0,1,1", "POST,0,1"),
            self.semantic.replace("POST,0,1,1", "POST,0,x,1"),
            self.semantic.replace("REG,0,2\n", ""),
            "MEMORY_DONE\n" + self.semantic.replace("MEMORY_DONE\n", ""),
        ]
        for trace in corruptions:
            with self.subTest(trace=trace), self.assertRaises(AssertionError):
                checks.concrete_mismatch(trace, self.expected)


if __name__ == "__main__":
    unittest.main()
