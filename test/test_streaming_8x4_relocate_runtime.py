from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import streaming_8x4_relocate_runtime as relocation


class RelocationTests(unittest.TestCase):
    def test_changed_historical_receipt_is_rejected_before_preparation(self):
        with tempfile.TemporaryDirectory() as tmp:
            recovery = Path(tmp) / "restored"
            report = recovery / relocation.REPORT
            report.parent.mkdir(parents=True)
            report.write_text('{"passed":true}\n')
            trusted = relocation.runtime.digest(report)
            report.write_text('{"passed":false}\n')
            output = Path(tmp) / "fresh"
            with self.assertRaisesRegex(ValueError, "Historical runtime audit hash mismatch"):
                relocation.relocate(recovery, trusted, output)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
