"""Controls for the single-use fullbox diagnostic exception."""

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import streaming_8x4_enclosure_admission as admission


def transcript(diagnostics, *, before="", after=""):
    body = "[INFO DRT-0149] Reading tech and libs.\n" + "\n".join(diagnostics) + "\n"
    raw = (before + "PINWHEEL_POLICY2_FULLBOX_BEGIN\n" + body + "PINWHEEL_POLICY2_FULLBOX_END\n"
           + after + "PINWHEEL_POLICY2_CHECKS_COMPLETE\n")
    return body + "\n", raw


class EnclosureAdmissionTests(unittest.TestCase):
    def test_accepts_only_exact_fullbox_diagnostics(self):
        admission.validate_checker_logs(*transcript(admission.WARNING_LINES))
        for diagnostics in (
            admission.WARNING_LINES[:-1],
            admission.WARNING_LINES + (admission.WARNING_LINES[-1],),
            tuple(reversed(admission.WARNING_LINES)),
            admission.WARNING_LINES + ("[ERROR ODB-0269] Missing output",),
            admission.WARNING_LINES + ("WARNING: unsupported rule",),
        ):
            with self.subTest(diagnostics=diagnostics), self.assertRaises(ValueError):
                admission.validate_checker_logs(*transcript(diagnostics))

    def test_rejects_diagnostics_outside_fullbox(self):
        for position in ("before", "after"):
            with self.subTest(position=position), self.assertRaisesRegex(ValueError, "outside fullbox"):
                admission.validate_checker_logs(*transcript(
                    admission.WARNING_LINES, **{position: admission.WARNING_LINES[0] + "\n"},
                ))

    def test_rejects_capture_that_does_not_match_raw_checker(self):
        fullbox, raw = transcript(admission.WARNING_LINES)
        modified_raw = raw.replace("Reading tech and libs.", "Different run.")
        with self.assertRaisesRegex(ValueError, "does not match the raw checker"):
            admission.validate_checker_logs(fullbox, modified_raw)
        with self.assertRaisesRegex(ValueError, "completion boundaries"):
            admission.validate_checker_logs(fullbox, raw.replace("PINWHEEL_POLICY2_CHECKS_COMPLETE\n", ""))


if __name__ == "__main__":
    unittest.main()
