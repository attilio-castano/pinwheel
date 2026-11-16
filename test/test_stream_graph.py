"""Independent transaction oracle and branch-stall coverage checks."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location("graph_check", ROOT / "scripts/check-stream-graph.py")
graph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(graph)


class StreamGraph(unittest.TestCase):
    def test_pairing_oracle_rejects_wrong_order_loss_duplication_and_latency(self):
        stimulus = [(1, 0, 1, 0), (0, 1, 1, 7), (0, 0, 1, 0), (0, 0, 1, 0), (0, 0, 1, 0)]
        value = (8 << 8) | 248
        good = [(0, 0, 0, 0, 0, 0, 0), (1, 1, 0, 0, 1, 0, 0),
                (2, 0, 0, 0, 0, 0, 0), (3, 0, 0, 0, 1, 1, value), (4, 1, 1, value, 1, 0, 0)]
        self.assertEqual(graph.scoreboard(stimulus, good, 8, 1, 3)["emitted_across_epochs"], 1)
        for wrong in ((248 << 8) | 8, (8 << 8) | 247, value ^ 1):
            with self.subTest(wrong=wrong), self.assertRaises(AssertionError):
                graph.scoreboard(stimulus, good[:-1] + [(4, 1, 1, wrong, 1, 0, 0)], 8, 1, 3)
        for bad in (good[:-1], good[:-1] + [(4, 1, 0, 0, 1, 0, 0)],
                    good[:3] + [(3, 0, 1, value, 1, 0, 0), good[4]]):
            with self.assertRaises(AssertionError): graph.scoreboard(stimulus, bad, 8, 1, 3)

    def test_stalled_pair_is_stable_and_reset_cancels_pending(self):
        value = (3 << 8) | 253
        stimulus = [(1, 0, 1, 0), (0, 1, 1, 2), (0, 0, 0, 0), (1, 1, 0, 255), (0, 0, 1, 0)]
        good = [(0, 0, 0, 0, 0, 0, 0), (1, 1, 0, 0, 0, 1, value),
                (2, 0, 1, value, 0, 1, value), (3, 0, 0, 0, 0, 0, 0), (4, 1, 0, 0, 1, 0, 0)]
        graph.scoreboard(stimulus, good, 8, 1, 1)
        bad_stimulus = stimulus[:3] + [(0, 0, 0, 0)] + stimulus[4:]
        with self.assertRaisesRegex(AssertionError, "changed while stalled"):
            graph.scoreboard(bad_stimulus, good, 8, 1, 1)

    def test_coverage_counts_each_branch_independently(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "trace.csv"
            path.write_text("B,0,x,x,x,x\nB,1,0,1,1,0\nB,2,1,0,0,1\nB,3,1,1,1,1\n")
            self.assertEqual(graph.branch_coverage(path, [(1, 0, 0, 0)] + [(0, 0, 0, 0)] * 3),
                             {"left_only_blocked": 1, "right_only_blocked": 1, "unpaired_offer": 2})


if __name__ == "__main__":
    unittest.main()
