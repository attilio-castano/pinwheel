"""Directed edge semantics and rejection controls for the independent switch oracle."""
import copy
from pathlib import Path
import random
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import switch_oracle as oracle


def row(offered, ready, reset=False):
    return {"reset": reset,
            "offered": [None if p is None else {"destination": p[0], "payload": p[1]} for p in offered],
            "ready": ready}


class SwitchOracle(unittest.TestCase):
    def checked(self, rows, inputs, outputs, depth, drained=True):
        frames = oracle.simulate(rows, inputs, outputs, depth)
        counts = oracle.check_trace(rows, frames, inputs, outputs, depth, require_drained=drained)
        return frames, counts

    def test_no_empty_fifo_bypass_and_exact_delivery(self):
        rows = [row([None], [True], True), row([(0, 19)], [True]),
                row([None], [True]), row([None], [True])]
        frames, counts = self.checked(rows, 1, 1, 1)
        self.assertIsNone(frames[1]["post"]["offered"][0])
        self.assertEqual(frames[2]["post"]["offered"][0], {"source": 0, "destination": 0, "payload": 19})
        self.assertEqual((counts["accepted"], counts["emitted"]), (1, 1))

    def test_full_replacement_and_output_stall(self):
        rows = [row([None], [True], True), row([(0, 10)], [True]), row([(0, 11)], [True]),
                row([(0, 12)], [False]), row([(0, 12)], [True]),
                row([None], [True]), row([None], [True])]
        frames, counts = self.checked(rows, 1, 1, 1)
        self.assertTrue(frames[2]["pre"]["ready"][0])
        self.assertFalse(frames[3]["pre"]["ready"][0])
        self.assertEqual(frames[3]["pre"]["offered"], frames[3]["post"]["offered"])
        self.assertTrue(frames[4]["pre"]["ready"][0])
        self.assertEqual(frames[4]["state"]["queues"][0][0]["payload"], 12)
        self.assertEqual((counts["accepted"], counts["emitted"]), (3, 3))

    def test_outputs_advance_independently(self):
        rows = [row([None, None], [False, False], True),
                row([(0, 10), (1, 20)], [False, False]), row([None, None], [False, False]),
                row([None, (1, 21)], [False, True]), row([None, None], [False, True]),
                row([None, None], [False, True]), row([None, None], [True, True])]
        frames, counts = self.checked(rows, 2, 2, 2)
        self.assertEqual(frames[4]["grants"], [None, 1])
        self.assertEqual(frames[3]["pre"]["offered"][0], frames[5]["pre"]["offered"][0])
        self.assertEqual((counts["accepted"], counts["emitted"]), (3, 3))

    def test_head_of_line_blocking_and_cross_destination_overtaking(self):
        rows = [row([None], [False, True], True), row([(0, 10)], [False, True]),
                row([(0, 11)], [False, True]), row([(1, 12)], [False, True]),
                row([None], [False, True]), row([None], [True, True]),
                row([None], [False, True]), row([None], [False, True]), row([None], [True, True])]
        frames, counts = self.checked(rows, 1, 2, 3)
        self.assertEqual(frames[4]["grants"], [None, None])
        self.assertEqual([p["payload"] for p in frames[4]["state"]["queues"][0]], [11, 12])
        self.assertEqual(frames[7]["pre"]["offered"][1]["payload"], 12)
        self.assertEqual(frames[8]["pre"]["offered"][0]["payload"], 11)
        self.assertEqual(counts["emitted"], 3)

    def test_reset_cancels_all_occurrences_and_resets_cursor(self):
        rows = [row([(0, 7)] * 3, [False], True), row([(0, 7)] * 3, [False]),
                row([(0, 7)] * 3, [False]), row([(0, 7)] * 3, [True], True),
                row([None] * 3, [True])]
        frames, counts = self.checked(rows, 3, 1, 2)
        self.assertEqual(frames[3]["pre"], {"ready": [False] * 3, "offered": [None]})
        self.assertEqual(frames[3]["state"], {"queues": [[], [], []], "slots": [None], "cursor": [0]})
        self.assertEqual(counts["accepted"], counts["discarded_by_reset"])
        self.assertGreater(counts["discarded_by_reset"], 0)

    def test_round_robin_non_power_of_two_and_repeated_payloads(self):
        n = 5
        rows = [row([None] * n, [True], True)] + [row([(0, 0)] * n, [True]) for _ in range(31)]
        rows += [row([None] * n, [True]) for _ in range(n * 2 + 2)]
        frames, counts = self.checked(rows, n, 1, 1)
        selected = [f["grants"][0] for f in frames[2:27]]
        self.assertEqual(selected, list(range(n)) * 5)
        self.assertEqual(counts["accepted"], counts["emitted"])
        self.assertEqual(counts["max_competing_services_waited"], n - 1)

    def test_fixed_priority_is_rejected_by_service_opportunity_fairness(self):
        class FixedPriority(oracle.SwitchOracle):
            def choose(self, output):
                return next((k for k, q in enumerate(self.queues) if q and q[0].destination == output), None)
        rows = [row([None] * 3, [True], True)] + [row([(0, 9)] * 3, [True]) for _ in range(10)]
        bad = FixedPriority(3, 1, 1)
        frames = [bad.edge(i) for i in rows]
        with self.assertRaisesRegex(AssertionError, "fairness bound"):
            oracle.scoreboard(rows, frames, 3, 1, 1)
        # Safety remains valid; this specifically distinguishes arbitration progress.
        oracle.scoreboard(rows, frames, 3, 1, 1, fairness=False)
        with self.assertRaisesRegex(AssertionError, "fairness bound"):
            oracle.check_trace(rows, frames, 3, 1, 1)

    def test_corrupt_grants_payload_reset_capacity_and_occurrences_are_rejected(self):
        rows = [row([None, None], [True, True], True), row([(0, 8), (1, 8)], [True, True]),
                row([None, None], [True, True]), row([None, None], [True, True])]
        good = oracle.simulate(rows, 2, 2, 1)

        def mutate_payload(f): f[2]["post"]["offered"][0]["payload"] = 9
        def duplicate_input(f): f[2]["grants"] = [0, 0]
        def swap_routes(f): f[2]["grants"] = [1, 0]
        def missing_transfer(f): f[2]["grants"] = [None, 1]
        def lose_queue(f): f[1]["state"]["queues"][0] = []
        def corrupt_cursor(f): f[2]["state"]["cursor"][0] = 0
        def false_capacity(f): f[1]["pre"]["ready"][0] = False
        def transfer_during_reset(f): f[0]["pre"]["ready"][0] = True
        def stale_delivery(f): f[3]["state"]["slots"][0] = f[2]["state"]["slots"][0]
        for change in (mutate_payload, duplicate_input, swap_routes, missing_transfer, lose_queue,
                       corrupt_cursor, false_capacity, transfer_during_reset, stale_delivery):
            with self.subTest(mutation=change.__name__):
                bad = copy.deepcopy(good)
                change(bad)
                with self.assertRaises(AssertionError): oracle.check_trace(rows, bad, 2, 2, 1)

    def test_seeded_matrix_conservation_and_drain(self):
        for n, m, depth in ((1, 1, 1), (1, 3, 1), (3, 1, 1), (3, 3, 3), (5, 3, 2), (3, 5, 3)):
            with self.subTest(inputs=n, outputs=m, depth=depth):
                rng = random.Random(0x53574954)
                rows = [row([None] * n, [False] * m, True)]
                for _ in range(150):
                    offers = [None if rng.randrange(3) == 0 else (rng.randrange(m), rng.randrange(4)) for _ in range(n)]
                    rows.append(row(offers, [bool(rng.randrange(2)) for _ in range(m)], rng.randrange(47) == 0))
                rows += [row([None] * n, [True] * m) for _ in range(n * depth + m + 3)]
                self.checked(rows, n, m, depth)

    def test_reject_invalid_logical_destinations_and_port_shapes(self):
        for counts in ((0, 1, 1), (1, 0, 1), (1, 1, 0)):
            with self.assertRaises(ValueError): oracle.simulate([], *counts)
        bad = row([(3, 7)], [True, True, True])
        with self.assertRaises(ValueError): oracle.simulate([bad], 1, 3, 1)
        bad = row([(0, -1)], [True])
        with self.assertRaises(ValueError): oracle.simulate([bad], 1, 1, 1)
        bad = row([(0, 1)], [True])
        bad["reset"] = 1
        with self.assertRaises(ValueError): oracle.simulate([bad], 1, 1, 1)
        with self.assertRaises(ValueError): oracle.simulate([row([], [True])], 1, 1, 1)


if __name__ == "__main__":
    unittest.main()
