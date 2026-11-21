"""Portable validation of the independent merge oracle and evidence boundary."""
import copy
import importlib.util
import sys
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import buffered_merge_oracle as oracle

spec = importlib.util.spec_from_file_location("merge_runner", SCRIPTS / "check-buffered-merge.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def row(valid, ready=True, reset=False, payload=7):
    return {"reset": reset, "valid": valid, "payload": [payload] * len(valid), "ready": ready}


def descriptor(n=3, w=8):
    return {
        "schema": 1, "module": "merge", "clock": "clk", "input_count": n,
        "output_count": 1, "payload_width": w, "cursor_encoding": "one_hot",
        "reset_synchronous": True,
        "inputs": [{"name": f"in_{k}", "width": 1 if k < n+2 else w} for k in range(2*n+2)],
        "outputs": [{"name": f"out_{k}", "width": w if k == n+1 else 1} for k in range(n+2)],
        "registers": [{"name": f"r_reg_{k}", "reference": f"r_reg_{k}", "width": w if k == 1 else 1,
                       "initial": int(k == 2), "reset": int(k == 2)} for k in range(n+2)],
        "roles": {"reset": "in_0", "out_ready": "in_1",
                  "in_valid": [f"in_{2+k}" for k in range(n)],
                  "in_payload": [f"in_{2+n+k}" for k in range(n)],
                  "in_ready": [f"out_{k}" for k in range(n)],
                  "out_valid": f"out_{n}", "out_payload": f"out_{n+1}"},
        "register_roles": {"slot_valid": "r_reg_0", "slot_payload": "r_reg_1",
                           "cursor": [f"r_reg_{2+k}" for k in range(n)]},
        "startup": "encoded_initial; hardware requires a reset edge before use"}


class MergeOracleTests(unittest.TestCase):
    def test_repeated_payloads_preserve_sources_and_occurrences(self):
        rows = [row([True]*3) for _ in range(9)] + [row([False]*3)]
        frames = oracle.simulate(rows, 3, 8)
        self.assertEqual([f["grant"] for f in frames], [0,1,2]*3 + [None])
        self.assertEqual([f["pre"]["offered"]["source"] for f in frames[1:]], [0,1,2]*3)
        self.assertEqual(oracle.check_trace(rows, frames, 3, 8, require_drained=True),
                         {"accepted": 9, "emitted": 9, "discarded_by_reset": 0,
                          "pending": 0, "max_competing_services_waited": 2})

    def test_stall_then_replacement(self):
        rows = [row([False, True], False)] + [row([True, True], False, payload=k) for k in range(15)]
        rows += [row([True, True], True, payload=12), row([False, False])]
        frames = oracle.simulate(rows, 2, 8)
        for f in frames[1:16]:
            self.assertEqual(f["state"], {"cursor": 0, "slot": {"source": 1, "payload": 7}})
            self.assertIsNone(f["grant"])
        self.assertEqual(frames[16]["grant"], 0)
        self.assertEqual(frames[16]["pre"]["offered"], {"source": 1, "payload": 7})
        self.assertEqual(frames[16]["post"]["offered"], {"source": 0, "payload": 12})
        oracle.check_trace(rows, frames, 2, 8, require_drained=True)

    def test_reset_discards_exactly_held_occurrence(self):
        rows = [row([True]*2, False), row([True]*2, True, True), row([True]*2), row([False]*2)]
        frames = oracle.simulate(rows, 2, 8)
        self.assertEqual(frames[1]["pre"], {"ready": [False]*2, "offered": None})
        self.assertEqual(frames[1]["state"], {"cursor": 0, "slot": None})
        result = oracle.check_trace(rows, frames, 2, 8, require_drained=True)
        self.assertEqual((result["accepted"], result["emitted"], result["discarded_by_reset"]), (2,1,1))

    def test_idle_garbage_has_no_acceptance(self):
        rows = [row([False]*5, payload=255) for _ in range(5)]
        frames = oracle.simulate(rows, 5, 8)
        self.assertEqual(oracle.check_trace(rows, frames, 5, 8)["accepted"], 0)

    def test_single_input_and_one_bit_payload(self):
        rows = [row([True], payload=1), row([True], payload=0), row([False], payload=1)]
        frames = oracle.simulate(rows, 1, 1)
        self.assertEqual([f["state"]["cursor"] for f in frames], [0]*3)
        self.assertEqual(oracle.check_trace(rows, frames, 1, 1, require_drained=True)["emitted"], 2)

    def test_full_traffic_matrix_drains_and_covers(self):
        for config in runner.MATRIX:
            with self.subTest(config=config):
                rows, phases = runner.traffic(config, 11)
                frames = oracle.simulate(rows, *config)
                oracle.check_trace(rows, frames, *config, require_drained=True)
                runner.coverage(rows, frames, phases, config[0])

    def test_exact_modulo_scan_checked_independently_of_conservation(self):
        rows = [row([True, True])]
        frames = oracle.simulate(rows, 2, 8)
        f = frames[0]
        f.update(grant=1, state={"cursor": 0, "slot": {"source": 1, "payload": 7}})
        f["pre"]["ready"] = [False, True]
        f["post"] = {"ready": [True, False], "offered": {"source": 1, "payload": 7}}
        oracle.scoreboard(rows, frames, 2, 8)
        with self.assertRaisesRegex(AssertionError, "modulo-scan"):
            oracle.check_trace(rows, frames, 2, 8)

    def test_malformed_and_semantic_logical_frames_rejected(self):
        rows = [row([True, True]), row([False, False])]
        frames = oracle.simulate(rows, 2, 8)
        mutations = [lambda fs: fs.pop(),
                     lambda fs: fs[0].update(cycle=False),
                     lambda fs: fs[0].update(grant=True),
                     lambda fs: fs[0]["state"].update(cursor=0),
                     lambda fs: fs[0]["pre"].update(ready=[True, True]),
                     lambda fs: fs[0]["post"].update(ready=[False, False]),
                     lambda fs: fs[1]["pre"]["offered"].update(source=1),
                     lambda fs: fs[1]["pre"]["offered"].update(payload=7.0)]
        for mutate in mutations:
            altered = copy.deepcopy(frames)
            mutate(altered)
            with self.assertRaises(AssertionError):
                oracle.check_trace(rows, altered, 2, 8)

    def test_invalid_stimulus_rejected(self):
        mutations = [lambda r: r.update(reset=0), lambda r: r.update(ready=1),
                     lambda r: r.update(valid=[True]), lambda r: r.update(valid=[1, False]),
                     lambda r: r.update(payload=[True, 0]), lambda r: r.update(payload=[0, 256]),
                     lambda r: r.update(payload=[-1, 0]), lambda r: r.update(extra=0)]
        for mutate in mutations:
            altered = row([True, False])
            mutate(altered)
            with self.assertRaises(ValueError):
                oracle.simulate([altered], 2, 8)
        for dimensions in ((0, 8), (2, 0), (True, 8), (2, 1.0)):
            with self.assertRaises(ValueError):
                oracle.MergeOracle(*dimensions)

    def test_pending_requires_explicit_drain(self):
        rows = [row([True])]
        with self.assertRaisesRegex(AssertionError, "Pending"):
            oracle.check_trace(rows, oracle.simulate(rows, 1, 8), 1, 8, require_drained=True)

    def test_descriptor_exact_width_reset_and_role_boundary(self):
        runner.validate_descriptor(descriptor(), 3, 8)
        mutations = [lambda d: d.update(schema=True), lambda d: d.update(reset_synchronous=1),
                     lambda d: d["registers"][0].update(reference="r_r_reg_0"),
                     lambda d: d["registers"][2].update(initial=0),
                     lambda d: d["inputs"][0].update(width=True),
                     lambda d: d["roles"]["in_ready"].reverse(),
                     lambda d: d["register_roles"]["cursor"].pop(),
                     lambda d: d.update(startup="zero initialized")]
        for mutate in mutations:
            altered = descriptor()
            mutate(altered)
            with self.assertRaises(ValueError):
                runner.validate_descriptor(altered, 3, 8)

    def test_trace_checker_rejects_malformed_negative_evidence(self):
        self.assertEqual(len(runner.checker_self_test()), 8)


if __name__ == "__main__":
    unittest.main()
