import copy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import transfer_host_oracle as oracle

SPEC = importlib.util.spec_from_file_location("host_checks", ROOT / "scripts/check-memory-transfer-host.py")
checks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checks)


def row(**kwargs):
    result = dict.fromkeys(oracle.INPUT_ROLES, 0)
    result.update(kwargs)
    return result


class OracleTests(unittest.TestCase):
    def test_stalled_snapshot_and_start_drain(self):
        state = oracle.State(oracle.Control(), oracle.Memory((10, 20), 99, 0), oracle.Memory((30, 40), 88, 0))
        state = oracle.step(1, 8, 8, state, row(source_req_valid=1, destination_req_valid=1,
                                              destination_req_address=1))
        self.assertEqual((state.source.q, state.destination.q), (10, 40))
        wait = row(start_valid=1, length=1, source_req_valid=1, source_req_write=1, source_req_data=255,
                   destination_req_valid=1, destination_req_write=1, destination_req_data=255)
        self.assertEqual(oracle.observe(state, wait), [0, 0, 0, 0, 0, 1, 10, 0, 1, 40])
        self.assertEqual(oracle.step(1, 8, 8, state, wait), state)
        wait.update(source_resp_ready=1, destination_resp_ready=1)
        drained = oracle.step(1, 8, 8, state, wait)
        self.assertEqual(drained.control.phase, 0)
        self.assertEqual((drained.source.words, drained.destination.words), ((10, 20), (30, 40)))
        self.assertEqual(oracle.observe(drained, wait)[0], 1)
        admitted = oracle.step(1, 8, 8, drained, wait)
        self.assertEqual(admitted.control.phase, 1)
        self.assertEqual(admitted.source.words, (10, 20))

    def test_two_word_prefix_and_reset_preservation(self):
        state = oracle.State(oracle.Control(), oracle.Memory((10, 20), 99, 0), oracle.Memory((30, 40), 88, 0))
        state = oracle.step(1, 8, 8, state, row(start_valid=1, length=2))
        attack = row(source_req_valid=1, source_req_write=1, source_req_data=0,
                     destination_req_valid=1, destination_req_write=1, destination_req_data=0)
        state = oracle.step(1, 8, 8, state, attack)
        self.assertEqual((state.control.phase, state.source.q, state.source.pending), (2, 10, 1))
        state = oracle.step(1, 8, 8, state, attack)
        self.assertEqual((state.control.index, state.destination.words, state.source.words), (1, (245, 40), (10, 20)))
        before = state
        state = oracle.step(1, 8, 8, state, row(reset=1, **{k: v for k, v in attack.items() if k != "reset"}))
        self.assertEqual(state.control, oracle.Control())
        self.assertEqual((state.source.words, state.source.q, state.destination.words, state.destination.q),
                         (before.source.words, before.source.q, before.destination.words, before.destination.q))

    def test_raw_recovery_and_invalid_zero_commands(self):
        state = oracle.State(oracle.Control(phase=3), oracle.Memory((1, 0), 1, 1), oracle.Memory((0, 1), 1, 1))
        self.assertEqual(oracle.observe(state, row()), [0]*10)
        state = oracle.step(1, 1, 1, state, row())
        self.assertEqual((state.control.error, state.source.pending, state.destination.pending), (1, 0, 0))
        invalid = oracle.step(1, 1, 1, state, row(start_valid=1, source_base=1, length=2))
        self.assertEqual(invalid.control, oracle.Control(error=1))
        empty = oracle.step(1, 1, 1, state, row(start_valid=1, source_base=1, destination_base=1))
        self.assertEqual((empty.control.done, empty.control.phase, empty.source, empty.destination),
                         (1, 0, state.source, state.destination))

    def test_complete_campaign_ledgers(self):
        for a, wi, wo in checks.MATRIX:
            with self.subTest(configuration=(a, wi, wo)):
                startup, rows, coverage = oracle.stimulus(a, wi, wo)
                frames, _, ledger = oracle.oracle(a, wi, wo, startup, rows)
                self.assertEqual(len(frames), len(rows))
                self.assertEqual(coverage["host_loaded_words"], 2*(1 << a))
                self.assertEqual(coverage["abort_positions"], list(range(2*(1 << a))))
                self.assertIsNone(ledger["unfinished_job"])
                for counts in ledger["host_reads"].values():
                    self.assertEqual(counts["accepted"], counts["emitted"]+counts["canceled"])
                    self.assertGreater(counts["canceled"], 0)
                self.assertTrue(any(j["length"] == 1 << a and not j["aborted"] for j in ledger["jobs"]))


class DescriptorTests(unittest.TestCase):
    @staticmethod
    def fixture():
        a, wi, wo = 1, 2, 3
        widths = checks.widths(a, wi, wo)
        d = dict(schema=1, address_width=a, input_width=wi, output_width=wo, clock="clk",
                 transform="invert_resize", module="host", roles={}, register_roles={})
        for group, roles, values in (("inputs", oracle.INPUT_ROLES, widths[0]),
                                     ("outputs", oracle.OUTPUT_ROLES, widths[1])):
            d[group] = [{"name": n, "width": w} for n, w in zip(roles, values)]
            d["roles"].update({n: n for n in roles})
        names = ["r_"+n for n in oracle.CONTROL_ROLES]
        d["register_roles"].update(dict(zip(oracle.CONTROL_ROLES, names)))
        for prefix in ("source", "destination"):
            words = [f"r_{prefix}_word{k}" for k in range(2)]
            d["register_roles"][prefix+"_words"] = words
            for suffix in ("q", "pending"):
                d["register_roles"][prefix+"_"+suffix] = f"r_{prefix}_{suffix}"
            names += words + [f"r_{prefix}_q", f"r_{prefix}_pending"]
        d["registers"] = [{"name": n, "reference": n, "width": w} for n, w in zip(names, widths[2])]
        return d

    def test_complete(self):
        checks.validate_descriptor(self.fixture(), 1, 2, 3)

    def test_reject_omission_alias_order_and_width(self):
        fixture = self.fixture()
        variants = []
        d = copy.deepcopy(fixture); d["registers"].pop(); variants.append(d)
        d = copy.deepcopy(fixture); d["register_roles"]["source_words"].reverse(); variants.append(d)
        d = copy.deepcopy(fixture); d["register_roles"]["source_q"] = d["register_roles"]["source_pending"]; variants.append(d)
        d = copy.deepcopy(fixture); d["registers"][0]["width"] = True; variants.append(d)
        d = copy.deepcopy(fixture); d["outputs"][0], d["outputs"][1] = d["outputs"][1], d["outputs"][0]; variants.append(d)
        for d in variants:
            with self.subTest(descriptor=d), self.assertRaises(ValueError):
                checks.validate_descriptor(d, 1, 2, 3)


if __name__ == "__main__":
    unittest.main()
