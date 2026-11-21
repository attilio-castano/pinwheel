from dataclasses import replace
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import byte_adapter_oracle as oracle


def initial(*, pending=0, write=0, signed=1, size=0, offset=1, q=0xfedcba98):
    return oracle.State((0x80ff7f01, 0x11223344), q,
                        oracle.Metadata(write, signed, size, 0, offset, 0xdeadbeef, pending))


class OracleTests(unittest.TestCase):
    def test_all_size_offset_faults(self):
        expected = [[0, 0, 0, 0], [0, 3, 0, 3], [0, 3, 3, 3], [2, 2, 2, 2]]
        self.assertEqual([[oracle.fault(size, offset) for offset in range(4)] for size in range(4)], expected)

    def test_all_signed_byte_and_half_loads(self):
        for size in (0, 1, 2):
            bits = 8*(1 << size)
            for offset in range(4):
                if oracle.fault(size, offset):
                    continue
                for value in (0, 1, (1 << (bits-1))-1, 1 << (bits-1), (1 << bits)-1):
                    q = value << (8*offset)
                    for signed in (0, 1):
                        metadata = oracle.Metadata(0, signed, size, 0, offset, 0x12345678, 1)
                        expected = value if not signed or value < 1 << (bits-1) else value-(1 << bits)
                        self.assertEqual(oracle.response(metadata, q), [0, expected & oracle.MASK])

    def test_store_changes_only_selected_bytes(self):
        old, data = bytes((1, 127, 255, 128)), bytes((0x78, 0x56, 0x34, 0x12))
        for size in range(3):
            count = 1 << size
            for offset in range(4):
                if oracle.fault(size, offset):
                    continue
                metadata = oracle.Metadata(1, 1, size, 0, offset, int.from_bytes(data, "little"), 1)
                expected = bytearray(old)
                expected[offset:offset+count] = data[:count]
                self.assertEqual(oracle.patch(int.from_bytes(old, "little"), metadata), int.from_bytes(expected, "little"))

    def test_capture_stall_commit_and_retained_irrelevant_fields(self):
        state = initial()
        offered = oracle.row(request_valid=True, write=True, signed=True, size=0, offset=2, data=0x12345678)
        pending = oracle.step(1, state, offered)
        self.assertEqual(pending.words, state.words)
        self.assertEqual(pending.q, state.words[0])
        self.assertEqual(pending.metadata, oracle.Metadata(1, 1, 0, 0, 2, 0x12345678, 1))
        attack = oracle.row(request_valid=True, size=3, address=1, offset=3, data=0xffffffff)
        self.assertEqual(oracle.step(1, pending, attack), pending)
        complete = dict(attack, response_ready=True)
        finished = oracle.step(1, pending, complete)
        self.assertEqual(finished.words, (0x80787f01, 0x11223344))
        self.assertEqual(finished.q, pending.q)
        self.assertEqual(finished.metadata, replace(pending.metadata, pending=0))
        self.assertEqual(oracle.observe(finished, complete), [1, 0, 0, 0])
        # The completing edge did not accept the hostile offer. Its later
        # admission captures even data ignored by a logical read request.
        later = oracle.step(1, finished, complete)
        self.assertEqual(later.metadata, oracle.Metadata(0, 0, 3, 1, 3, 0xffffffff, 1))
        self.assertEqual(later.q, finished.q)
        self.assertEqual(oracle.observe(later, complete), [0, 1, 2, 0])

    def test_reset_preserves_every_inactive_bit(self):
        state = initial(pending=1, write=1, size=2, offset=0)
        reset = oracle.row(reset=True, request_valid=True, write=True, size=2, data=0, response_ready=True)
        self.assertEqual(oracle.observe(state, reset), [0, 0, 0, 0])
        after = oracle.step(1, state, reset)
        self.assertEqual(after.registers()[:-1], state.registers()[:-1])
        self.assertEqual(after.metadata.pending, 0)
        self.assertEqual(oracle.step(1, after, oracle.row(response_ready=True)), after)

    def test_raw_startup_pending_is_not_invented_acceptance(self):
        state = initial(pending=1, write=0, signed=0, size=2, offset=0, q=99)
        frames, events, ledger = oracle.oracle(1, state.registers(), [oracle.row(response_ready=True)])
        self.assertEqual(frames[0]["pre"], [0, 1, 0, 99])
        self.assertEqual(events[0]["completed"]["origin"], "startup")
        self.assertEqual((ledger["startup_pending"], ledger["accepted"], ledger["completed"]), (1, 0, 1))

    def test_width_validation_and_zero_address(self):
        startup, rows, _ = oracle.stimulus(0)
        self.assertEqual(len(startup), 9)
        oracle.oracle(0, startup, rows)
        for bad in (startup[:-1], startup[:-1]+[2], [True]+startup[1:]):
            with self.assertRaises(ValueError):
                oracle.restore(0, bad)
        for invalid in (oracle.row(address=1), oracle.row(size=4), oracle.row(offset=4), oracle.row(data=1 << 32)):
            with self.assertRaises(ValueError):
                oracle.step(0, oracle.restore(0, startup), invalid)

    def test_deterministic_campaign_and_initialization(self):
        for a in (0, 1, 2, 3):
            with self.subTest(address_width=a):
                startup, rows, coverage = oracle.stimulus(a)
                self.assertEqual((startup, rows, coverage), oracle.stimulus(a))
                frames, events, ledger = oracle.oracle(a, startup, rows)
                self.assertEqual(len(frames), len(rows))
                self.assertEqual(frames[0]["registers"][:-1], startup[:-1])
                self.assertIsNone(ledger["pending"])
                self.assertEqual(ledger["accepted"]+ledger["startup_pending"], ledger["completed"]+ledger["canceled"])
                for kind in ("reads", "stores", "faults", "canceled"):
                    self.assertGreater(ledger[kind], 0)
                defined = set()
                for event in events[:coverage["initialization_edges"]]:
                    if event["accepted"] is not None:
                        write, _, size, address, offset, _ = event["accepted"]["request"]
                        self.assertEqual((size, offset), (2, 0))
                        if not write:
                            self.assertEqual(len(defined), 1 << a)
                    if event["write"] is not None:
                        defined.add(event["write"][0])
                self.assertEqual(len(defined), coverage["host_loaded_words"])

    def test_semantic_oracle_guards(self):
        original = oracle.step
        state = initial()
        rows = [oracle.row(request_valid=True, write=True, size=0, data=0x78), oracle.row(response_ready=True)]

        def early_write(a, old, item):
            result = original(a, old, item)
            if item["request_valid"] and not old.metadata.pending:
                return replace(result, words=(oracle.patch(result.q, result.metadata),)+result.words[1:])
            return result

        with patch.object(oracle, "step", early_write), self.assertRaisesRegex(AssertionError, "Memory effect"):
            oracle.oracle(1, state.registers(), rows)

        def corrupt_q(a, old, item):
            result = original(a, old, item)
            return replace(result, q=result.q ^ 1) if item["request_valid"] and not old.metadata.pending else result

        read_rows = [oracle.row(request_valid=True, size=2), oracle.row(response_ready=True)]
        with patch.object(oracle, "step", corrupt_q), self.assertRaisesRegex(AssertionError, "snapshot"):
            oracle.oracle(1, state.registers(), read_rows)

        def clear_metadata(a, old, item):
            result = original(a, old, item)
            return replace(result, metadata=replace(result.metadata, data=0)) if item["reset"] else result

        with patch.object(oracle, "step", clear_metadata), self.assertRaisesRegex(AssertionError, "Reset changed"):
            oracle.oracle(1, state.registers(), [oracle.row(reset=True)])


if __name__ == "__main__":
    unittest.main()
