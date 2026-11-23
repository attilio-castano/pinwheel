"""Portable independent MMIO arithmetic, simultaneous effects, and ledger tests."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import mmio_oracle as o


class OracleTests(unittest.TestCase):
    def setUp(self):
        self.dirty = [0x12345678, o.MASK, 1, 0xa5, 1, 0x81, 1, 1]
        self.empty = [0, 0, 0, 0xa5, 0, 0x81, 0, 0]

    def test_complete_address_permissions_and_invalid_device(self):
        allowed = {(0, 0): (0, 3), (0, 1): (0, 1), (1, 0): (0, 3),
                   (2, 0): (0, 3), (2, 1): (3, 4), (2, 2): (0, 3), (2, 3): (3, 1)}
        for device in range(4):
            for word in range(64):
                for write in (False, True):
                    i = o.row(request_valid=True, device=device, word=word, write=write, data=0x89abcdef)
                    result, after = o.access(self.dirty, i)
                    self.assertEqual(result[0], allowed.get((device, word), (2, 2))[int(write)])
                    if result[0] >= 2:
                        self.assertEqual(after, self.dirty)

    def test_pre_edge_status_gpio_and_timer_wrap(self):
        i = o.row(request_valid=True, device=1, word=0)
        self.assertEqual(o.observe(self.dirty, i)[2:4], [0, o.MASK])
        self.assertEqual(o.step(self.dirty, i)[1], 0)
        for flags in range(16):
            s = self.dirty.copy()
            s[2], s[4], s[6], s[7] = (flags >> k & 1 for k in range(4))
            self.assertEqual(o.observe(s, o.row(request_valid=True, device=2))[3], flags ^ 1)
        self.assertEqual(o.observe(self.dirty, o.row(request_valid=True, gpio_input=0xfedcba98))[3], 0xfedcba98)

    def test_tx_preexisting_completion_and_low_byte(self):
        i = o.row(request_valid=True, device=2, word=1, write=True, data=0x87654321, tx_complete=True)
        self.assertEqual(o.observe(self.empty, i)[2:4], [1, 0])
        self.assertEqual(o.step(self.empty, i)[2:4], [1, 0x21])
        self.assertEqual(o.observe(self.dirty, i)[2:4], [4, 0])
        self.assertEqual(o.step(self.dirty, i)[2:4], [0, 0xa5])
        _, es, _ = o.oracle(self.empty, [i])
        self.assertNotIn("tx_complete", [e["kind"] for e in es[0]["events"]])

    def test_rx_empty_arrival_and_consume_refill(self):
        i = o.row(request_valid=True, device=2, word=2, rx_valid=True, rx_data=0x19)
        self.assertEqual(o.observe(self.empty, i)[2:4], [5, 0])
        self.assertEqual(o.step(self.empty, i)[4:6], [1, 0x19])
        self.assertEqual(o.observe(self.dirty, i)[2:4], [0, 0x81])
        self.assertEqual(o.step(self.dirty, i)[4:6], [1, 0x19])
        full = o.step(self.dirty, o.row(rx_valid=True, rx_data=0x22))
        self.assertEqual(full[4:7], [1, 0x81, 1])

    def test_errors_override_w1c_and_other_bits_ignored(self):
        clear = o.row(request_valid=True, device=2, word=3, write=True, data=12)
        self.assertEqual(o.step(self.dirty, clear)[6:], [0, 0])
        collide = dict(clear, rx_valid=True, rx_data=0x22, framing_error=True)
        self.assertEqual(o.step(self.dirty, collide)[6:], [1, 1])
        self.assertEqual(o.step(self.dirty, dict(clear, data=o.MASK ^ 12))[6:], [1, 1])

    def test_fault_cpu_atomicity_does_not_suppress_autonomous_effects(self):
        i = o.row(request_valid=True, device=3, word=1, write=True, data=0, tx_complete=True,
                  rx_valid=True, rx_data=0xff, framing_error=True)
        self.assertEqual(o.observe(self.dirty, i)[2:4], [2, 0])
        after = o.step(self.dirty, i)
        self.assertEqual(after, [0x12345678, 0, 0, 0xa5, 1, 0x81, 1, 1])
        _, events, ledger = o.oracle(self.dirty, [i])
        self.assertEqual([e["kind"] for e in events[0]["events"]], ["cpu", "tick", "tx_complete", "rx_arrival", "framing_error"])
        self.assertEqual((ledger["responses"], ledger["faults"], ledger["ticks"]), (1, 1, 1))

    def test_reset_dominance_and_inactive_retention(self):
        i = o.row(reset=True, request_valid=True, device=0, word=1, write=True, data=o.MASK,
                  tx_complete=True, rx_valid=True, rx_data=255, framing_error=True)
        self.assertEqual(o.observe(self.dirty, i), [0]*7)
        frames, events, ledger = o.oracle(self.dirty, [i, o.row()])
        self.assertEqual(frames[0]["registers"], [0]*8)
        self.assertEqual(events[0]["events"], [{"kind": "reset"}])
        self.assertEqual((ledger["offers"], ledger["responses"], ledger["ticks"]), (0, 0, 1))
        self.assertEqual(o.step(self.empty, o.row())[2:6], self.empty[2:6])
        self.assertEqual(o.observe(self.empty, o.row())[-1], 0)

    def test_widths_exact_json_types(self):
        for bank in (self.dirty[:-1], [True]+self.dirty[1:], self.dirty[:-1]+[2]):
            with self.assertRaises(ValueError):
                o.restore(bank)
        for bad in (dict(o.row(), reset=1), dict(o.row(), device=True), dict(o.row(), device=4),
                    dict(o.row(), rx_data=256), dict(o.row(), extra=0), dict(o.row(), word=-1)):
            with self.assertRaises(ValueError):
                o.validate_row(bad)

    def test_deterministic_complete_campaign_and_all_raw_flags(self):
        self.assertEqual(o.stimulus(), o.stimulus())
        startup, rows, coverage = o.stimulus()
        _, _, ledger = o.oracle(startup, rows)
        self.assertTrue(rows[0]["reset"])
        self.assertEqual(ledger["offers"], ledger["responses"])
        self.assertEqual(coverage["all_device_word_direction_codes"], 512)
        self.assertEqual({(r["device"], r["word"], r["write"]) for r in rows if r["request_valid"] and not r["reset"]},
                         {(d, w, write) for d in range(4) for w in range(64) for write in (False, True)})
        self.assertEqual(len(o.raw_cases()), 16)
        for case in o.raw_cases():
            frames, _, _ = o.oracle(case["startup"], case["rows"])
            self.assertEqual((frames[0]["pre"][3], frames[0]["registers"][1]), (o.MASK, 0))

    def test_replay_rejects_corrupt_response_effect_reset(self):
        original_step, original_observe = o.step, o.observe
        def corrupt_state(state, item):
            nxt = original_step(state, item)
            nxt[0] ^= 1
            return nxt
        with patch.object(o, "step", corrupt_state), self.assertRaisesRegex(AssertionError, "event replay"):
            o.oracle(self.dirty, [o.row()])
        def corrupt_reset(state, item):
            return state.copy() if item["reset"] else original_step(state, item)
        with patch.object(o, "step", corrupt_reset), self.assertRaisesRegex(AssertionError, "event replay"):
            o.oracle(self.dirty, [o.row(reset=True)])
        def corrupt_read(state, item):
            result = original_observe(state, item)
            result[3] ^= 1
            return result
        with patch.object(o, "observe", corrupt_read), self.assertRaisesRegex(AssertionError, "Actual response"):
            o.oracle(self.dirty, [o.row(request_valid=True, device=1)])


if __name__ == "__main__":
    unittest.main()
