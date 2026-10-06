"""Fail-closed public-state and command boundaries for buffered RTL evidence."""
from dataclasses import asdict
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from buffered_hardware_rtl import (BufferedRTL, COMMAND_FIELDS, RTLSnapshot,
                                  compare_public_state, replay_vectors)


def snapshot():
    return RTLSnapshot(valid=1, busy=0, retained=1, rejected=0, mode=2, pc=0,
        remaining=0, levels=4, enabled=7, tx_consumed=32, rx_length=32,
        rx_data=0x96a53cc3, read_valid=1, read_bit=1, generation=1,
        transfer=1, exhausted=0, pending=0, stage1=1, stage2=2,
        wires=0xf1, known=255)


class PublicStateTests(unittest.TestCase):
    def test_every_public_state_field_is_compared(self):
        actual = snapshot()
        expected = {key: value for key, value in asdict(actual).items()
                    if key not in ('wires', 'known')}
        compare_public_state(actual, expected)
        self.assertEqual(len(expected), 20)
        for key in expected:
            with self.subTest(field=key):
                mutated = dict(expected, **{key: expected[key] ^ 1})
                with self.assertRaisesRegex(RuntimeError, 'public state mismatch'):
                    compare_public_state(actual, mutated)

    def test_missing_and_extra_state_fields_are_rejected(self):
        expected = {key: value for key, value in asdict(snapshot()).items()
                    if key not in ('wires', 'known')}
        missing = dict(expected)
        del missing['generation']
        for malformed in (missing, dict(expected, wires=0), {}, None):
            with self.subTest(expected=malformed):
                with self.assertRaises(ValueError):
                    compare_public_state(snapshot(), malformed)
        for value in (True, -1, 2, 1.0):
            with self.subTest(value=value):
                with self.assertRaisesRegex(ValueError, 'exceeds its port width'):
                    compare_public_state(snapshot(), dict(expected, valid=value))

    def test_wire_bit_order_preserves_all_four_byte_lanes(self):
        actual = snapshot()
        expected = tuple(bool((0x96a53cc3 >> bit) & 1) for bit in range(32))
        self.assertEqual(actual.rx_bits, expected)
        self.assertEqual(actual.observation.levels, 16)
        self.assertEqual(actual.observation.enabled, 28)

    def test_port_widths_reject_truncation_before_transport(self):
        transport = BufferedRTL.__new__(BufferedRTL)
        for name, width in COMMAND_FIELDS.items():
            for invalid in (-1, 1 << width, True, 1.0):
                with self.subTest(field=name, invalid=invalid):
                    with self.assertRaisesRegex(ValueError, 'exceeds its port width'):
                        transport.edge(**{name: invalid})
        with self.assertRaisesRegex(ValueError, 'Unknown buffered hardware fields'):
            transport.edge(unknown_port=0)

    def test_vector_schema_raw_inputs_and_state_are_not_optional(self):
        for malformed in ([], (), [{'command': {}, 'raw_inputs': 0}],
                          [{'command': [], 'raw_inputs': 0, 'state': {}}],
                          [{'command': {}, 'raw_inputs': 4, 'state': {}}],
                          [{'command': {}, 'raw_inputs': True, 'state': {}}]):
            with self.subTest(vectors=malformed):
                with self.assertRaises(ValueError):
                    replay_vectors(None, malformed)

    def test_replay_applies_raw_inputs_as_external_pad_drive(self):
        actual = snapshot()
        expected = {key: value for key, value in asdict(actual).items()
                    if key not in ('wires', 'known')}

        class Transport:
            def edge(self, *, drive, **command):
                self.drive, self.command = drive, command
                return actual

        transport = Transport()
        result = replay_vectors(transport, [dict(command=dict(command=3),
            raw_inputs=2, state=expected)])
        self.assertEqual((transport.drive.levels, transport.drive.enabled), (2, 3))
        self.assertEqual(transport.command, {'command': 3})
        self.assertEqual(result, {'edges': 1, 'public_state_fields': 20})


if __name__ == '__main__':
    unittest.main()
