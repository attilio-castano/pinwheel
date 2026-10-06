"""Fail-closed public-state and command boundaries for buffered RTL evidence."""
from dataclasses import asdict
from collections import deque
from io import BytesIO
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from buffered_reactive_hardware_rtl import (BufferedReactiveRTL, COMMAND_FIELDS, STATE_WIDTHS, RTLSnapshot,
                                  compare_public_state, replay_vectors)
from pad_io import PadDrive, PadObservation


def snapshot():
    return RTLSnapshot(valid=1, busy=0, retained=1, rejected=0, mode=2, pc=0,
        remaining=0, levels=4, enabled=7, tx_consumed=32, rx_length=32,
        rx_data=0x96a53cc3, read_valid=1, read_bit=1, generation=1,
        transfer=1, exhausted=0, pending=0, stage1=1, stage2=2, virtual_pc=1023, env0=7, env1=6, phase=5, wait_left=0, scratch=0xa659,
        wires=0xf1, known=255, edge_inputs=2)


class PublicStateTests(unittest.TestCase):
    def test_every_public_state_field_is_compared(self):
        actual = snapshot()
        expected = {key: value for key, value in asdict(actual).items()
                    if key not in ('wires', 'known', 'edge_inputs')}
        compare_public_state(actual, expected)
        self.assertEqual(len(expected), 26)
        for key in expected:
            with self.subTest(field=key):
                mutated = dict(expected, **{key: expected[key] ^ 1})
                with self.assertRaisesRegex(RuntimeError, 'public state mismatch'):
                    compare_public_state(actual, mutated)

    def test_missing_and_extra_state_fields_are_rejected(self):
        expected = {key: value for key, value in asdict(snapshot()).items()
                    if key not in ('wires', 'known', 'edge_inputs')}
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

    def test_snapshot_rejects_unrepresentable_public_fields_and_pads(self):
        for name, width in {**STATE_WIDTHS, 'wires': 8, 'known': 8, 'edge_inputs': 2}.items():
            for invalid in (-1, 1 << width, True, 1.0):
                with self.subTest(field=name, invalid=invalid):
                    values = dict(asdict(snapshot()), **{name: invalid})
                    with self.assertRaisesRegex(ValueError, 'exceeds its port width'):
                        RTLSnapshot(**values)

    def test_port_widths_reject_truncation_before_transport(self):
        transport = BufferedReactiveRTL.__new__(BufferedReactiveRTL)
        for name, width in COMMAND_FIELDS.items():
            for invalid in (-1, 1 << width, True, 1.0):
                with self.subTest(field=name, invalid=invalid):
                    with self.assertRaisesRegex(ValueError, 'exceeds its port width'):
                        transport.edge(**{name: invalid})
        with self.assertRaisesRegex(ValueError, 'Unknown reactive buffered hardware fields'):
            transport.edge(unknown_port=0)

    def test_wide_instruction_and_branch_tokens_are_hexadecimal(self):
        actual = snapshot()
        transport = BufferedReactiveRTL.__new__(BufferedReactiveRTL)
        transport.process = SimpleNamespace(stdin=BytesIO())
        transport.buffer = bytearray(('REACTIVE ' + ' '.join(map(str, asdict(actual).values())) + '\n').encode())
        transport.log, transport.cycle, transport.records = deque(), 0, []
        transport._device = None
        transport._drive = PadDrive()
        transport.observation = actual.observation
        word, branch = 0xfedcba9876543210, 0x81abcdef123456
        returned = transport.edge(word=word, control=0xabcdef, branch=branch)
        tokens = transport.process.stdin.getvalue().decode().split()
        indexes = {name: index for index, name in enumerate(COMMAND_FIELDS)}
        self.assertEqual(tokens[indexes['word']], 'fedcba9876543210')
        self.assertEqual(tokens[indexes['branch']], '81abcdef123456')
        self.assertEqual(int(tokens[indexes['control']]), 0xabcdef)
        self.assertEqual(transport.records[0]['command']['word'], word)
        self.assertEqual(transport.records[0]['command']['branch'], branch)
        self.assertEqual(returned, actual)

    def test_release_cannot_hide_pre_edge_output_ownership_or_high_drive(self):
        transport = BufferedReactiveRTL.__new__(BufferedReactiveRTL)
        transport.process = SimpleNamespace(stdin=BytesIO())
        transport.observation = PadObservation(1, 4, 4, 255, 255)
        for drive, reason in ((PadDrive(enabled=4), 'DUT-owned'),
                              (PadDrive(links=1), 'open-drain')):
            with self.subTest(drive=drive):
                with self.assertRaisesRegex(RuntimeError, reason):
                    transport.edge(command=4, drive=drive)
                self.assertEqual(transport.process.stdin.getvalue(), b'')

    def test_pre_edge_inputs_are_recorded_separately_from_post_edge_sampler(self):
        actual = snapshot()
        self.assertNotEqual(actual.edge_inputs, actual.stage1)
        expected = {key: value for key, value in asdict(actual).items()
                    if key not in ('wires', 'known', 'edge_inputs')}
        compare_public_state(actual, expected)
        with self.assertRaisesRegex(ValueError, 'every public state field'):
            compare_public_state(actual, dict(expected, edge_inputs=actual.edge_inputs))

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
                    if key not in ('wires', 'known', 'edge_inputs')}

        class Transport:
            def edge(self, *, drive, **command):
                self.drive, self.command = drive, command
                return actual

        transport = Transport()
        result = replay_vectors(transport, [dict(command=dict(command=3),
            raw_inputs=2, state=expected)])
        self.assertEqual((transport.drive.levels, transport.drive.enabled), (2, 3))
        self.assertEqual(transport.command, {'command': 3})
        self.assertEqual(result, {'edges': 1, 'public_state_fields': 26})


if __name__ == '__main__':
    unittest.main()
