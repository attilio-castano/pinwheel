"""UART source shape, timing compensation and LSB-first host interpretation."""
from dataclasses import replace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_ready_compile import Guard, Instruction, WaitLimit, i2c_image, lower
from streaming_uart_compile import (Profile, lean_certificate, project, reverse_byte,
    uart_image, validate_uart_image)


class UartCompileTests(unittest.TestCase):
    def test_nine_rows_use_generic_released_ready_operations(self):
        for q in (4, 12, 128):
            image = uart_image(q)
            self.assertEqual([i.operation for i in image.source.instructions],
                ['drive_wait', 'drive_wait', 'pulse', 'drive_wait', 'pulse', 'stream', 'pulse', 'drive_wait', 'halt'])
            self.assertEqual((image.idle_levels, image.idle_enabled, image.certificate.stream_row), (0, 0, 5))
            stream = image.source.instructions[5]
            self.assertFalse(stream.cell.transmit)
            self.assertTrue(stream.cell.receive)
            self.assertIsNone(stream.guard)
            for instruction in image.source.instructions:
                if instruction.cell:
                    c = instruction.cell
                    self.assertEqual((c.low_levels, c.low_enabled, c.high_levels, c.high_enabled), (0, 0, 0, 0))
                if instruction.pins: self.assertEqual((instruction.pins.levels, instruction.pins.enabled), (0, 0))

    def test_timing_compensation_includes_fetch_boundary_and_check_edges(self):
        for q in range(4, 129):
            image = uart_image(q)
            a, b, stream = [image.source.instructions[row].cell for row in (2, 4, 5)]
            self.assertEqual(a.low_cycles + a.high_cycles + 4, 2 * q)
            self.assertEqual(b.low_cycles + b.high_cycles + 4 + stream.low_cycles, 4 * q)
            self.assertEqual(stream.low_cycles + stream.high_cycles + 1, 4 * q)
            self.assertEqual(stream.high_cycles + a.low_cycles + a.high_cycles + 4, 4 * q)
            self.assertEqual(validate_uart_image(image), Profile(q, 0))

    def test_idle_and_start_waits_are_unbounded_center_checks_are_one_poll(self):
        for rx in (0, 1):
            image = uart_image(12, rx)
            for row, expected, budget in ((0, 1 << rx, None), (1, 0, None), (3, 0, 1), (7, 1 << rx, 1)):
                guard = image.source.instructions[row].guard
                self.assertEqual((guard.mask, guard.expected, guard.limit.budget), (1 << rx, expected, budget))

    def test_wrong_q_selector_and_integer_aliases_refuse(self):
        for q in (3, 129, True, 4.0, None):
            with self.subTest(q=q), self.assertRaises(ValueError): uart_image(q)
        for rx in (-1, 2, True, None):
            with self.subTest(rx=rx), self.assertRaises(ValueError): uart_image(4, rx)

    def test_generic_valid_but_non_uart_image_refuses_uart_validation(self):
        with self.assertRaises(ValueError): validate_uart_image(i2c_image())
        image = uart_image()
        for row, changed in ((3, replace(image.source.instructions[3], guard=Guard(1, 0, WaitLimit.misses(2)))),
                (5, replace(image.source.instructions[5], cell=replace(image.source.instructions[5].cell, transmit=True))),
                (2, replace(image.source.instructions[2], cell=replace(image.source.instructions[2].cell, low_cycles=3)))):
            source = list(image.source.instructions)
            source[row] = changed
            with self.subTest(row=row), self.assertRaises(ValueError): validate_uart_image(lower(source))

    def test_word_source_tampering_refuses_before_any_io(self):
        image = uart_image()
        object.__setattr__(image, 'words', (*image.words[:-1], 3))
        with self.assertRaises(ValueError): validate_uart_image(image)

    def test_all_256_lsb_first_values_differ_from_msb_packed_receipt_interpretation(self):
        for byte in range(256):
            bits = tuple(bool((byte >> bit) & 1) for bit in range(8))
            result = project(bits)
            self.assertEqual(result.value, byte)
            self.assertTrue(result.payload_valid)
            packed = sum(int(bit) << (7 - index) for index, bit in enumerate(bits))
            self.assertEqual(packed, reverse_byte(byte))
        self.assertNotEqual(reverse_byte(0x96), 0x96)

    def test_bad_stop_retains_data_without_valid_payload_and_partial_is_explicit(self):
        bits = (True, False) * 4
        result = project(bits, fault=True)
        self.assertEqual((result.value, result.raw_bits, result.complete, result.payload_valid), (0x55, bits, True, False))
        result = project(bits[:3], fault=True)
        self.assertIsNone(result.value)
        self.assertFalse(result.complete)
        self.assertEqual(result.raw_bits, bits[:3])
        self.assertFalse(project(bits, uart_timing=False).payload_valid)

    def test_projection_rejects_mutable_nonboolean_or_long_inputs(self):
        for bits in ([True] * 8, (1,) * 8, (True,) * 9):
            with self.subTest(bits=bits), self.assertRaises(ValueError): project(bits)

    def test_generated_kernel_certificate_uses_independent_lean_profile(self):
        for q in (4, 12, 128):
            image = uart_image(q)
            text = lean_certificate(image)
            self.assertIn('import Pinwheel.Program.StreamingUART', text)
            self.assertIn(f'⟨⟨{q - 4}, by decide⟩, 0⟩', text)
            self.assertIn('(image profile).words', text)
            self.assertIn(', '.join(map(str, image.words)), text)
            self.assertIn('decide +kernel', text)


if __name__ == '__main__': unittest.main()
