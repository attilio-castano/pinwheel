"""Static rejection and source-binding controls for the opt-in Ready codec."""
from dataclasses import replace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_compile as old
import streaming_ready_compile as c


class ReadyCompile(unittest.TestCase):
    def test_unguarded_legacy_words_are_preserved(self):
        for image in (old.spi_image(), old.jtag_image()):
            lifted = tuple(c.Instruction(i.operation, i.cell) for i in image.source.instructions)
            ready = c.lower(lifted, idle_levels=image.idle_levels, idle_enabled=image.idle_enabled)
            self.assertEqual(ready.words, image.words)
            self.assertNotEqual(ready.certificate.format, image.certificate.format)

    def test_seven_row_i2c_keeps_data_and_length_external(self):
        image = c.i2c_image()
        self.assertEqual(tuple(i.operation for i in image.source.instructions),
                         ('drive_wait', 'pulse', 'stream', 'pulse', 'drive_wait', 'pulse', 'halt'))
        self.assertEqual((len(image.words), image.certificate.stream_row, c.I2C64_BITS), (7, 2, 585))
        self.assertEqual((image.idle_levels, image.idle_enabled), (0, 0))
        stream = image.source.instructions[2]
        self.assertEqual((stream.cell.tx_output, stream.cell.rx_input), (1, 1))
        self.assertEqual((stream.cell.low_enabled, stream.cell.high_enabled), (1, 0))
        self.assertTrue(stream.cell.tx_enable_mode)
        self.assertEqual((stream.guard.mask, stream.guard.expected, stream.guard.limit.budget), (1, 1, 31))
        for index, enabled in ((1, 2), (3, 3), (5, 2)):
            pulse = image.source.instructions[index].cell
            self.assertEqual((pulse.low_levels, pulse.high_levels), (0, 0))
            self.assertEqual((pulse.low_enabled, pulse.high_enabled), (enabled, enabled))
        self.assertNotIn('count', c.Source.__dataclass_fields__)

    def test_all_i2c_words_round_trip(self):
        image = c.i2c_image()
        self.assertEqual(tuple(map(c.decode, image.words)), image.source.instructions)

    def test_stop_preparation_uses_low_profile_and_preserves_standard_words(self):
        self.assertEqual(c.i2c_image().words, (0x07fc000000000004, 0x20801818,
            0x47d4080e80401819, 0x30c01818, 0x07d4000000800004, 0x20801818, 2))
        for low, high in ((16, 3), (256, 3), (4, 256)):
            image = c.i2c_image(low, high)
            stop_low = image.source.instructions[3].cell
            self.assertEqual((stop_low.low_cycles, stop_low.high_cycles), (low, high))
            self.assertEqual((stop_low.low_levels, stop_low.high_levels), (0, 0))
            self.assertEqual((stop_low.low_enabled, stop_low.high_enabled), (3, 3))
            for row in (1, 5):
                hold = image.source.instructions[row].cell
                self.assertEqual((hold.low_cycles, hold.high_cycles), (high, high))
            self.assertEqual(c.decode(image.words[3]), image.source.instructions[3])
        self.assertEqual(c.i2c_image(16, 3).words[3], 0x30c01078)

    def test_guard_boundaries_and_explicit_unbounded_round_trip(self):
        for mask in range(4):
            for expected in range(4):
                if expected & ~mask:
                    continue
                for budget in (None, 1, 2, 254, 255):
                    limit = c.WaitLimit.unbounded() if budget is None else c.WaitLimit.misses(budget)
                    for instruction in (c.Instruction('stream', c.Cell(), c.Guard(mask, expected, limit)),
                                        c.Instruction('drive_wait', guard=c.Guard(mask, expected, limit),
                                                      pins=c.Pins(7, 5))):
                        self.assertEqual(c.decode(c.encode(instruction)), instruction)
                        self.assertEqual((c.encode(instruction) >> 54) & 255, 0 if budget is None else budget)

    def test_zero_mask_guard_is_distinct_from_disabled_guard(self):
        plain = c.Instruction('stream', c.Cell())
        guarded = c.Instruction('stream', c.Cell(), c.Guard())
        self.assertEqual(c.encode(guarded) ^ c.encode(plain), 1 << 62)
        self.assertEqual(c.decode(c.encode(guarded)), guarded)

    def test_zero_or_implicit_budget_rejects(self):
        for value in (0, -1, 256, True, None):
            with self.subTest(value=value), self.assertRaises(ValueError):
                c.WaitLimit.misses(value)
        with self.assertRaises(ValueError):
            c.Guard(1, 1, 0)

    def test_expected_outside_mask_rejects_in_source_and_word(self):
        for mask in range(4):
            for expected in range(4):
                if expected & ~mask:
                    with self.assertRaises(ValueError): c.Guard(mask, expected)
                    with self.assertRaises(ValueError): c.decode(4 | mask << 50 | expected << 52)

    def test_disabled_stream_guard_fields_reject(self):
        for bit in range(50, 62):
            with self.subTest(bit=bit), self.assertRaises(ValueError): c.decode(1 | 1 << bit)

    def test_drive_wait_unused_fields_reject(self):
        word = c.encode(c.Instruction('drive_wait', guard=c.Guard(), pins=c.Pins(5, 3)))
        for bit in (*range(3, 19), *range(25, 50), 62, 63):
            with self.subTest(bit=bit), self.assertRaises(ValueError): c.decode(word | 1 << bit)

    def test_pulse_stream_and_guard_operands_reject(self):
        for bit in range(31, 64):
            with self.subTest(bit=bit), self.assertRaises(ValueError): c.decode(1 << bit)

    def test_terminal_operands_and_invalid_opcodes_reject(self):
        for opcode in (2, 3):
            self.assertEqual(c.encode(c.decode(opcode)), opcode)
            for bit in range(3, 64):
                with self.assertRaises(ValueError): c.decode(opcode | 1 << bit)
        for opcode in (5, 6, 7):
            with self.assertRaises(ValueError): c.decode(opcode)
        with self.assertRaises(ValueError): c.decode((1 << 63) | 1)

    def test_pulse_and_terminal_typed_operands_are_strict(self):
        for operation in (lambda: c.Instruction('pulse', c.Cell(), c.Guard()),
                          lambda: c.Instruction('pulse', c.Cell(transmit=True)),
                          lambda: c.Instruction('halt', guard=c.Guard()),
                          lambda: c.Instruction('drive_wait', c.Cell(), c.Guard(), c.Pins()),
                          lambda: c.Instruction('stream', c.Cell(), pins=c.Pins())):
            with self.assertRaises(ValueError): operation()

    def test_shape_and_row_limits(self):
        stream, halt = c.Instruction('stream', c.Cell()), c.Instruction('halt')
        wait = c.Instruction('drive_wait', guard=c.Guard(), pins=c.Pins())
        self.assertEqual(len(c.lower((wait,) * 62 + (stream, halt)).words), 64)
        for source in ((), (halt,), (stream,), (stream, stream, halt),
                       (halt, stream, halt), (wait, halt), (wait,) * 63 + (stream, halt)):
            with self.assertRaises(ValueError): c.lower(source)

    def test_timing_profiles_reject_before_compilation(self):
        for arguments in (dict(wait_budget=0), dict(wait_budget=256), dict(low_cycles=2),
                          dict(high_cycles=2), dict(peer_tco=2), dict(stretch_bound=29),
                          dict(wait_budget=True), dict(peer_tco=-1)):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError): c.i2c_image(**arguments)
        self.assertEqual(len(c.i2c_image(256, 256, 255, peer_tco=253, stretch_bound=252).words), 7)

    def test_word_source_certificate_and_old_format_refuse(self):
        image = c.i2c_image()
        for operation in (lambda: replace(image, words=(*image.words[:-1], 3)),
                          lambda: replace(image, certificate=replace(image.certificate, source_sha256='0' * 64)),
                          lambda: replace(image, certificate=replace(image.certificate, words_sha256='0' * 64)),
                          lambda: replace(image, source=replace(image.source, idle_enabled=1)),
                          lambda: c.validate_image(old.spi_image()),
                          lambda: replace(image.certificate, format=old.FORMAT)):
            with self.assertRaises(ValueError): operation()

    def test_mutated_objects_are_revalidated(self):
        image = c.i2c_image()
        object.__setattr__(image.source.instructions[2].guard.limit, 'budget', 0)
        with self.assertRaises(ValueError): c.validate_image(image)

    def test_boolean_integer_aliases_refuse(self):
        for operation in (lambda: c.Guard(True, 0), lambda: c.Pins(0, False),
                          lambda: c.decode(True), lambda: c.lower((c.Instruction('stream', c.Cell()),
                              c.Instruction('halt')), idle_levels=False)):
            with self.assertRaises(ValueError): operation()

    def test_generated_kernel_check_binds_exact_words(self):
        image = c.i2c_image()
        text = c.lean_certificate(image)
        self.assertIn('import Pinwheel.Program.StreamingReadyCompile', text)
        self.assertIn('.driveWait ⟨0, 0⟩', text)
        self.assertIn('.misses 30', text)
        self.assertIn('compile source ⟨0, 0⟩', text)
        self.assertIn(', '.join(map(str, image.words)), text)
        self.assertIn('decide +kernel', text)


if __name__ == '__main__':
    unittest.main()
