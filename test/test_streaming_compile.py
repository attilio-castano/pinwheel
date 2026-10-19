"""Source/word refusal checks for the versioned streaming compiler."""
from dataclasses import replace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_compile as c


class StreamingCompile(unittest.TestCase):
    def test_spi_exact_words(self):
        image = c.spi_image()
        self.assertEqual(image.words, (0x71c01818, 0xc75c01819, 0x71c01818, 2))
        self.assertEqual((image.idle_levels, image.idle_enabled), (4, 7))
        self.assertEqual(image.certificate.stream_row, 1)

    def test_spi_finishing_pulse_keeps_cs_asserted_until_halt(self):
        source = c.spi_image().source.instructions
        finishing = source[-2].cell
        self.assertEqual((finishing.low_levels, finishing.high_levels), (0, 0))
        self.assertEqual(source[-1], c.Instruction('halt'))
        self.assertEqual(c.spi_image().idle_levels, 4)

    def test_jtag_exact_reset_navigation_and_last_bit(self):
        image = c.jtag_image()
        self.assertEqual(image.words,
            (0x7de01818,) * 5 + (0x75c01818, 0x7de01818, 0x75c01818, 0x75c01818,
                                  0x24c75c01819, 0x7de01818, 0x75c01818, 2))
        cell = image.source.instructions[9].cell
        self.assertEqual((cell.last_low_levels, cell.last_high_levels), (4, 4))
        self.assertEqual((cell.low_levels, cell.high_levels), (0, 2))

    def test_all_cell_field_boundaries_round_trip(self):
        base = c.Cell()
        for name, _, width in c.FIELDS:
            values = (False, True) if name in c.BOOLS else (1, 2, 255, 256) if name.endswith('_cycles') else (
                0, 1, 2) if name == 'tx_output' else (0, (1 << width) - 1)
            for value in values:
                with self.subTest(field=name, value=value):
                    instruction = c.Instruction('stream', replace(base, **{name: value}))
                    self.assertEqual(c.decode(c.encode(instruction)), instruction)

    def test_reserved_and_unsupported_opcodes_reject(self):
        word = c.spi_image().words[1]
        for bit in range(50, 64):
            with self.assertRaisesRegex(ValueError, 'Reserved'):
                c.decode(word | (1 << bit))
        for opcode in range(4, 8):
            with self.assertRaisesRegex(ValueError, 'Reserved'):
                c.decode((word & ~7) | opcode)

    def test_invalid_tx_selector_rejects(self):
        with self.assertRaises(ValueError):
            c.decode(c.spi_image().words[1] | (3 << 31))
        with self.assertRaises(ValueError):
            c.Cell(tx_output=3)

    def test_every_noncanonical_pulse_stream_operand_rejects(self):
        word = c.spi_image().words[0]
        for bit in range(31, 50):
            with self.subTest(bit=bit), self.assertRaisesRegex(ValueError, 'Pulse'):
                c.decode(word | (1 << bit))

    def test_every_terminal_operand_rejects(self):
        for opcode in (2, 3):
            self.assertEqual(c.encode(c.decode(opcode)), opcode)
            for bit in range(3, 64):
                with self.assertRaises(ValueError):
                    c.decode(opcode | (1 << bit))

    def test_missing_duplicate_stream_and_early_terminal_reject(self):
        stream = c.Instruction('stream', c.Cell())
        terminal = c.Instruction('halt')
        for source in ((), (terminal,), (stream,), (terminal, stream, terminal),
                       (stream, stream, terminal), (c.Instruction('pulse', c.Cell()), terminal)):
            with self.subTest(source=source), self.assertRaises(ValueError):
                c.lower(source)

    def test_row_limit_and_fault_terminal(self):
        prefix = (c.Instruction('pulse', c.Cell()),) * 62
        stream, fault = c.Instruction('stream', c.Cell()), c.Instruction('fault')
        image = c.lower((*prefix, stream, fault))
        self.assertEqual(len(image.words), 64)
        with self.assertRaises(ValueError):
            c.lower((*prefix, prefix[0], stream, fault))

    def test_corrupted_source_word_and_certificate_reject(self):
        image = c.spi_image()
        with self.assertRaisesRegex(ValueError, 'words differ'):
            replace(image, words=(*image.words[:-1], 3))
        with self.assertRaisesRegex(ValueError, 'certificate'):
            replace(image, certificate=replace(image.certificate, source_sha256='0' * 64))
        with self.assertRaisesRegex(ValueError, 'words differ'):
            replace(image, source=replace(image.source, instructions=c.jtag_image().source.instructions))

    def test_mutation_after_construction_detected_on_revalidation(self):
        image = c.spi_image()
        object.__setattr__(image, 'words', (0,) * 4)
        with self.assertRaises(ValueError):
            c.validate_image(image)

    def test_typed_values_reject_boolean_integer_aliases(self):
        for operation in (lambda: c.Cell(low_cycles=True), lambda: c.Cell(transmit=1),
                          lambda: c.decode(True), lambda: c.spi_image(True),
                          lambda: c.lower((c.Instruction('stream', c.Cell()), c.Instruction('halt')),
                                          idle_levels=False)):
            with self.assertRaises(ValueError):
                operation()

    def test_generic_pin_program_is_not_protocol_special_cased(self):
        cell = c.Cell(2, 256, low_levels=5, low_enabled=3, high_levels=1, high_enabled=2,
            tx_output=2, rx_input=1, transmit=True, receive=False, tx_enable_mode=True,
            tx_invert=True, last_low_enabled=1, last_high_enabled=4)
        image = c.lower((c.Instruction('stream', cell), c.Instruction('fault')), idle_levels=3)
        self.assertEqual(c.decode(image.words[0]), c.Instruction('stream', cell))

    def test_program_words_are_independent_of_transfer_length(self):
        spi, jtag = c.spi_image(), c.jtag_image()
        self.assertEqual(len(spi.words), 4)
        self.assertEqual(len(jtag.words), 13)
        # 32768/4097 are START operands; neither creates virtual source slots.
        self.assertNotIn('count', c.Source.__dataclass_fields__)

    def test_automatic_kernel_check_binds_every_word_and_idle(self):
        image = c.spi_image()
        text = c.lean_certificate(image)
        self.assertIn('import Pinwheel.Program.StreamingCompile', text)
        self.assertIn('compile source ⟨4, 7⟩', text)
        self.assertIn('decide +kernel', text)
        self.assertIn(', '.join(str(word) for word in image.words), text)


if __name__ == '__main__':
    unittest.main()
