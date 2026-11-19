import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))

from streaming_8x4_can import IDENTIFIER, PAYLOAD, peer_frame
from streaming_ready_can import CAPTURE_BITS, can_receive_image, decode_can_frame
from streaming_ready_compile import decode


class StreamingReadyCANTests(unittest.TestCase):
    def test_released_receive_image(self):
        image = can_receive_image()
        self.assertEqual(image.words, (0x4000000000004, 0x800008069, 2))
        self.assertEqual((image.idle_levels, image.idle_enabled, image.certificate.stream_row), (0, 0, 1))
        wait, receive, halt = map(decode, image.words)
        self.assertEqual((wait.operation, receive.operation, halt.operation), ('drive_wait', 'stream', 'halt'))
        self.assertEqual((wait.guard.mask, wait.guard.expected, wait.guard.limit.budget), (1, 0, None))
        self.assertEqual((wait.pins.levels, wait.pins.enabled), (0, 0))
        self.assertIsNone(receive.guard)
        cell = receive.cell
        self.assertEqual((cell.low_cycles, cell.high_cycles, cell.rx_input), (14, 17, 0))
        self.assertEqual((cell.transmit, cell.receive), (False, True))
        self.assertEqual((cell.low_enabled, cell.high_enabled, cell.last_low_enabled, cell.last_high_enabled),
                         (0, 0, 0, 0))

    def test_independent_negative_controls(self):
        valid = peer_frame(IDENTIFIER, PAYLOAD)
        bad_stuff = peer_frame(IDENTIFIER, PAYLOAD, 'stuffing')
        bad_crc = peer_frame(IDENTIFIER, PAYLOAD, 'crc')
        self.assertEqual(valid.crc, 0x7d6e)
        self.assertEqual(bad_stuff.crc, valid.crc)
        self.assertEqual([i for i, (a, b) in enumerate(zip(valid.samples, bad_stuff.samples)) if a != b],
                         [valid.stuff_slots[0]])
        self.assertEqual(bad_crc.crc, valid.crc ^ 1)
        self.assertEqual(decode_can_frame(valid.samples), (IDENTIFIER, PAYLOAD))
        self.assertIsNone(decode_can_frame(bad_stuff.samples))
        self.assertIsNone(decode_can_frame(bad_crc.samples))

    def test_valid_payloads_and_final_crc_stuff_bit(self):
        for identifier in (0, IDENTIFIER, 0x123, 0x456, 0x7ef):
            for byte in range(256):
                with self.subTest(identifier=identifier, byte=byte):
                    samples = peer_frame(identifier, byte).samples
                    self.assertEqual(decode_can_frame(samples), (identifier, byte))
        final_stuff = peer_frame(0, 0x1d)
        index = final_stuff.stuff_slots[-1]
        self.assertEqual(index, final_stuff.ack_slot - 2)
        bits = final_stuff.samples
        self.assertIsNone(decode_can_frame(bits[:index] + (bits[index - 1],) + bits[index + 1:]))

    def test_rejects_incomplete_capture_and_inactive_ack(self):
        frame = peer_frame(IDENTIFIER, PAYLOAD)
        self.assertIsNone(decode_can_frame(frame.sender))
        for samples in (frame.samples[:-1], (*frame.samples, True), [True] * CAPTURE_BITS, (1,) * CAPTURE_BITS):
            with self.subTest(samples=samples), self.assertRaises(ValueError):
                decode_can_frame(samples)


if __name__ == '__main__':
    unittest.main()
