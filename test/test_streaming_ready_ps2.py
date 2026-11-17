import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))

from streaming_ready_compile import decode
from streaming_ready_ps2 import decode_ps2_frame, ps2_receive_image


class StreamingReadyPS2Tests(unittest.TestCase):
    def test_released_receive_only_image(self):
        image = ps2_receive_image()
        self.assertEqual(image.words, (0x4004000A0006C001, 2))
        self.assertEqual((image.idle_levels, image.idle_enabled), (0, 0))
        self.assertEqual(image.certificate.stream_row, 0)
        receive, halt = map(decode, image.words)
        self.assertEqual((receive.operation, halt.operation), ('stream', 'halt'))
        self.assertEqual((receive.cell.low_cycles, receive.cell.high_cycles), (1, 217))
        self.assertEqual((receive.guard.mask, receive.guard.expected, receive.guard.limit.budget), (1, 0, None))
        self.assertEqual((receive.cell.transmit, receive.cell.receive, receive.cell.rx_input), (False, True, 1))
        self.assertEqual((receive.cell.low_enabled, receive.cell.high_enabled,
                          receive.cell.last_low_enabled, receive.cell.last_high_enabled), (0, 0, 0, 0))

    def test_all_bytes_and_independent_invalid_fields(self):
        for byte in range(256):
            with self.subTest(byte=byte):
                bits = (False, *(bool(byte & (1 << index)) for index in range(8)),
                        not byte.bit_count() % 2, True)
                self.assertEqual(decode_ps2_frame(bits), byte)
                for field in (0, 9, 10):
                    invalid = bits[:field] + (not bits[field],) + bits[field + 1:]
                    self.assertIsNone(decode_ps2_frame(invalid))

    def test_decoder_requires_exact_boolean_frame(self):
        for bits in ((False,) * 10, (False,) * 12, [False] * 11, (0,) * 11):
            with self.subTest(bits=bits), self.assertRaises(ValueError):
                decode_ps2_frame(bits)


if __name__ == '__main__':
    unittest.main()
