import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))

from streaming_8x4_ethernet import fixture_frame, phy_accepts
from streaming_ready_compile import decode
from streaming_ready_ethernet import ethernet_sni_image, minimum_frame, serial_bits


class StreamingReadyEthernetTests(unittest.TestCase):
    def test_alignment_and_transmit_words(self):
        image = ethernet_sni_image()
        self.assertEqual(image.words, (0x28000000c00004, 0x14000000c00004, 0x4000000c00004,
                                       0x14000000c00004, 0x4014000434d00001, 2))
        self.assertEqual((image.idle_levels, image.idle_enabled), (0, 3))
        self.assertEqual(image.certificate.stream_row, 4)
        stream = decode(image.words[4])
        self.assertTrue(stream.cell.transmit)
        self.assertFalse(stream.cell.receive)
        self.assertEqual((stream.cell.low_cycles, stream.cell.high_cycles), (1, 1))

    def test_independent_phy_rejects_preamble_and_crc_changes(self):
        frame = fixture_frame()
        self.assertEqual(frame[-4:].hex(), 'c6e81298')
        bits = serial_bits(frame)
        self.assertTrue(phy_accepts(bits))
        for index in (0, 63, 64, 575):
            with self.subTest(index=index):
                changed = (*bits[:index], not bits[index], *bits[index + 1:])
                self.assertFalse(phy_accepts(changed))

    def test_padding_is_covered_by_fcs(self):
        frame = minimum_frame(b'\0' * 6, b'\x02' + b'\0' * 5, 0x88b5, b'xyz')
        self.assertEqual(frame[22:-4], b'xyz' + b'\0' * 43)
        self.assertTrue(phy_accepts(serial_bits(frame)))


if __name__ == '__main__':
    unittest.main()
