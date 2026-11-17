import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))

from streaming_ready_compile import decode
from streaming_ready_swd import decode_dpidr, dpidr_image
from streaming_ready_wrapper import bridge_source


def reply(value, *, ack=1, wrong_parity=False):
    word = ack | (value << 3) | ((value.bit_count() % 2 ^ int(wrong_parity)) << 35)
    return tuple(bool(word & (1 << index)) for index in range(36))


class StreamingReadySwdTests(unittest.TestCase):
    def test_fixed_dpidr_image(self):
        image = dpidr_image()
        rows = tuple(map(decode, image.words))
        self.assertEqual(len(rows), 20)
        self.assertEqual(image.certificate.stream_row, 9)
        self.assertEqual((image.idle_levels, image.idle_enabled), (0, 1))
        self.assertEqual(sum(row.cell.low_levels // 2 << index for index, row in enumerate(rows[:8])), 0xA5)
        self.assertTrue(all(row.operation == 'pulse' and row.cell.low_enabled == row.cell.high_enabled == 3
            for row in rows[:8]))
        for index in (8, 10):
            cell = rows[index].cell
            self.assertEqual((cell.low_levels, cell.high_levels, cell.low_enabled, cell.high_enabled), (0, 1, 1, 1))
        self.assertTrue(rows[9].cell.receive)
        self.assertFalse(rows[9].cell.transmit)
        self.assertEqual(rows[9].cell.rx_input, 1)
        self.assertTrue(all(row.cell.low_levels == 0 and row.cell.high_levels == 1 and
            row.cell.low_enabled == row.cell.high_enabled == 3 for row in rows[11:19]))
        self.assertEqual(rows[-1].operation, 'halt')

    def test_exact_ack_and_parity(self):
        for value in (0, 1, 0xffffffff, 0x80000000, 0x2ba01477):
            self.assertEqual(decode_dpidr(reply(value)), value)
            self.assertIsNone(decode_dpidr(reply(value, wrong_parity=True)))
        for ack in (0, 2, 3, 4, 5, 6, 7):
            self.assertIsNone(decode_dpidr(reply(0x2ba01477, ack=ack)))
        with self.assertRaises(ValueError):
            decode_dpidr(reply(1)[:-1])

    def test_board_link_is_an_explicit_fixture_option(self):
        self.assertIn('tranif1 sda_link(pads[1],pads[3],links[1]);', bridge_source(2))
        shared = bridge_source(2, swdio_link=True)
        self.assertIn('tran swdio_link(pads[1],pads[3]);', shared)
        self.assertIn('if(links!==2\'b0)', shared)


if __name__ == '__main__':
    unittest.main()
