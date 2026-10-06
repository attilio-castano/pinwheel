"""Compact read results preserve flags and discard every partial failure bit."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from pinwheel_host import Result
from protocol_results import i2c_read_result


class I2CReadResultTests(unittest.TestCase):
    def test_success_decodes_wire_order_for_one_and_two_bytes(self):
        for first in range(256):
            raw_first = int(f'{first:08b}'[::-1], 2)
            self.assertEqual(i2c_read_result(Result(raw_first, 5, False, False),
                                             byte_count=1).payload, (first,))
            for second in (0, 1, 0x53, 0x80, 0xa6, 255):
                raw_second = int(f'{second:08b}'[::-1], 2)
                result = i2c_read_result(Result(raw_first | raw_second << 8, 5, True, True),
                                         byte_count=2)
                self.assertEqual((result.outcome, result.payload), ('success', (first, second)))
                self.assertTrue(result.overrun)
                self.assertTrue(result.rejected)

    def test_failures_never_interpret_ack_slots_or_partial_payload(self):
        for byte_count in (1, 2):
            for outcome, name in ((6, 'timeout'), (7, 'nack_or_bus_fault')):
                for samples in (0, 1, 2, 4, 7, 0x69, 0xa600, 0xffff):
                    for overrun, rejected in ((False, False), (True, False), (False, True), (True, True)):
                        result = i2c_read_result(Result(samples, outcome, overrun, rejected),
                                                 byte_count=byte_count)
                        self.assertEqual((result.outcome, result.payload), (name, None))
                        self.assertEqual((result.overrun, result.rejected), (overrun, rejected))

    def test_invalid_count_raw_capture_or_outcome_fails_explicitly(self):
        for count in (0, 3, True, 1.0):
            with self.subTest(count=count), self.assertRaises(ValueError):
                i2c_read_result(Result(0, 5, False, False), byte_count=count)
        for samples in (-1, 1 << 16, True, 0.0):
            with self.subTest(samples=samples), self.assertRaises(ValueError):
                i2c_read_result(Result(samples, 5, False, False), byte_count=2)
        for outcome in (0, 1, 4, 8, True, 5.0):
            with self.subTest(outcome=outcome), self.assertRaises(ValueError):
                i2c_read_result(Result(0, outcome, False, False), byte_count=2)
        with self.assertRaisesRegex(ValueError, 'upper captures'):
            i2c_read_result(Result(0x0100, 5, False, False), byte_count=1)


if __name__ == '__main__':
    unittest.main()
