"""Host failures and serialization boundaries; protocol behavior is tested in RTL."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from pinwheel_host import Host, Pins, Program, LEGACY_FORMAT, PAIRED_FORMAT


class Transport:
    def __init__(self, pages=(2, 0x53, 0xa6, 0xb1)):
        self.pages = pages
        self.edges = 0
        self.controls = []

    def advance(self, ui, cycles, *, rst_n=1):
        self.edges += cycles
        self.controls.append(ui)
        return Pins(self.pages[(ui >> 3) & 3], 0, 0)


class HostTests(unittest.TestCase):
    def test_formats_cannot_be_cross_uploaded(self):
        for target, supplied in [(LEGACY_FORMAT, PAIRED_FORMAT), (PAIRED_FORMAT, LEGACY_FORMAT)]:
            transport = Transport()
            with self.subTest(target=target), self.assertRaisesRegex(ValueError, 'format'):
                Host(transport, image_format=target).upload(Program((4,), 0, image_format=supplied))
            self.assertEqual(transport.edges, 0)

    def test_paired_format_is_explicit_and_rejects_noncanonical_source(self):
        program = Program((4,), 0, 5, 3, PAIRED_FORMAT)
        stream = program.upload_words()
        self.assertEqual(len(stream), 290)
        self.assertEqual(stream[-2:], (4, 29))
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'paired.json'
            program.write(path)
            self.assertEqual(json.loads(path.read_text())['format'], PAIRED_FORMAT)
            self.assertEqual(Program.read(path), program)
        transport = Transport()
        with self.assertRaisesRegex(ValueError, 'E64 grammar'):
            Host(transport, image_format=PAIRED_FORMAT).upload(
                Program((1 << 63, 4), 1, image_format=PAIRED_FORMAT))
        self.assertEqual(transport.edges, 0)

    def test_program_padding_is_included_in_capacity(self):
        # 31 distinct records plus the padding halt fill all 32 dictionary slots.
        words = tuple(k << 9 for k in range(31))
        stream = Program(words, 30).upload_words()
        self.assertEqual(len(stream), 322)
        self.assertEqual(stream[31:64], (4,) * 33)
        self.assertEqual(tuple(stream[k] for k in stream[64:320]), words + (4,) * 225)
        with self.assertRaisesRegex(ValueError, '32 distinct'):
            Program(tuple(k << 9 for k in range(32)), 31).upload_words()

    def test_exact_capacity_without_padding_and_metadata(self):
        words = tuple((k % 32) << 9 for k in range(256))
        stream = Program(words, 255, 5, 3).upload_words()
        self.assertEqual(stream[-2:], (29, 255))
        self.assertEqual(tuple(stream[k] for k in stream[64:320]), words)

    def test_invalid_image_never_touches_the_transport(self):
        transport = Transport()
        host = Host(transport)
        for program in [Program((), 0), Program((4,), 1), Program((-1,), 0),
                        Program((1 << 64,), 0), Program((4,), 0, 8, 0),
                        Program((4,), 0.5), Program((4,), 0, True, 0)]:
            with self.subTest(program=program), self.assertRaises(ValueError):
                host.upload(program)
        self.assertEqual(transport.edges, 0)

    def test_json_round_trip_and_schema(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'program.json'
            program = Program((4,), 0, 7, 3)
            program.write(path)
            self.assertEqual(Program.read(path), program)
            self.assertEqual(Program.from_bytes(path.read_bytes()), program)
            path.write_text('{"format":"pinwheel-e64-v99"}')
            with self.assertRaisesRegex(ValueError, 'schema'):
                Program.read(path)
            path.write_text('[1, 2, 3]')
            with self.assertRaisesRegex(ValueError, 'schema'):
                Program.read(path)

    def test_captured_bytes_use_the_same_schema_and_capacity_validation(self):
        image = dict(format='pinwheel-e64-v1', words=[4], last=0, idle_levels=0, idle_enabled=0)
        for changes in [dict(format='other'), dict(words='4'), dict(words=[]),
                        dict(words=[1 << 64]), dict(last=True), dict(last=1),
                        dict(words=[k << 9 for k in range(32)], last=31)]:
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                Program.from_bytes(json.dumps(image | changes).encode('utf-8'))

    def test_result_read_is_nondestructive_and_preserves_error_flags(self):
        transport = Transport((2, 0x53, 0xa6, 0xb7))
        host = Host(transport)
        result = host.read_result(timeout_cycles=0, consume=False)
        self.assertEqual((result.samples, result.outcome_name, result.overrun, result.rejected),
                         (0xa653, 'complete', True, True))
        self.assertFalse(any(ui & 32 for ui in transport.controls))

    def test_unread_result_blocks_start(self):
        transport = Transport()
        with self.assertRaisesRegex(RuntimeError, 'Consume'):
            Host(transport).start()
        self.assertTrue(all(ui & 4 for ui in transport.controls))

    def test_busy_or_invalid_chip_blocks_start(self):
        for live in [0, 3]:
            transport = Transport((live, 0, 0, 0x10))
            with self.subTest(live=live), self.assertRaisesRegex(RuntimeError, 'valid program'):
                Host(transport).start()
            self.assertTrue(all(ui & 4 for ui in transport.controls))

    def test_poll_timeout_is_bounded_and_does_not_consume(self):
        transport = Transport((2, 0, 0, 0x10))
        with self.assertRaises(TimeoutError):
            Host(transport).read_result(timeout_cycles=23)
        self.assertLessEqual(transport.edges, 26)
        self.assertFalse(any(ui & 32 for ui in transport.controls))

    def test_unknown_interface_and_invalid_outcome_fail_closed(self):
        for status in [0, 0x18, 0x11]:
            transport = Transport((2, 0, 0, status))
            with self.subTest(status=status), self.assertRaises(RuntimeError):
                Host(transport).read_result(timeout_cycles=0)
            self.assertFalse(any(ui & 32 for ui in transport.controls))


if __name__ == '__main__':
    unittest.main()
