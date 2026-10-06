"""Public resident admission, payload ownership and named control-flow checks."""
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from paired_execution import Machine, compile_resident, spi_image, uart_image
from pinwheel_host import (Command, Host, LEGACY_FORMAT, PAIRED_FORMAT,
                           RESIDENT_FORMAT, Pins, Program)
from pinwheel_program import ProgramBuilder, resident_spi, resident_uart, resource_report


class Transport:
    def __init__(self, *, live=2, result=0x10):
        self.pages = (live, 0, 0, result)
        self.edges = 0

    def advance(self, ui, cycles, *, rst_n=1):
        self.edges += cycles
        return Pins(self.pages[(ui >> 3) & 3], 0, 0)


class HostPayloadTests(unittest.TestCase):
    def test_byte_payload_is_sent_only_to_paired_hardware(self):
        transport = Transport()
        host = Host(transport, image_format=PAIRED_FORMAT)
        commands = []
        host.command = lambda command, data=0: commands.append((command, data))
        host.start(payload=0xa6)
        self.assertEqual(commands, [(Command.START, 0xa6)])
        legacy = Host(Transport())
        legacy.command = lambda command, data=0: commands.append((command, data))
        legacy.start()
        self.assertEqual(commands[-1], (Command.START, 0))

    def test_bad_or_unsupported_payload_never_touches_transport(self):
        for image_format, payload in [(PAIRED_FORMAT, -1), (PAIRED_FORMAT, 256),
                                      (PAIRED_FORMAT, True), (PAIRED_FORMAT, 1.0),
                                      (LEGACY_FORMAT, 1), (LEGACY_FORMAT, 255)]:
            with self.subTest(image_format=image_format, payload=payload):
                transport = Transport()
                with self.assertRaises(ValueError):
                    Host(transport, image_format=image_format).start(payload=payload)
                self.assertEqual(transport.edges, 0)

    def test_payload_start_preserves_busy_unread_and_stream_gates(self):
        for live, status, error in [(3, 0x10, 'valid program'),
                                    (2, 0x11, 'Consume'),
                                    (3, 0x18, 'Stop the UART stream')]:
            host = Host(Transport(live=live, result=status), image_format=PAIRED_FORMAT)
            if status & 8:
                host._stream_access = True
            commands = []
            host.command = lambda *args: commands.append(args)
            with self.subTest(live=live, status=status), self.assertRaisesRegex(RuntimeError, error):
                host.start(payload=0xa6)
            self.assertEqual(commands, [])

    def test_resident_source_targets_paired_hardware_only(self):
        program = resident_uart()
        transport = Transport()
        with self.assertRaisesRegex(ValueError, 'format'):
            Host(transport).upload(program)
        self.assertEqual(transport.edges, 0)
        host = Host(transport, image_format=PAIRED_FORMAT)
        commands = []
        host.command = lambda command, data=0: commands.append((command, data))
        host.upload(program)
        self.assertEqual(commands[0], (Command.BEGIN, 0))
        self.assertEqual(commands[-1], (Command.COMMIT, 0))
        self.assertEqual(tuple(value for command, value in commands if command == Command.PUSH),
                         program.upload_words())
        with self.assertRaisesRegex(ValueError, 'host image format'):
            Host(Transport(), image_format=RESIDENT_FORMAT)


class ResidentProgramTests(unittest.TestCase):
    def test_default_builders_reproduce_existing_resident_controller_images(self):
        self.assertEqual(resident_uart().upload_words(), uart_image().upload())
        self.assertEqual(resident_spi().upload_words(), spi_image().upload())

    def test_all_uart_payloads_keep_one_image_and_busy_start_cannot_replace_data(self):
        program = resident_uart()
        machine = Machine()
        machine.load(compile_resident(program.words, (program.idle_levels, program.idle_enabled), program.last))
        for byte in range(256):
            with self.subTest(byte=byte):
                machine.edge(command=5, data=byte)
                for edge in range(40):
                    expected = 0 if edge < 4 else (byte >> (edge // 4 - 1)) & 1 if edge < 36 else 1
                    self.assertEqual(machine.levels & 1, expected)
                    machine.edge(command=5, data=byte ^ 255)
                self.assertEqual(machine.mode, 5)

    def test_spi_data_is_preserved_on_clock_capture_and_wire_order_is_explicit(self):
        program = resident_spi()
        machine = Machine()
        machine.load(compile_resident(program.words, (program.idle_levels, program.idle_enabled), program.last))
        for byte in range(256):
            received = byte ^ 0xa5
            machine.edge(command=5, data=byte)
            for edge in range(68):
                phase = edge // 4
                self.assertEqual((machine.levels >> 1) & 1, phase % 2)
                self.assertEqual((machine.levels >> 2) & 1, 0)
                if phase < 16:
                    self.assertEqual(machine.levels & 1, (byte >> (7 - phase // 2)) & 1)
                slot = min(7, (edge + 1) // 8)
                machine.edge(incoming=(received >> (7 - slot)) & 1)
            self.assertEqual(machine.mode, 5)
            self.assertEqual(machine.samples & 255,
                             int(f'{received:08b}'[::-1], 2))

    def test_source_round_trip_keeps_format_and_resource_admission(self):
        program = resident_uart()
        encoded = json.dumps(dict(format=program.image_format, words=program.words,
            last=program.last, idle_levels=program.idle_levels,
            idle_enabled=program.idle_enabled)).encode()
        self.assertEqual(Program.from_bytes(encoded), program)
        uart = resource_report(program)
        spi = resource_report(resident_spi())
        self.assertEqual((uart['positions'], uart['upload_words'], uart['capture_slots']), (11, 290, []))
        self.assertEqual((spi['positions'], spi['upload_words'], spi['capture_slots']), (18, 290, list(range(8))))
        self.assertLessEqual(spi['used_parameters'], 32)

    def test_malformed_resident_sources_reject_before_io(self):
        shift = resident_uart().words[1]
        keep = resident_spi().words[1]
        for bad in [shift | 1 << 63, shift | 3 << 29, shift | 1 << 17,
                    keep | 8 << 35, (keep & ~(63 << 29)) | 2 << 29]:
            with self.subTest(bad=bad):
                transport = Transport()
                with self.assertRaises(ValueError):
                    Host(transport, image_format=PAIRED_FORMAT).upload(
                        Program((bad, 4), 1, image_format=RESIDENT_FORMAT))
                self.assertEqual(transport.edges, 0)


class NamedBuilderTests(unittest.TestCase):
    def test_terminal_capture_selects_two_literal_responses_without_new_opcode(self):
        builder = ProgramBuilder(outputs={'reply': 0}, inputs={'request': 0, 'selector': 1},
                                 captures={'choice': 7}, image_format=PAIRED_FORMAT)
        builder.wait('request', True, 8)
        builder.checked(1, terminal_capture=('selector', 'choice'),
                        branch=('choice', 'yes', 'no'))
        builder.label('yes').checked(8, high=('reply',), enabled=('reply',), jump='done')
        builder.label('no').checked(8, enabled=('reply',), jump='done')
        program = builder.label('done').halt().build()
        for selector in (0, 1):
            machine = Machine()
            machine.load(compile_resident(program.words, (0, 0), program.last))
            machine.edge(command=5)
            machine.edge(incoming=1)
            # Selector at the terminal edge chooses the successor entered on that edge.
            machine.edge(incoming=selector << 1)
            self.assertEqual(machine.levels & 1, selector)
            self.assertEqual(machine.enabled, 1)
            for _ in range(8):
                machine.edge()
            self.assertEqual(machine.mode, 5)

    def test_guard_and_qualification_use_named_inputs_and_full_bounds(self):
        builder = ProgramBuilder(outputs={'clock': 2}, inputs={'sense': 1}, captures={'bit': 15})
        builder.qualify(256, 256, condition={'sense': True})
        builder.checked(256, high=('clock',), enabled=('clock',), guard={'sense': True},
                        capture=('sense', 'bit'), terminal_capture=('sense', 'bit')).halt()
        self.assertEqual(resource_report(builder.build())['capture_slots'], [15])

    def test_bad_names_labels_cycles_and_legacy_extensions_are_rejected(self):
        for operation in [lambda b: b.action(0), lambda b: b.action(257),
                          lambda b: b.action(True), lambda b: b.action(1, high=('unknown',)),
                          lambda b: b.wait('unknown', True, 1), lambda b: b.wait('in0', 1, 1),
                          lambda b: b.action(1, capture=('in0', 16)),
                          lambda b: b.checked(1, jump='missing').build(),
                          lambda b: b.label('end').checked(1, jump='outside').label('outside').build(),
                          lambda b: b.checked(1, jump=0, branch=(0, 0, 0)),
                          lambda b: b.label('same').label('same')]:
            with self.subTest(operation=operation), self.assertRaises(ValueError):
                operation(ProgramBuilder())
        for image_format in (LEGACY_FORMAT, PAIRED_FORMAT):
            builder = ProgramBuilder(image_format=image_format)
            with self.assertRaisesRegex(ValueError, 'resident source format'):
                builder.shift('out0', 1)
            with self.assertRaisesRegex(ValueError, 'resident source format'):
                builder.keep(1)

    def test_builder_checks_record_and_position_capacity_before_returning_program(self):
        builder = ProgramBuilder(image_format=PAIRED_FORMAT)
        for duration in range(1, 33):
            builder.action(duration)
        with self.assertRaisesRegex(ValueError, 'capacity'):
            builder.build()
        # Resident admission uses actual parameter capacity, rather than the
        # stricter canonical E64 record-count theorem. These 32 captures plus
        # the noncapturing action need 33 distinct hardware parameter entries.
        builder = ProgramBuilder()
        for slot in range(32):
            builder.action(1, capture=(slot // 16, slot % 16))
        builder.action(1).halt()
        with self.assertRaisesRegex(ValueError, 'parameter capacity'):
            builder.build()
        builder = ProgramBuilder()
        for _ in range(256):
            builder.action(1)
        self.assertEqual(resource_report(builder.build())['positions'], 256)
        with self.assertRaisesRegex(ValueError, '256 positions'):
            builder.halt()


if __name__ == '__main__':
    unittest.main()
