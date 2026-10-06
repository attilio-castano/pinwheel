"""Transaction requests, artifact binding, decoding and host ownership boundaries.

Injected fixed-protocol exporters are plumbing fixtures, not protocol oracles.
Resident programs use the public production factories and need no ignored files.
"""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from pinwheel_host import Command, Host, LEGACY_FORMAT, PAIRED_FORMAT, Pins, Result
from pinwheel_program import ProgramBuilder
from pinwheel_transactions import (ARTIFACT_SCHEMA, CapabilityError, Transaction,
    TransactionSpec, compile_transaction, i2c_register_read, jtag_scan,
    spi_transfer, uart_tx)


def program_object(program):
    return dict(format=program.image_format, words=list(program.words),
                last=program.last, idle_levels=program.idle_levels,
                idle_enabled=program.idle_enabled)


def fixture_exporter(request):
    """A deterministic legal image whose words bind the fixed request fields.

    It deliberately does not emulate SPI/I2C. Tests of their digital protocol
    compiler and resolved-pin behavior belong to their independent gates.
    """
    if request['protocol'] == 'spi-transaction':
        durations = [request['mode'] + 1, *[byte + 1 for byte in request['payload']],
                     request['half_cycles']]
    else:
        durations = [request['address'] + 1, request['register'] + 1,
                     request['byte_count'], request['phase_cycles'], request['wait_cycles']]
    builder = ProgramBuilder(image_format=PAIRED_FORMAT)
    for duration in durations:
        builder.action(duration)
    program = builder.halt().build()
    return dict(schema='pinwheel-compiled-program-v1', request=deepcopy(request),
                program=program_object(program))


def compiled(spec):
    return compile_transaction(spec, exporter=fixture_exporter)


def wire_slots(*bytes):
    return sum(sum(((byte >> (7 - bit)) & 1) << (8 * n + bit)
                   for bit in range(8)) for n, byte in enumerate(bytes))


class FakeHost:
    """Retained-result owner with all chip operations visible as recorded calls."""
    def __init__(self, raw=Result(0, 5, False, False), image_format=PAIRED_FORMAT,
                 busy_cycles=0):
        self.image_format = image_format
        self.committed_program = None
        self.program_generation = 0
        self.raw, self.unread, self.calls = raw, False, []
        self.edges, self.busy_cycles, self.busy_until = 0, busy_cycles, None

    def upload(self, program):
        self.calls.append(('upload', program))
        self.committed_program = program
        self.program_generation += 1

    def start(self, *, payload=0):
        if self.unread:
            raise RuntimeError('Consume the previous result before starting')
        if self.busy_until is not None and self.edges < self.busy_until:
            raise RuntimeError('Start requires an idle engine')
        self.calls.append(('start', payload))
        self.busy_until = self.edges + self.busy_cycles
        self.unread = not self.busy_cycles

    def _complete_if_ready(self):
        if self.busy_until is not None and self.edges >= self.busy_until:
            self.unread = True

    def page(self, page):
        self.calls.append(('page', page))
        self.edges += 3
        self._complete_if_ready()
        return 2 | int(self.busy_until is not None and self.edges < self.busy_until)

    def advance(self, cycles):
        self.calls.append(('advance', cycles))
        self.edges += cycles
        self._complete_if_ready()

    def read_result(self, *, timeout_cycles, consume):
        self.calls.append(('read', timeout_cycles, consume))
        if not self.unread:
            raise TimeoutError('No retained result')
        if consume:
            self.consume()
        return self.raw

    def consume(self):
        self.calls.append(('consume',))
        self.unread = False

    def reset(self):
        self.calls.append(('reset',))
        self.committed_program = None
        self.program_generation += 1
        self.unread = False
        self.busy_until = None


class TransactionRequestTests(unittest.TestCase):
    def test_supported_ranges_and_capabilities_are_declared_without_io(self):
        for cycles in (1, 4, 256):
            uart_tx(bit_cycles=cycles)
            spi_transfer(half_cycles=cycles)
            jtag_scan(half_cycles=cycles)
            i2c_register_read(127, 255, byte_count=2, phase_cycles=cycles, wait_cycles=cycles)
        for mode in range(4):
            for payload in ([0], bytes([0xa6, 0xff])):
                self.assertEqual(spi_transfer(payload, mode=mode).request['payload'], list(payload))
        with patch('pinwheel_transactions.export_lean', side_effect=AssertionError('compiler I/O')):
            for settings in ({'outgoing_bits': 32}, {'captured_bits': 32},
                             {'outgoing_bits': 32, 'captured_bits': 32}):
                with self.subTest(settings=settings), self.assertRaisesRegex(CapabilityError, '8-bit START operand or 16 capture'):
                    jtag_scan(**settings)
        for settings in ({'outgoing_bits': 7}, {'captured_bits': 16}):
            with self.assertRaisesRegex(CapabilityError, 'frontend implements'):
                jtag_scan(**settings)
        with self.assertRaisesRegex(CapabilityError, 'Resident SPI'):
            spi_transfer(mode=1)
        with self.assertRaises(CapabilityError):
            spi_transfer([0, 1, 2])

    def test_invalid_request_integers_bool_and_unknown_fields_fail(self):
        operations = [lambda value: uart_tx(bit_cycles=value),
                      lambda value: spi_transfer(half_cycles=value),
                      lambda value: i2c_register_read(0, 0, phase_cycles=value),
                      lambda value: i2c_register_read(0, 0, wait_cycles=value)]
        for operation in operations:
            for value in (0, 257, True, 4.0):
                with self.subTest(value=value), self.assertRaises(ValueError):
                    operation(value)
        for address in (-1, 128, True, 1.0):
            with self.assertRaises(ValueError):
                i2c_register_read(address, 0)
        for register in (-1, 256, True, 1.0):
            with self.assertRaises(ValueError):
                i2c_register_read(0, register)
        for count in (0, 3, True, 1.0):
            with self.assertRaises(CapabilityError):
                i2c_register_read(0, 0, byte_count=count)
        for byte in (-1, 256, True, 1.0):
            with self.assertRaises(ValueError):
                spi_transfer([byte])
        request = uart_tx().request
        for change in ({'unknown': 1}, {'bit_cycles': True}, {'protocol': 'unknown'}):
            with self.assertRaises(ValueError):
                TransactionSpec.from_request(dict(request, **change))

    def test_request_immutability_and_duplicate_json_fields(self):
        request = spi_transfer([0xa6]).request
        spec = TransactionSpec.from_request(request)
        request['payload'][0] = 0x53
        returned = spec.request
        returned['payload'][0] = 0x12
        self.assertEqual(spec.request['payload'], [0xa6])
        duplicate = uart_tx().request
        data = json.dumps(duplicate)[:-1] + ', "bit_cycles": 8}'
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON field'):
            TransactionSpec(data)

    def test_exporter_response_must_match_request_and_paired_format(self):
        spec = i2c_register_read(0x53, 0xa6, byte_count=2)
        good = fixture_exporter(spec.request)
        variants = []
        wrong_request = deepcopy(good)
        wrong_request['request']['address'] = 0x52
        variants.append(wrong_request)
        bool_request = deepcopy(good)
        bool_request['request']['byte_count'] = True
        variants.append(bool_request)
        wrong_format = deepcopy(good)
        wrong_format['program']['format'] = LEGACY_FORMAT
        variants.append(wrong_format)
        extra = deepcopy(good)
        extra['unbound'] = True
        variants.append(extra)
        for response in variants:
            with self.subTest(response=response), self.assertRaises(ValueError):
                compile_transaction(spec, exporter=lambda request: response)
        # Python treats False == 0 and True == 1; response validation must
        # still reject those types after the request-equality comparison.
        spec = i2c_register_read(0, 0, byte_count=1, phase_cycles=1)
        for field, value in (('address', False), ('byte_count', True), ('phase_cycles', True)):
            response = fixture_exporter(spec.request)
            response['request'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                compile_transaction(spec, exporter=lambda request: response)


class TransactionDecodeTests(unittest.TestCase):
    def test_all_spi_and_jtag_bytes_decode_distinct_wire_orders(self):
        spi = compiled(spi_transfer())
        jtag = compiled(jtag_scan())
        fixed_spi = compiled(spi_transfer([0xa6, 0x53], mode=3))
        for byte in range(256):
            with self.subTest(byte=byte):
                self.assertEqual(spi.decode(Result(wire_slots(byte), 5, False, False)).payload, (byte,))
                self.assertEqual(jtag.decode(Result(byte, 5, False, False)).payload, (byte,))
                self.assertEqual(fixed_spi.decode(Result(wire_slots(byte, byte ^ 0xa5), 5, False, False)).payload,
                                 (byte, byte ^ 0xa5))

    def test_i2c_failure_never_decodes_ack_or_partial_data(self):
        for count in (1, 2):
            transaction = compiled(i2c_register_read(0x53, 0xa6, byte_count=count))
            for outcome, name in ((6, 'timeout'), (7, 'nack_or_bus_fault')):
                for samples in (0, 1, 2, 4, 0x69, 0xa600, 0xffff):
                    result = transaction.decode(Result(samples, outcome, True, True))
                    self.assertEqual((result.outcome, result.payload), (name, None))
                    self.assertTrue(result.overrun and result.rejected)
            expected = (0xa6,) if count == 1 else (0xa6, 0x53)
            self.assertEqual(transaction.decode(Result(wire_slots(*expected), 5, False, False)).payload, expected)

    def test_failed_non_i2c_results_discard_captures_and_preserve_flags(self):
        for transaction in (compiled(uart_tx()), compiled(spi_transfer()), compiled(jtag_scan())):
            for outcome, name in ((6, 'timeout'), (7, 'fault')):
                result = transaction.decode(Result(0xffff, outcome, True, True))
                self.assertEqual((result.outcome, result.payload, result.overrun, result.rejected),
                                 (name, None, True, True))

    def test_success_layout_and_raw_integer_validation_are_strict(self):
        for transaction in (compiled(spi_transfer()), compiled(jtag_scan()),
                            compiled(i2c_register_read(0x53, 0xa6))):
            with self.assertRaises(ValueError):
                transaction.decode(Result(0x100, 5, False, False))
        with self.assertRaises(ValueError):
            compiled(uart_tx()).decode(Result(1, 5, False, False))
        for samples in (-1, 65536, True, 0.0):
            with self.assertRaises(ValueError):
                compiled(jtag_scan()).decode(Result(samples, 5, False, False))
        for outcome in (0, 4, 8, True, 5.0):
            with self.assertRaises(ValueError):
                compiled(jtag_scan()).decode(Result(0, outcome, False, False))


class TransactionArtifactTests(unittest.TestCase):
    def test_round_trip_binds_request_program_and_description(self):
        for spec in (uart_tx(), spi_transfer(), jtag_scan(), spi_transfer([0xa6, 0x53], mode=2),
                     i2c_register_read(0x53, 0xa6, byte_count=2)):
            transaction = compiled(spec)
            self.assertEqual(Transaction.from_bytes(json.dumps(transaction.artifact()).encode(),
                exporter=fixture_exporter), transaction)

    def test_request_program_and_metadata_tampering_are_rejected(self):
        transaction = compiled(uart_tx())
        mutations = []
        for field, value in (('bit_cycles', 8), ('bit_cycles', True)):
            artifact = transaction.artifact()
            artifact['request'][field] = value
            mutations.append(artifact)
        artifact = transaction.artifact()
        artifact['program']['words'][0] ^= 1 << 9  # A legal changed action duration.
        mutations.append(artifact)
        artifact = transaction.artifact()
        artifact['program']['words'][0] = True
        mutations.append(artifact)
        for field, value in (('last', True), ('idle_enabled', True), ('last', 0)):
            artifact = transaction.artifact()
            artifact['program'][field] = value
            mutations.append(artifact)
        for section, field, value in (('resources', 'positions', 12),
                                     ('resources', 'positions', True),
                                     ('pins', 'open_drain', 0),
                                     ('timing', 'input_sampler_edges', True),
                                     ('result_layout', 'bit_order', 'lsb_first_wire_slots')):
            artifact = transaction.artifact()
            artifact['description'][section][field] = value
            mutations.append(artifact)
        for artifact in mutations:
            with self.subTest(artifact=artifact), self.assertRaises(ValueError):
                Transaction.from_bytes(json.dumps(artifact).encode(), exporter=fixture_exporter)

    def test_nested_duplicate_fields_and_extra_schema_fields_fail_before_export(self):
        artifact = compiled(uart_tx()).artifact()
        data = json.dumps(artifact)
        duplicate = data.replace('"last": 10', '"last": 10, "last": 9')
        exporter = Mock(side_effect=AssertionError('unexpected exporter'))
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON field'):
            Transaction.from_bytes(duplicate.encode(), exporter=exporter)
        self.assertEqual(exporter.call_count, 0)
        artifact['schema'] = ARTIFACT_SCHEMA
        artifact['extra'] = 1
        with self.assertRaises(ValueError):
            Transaction.from_bytes(json.dumps(artifact).encode(), exporter=exporter)
        self.assertEqual(exporter.call_count, 0)


class LoadedTransactionOwnershipTests(unittest.TestCase):
    def test_success_reads_without_consuming_then_decodes_then_consumes(self):
        transaction = compiled(spi_transfer())
        host = FakeHost(Result(wire_slots(0x96), 5, True, True))
        loaded = transaction.load(host)
        host.calls.clear()
        result = loaded.run(payload=0xa6, timeout_cycles=99)
        self.assertEqual(result.payload, (0x96,))
        self.assertEqual(host.calls, [('start', 0xa6), ('page', 0), ('read', 96, False), ('consume',)])
        self.assertFalse(host.unread)

    def test_decode_failure_preserves_raw_unread_result(self):
        transaction = compiled(spi_transfer())
        raw = Result(0x100, 5, True, False)
        host = FakeHost(raw)
        loaded = transaction.load(host)
        host.calls.clear()
        with self.assertRaisesRegex(ValueError, 'outside its declared'):
            loaded.run(payload=0xa6)
        self.assertEqual(host.calls, [('start', 0xa6), ('page', 0), ('read', 99_997, False)])
        self.assertTrue(host.unread)
        self.assertIs(host.raw, raw)
        before = list(host.calls)
        with self.assertRaisesRegex(RuntimeError, 'Consume'):
            loaded.run(payload=0x53)
        self.assertEqual(host.calls, before)

    def test_busy_poll_and_result_read_share_one_remaining_timeout(self):
        transaction = compiled(uart_tx())
        host = FakeHost(busy_cycles=12)
        loaded = transaction.load(host)
        host.calls.clear()
        loaded.run(payload=0xa6, timeout_cycles=100)
        self.assertEqual(host.calls, [('start', 0xa6), ('page', 0), ('advance', 16),
                                     ('page', 0), ('read', 78, False), ('consume',)])

    def test_host_timeout_preserves_program_and_pending_retained_result(self):
        transaction = compiled(spi_transfer())
        raw = Result(wire_slots(0x96), 5, False, False)
        host = FakeHost(raw, busy_cycles=20)
        loaded = transaction.load(host)
        generation = host.program_generation
        host.calls.clear()
        with self.assertRaisesRegex(TimeoutError, 'engine state is unchanged'):
            loaded.run(payload=0xa6, timeout_cycles=10)
        self.assertEqual(host.committed_program, transaction.program)
        self.assertEqual(host.program_generation, generation)
        self.assertIs(host.raw, raw)
        self.assertFalse(host.unread)
        self.assertFalse(any(call[0] in ('read', 'consume', 'reset', 'upload') for call in host.calls))
        before = list(host.calls)
        with self.assertRaisesRegex(RuntimeError, 'idle engine'):
            loaded.run(payload=0x53)
        self.assertEqual(host.calls, before)
        host.advance(7)
        self.assertTrue(host.unread)
        before = list(host.calls)
        with self.assertRaisesRegex(RuntimeError, 'Consume'):
            loaded.run(payload=0x53)
        self.assertEqual(host.calls, before)
        self.assertIs(host.read_result(timeout_cycles=0, consume=False), raw)
        self.assertTrue(host.unread)

    def test_reset_or_replaced_image_stops_stale_session_before_io(self):
        uart, spi = compiled(uart_tx()), compiled(spi_transfer())
        for invalidation in ('reset', 'replace', 'unknown'):
            host = FakeHost()
            loaded = uart.load(host)
            if invalidation == 'reset':
                host.reset()
            elif invalidation == 'replace':
                spi.load(host)
            else:
                host.committed_program = None
            before = list(host.calls)
            with self.subTest(invalidation=invalidation), self.assertRaisesRegex(RuntimeError, 'lost its committed'):
                loaded.run(payload=0xa6)
            self.assertEqual(host.calls, before)

    def test_identical_reload_invalidates_old_session_and_new_session_runs(self):
        transaction = compiled(uart_tx())
        host = FakeHost()
        old = transaction.load(host)
        new = transaction.load(host)
        self.assertEqual(host.committed_program, transaction.program)
        before = list(host.calls)
        with self.assertRaisesRegex(RuntimeError, 'lost its committed'):
            old.run(payload=0xa6)
        self.assertEqual(host.calls, before)
        self.assertEqual(new.run(payload=0xa6).payload, ())

    def test_invalid_payload_fixed_nonzero_and_timeout_do_no_chip_io(self):
        for transaction, values in ((compiled(uart_tx()), (-1, 256, True, 1.0)),
                                   (compiled(spi_transfer([0xa6])), (1, 255)),
                                   (compiled(i2c_register_read(0x53, 0xa6)), (1, 255))):
            host = FakeHost()
            loaded = transaction.load(host)
            before = list(host.calls)
            for value in values:
                with self.subTest(protocol=transaction.protocol, payload=value), self.assertRaises(ValueError):
                    loaded.run(payload=value)
                self.assertEqual(host.calls, before)
            for timeout in (-1, True, 1.0):
                with self.assertRaises(ValueError):
                    loaded.run(timeout_cycles=timeout)
                self.assertEqual(host.calls, before)
        host = FakeHost(image_format=LEGACY_FORMAT)
        with self.assertRaises(CapabilityError):
            compiled(uart_tx()).load(host)
        self.assertEqual(host.calls, [])


class TrackerTransport:
    def __init__(self):
        self.live, self.result = 2, 0x10
        self.calls = []

    def advance(self, ui, cycles, *, rst_n=1):
        self.calls.append((ui, cycles, rst_n))
        return Pins((self.live, 0, 0, self.result)[(ui >> 3) & 3], 0, 0)


class HostCommittedProgramTests(unittest.TestCase):
    def test_only_successful_public_upload_establishes_image_identity(self):
        transport = TrackerTransport()
        host = Host(transport, image_format=PAIRED_FORMAT)
        program = compiled(uart_tx()).program
        self.assertIsNone(host.committed_program)
        host.upload(program)
        self.assertEqual(host.committed_program, program)
        generation = host.program_generation
        host.start(payload=0xa6)
        self.assertEqual(host.committed_program, program)
        self.assertEqual(host.program_generation, generation)

    def test_actual_host_identical_commit_invalidates_the_old_loaded_session(self):
        transport = TrackerTransport()
        host = Host(transport, image_format=PAIRED_FORMAT)
        transaction = compiled(uart_tx())
        old = transaction.load(host)
        new = transaction.load(host)
        self.assertEqual(host.committed_program, transaction.program)
        self.assertEqual(new.generation, old.generation + 1)
        before = list(transport.calls)
        with self.assertRaisesRegex(RuntimeError, 'lost its committed'):
            old.run(payload=0xa6)
        self.assertEqual(transport.calls, before)

    def test_reset_and_raw_commit_invalidate_before_transport(self):
        program = compiled(uart_tx()).program
        for invalidation in ('reset', 'low_reset', Command.RESET, Command.COMMIT):
            transport = TrackerTransport()
            host = Host(transport, image_format=PAIRED_FORMAT)
            host.upload(program)
            generation = host.program_generation
            observed = []
            advance = transport.advance

            def observe(ui, cycles, *, rst_n=1):
                observed.append((host.committed_program, host.program_generation))
                return advance(ui, cycles, rst_n=rst_n)

            transport.advance = observe
            if invalidation == 'reset':
                host.reset()
            elif invalidation == 'low_reset':
                host.advance(rst_n=0)
            else:
                host.command(invalidation)
            self.assertIsNone(host.committed_program)
            self.assertTrue(observed)
            self.assertTrue(all(image is None and epoch == generation + 1 for image, epoch in observed))

    def test_invalid_command_does_not_invalidate_known_image_or_touch_transport(self):
        transport = TrackerTransport()
        host = Host(transport, image_format=PAIRED_FORMAT)
        program = compiled(uart_tx()).program
        host.upload(program)
        before = list(transport.calls)
        generation = host.program_generation
        with self.assertRaises(ValueError):
            host.command(Command.COMMIT, -1)
        self.assertEqual(host.committed_program, program)
        self.assertEqual(host.program_generation, generation)
        self.assertEqual(transport.calls, before)

    def test_rejected_staging_preserves_old_identity_but_failed_commit_clears_it(self):
        for fail_at in (Command.PUSH, Command.COMMIT):
            transport = TrackerTransport()
            host = Host(transport, image_format=PAIRED_FORMAT)
            old = compiled(uart_tx()).program
            host.upload(old)
            generation = host.program_generation
            command = host.command
            commands = []

            def rejected(kind, data=0):
                commands.append(kind)
                command(kind, data)
                if kind == fail_at:
                    if fail_at == Command.PUSH:
                        transport.result |= 4
                    else:
                        transport.live = 0

            host.command = rejected
            with self.assertRaises(RuntimeError):
                host.upload(compiled(spi_transfer()).program)
            if fail_at == Command.PUSH:
                self.assertEqual(host.committed_program, old)
                self.assertEqual(host.program_generation, generation)
                self.assertIn(Command.ABORT, commands)
                self.assertNotIn(Command.COMMIT, commands)
            else:
                self.assertIsNone(host.committed_program)
                self.assertEqual(host.program_generation, generation + 1)

    def test_raw_commit_transport_failure_still_invalidates_old_ownership(self):
        transport = TrackerTransport()
        host = Host(transport, image_format=PAIRED_FORMAT)
        host.upload(compiled(uart_tx()).program)
        generation = host.program_generation
        transport.advance = Mock(side_effect=RuntimeError('transport interrupted'))
        with self.assertRaisesRegex(RuntimeError, 'transport interrupted'):
            host.command(Command.COMMIT)
        self.assertIsNone(host.committed_program)
        self.assertEqual(host.program_generation, generation + 1)


if __name__ == '__main__':
    unittest.main()
