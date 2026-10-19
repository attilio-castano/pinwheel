"""Ready host ownership controls and independent I2C slot packing checks."""
from dataclasses import replace
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from streaming_ready_transport import (LoadedReady, ReadyHost, pack_read, pack_write, project)
from streaming_ready_compile import Cell, Instruction, lower
from streaming_transport import (Code, Flags, Opcode, QuadTransport, Receipt,
    StreamProtocolError, StreamRejected, StreamTransportError, decode_request)
from test_streaming_transport import QuadFixture


TAG = 65537


def image(transmit=True, receive=True):
    return lower((Instruction('stream', Cell(transmit=transmit, receive=receive)), Instruction('halt')))


def loaded(host, transmit=True, receive=True):
    return LoadedReady(host, image(transmit, receive), host._epoch, 1)


def reply(request, *, flags=Flags.VALID | Flags.BUSY, **fields):
    return Receipt(request.sequence, Code.ACCEPTED, tag=TAG, tx_free=2, flags=int(flags), **fields)


def read_trace(plan, payload, *, address_ack=True):
    result = list(plan.tx_bits[:8]) + [not address_ack]
    for index, value in enumerate(payload):
        result.extend(bool((value >> bit) & 1) if address_ack else True for bit in range(7, -1, -1))
        result.append(index == plan.length - 1)
    return tuple(result)


class ReadyHostTests(unittest.TestCase):
    def test_new_image_validator_runs_before_any_io(self):
        backend = QuadFixture()
        host = ReadyHost(QuadTransport(backend), depth=2)
        calls = []
        def invalid(value):
            calls.append(value)
            raise ValueError('wrong Ready image')
        with patch.dict(sys.modules, streaming_ready_compile=SimpleNamespace(validate_image=invalid)):
            with self.assertRaisesRegex(ValueError, 'wrong Ready'): host.load(image())
        self.assertEqual(len(calls), 1)
        self.assertEqual(backend.cycle, 0)
        self.assertEqual(backend.frames, [])

    def test_ready_load_uses_fresh_handle_and_revalidates_each_attempt(self):
        backend = QuadFixture(lambda request: reply(request, flags=Flags.VALID))
        host = ReadyHost(QuadTransport(backend), depth=2)
        calls = []
        value = image(False, True)
        with patch.dict(sys.modules, streaming_ready_compile=SimpleNamespace(validate_image=lambda value: calls.append(value))):
            handle = host.load(value)
        self.assertIsInstance(handle, LoadedReady)
        self.assertEqual(calls, [value])
        self.assertEqual([decode_request(packet).opcode for packet in backend.frames],
            [Opcode.WRITE, Opcode.WRITE, Opcode.COMMIT])

    def test_tampered_loaded_image_is_refused_before_start(self):
        backend = QuadFixture()
        host = ReadyHost(QuadTransport(backend), depth=2)
        handle = loaded(host)
        object.__setattr__(handle.image, 'words', (0, 2))
        with self.assertRaises(ValueError): handle.submit((False,) * 8)
        self.assertEqual(backend.cycle, 0)

    def test_simplex_receive_count_is_independent_of_empty_tx(self):
        def respond(request):
            if request.opcode is Opcode.START: return reply(request)
            return reply(request, flags=Flags.VALID | Flags.RETAINED, data=0xa5, rx_valid=8)
        backend = QuadFixture(respond)
        host = ReadyHost(QuadTransport(backend), depth=2)
        pending = loaded(host, False, True).submit(bit_count=8)
        pending.wait(max_exchanges=3)
        self.assertEqual(pending.total_bits, 8)
        self.assertEqual(pending.tx_accepted, 0)
        self.assertEqual(pending.rx_bits, (True, False, True, False, False, True, False, True))
        self.assertEqual([decode_request(packet).opcode for packet in backend.frames], [Opcode.START, Opcode.EXCHANGE0])
        start = decode_request(backend.frames[0])
        self.assertEqual((start.payload >> 96) & 65535, 8)

    def test_simplex_modes_and_explicit_count_rejected_before_start(self):
        for transmit, receive, bits, count in ((False, True, (True,), 8), (True, False, (True,), 8),
                (False, True, (), None), (True, True, (True,), True), (True, True, (), 65536)):
            backend = QuadFixture()
            host = ReadyHost(QuadTransport(backend), depth=2)
            with self.subTest(transmit=transmit, receive=receive, count=count), self.assertRaises(ValueError):
                loaded(host, transmit, receive).submit(bits, bit_count=count)
            self.assertEqual(backend.frames, [])

    def test_transmit_only_completes_without_rx(self):
        def respond(request):
            if request.opcode is Opcode.START: return reply(request)
            return reply(request, flags=Flags.VALID | Flags.RETAINED, tx_accepted=8)
        host = ReadyHost(QuadTransport(QuadFixture(respond)), depth=2)
        pending = loaded(host, True, False).submit((True, False) * 4)
        pending.wait(max_exchanges=3)
        self.assertEqual(pending.tx_accepted, 8)
        self.assertEqual(pending.rx_bits, ())

    def test_rx_limit_tracks_receive_mode(self):
        def respond(request):
            if request.opcode is Opcode.START: return reply(request)
            return reply(request, flags=Flags.VALID | Flags.RETAINED, tx_accepted=8, rx_valid=1)
        host = ReadyHost(QuadTransport(QuadFixture(respond)), depth=2)
        pending = loaded(host, True, False).submit((False,) * 8)
        with self.assertRaises(StreamTransportError): pending.pump()
        self.assertIsNotNone(host.transport.inflight)

    def terminal_fixture(self, mutation=None):
        def respond(request):
            if request.opcode is Opcode.START: return reply(request)
            if request.opcode is Opcode.EXCHANGE64:
                result = Receipt(request.sequence, Code.REJECTED, tag=TAG, tx_free=2, rx_queued=1,
                    flags=int(Flags.VALID | Flags.RETAINED | Flags.FAULT | Flags.REJECTED))
                return mutation(result) if mutation else result
            if request.opcode is Opcode.EXCHANGE0:
                return reply(request, flags=Flags.VALID | Flags.RETAINED | Flags.FAULT,
                    data=0x15, rx_valid=5)
            raise AssertionError('unexpected opcode')
        backend = QuadFixture(respond)
        host = ReadyHost(QuadTransport(backend), depth=2)
        return backend, host, loaded(host).submit((False,) * 64)

    def test_stale_busy_terminal_rejection_gets_one_fresh_empty_exchange(self):
        backend, host, pending = self.terminal_fixture()
        pending.pump()
        self.assertEqual(pending.tx_accepted, 0)
        self.assertEqual(len(pending.rx_bits), 5)
        self.assertTrue(pending.last.fault)
        self.assertEqual(len(pending.terminal_retries), 1)
        self.assertEqual([decode_request(packet).opcode for packet in backend.frames],
            [Opcode.START, Opcode.EXCHANGE64, Opcode.EXCHANGE0])
        self.assertEqual(pending.terminal_retries[0]['empty_sequence'], 2)
        self.assertIsNone(host.transport.inflight)

    def test_terminal_rejection_recovery_keeps_exact_owner(self):
        backend, host, pending = self.terminal_fixture()
        backend.fail_at = backend.cycle + 90
        with self.assertRaises(StreamTransportError): pending.pump()
        pending.recover()
        self.assertTrue(pending.last.fault)
        self.assertEqual(pending.tx_accepted, 0)
        self.assertEqual(len(pending.terminal_retries), 1)
        self.assertIsNone(host.transport.inflight)

    def test_rejected_bulk_empty_diagnostic_does_not_discard_held_export(self):
        offers = []
        def respond(request):
            if request.opcode is Opcode.START: return reply(request)
            if request.opcode is Opcode.EXCHANGE64:
                offers.append(request)
                if len(offers) == 1:
                    return reply(request, tx_accepted=64, data=0x12345678, rx_start=0, rx_valid=32)
                return Receipt(request.sequence, Code.REJECTED, tag=TAG, tx_accepted=64,
                    rx_start=32, tx_free=2, rx_queued=1,
                    flags=int(Flags.VALID | Flags.RETAINED | Flags.FAULT | Flags.REJECTED))
            return reply(request, flags=Flags.VALID | Flags.RETAINED | Flags.FAULT,
                tx_accepted=64, rx_start=32, rx_valid=18, data=0x12345)
        backend = QuadFixture(respond)
        host = ReadyHost(QuadTransport(backend), depth=2)
        pending = loaded(host).submit((False,) * 128)
        pending.pump()
        before = pending.rx_bits
        pending.pump()
        self.assertEqual(pending.tx_accepted, 64)
        self.assertEqual(pending.rx_bits[:32], before)
        self.assertEqual(len(pending.rx_bits), 50)
        self.assertEqual(len(pending.terminal_retries), 1)
        last_request = decode_request(backend.frames[-1])
        self.assertEqual(last_request.opcode, Opcode.EXCHANGE0)
        self.assertEqual((last_request.payload >> 64) & 65535, 32)

    def test_stale_owner_unrelated_rejection_and_changed_custody_are_not_swallowed(self):
        mutations = [lambda receipt: replace(receipt, tag=TAG + 1),
            lambda receipt: replace(receipt, flags=int(Flags.VALID | Flags.BUSY | Flags.REJECTED)),
            lambda receipt: replace(receipt, data=1, rx_valid=1)]
        for mutation in mutations:
            backend, host, pending = self.terminal_fixture(mutation)
            with self.assertRaises(StreamRejected): pending.pump()
            self.assertEqual(len(backend.frames), 2)
            self.assertEqual(pending.tx_accepted, 0)
            self.assertEqual(pending.rx_bits, ())

    def test_success_reply_must_accept_exact_reservation(self):
        def respond(request):
            return reply(request) if request.opcode is Opcode.START else reply(request, tx_accepted=32)
        host = ReadyHost(QuadTransport(QuadFixture(respond)), depth=2)
        pending = loaded(host).submit((False,) * 64)
        with self.assertRaises(StreamTransportError): pending.pump()
        self.assertEqual(pending.tx_accepted, 0)


class I2cPackingTests(unittest.TestCase):
    def test_sixty_four_byte_write_has_585_slots_and_released_ack_slots(self):
        data = bytes(range(64))
        plan = pack_write(0x52, data)
        self.assertEqual(plan.bit_count, 585)
        self.assertEqual(plan.tx_bits[:8], tuple(bool(0xa4 & (1 << bit)) for bit in range(7, -1, -1)))
        self.assertTrue(all(plan.tx_bits[index] for index in range(8, 585, 9)))
        self.assertEqual(len(plan.tx_bits) % 32, 9)
        raw = tuple(False if index % 9 == 8 else value for index, value in enumerate(plan.tx_bits))
        result = project(plan, raw)
        self.assertTrue(result.payload_valid)
        self.assertEqual(result.data, data)
        self.assertEqual(result.acknowledgements, (True,) * 65)

    def test_read_releases_data_and_finishes_with_exact_master_nack(self):
        plan = pack_read(0x52, 64)
        self.assertTrue(all(plan.tx_bits[index] for index in range(9, 585) if (index - 9) % 9 < 8))
        self.assertEqual(tuple(plan.tx_bits[index] for index in range(17, 585, 9)), (False,) * 63 + (True,))
        data = bytes((73 * index + 0x5d) & 255 for index in range(64))
        result = project(plan, read_trace(plan, data))
        self.assertTrue(result.payload_valid)
        self.assertEqual(result.data, data)

    def test_address_nack_is_not_a_successful_ff_payload(self):
        plan = pack_read(0x52, 64)
        result = project(plan, read_trace(plan, bytes(64), address_ack=False))
        self.assertFalse(result.address_ack)
        self.assertFalse(result.payload_valid)
        self.assertEqual(result.data, b'')
        self.assertEqual(len(result.raw_bits), 585)
        self.assertTrue(result.complete)

    def test_timeout_preserves_50_bits_complete_bytes_and_partial_byte(self):
        plan = pack_read(0x52, 64)
        data = bytes(range(64))
        raw = read_trace(plan, data)[:50]
        result = project(plan, raw, fault=True)
        self.assertEqual(result.raw_bits, raw)
        self.assertEqual(result.data, data[:4])
        self.assertEqual(len(result.partial_data_bits), 5)
        self.assertFalse(result.payload_valid)
        self.assertFalse(result.complete)

    def test_wrong_echo_bit_order_and_master_ack_refused(self):
        plan = pack_read(0x52, 64)
        raw = list(read_trace(plan, bytes(range(64))))
        for index in (0, 7, 17, 584):
            bad = list(raw)
            bad[index] = not bad[index]
            with self.assertRaises(StreamProtocolError): project(plan, tuple(bad))

    def test_plan_and_projection_bounds_are_checked_before_io(self):
        for call in (lambda: pack_write(128, b'x'), lambda: pack_write(0x52, []),
                lambda: pack_read(0x52, 0), lambda: pack_read(0x52, True), lambda: pack_read(0x52, 7281)):
            with self.assertRaises(ValueError): call()
        with self.assertRaises(ValueError): project(pack_read(0x52, 1), (True,) * 19)
        with self.assertRaises(ValueError): project(pack_read(0x52, 1), (1,))


if __name__ == '__main__': unittest.main()
