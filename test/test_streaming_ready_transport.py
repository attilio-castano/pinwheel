"""Ready host ownership controls and independent I2C slot packing checks."""
from dataclasses import replace
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from streaming_ready_transport import (BranchingSwdRead, CheckedReadyImage, CombinedI2cRead, LoadedReady,
    ReadyHost, byte_bits, pack_read, pack_write, project)
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

    def test_pending_tx_recovery_keeps_the_original_offer_after_blocked_pump(self):
        def respond(request):
            if request.opcode is Opcode.START:
                return reply(request)
            self.assertEqual(request.opcode, Opcode.EXCHANGE64)
            return reply(request, tx_accepted=36)

        backend = QuadFixture(respond)
        host = ReadyHost(QuadTransport(backend), depth=2)
        pending = loaded(host).submit((False,) * 36)
        backend.fail_at = backend.cycle + 90
        with self.assertRaises(StreamTransportError):
            pending.pump()
        with self.assertRaises(StreamProtocolError):
            pending.pump(max_bits=0)
        self.assertEqual(pending.recover().tx_accepted, 36)
        self.assertEqual(pending.tx_accepted, 36)

    def test_scheduled_offer_uses_live_room_and_preserves_a_rejected_prefix(self):
        offers = []

        def respond(request):
            if request.opcode in (Opcode.START, Opcode.EXCHANGE0):
                return replace(reply(request), tx_free=0)
            self.assertEqual(request.opcode, Opcode.EXCHANGE64)
            offers.append(request)
            if len(offers) == 1:
                return Receipt(request.sequence, Code.REJECTED, tag=TAG,
                               flags=int(Flags.VALID | Flags.BUSY | Flags.REJECTED))
            return reply(request, tx_accepted=64)

        backend = QuadFixture(respond)
        host = ReadyHost(QuadTransport(backend), depth=2)
        pending = loaded(host, receive=False).submit((True, False) * 32)
        self.assertEqual(pending.pump().tx_free, 0)
        self.assertEqual(decode_request(backend.frames[-1]).opcode, Opcode.EXCHANGE0)
        with self.assertRaises(StreamRejected):
            pending.pump(scheduled_bits=64)
        self.assertEqual(pending.tx_accepted, 0)
        self.assertIsNone(host.transport.inflight)
        self.assertEqual(pending.pump(scheduled_bits=64).tx_accepted, 64)
        self.assertEqual(offers[0].payload, offers[1].payload)

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


class UnifiedCompletionTests(unittest.TestCase):
    @staticmethod
    def manifest():
        tx = [bit for value in (0xa6, 0xa6, 0xa7) for bit in (*byte_bits(value), True)] + [True] * 9
        return dict(schema='pinwheel.ready-register-read.v1', words=[77, 7], address=0x53, register=0xa6,
                    tx_bits=tx, tx_budget=36, wait_budget=31, idle_levels=0, idle_enabled=0,
                    exits=[dict(kind='complete' if size == 36 else 'discard', tx=size, rx=size)
                           for size in (36, 27, 18, 9)])

    @staticmethod
    def swd_manifest():
        return dict(schema='pinwheel.ready-swd-read.v1', words=[13, 2], tx_bits=[], tx_budget=0, start_count=0,
                    idle_levels=0, idle_enabled=1, exits=[dict(kind='complete', tx=0, rx=size) for size in (3, 36)])

    @staticmethod
    def checked_manifest(*, start_count=0, tx_bits=None, exits=None):
        return dict(schema='pinwheel.ready-image.v1', words=[13, 2], start_count=start_count,
                    tx_bits=[] if tx_bits is None else tx_bits, idle_levels=0, idle_enabled=0,
                    exits=[dict(kind='complete', tx=0, rx=3, core_clocks=None, external_polls=3)]
                    if exits is None else exits)

    def fixture(self, raw, *, accepted, fault=False):
        terminal = Flags.VALID | Flags.RETAINED | (Flags.FAULT if fault else 0)

        def respond(request):
            if request.opcode in (Opcode.WRITE, Opcode.COMMIT, Opcode.RELEASE):
                return reply(request, flags=Flags.VALID)
            if request.opcode is Opcode.START:
                return reply(request)
            ack = (request.payload >> 64) & 65535
            if request.opcode in (Opcode.EXCHANGE32, Opcode.EXCHANGE64) or (
                    request.opcode is Opcode.EXCHANGE0 and ack == 0 and raw):
                data = sum(bit << index for index, bit in enumerate(reversed(raw)))
                return reply(request, flags=terminal, tx_accepted=accepted, rx_valid=len(raw), data=data)
            if request.opcode is Opcode.EXCHANGE0:
                self.assertEqual(ack, len(raw))
                return reply(request, flags=terminal, tx_accepted=accepted, rx_start=len(raw))
            if request.opcode is Opcode.WARM_RESET:
                return reply(request, flags=Flags(0))
            raise AssertionError(request.opcode)

        link = QuadFixture(respond)
        return ReadyHost(QuadTransport(link), depth=2), link

    def test_spi_and_every_i2c_exit_use_the_same_runner(self):
        program = CombinedI2cRead.from_manifest(self.manifest())
        signed = (('write-address-nack', 9), ('register-nack', 18), ('read-address-nack', 27), ('read', 36))
        for name, consumed in signed:
            with self.subTest(name=name):
                raw = list(program.tx_bits[:consumed])
                for offset in (8, 17, 26):
                    if offset < consumed:
                        raw[offset] = offset + 1 == consumed
                if consumed == 36:
                    raw[27:35] = byte_bits(0x96)
                host, link = self.fixture(raw, accepted=36)
                pending = host.load(program).submit()
                result = pending.finish(max_exchanges=1)
                self.assertEqual(result.result.outcome, name)
                self.assertEqual(result.result.byte, 0x96 if consumed == 36 else None)
                self.assertEqual((result.tx_consumed, result.tx_cancelled), (consumed, 36 - consumed))
                self.assertEqual(result.rx_bits, tuple(raw))
                self.assertEqual((result.terminal.rx_start, result.terminal.rx_valid), (consumed, 0))
                self.assertEqual(result.release.tag, pending.tag)
                self.assertEqual([decode_request(packet).opcode for packet in link.frames][-4:],
                                 [Opcode.START, Opcode.EXCHANGE64, Opcode.EXCHANGE0, Opcode.RELEASE])

        host, link = self.fixture((True, False), accepted=2)
        spi = host.load(image()).submit((False, True))
        result = spi.finish(max_exchanges=1)
        self.assertEqual((result.result, result.tx_consumed, result.tx_cancelled), ((True, False), 2, 0))
        self.assertIs(result.release, host._last)
        self.assertIsNone(host._pending)

    def test_checked_receive_uses_manifest_count_and_returns_chronological_bits(self):
        manifest = self.checked_manifest()
        program = CheckedReadyImage.from_manifest(manifest)
        manifest['exits'][0]['rx'] = 9
        host, link = self.fixture((True, False, False), accepted=0)
        loaded = host.load(program)
        with self.assertRaisesRegex(ValueError, 'supplies its own TX plan and START count'):
            loaded.submit(bit_count=3)
        pending = loaded.submit()
        with self.assertRaisesRegex(TimeoutError, 'owner remains live'):
            pending.wait(max_exchanges=0)
        self.assertIs(host._pending, pending)
        finished = pending.finish(max_exchanges=1)
        self.assertEqual(finished.result, finished.rx_bits)
        self.assertEqual(finished.rx_bits, (True, False, False))
        self.assertEqual((finished.tx_consumed, finished.tx_cancelled), (0, 0))
        self.assertEqual(finished.release.tag, pending.tag)
        self.assertIsNone(host._pending)
        requests = [decode_request(packet) for packet in link.frames]
        self.assertEqual([request.opcode for request in requests],
                         [Opcode.WRITE, Opcode.WRITE, Opcode.COMMIT, Opcode.START,
                          Opcode.EXCHANGE0, Opcode.EXCHANGE0, Opcode.RELEASE])
        self.assertEqual((requests[3].payload >> 96) & 65535, 0)
        self.assertEqual((program.exits[0].core_clocks, program.exits[0].external_polls), (None, 3))

    def test_checked_manifest_accounts_for_discard_and_retains_a_fault_prefix(self):
        exits = [dict(kind=kind, tx=tx, rx=rx, core_clocks=20, external_polls=0)
                 for kind, tx, rx in [('complete', 4, 4), ('discard', 2, 2), ('fault', 3, 5)]]
        program = CheckedReadyImage.from_manifest(self.checked_manifest(start_count=4, tx_bits=[True] * 4, exits=exits))
        for raw, fault, consumed in (((False, True), False, 2), ((True, False, True, True, False), True, None)):
            with self.subTest(fault=fault):
                host, _ = self.fixture(raw, accepted=4, fault=fault)
                pending = host.load(program).submit()
                finished = pending.finish(max_exchanges=1)
                self.assertEqual(finished.rx_bits, raw)
                self.assertEqual(finished.terminal.rx_start, len(raw))
                self.assertEqual(finished.tx_consumed, consumed)
                if fault:
                    self.assertIsNone(finished.result)
                    self.assertIsNone(finished.release)
                    self.assertIsNone(finished.tx_cancelled)
                    self.assertIs(host._pending, pending)
                    pending.cancel()
                    self.assertIsNone(host._pending)
                else:
                    self.assertEqual(finished.result, raw)
                    self.assertEqual(finished.tx_cancelled, 2)
                    self.assertEqual(finished.release.tag, pending.tag)

    def test_checked_manifest_rejects_incoherent_metadata_and_ambiguous_accounting(self):
        manifest = self.checked_manifest()
        exit_ = manifest['exits'][0]
        candidates = (dict(manifest, words=[True]), dict(manifest, start_count=True),
                      dict(manifest, idle_enabled=8), dict(manifest, exits=[]),
                      dict(manifest, exits=[dict(exit_, core_clocks=7)]),
                      dict(manifest, exits=[dict(exit_, external_polls=0)]),
                      dict(manifest, exits=[dict(exit_, core_clocks=0, external_polls=0)]),
                      dict(manifest, exits=[dict(exit_, external_polls=True)]),
                      dict(manifest, exits=[dict(exit_, rx=65536)]))
        for candidate in candidates:
            with self.subTest(candidate=candidate), self.assertRaises(ValueError):
                CheckedReadyImage.from_manifest(candidate)
        with self.assertRaisesRegex(ValueError, 'TX payload length must equal its START budget'):
            CheckedReadyImage.from_manifest(dict(manifest, start_count=1))
        program = CheckedReadyImage.from_manifest(self.checked_manifest(start_count=2, tx_bits=[True, False],
            exits=[dict(exit_, tx=2), dict(exit_, kind='discard', tx=1, rx=2)]))
        inconsistent = replace(program, exits=(program.exits[0], replace(program.exits[1], rx=3)))
        host, link = self.fixture((), accepted=0)
        with self.assertRaisesRegex(ValueError, 'same RX length disagree on TX consumed'):
            host.load(inconsistent)
        self.assertEqual(link.cycle, 0)

    def test_swd_ack_selects_terminal_length_and_decoded_status(self):
        program = BranchingSwdRead.from_manifest(self.swd_manifest())
        word = 0x915DC37B
        data = tuple(bool(word >> bit & 1) for bit in range(32))
        parity = bool(word.bit_count() % 2)
        ok = (True, False, False)
        cases = (
            ('ok', ok + data + (parity,), word),
            ('bad-parity', ok + data + (not parity,), None),
            ('wait', (False, True, False), None),
            ('fault', (False, False, True), None),
            ('invalid-ack', (True, True, False), None),
        )
        for name, raw, expected in cases:
            with self.subTest(outcome=name):
                host, link = self.fixture(raw, accepted=0)
                pending = host.load(program).submit()
                result = pending.finish(max_exchanges=1)
                self.assertEqual((result.result.outcome, result.result.word), (name, expected))
                self.assertEqual((result.tx_consumed, result.tx_cancelled), (0, 0))
                self.assertEqual(result.rx_bits, raw)
                self.assertFalse(result.terminal.fault)
                self.assertEqual((result.terminal.rx_start, result.terminal.rx_valid), (len(raw), 0))
                self.assertEqual(result.release.tag, pending.tag)
                requests = [decode_request(packet) for packet in link.frames][-4:]
                self.assertEqual([request.opcode for request in requests],
                                 [Opcode.START, Opcode.EXCHANGE0, Opcode.EXCHANGE0, Opcode.RELEASE])
                self.assertEqual((requests[0].payload >> 96) & 65535, 0)

    def test_swd_wrong_ack_length_retains_owner_and_engine_fault_needs_cancel(self):
        program = BranchingSwdRead.from_manifest(self.swd_manifest())
        for raw in ((True, False, False), (False, True, False) + (False,) * 33):
            with self.subTest(length=len(raw)):
                host, _ = self.fixture(raw, accepted=0)
                pending = host.load(program).submit()
                with self.assertRaises(StreamProtocolError):
                    pending.finish(max_exchanges=1)
                self.assertEqual(host.transport.opcode_counts[Opcode.RELEASE], 0)
                self.assertIs(host._pending, pending)

        host, _ = self.fixture((True,), accepted=0, fault=True)
        pending = host.load(program).submit()
        result = pending.finish(max_exchanges=1)
        self.assertEqual((result.result.outcome, result.rx_bits), ('deadline', (True,)))
        self.assertTrue(result.terminal.fault)
        self.assertIsNone(result.release)
        self.assertIsNone(result.tx_consumed)
        self.assertIs(host._pending, pending)
        pending.cancel()
        self.assertIsNone(host._pending)

    def test_timeout_is_acknowledged_but_cancellation_is_explicit_and_recoverable(self):
        program = CombinedI2cRead.from_manifest(self.manifest())
        raw = program.tx_bits[:8] + (False,) + program.tx_bits[9:13]
        host, link = self.fixture(raw, accepted=36, fault=True)
        loaded_program = host.load(program)
        pending = loaded_program.submit()
        with self.assertRaises(StreamProtocolError):
            pending.cancel()
        result = pending.finish(max_exchanges=1)
        self.assertIsNone(result.release)
        self.assertIsNone(result.tx_consumed)
        self.assertIsNone(result.tx_cancelled)
        self.assertEqual(result.result.outcome, 'deadline')
        self.assertEqual(result.rx_bits, raw)
        self.assertEqual((result.terminal.rx_start, result.terminal.rx_valid), (13, 0))
        self.assertIs(host._pending, pending)
        self.assertEqual([decode_request(packet).opcode for packet in link.frames][-3:],
                         [Opcode.START, Opcode.EXCHANGE64, Opcode.EXCHANGE0])

        link.fail_at = link.cycle + 90
        with self.assertRaises(StreamTransportError):
            pending.cancel()
        self.assertIs(host._pending, pending)
        self.assertEqual(pending.recover().tag, pending.tag)
        self.assertEqual(host.transport.opcode_counts[Opcode.WARM_RESET], 1)
        self.assertIsNone(host._pending)
        with self.assertRaises(StreamProtocolError):
            loaded_program.submit()

    def test_early_rejection_preserves_the_prior_accepted_tx_and_drains_one_prefix(self):
        program = CombinedI2cRead.from_manifest(self.manifest())
        terminal = Flags.VALID | Flags.RETAINED
        captured = sum(bit << index for index, bit in enumerate(reversed(program.tx_bits[:9])))

        def respond(request):
            if request.opcode in (Opcode.WRITE, Opcode.COMMIT, Opcode.RELEASE):
                return reply(request, flags=Flags.VALID)
            if request.opcode is Opcode.START:
                return reply(request)
            if request.opcode is Opcode.EXCHANGE32:
                if (request.payload >> 80) & 65535 == 0:
                    return reply(request, tx_accepted=32)
                return Receipt(request.sequence, Code.REJECTED, tag=TAG, tx_accepted=32,
                               flags=int(terminal | Flags.REJECTED), tx_free=2, rx_queued=1)
            if request.opcode is Opcode.EXCHANGE0:
                if (request.payload >> 64) & 65535 == 0:
                    return reply(request, flags=terminal, tx_accepted=32, data=captured, rx_valid=9)
                return reply(request, flags=terminal, tx_accepted=32, rx_start=9)
            raise AssertionError(request.opcode)

        host = ReadyHost(QuadTransport(QuadFixture(respond)), depth=2)
        pending = host.load(program).submit()
        pending.pump(max_bits=32)
        result = pending.finish(max_exchanges=1)
        self.assertEqual(len(pending.terminal_retries), 1)
        self.assertEqual(result.terminal.tx_accepted, 32)
        self.assertEqual(result.result.outcome, 'write-address-nack')
        self.assertEqual((result.tx_consumed, result.tx_cancelled), (9, 23))

    def test_invalid_manifest_and_invalid_exit_never_release_owner(self):
        source = self.manifest()
        with self.assertRaises(ValueError):
            CombinedI2cRead.from_manifest(dict(source, exits=source['exits'][:-1]))
        with self.assertRaises(ValueError):
            CombinedI2cRead.from_manifest(dict(source, tx_bits=[False] * 36))
        program = CombinedI2cRead.from_manifest(source)
        bad = replace(program, words=(1 << 64,))
        host, link = self.fixture(program.tx_bits[:8] + (False,), accepted=36)
        with self.assertRaises(ValueError):
            host.load(bad)
        self.assertEqual(link.cycle, 0)
        pending = host.load(program).submit()
        with self.assertRaisesRegex(StreamProtocolError, 'invalid RX prefix'):
            pending.finish(max_exchanges=1)
        self.assertEqual(host.transport.opcode_counts[Opcode.RELEASE], 0)
        self.assertIs(host._pending, pending)


if __name__ == '__main__': unittest.main()
