"""Serial codec, held receipts and host ownership through a pin-only fixture.

This independent endpoint fixture injects public command receipts/completions;
it does not execute instructions, model SRAM or establish RTL correspondence.
The complete emitted package gate owns those checks.
"""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'test'))

from buffered_hardware import BufferedHardwareTransportError, BufferedHardwareWaitTimeout
from buffered_reactive_hardware import compact_spi
from buffered_sram_hardware import lower_sram
from buffered_sram_serial import (REQUEST_BITS, RESPONSE_BITS, STATUS_BITS,
    BufferedSramSerialHost, BufferedSramSerialTransport, SerialProtocolError,
    decode_request, decode_response, encode_request, encode_response)
from pinwheel_buffers import TransferError
from test_buffered_shared_branches import SharedBranchesPortFixture


class SerialPortFixture(SharedBranchesPortFixture):
    @staticmethod
    def fresh():
        return dict(SharedBranchesPortFixture.fresh(), stage1=0, stage2=0)

class SerialEndpointFixture:
    """Only tick pins are visible to the transport; packing is independently read."""
    def __init__(self):
        self.port = SerialPortFixture()
        self.cycle = 0
        self.delivered = []
        self.drop_after_start = False
        self.drop_during_response = None
        self.drop_response_close = False
        self.mutate_response = None
        self.silent = False
        self._clear()

    def _clear(self):
        self.selected = self.high = self.reading = False
        self.count = self.shift = 0
        self.response = None
        self.delay = 0

    def cold_reset(self):
        self.tick(csn=1, sck=0, mosi=0, initialize=1)
        self.tick(csn=1, sck=0, mosi=0)

    def _reply(self, sequence, code, status):
        # Exact wire-order list is deliberately independent of the codec table.
        names = ('valid', 'busy', 'retained', 'pending', 'rejected', 'mode', 'pc',
            'remaining', 'levels', 'enabled', 'tx_consumed', 'rx_length', 'rx_data',
            'read_valid', 'read_bit', 'generation', 'transfer', 'exhausted',
            'stage1', 'stage2', 'virtual_pc', 'env0', 'env1', 'phase', 'wait_left', 'scratch')
        widths = (1, 1, 1, 1, 1, 2, 8, 8, 3, 3, 6, 6, 32, 1, 1, 16, 16, 1, 2, 2, 10, 3, 3, 3, 8, 16)
        packed, offset = 0, 0
        for name, width in zip(names, widths, strict=True):
            packed |= status[name] << offset
            offset += width
        self.response = ((0x5A10 | code) << 176) | (sequence << 160) | packed
        if self.mutate_response:
            self.response = self.mutate_response(self.response)
        self.delay = 2

    def _dispatch(self):
        packet = self.shift
        sequence = (packet >> 128) & 65535
        header, payload = packet >> 144, packet & ((1 << 128) - 1)
        status, code = dict(self.port.state), 0
        if self.count != 160:
            code = 1
        elif header & 0xFFF0 != 0xA710:
            code = 2
        else:
            op = header & 15
            # Independent payload decoding, without production codec calls.
            if op == 0:
                used, fields = 5, dict(command=0, read_index=payload & 31)
            elif op == 1:
                used, fields = 98, dict(command=1, word=payload & ((1 << 64) - 1),
                    control=(payload >> 64) & 0xFFFFFF, branch=(payload >> 88) & 15,
                    address=(payload >> 92) & 63)
            elif op == 2:
                used, fields = 24, dict(command=2, count=payload & 127,
                    virtual_span=(payload >> 7) & 2047, idle_levels=(payload >> 18) & 7,
                    idle_enabled=(payload >> 21) & 7)
            elif op == 3:
                used, fields = 60, dict(command=3, tx_data=payload & 0xFFFFFFFF,
                    tx_length=(payload >> 32) & 63, rx_capacity=(payload >> 38) & 63,
                    expected_generation=(payload >> 44) & 65535)
            elif op == 4:
                used, fields = 32, dict(command=4, expected_generation=payload & 65535,
                    expected_transfer=(payload >> 16) & 65535)
            elif op == 6:
                used, fields = 60, dict(command=6, branch=payload & ((1 << 56) - 1),
                    address=(payload >> 56) & 15)
            elif op in (7, 8):
                used, fields = 0, dict(command=7) if op == 7 else dict(initialize=1)
            else:
                used, fields, code = 0, {}, 3
            if payload >> used:
                code = 3
            if not code:
                self.delivered.append(fields)
                status = self.port.edge(**fields)
                code = 4 if status['rejected'] else 0
                if op == 3 and not code and self.drop_after_start:
                    self.drop_after_start = False
                    self._reply(sequence, code, status)
                    raise OSError('Dropped START receipt after actual delivery')
        self._reply(sequence, code, status)

    def tick(self, *, csn, sck, mosi, initialize=0):
        self.cycle += 1
        miso = ((self.response >> (191 - min(self.count, 191))) & 1
                if self.response is not None and self.delay == 0 and self.reading else 0)
        if initialize:
            self._clear()
            self.port.edge(initialize=1)
            return dict(miso=0, ready=0)
        if self.delay:
            self.delay -= 1
        if not csn and not self.selected:
            self.selected, self.reading = True, self.response is not None and self.delay == 0
            self.count = self.shift = 0
        if self.selected and not csn and sck and not self.high:
            if not self.reading:
                self.shift = (self.shift << 1) | mosi
            self.count += 1
            if self.reading and self.count == self.drop_during_response:
                self.drop_during_response = None
                self.high = bool(sck)
                raise OSError('Dropped transport while reading held response')
        if csn and self.selected:
            self.selected = False
            if self.reading:
                if self.count == 192:
                    self.response = None
                    if self.drop_response_close:
                        self.drop_response_close = False
                        self.count = self.shift = 0
                        self.high = bool(sck)
                        raise OSError('Exact response consumed, close acknowledgement dropped')
            else:
                self._dispatch()
            self.count = self.shift = 0
        self.high = bool(sck)
        return dict(miso=miso, ready=int(self.response is not None and self.delay == 0 and not self.silent))


def raw_send(endpoint, packet, length=160):
    for bit in range(length - 1, -1, -1):
        endpoint.tick(csn=0, sck=0, mosi=(packet >> bit) & 1)
        endpoint.tick(csn=0, sck=1, mosi=(packet >> bit) & 1)
    endpoint.tick(csn=1, sck=0, mosi=0)
    endpoint.tick(csn=1, sck=0, mosi=0)
    endpoint.tick(csn=1, sck=0, mosi=0)


def raw_read(endpoint, length=192):
    packet = 0
    for _ in range(length):
        endpoint.tick(csn=0, sck=0, mosi=0)
        packet = (packet << 1) | endpoint.tick(csn=0, sck=1, mosi=0)['miso']
    closed = endpoint.tick(csn=1, sck=0, mosi=0)
    return packet, closed['ready']


class SerialCodecTests(unittest.TestCase):
    def test_request_golden_fields_and_full_header(self):
        packet = encode_request(0x369C, command=1, word=0xFEDCBA9876543210,
            control=0xA13579, branch=13, address=61)
        self.assertEqual(packet, (0xA711 << 144) | (0x369C << 128) |
            (61 << 92) | (13 << 88) | (0xA13579 << 64) | 0xFEDCBA9876543210)
        sequence, fields = decode_request(packet)
        self.assertEqual((sequence, fields['address'], fields['word']), (0x369C, 61, 0xFEDCBA9876543210))
        for op, fields in ((0, {'read_index': 31}), (2, dict(count=64, virtual_span=1024,
                idle_levels=7, idle_enabled=5)), (3, dict(tx_data=0x96, tx_length=32,
                rx_capacity=32, expected_generation=65535)), (4, dict(expected_generation=123,
                expected_transfer=456)), (6, dict(branch=(1 << 56) - 1, address=15)), (7, {})):
            value = encode_request(65535, command=op, **fields)
            self.assertEqual(decode_request(value), (65535, dict(command=op, initialize=0, **fields)))
        self.assertEqual(decode_request(encode_request(0, initialize=1)),
                         (0, dict(command=0, initialize=1)))

    def test_request_bounds_schema_bool_and_reserved_rejection(self):
        invalid = [dict(command=True), dict(initialize=True), dict(command=5),
            dict(command=7, word=0), dict(command=1, branch=16), dict(command=6, address=16),
            dict(command=2, count=0, virtual_span=1), dict(command=2, count=65, virtual_span=1),
            dict(command=2, count=1, virtual_span=1025), dict(command=3, tx_length=33),
            dict(command=0, read_index=True), dict(command=1, word=1 << 64),
            dict(initialize=1, command=7)]
        for fields in invalid:
            with self.subTest(fields=fields), self.assertRaises(ValueError):
                encode_request(0, **fields)
        for packet in (True, -1, 1 << 160, (0xA610 << 144),
                (0xA715 << 144), (0xA717 << 144) | 1, (0xA711 << 144) | (1 << 98)):
            with self.subTest(packet=packet), self.assertRaises(ValueError): decode_request(packet)

    def test_response_offsets_reservation_and_identity_validation(self):
        endpoint = SerialEndpointFixture()
        status = dict(endpoint.port.state, generation=0xA596, transfer=0x1369, scratch=0xC753)
        packet = encode_response(0x68AC, 0, status)
        self.assertEqual((REQUEST_BITS, RESPONSE_BITS, STATUS_BITS), (160, 192, 155))
        self.assertEqual((packet >> 176, (packet >> 160) & 65535), (0x5A10, 0x68AC))
        self.assertEqual((packet >> 75) & 65535, status['generation'])
        self.assertEqual((packet >> 91) & 65535, status['transfer'])
        self.assertEqual((packet >> 139) & 65535, status['scratch'])
        self.assertEqual(decode_response(packet, expected_sequence=0x68AC)[2], status)
        for mutated in (packet ^ (1 << 180), packet | (1 << 155), packet | (1 << 4)):
            with self.assertRaises(SerialProtocolError): decode_response(mutated)
        with self.assertRaises(SerialProtocolError): decode_response(packet, expected_sequence=0)
        with self.assertRaises(ValueError): encode_response(True, 0, status)


class SerialTransportTests(unittest.TestCase):
    def setUp(self):
        self.endpoint = SerialEndpointFixture()
        self.transport = BufferedSramSerialTransport(self.endpoint)
        self.host = BufferedSramSerialHost(self.transport)
        self.host.initialize()

    def test_all_commands_public_fields_and_physical_costs(self):
        loaded = self.host.load(compact_spi(1))
        image = loaded.image
        writes = [fields for fields in self.endpoint.delivered if fields.get('command') in (1, 6)]
        self.assertEqual(writes[:16], [dict(command=6, branch=b, address=k)
            for k, b in enumerate(image.branch_table)])
        self.assertEqual(writes[16:], [dict(command=1, word=w, control=c, branch=b, address=k)
            for k, (w, c, b) in enumerate(zip(image.words, image.controls, image.branch_indices, strict=True))])
        self.assertEqual(self.transport.requests, self.transport.responses)
        self.assertEqual(self.transport.physical_edges, self.endpoint.cycle)
        self.assertGreater(self.transport.physical_edges, self.transport.requests * 704)

    def test_invalid_command_and_image_reject_before_io(self):
        before = self.endpoint.cycle
        with self.assertRaises(ValueError): self.transport.edge(command=3, rx_capacity=33)
        image = lower_sram(compact_spi(1)); object.__setattr__(image, 'words', (True,) + image.words[1:])
        with self.assertRaises(ValueError): self.host.load(image)
        self.assertEqual(self.endpoint.cycle, before)

    def test_retained_read_release_timeout_and_stale_handle(self):
        loaded = self.host.load(compact_spi(1))
        pending = loaded.submit(tx=b'\x96')
        with self.assertRaises(BufferedHardwareWaitTimeout) as error: pending.wait(timeout_polls=0)
        self.assertIs(error.exception.pending, pending)
        self.endpoint.port.finish((True, False), 3, outcome='fault', scratch=0x8001)
        pending.wait(timeout_polls=1)
        first = pending.read()
        self.assertEqual(first, pending.read())
        self.assertEqual((first.raw_rx_bits, first.scratch, first.outcome), ((True, False), 0x8001, 'fault'))
        with self.assertRaises(TransferError): self.host.load(compact_spi(1))
        pending.release()
        with self.assertRaises(TransferError): pending.read()
        next_pending = loaded.submit(tx=b'\x96')
        self.assertEqual(next_pending.identity.transfer, pending.identity.transfer + 1)
        self.host.reset()
        with self.assertRaises(TransferError): next_pending.read()
        with self.assertRaises(TransferError): loaded.submit(tx=b'\x96')

    def test_full_rx_word_read_uses_one_atomic_request(self):
        loaded = self.host.load(compact_spi(4))
        pending = loaded.submit(tx=b'\x96\xa5\x3c\xc3')
        expected = b'\xa6\x9b\x42\xe1'
        bits = tuple(bool((byte >> bit) & 1) for byte in expected for bit in range(7, -1, -1))
        self.endpoint.port.finish(bits, 32, scratch=0x5AA5)
        for _ in range(2):
            requests, deliveries = self.transport.requests, len(self.endpoint.delivered)
            result = pending.read()
            self.assertEqual((result.payload, result.raw_rx_bits, result.rx_valid_bits,
                result.tx_consumed_bits, result.scratch), (expected, bits, 32, 32, 0x5AA5))
            self.assertEqual(self.transport.requests, requests + 1)
            self.assertEqual(len(self.endpoint.delivered), deliveries + 1)
            self.assertEqual(self.endpoint.delivered[-1], dict(command=0, read_index=0))
        pending.release()

    def test_empty_and_fault_prefix_atomic_reads_preserve_diagnostics(self):
        loaded = self.host.load(compact_spi(1))
        pending = loaded.submit(tx=b'\x96')
        self.endpoint.port.finish((), 0, outcome='timeout', scratch=0x8000)
        requests = self.transport.requests
        empty = pending.read()
        self.assertEqual((empty.outcome, empty.payload, empty.raw_rx_bits, empty.scratch),
                         ('timeout', None, (), 0x8000))
        self.assertEqual(self.transport.requests, requests + 1)
        pending.release()
        pending = loaded.submit(tx=b'\xA5')
        self.endpoint.port.finish((True, False, True), 2, outcome='fault', scratch=3)
        # Prefix ownership makes no new claim about unused high RX bits.
        self.endpoint.port.state['rx_data'] |= 1 << 31
        requests = self.transport.requests
        prefix = pending.read()
        self.assertEqual((prefix.outcome, prefix.payload, prefix.raw_rx_bits,
            prefix.tx_consumed_bits, prefix.scratch), ('fault', None, (True, False, True), 2, 3))
        self.assertEqual(self.transport.requests, requests + 1)

    def test_atomic_read_rejects_wrong_identity_and_result_bounds(self):
        loaded = self.host.load(compact_spi(1))
        pending = loaded.submit(tx=b'\x96')
        self.endpoint.port.finish((True, False), 2, outcome='fault')
        original = dict(self.endpoint.port.state)
        for field in ('generation', 'transfer'):
            self.endpoint.port.state = dict(original, **{field: original[field] + 1})
            with self.subTest(field=field), self.assertRaises(TransferError): pending.read()
        self.endpoint.port.state = dict(original, rx_length=9)
        with self.assertRaises(BufferedHardwareTransportError) as error: pending.read()
        self.assertIsInstance(error.exception.cause, RuntimeError)
        self.endpoint.port.state = original

    def test_atomic_read_rejects_invalid_window_and_inconsistent_first_bit(self):
        loaded = self.host.load(compact_spi(1))
        pending = loaded.submit(tx=b'\x96')
        self.endpoint.port.finish((True, False), 2, outcome='fault')
        # Mutate only the received public fields; status remains width-correct.
        for bit in (73, 74):
            self.endpoint.mutate_response = lambda packet, bit=bit: packet ^ (1 << bit)
            with self.subTest(bit=bit), self.assertRaises(RuntimeError): pending.read()
        self.endpoint.mutate_response = None
        self.endpoint.port.finish((), 0, outcome='fault')
        self.endpoint.mutate_response = lambda packet: packet | (1 << 73)
        with self.assertRaises(RuntimeError): pending.read()
        self.endpoint.mutate_response = None
        self.endpoint.port.finish((True, False), 2, outcome='complete')
        with self.assertRaises(ValueError): pending.read()

    def test_uncertain_start_recovers_receipt_without_repeating_start(self):
        loaded = self.host.load(compact_spi(1))
        self.endpoint.drop_after_start = True
        with self.assertRaises(BufferedHardwareTransportError) as error: loaded.submit(tx=b'\xA5')
        pending = error.exception.pending
        self.assertIs(self.host._pending, pending)
        with self.assertRaises(SerialProtocolError): self.transport.edge(command=0)
        recovered = pending.recover()
        self.assertEqual(recovered['transfer'], pending.identity.transfer)
        self.assertEqual(sum(v.get('command') == 3 for v in self.endpoint.delivered), 1)
        self.assertEqual(self.transport.physical_edges, self.endpoint.cycle)
        self.endpoint.port.finish((), 0, outcome='fault')
        pending.wait(timeout_polls=1)
        pending.release()

    def test_wrong_receipt_readiness_timeout_and_constructor_validation(self):
        self.endpoint.mutate_response = lambda packet: packet ^ (1 << 160)
        with self.assertRaises(SerialProtocolError): self.transport.edge(command=0)
        self.assertIsNotNone(self.transport._inflight)
        self.endpoint.mutate_response = None
        self.host.initialize()
        self.endpoint.silent = True
        with self.assertRaises(TimeoutError): self.transport.edge(command=0)
        self.endpoint.silent = False
        self.transport.recover_response()
        with self.assertRaises(ValueError): BufferedSramSerialTransport(self.endpoint, phase_cycles=True)
        with self.assertRaises(ValueError): BufferedSramSerialTransport(self.endpoint, ready_timeout_edges=0)

    def test_partial_response_failure_restarts_read_without_reissuing_command(self):
        before = len(self.endpoint.delivered)
        self.endpoint.drop_during_response = 87
        with self.assertRaises(OSError): self.transport.edge(command=0, read_index=3)
        held = self.endpoint.response
        status = self.transport.recover_response()
        self.assertEqual(status['generation'], 0)
        self.assertEqual(len(self.endpoint.delivered), before + 1)
        self.assertIsNotNone(held)
        self.assertIsNone(self.endpoint.response)
        self.assertEqual(self.transport.physical_edges, self.endpoint.cycle)

    def test_consumed_response_close_failure_recovers_validated_cache(self):
        loaded = self.host.load(compact_spi(1))
        # Submit first polls STATUS, so inject the failure only on START's receipt.
        original = self.endpoint._reply
        def drop_start_close(sequence, code, status):
            original(sequence, code, status)
            if status['transfer'] == 1:
                self.endpoint.drop_response_close = True
        self.endpoint._reply = drop_start_close
        with self.assertRaises(BufferedHardwareTransportError) as error: loaded.submit(tx=b'\xA5')
        pending = error.exception.pending
        self.assertIsNone(self.endpoint.response)
        requests = self.transport.requests
        recovered = pending.recover()
        self.assertEqual(recovered['transfer'], 1)
        self.assertEqual(self.transport.requests, requests)
        self.assertEqual(sum(v.get('command') == 3 for v in self.endpoint.delivered), 1)

    def test_lost_release_receipt_frees_local_owner_without_reset_or_retry(self):
        for failure in ('capture', 'close'):
            with self.subTest(failure=failure):
                endpoint = SerialEndpointFixture()
                transport = BufferedSramSerialTransport(endpoint)
                host = BufferedSramSerialHost(transport)
                host.initialize()
                loaded = host.load(compact_spi(1))
                pending = loaded.submit(tx=b'\x96')
                endpoint.port.finish((), 0, outcome='fault')
                original = endpoint._reply
                armed = [True]
                def lose_release(sequence, code, status):
                    original(sequence, code, status)
                    if armed[0] and endpoint.delivered[-1].get('command') == 4:
                        armed[0] = False
                        if failure == 'capture':
                            raise OSError('RELEASE delivered, receipt publication acknowledgement lost')
                        endpoint.drop_response_close = True
                endpoint._reply = lose_release
                with self.assertRaises(BufferedHardwareTransportError) as error: pending.release()
                self.assertIs(error.exception.pending, pending)
                self.assertIs(host._pending, pending)
                requests = transport.requests
                recovered = pending.recover()
                self.assertEqual((recovered['busy'], recovered['retained'], recovered['valid']), (0, 0, 1))
                self.assertIsNone(host._pending)
                self.assertIsNone(host._release_attempt)
                self.assertEqual(transport.requests, requests)
                self.assertEqual(sum(v.get('command') == 4 for v in endpoint.delivered), 1)
                with self.assertRaises(TransferError): pending.read()
                restarted = loaded.submit(tx=b'\xA5')
                self.assertEqual(restarted.identity.transfer, pending.identity.transfer + 1)
                self.assertEqual(restarted.identity.generation, pending.identity.generation)

    def test_run_release_transport_error_keeps_already_read_result(self):
        for failure in ('capture', 'close'):
            with self.subTest(failure=failure):
                endpoint = SerialEndpointFixture()
                host = BufferedSramSerialHost(BufferedSramSerialTransport(endpoint))
                host.initialize()
                loaded = host.load(compact_spi(1))
                bits = tuple(bool((0xA6 >> bit) & 1) for bit in range(7, -1, -1))
                endpoint.port.complete_after = 1
                endpoint.port.completion = (bits, 8, False)
                original = endpoint._reply
                armed = [True]
                def lose_release(sequence, code, status):
                    original(sequence, code, status)
                    if armed[0] and endpoint.delivered[-1].get('command') == 4:
                        armed[0] = False
                        if failure == 'capture':
                            raise OSError('Run RELEASE delivered; receipt acknowledgement lost')
                        endpoint.drop_response_close = True
                endpoint._reply = lose_release
                with self.assertRaises(BufferedHardwareTransportError) as raised:
                    loaded.run(tx=b'\x96', timeout_polls=1)
                error = raised.exception
                result, pending = error.result, error.pending
                self.assertEqual((result.payload, result.raw_rx_bits, result.outcome),
                                 (b'\xA6', bits, 'complete'))
                self.assertEqual(result.identity, pending.identity)
                self.assertIsInstance(error.cause, OSError)
                self.assertIs(host._pending, pending)
                self.assertFalse(pending.recover()['retained'])
                self.assertIsNone(host._pending)
                self.assertEqual(sum(v.get('command') == 4 for v in endpoint.delivered), 1)
                restarted = loaded.submit(tx=b'\x3C')
                self.assertEqual(restarted.identity.transfer, result.identity.transfer + 1)
                # Recovery/new START cannot mutate the caller's immutable copy.
                self.assertEqual((error.result.payload, error.result.raw_rx_bits), (b'\xA6', bits))

    def test_rejected_release_recovery_keeps_owner_for_explicit_retry(self):
        loaded = self.host.load(compact_spi(1))
        pending = loaded.submit(tx=b'\x96')
        self.endpoint.port.finish((), 0, outcome='fault')
        self.endpoint.port.reject_command = 4
        original = self.endpoint._reply
        armed = [True]
        def lose_release(sequence, code, status):
            original(sequence, code, status)
            if armed[0] and self.endpoint.delivered[-1].get('command') == 4:
                armed[0] = False
                self.endpoint.drop_response_close = True
        self.endpoint._reply = lose_release
        with self.assertRaises(BufferedHardwareTransportError): pending.release()
        recovered = pending.recover()
        self.assertEqual((recovered['retained'], recovered['rejected']), (1, 1))
        self.assertIs(self.host._pending, pending)
        self.assertIsNone(self.host._release_attempt)
        with self.assertRaises(TransferError): loaded.submit(tx=b'\x96')
        self.endpoint.port.reject_command = None
        pending.release()
        self.assertIsNone(self.host._pending)

    def test_release_recovery_requires_matching_identity_and_valid_free_image(self):
        for corrupt in ('identity', 'invalid_image'):
            with self.subTest(corrupt=corrupt):
                endpoint = SerialEndpointFixture()
                host = BufferedSramSerialHost(BufferedSramSerialTransport(endpoint))
                host.initialize()
                loaded = host.load(compact_spi(1))
                pending = loaded.submit(tx=b'\x96')
                endpoint.port.finish((), 0, outcome='fault')
                original = endpoint._reply
                def lose_release(sequence, code, status):
                    original(sequence, code, status)
                    if endpoint.delivered[-1].get('command') == 4:
                        endpoint.drop_response_close = True
                        if corrupt == 'identity':
                            endpoint.response ^= 1 << 91
                        else:
                            endpoint.response &= ~1
                endpoint._reply = lose_release
                with self.assertRaises(BufferedHardwareTransportError): pending.release()
                with self.assertRaises((TransferError, BufferedHardwareTransportError)): pending.recover()
                self.assertIs(host._pending, pending)
                with self.assertRaises(TransferError): loaded.submit(tx=b'\x96')

    def test_corrupt_complete_start_receipt_recovers_with_status_only(self):
        loaded = self.host.load(compact_spi(1))
        original = self.endpoint._reply
        def corrupt_start(sequence, code, status):
            original(sequence, code, status)
            if self.endpoint.delivered[-1].get('command') == 3:
                self.endpoint.response ^= 1 << 160
        self.endpoint._reply = corrupt_start
        with self.assertRaises(BufferedHardwareTransportError) as error: loaded.submit(tx=b'\xA5')
        pending = error.exception.pending
        requests = self.transport.requests
        self.assertEqual(pending.recover()['transfer'], 1)
        self.assertEqual(self.transport.requests, requests + 1)
        self.assertEqual(self.endpoint.delivered[-1]['command'], 0)
        self.assertEqual(sum(v.get('command') == 3 for v in self.endpoint.delivered), 1)

    def test_failed_physical_initialization_invalidates_old_software_handles(self):
        loaded = self.host.load(compact_spi(1))
        pending = loaded.submit(tx=b'\x96')
        original = self.endpoint.cold_reset
        def failed_reset():
            original()
            raise OSError('Reset reached endpoint, acknowledgement dropped')
        self.endpoint.cold_reset = failed_reset
        with self.assertRaises(OSError): self.host.initialize()
        with self.assertRaises(TransferError): pending.read()
        with self.assertRaises(TransferError): loaded.submit(tx=b'\x96')
        self.endpoint.cold_reset = original
        self.host.initialize()
        new_loaded = self.host.load(compact_spi(1))
        self.assertEqual(new_loaded.generation, loaded.generation)
        self.assertNotEqual(new_loaded.epoch, loaded.epoch)
        with self.assertRaises(TransferError): loaded.submit(tx=b'\x96')
        self.assertEqual(self.transport.physical_edges, self.endpoint.cycle)

    def test_held_high_bits_and_sequence_wrap(self):
        self.transport = BufferedSramSerialTransport(self.endpoint, phase_cycles=3)
        self.transport._sequence = 65535
        self.transport.edge(command=0, read_index=31)
        self.transport.edge(command=0, read_index=0)
        self.assertEqual(self.transport._sequence, 1)
        self.assertEqual(self.endpoint.delivered[-2:],
                         [dict(command=0, read_index=31), dict(command=0, read_index=0)])

    def test_core_rejection_is_receipted_and_not_a_framing_exception(self):
        self.host.load(compact_spi(1))
        pending = self.host._image
        status = self.transport.edge(command=3, expected_generation=65535)
        self.assertEqual(status['rejected'], 1)
        self.assertEqual((status['generation'], status['transfer']), (1, 0))
        self.assertEqual(self.host._image, pending)

    def test_truncated_and_overlong_reads_keep_exact_snapshot(self):
        raw_send(self.endpoint, encode_request(54321, command=0))
        held = self.endpoint.response
        _, ready = raw_read(self.endpoint, 191)
        self.assertEqual((ready, self.endpoint.response), (1, held))
        _, ready = raw_read(self.endpoint, 193)
        self.assertEqual((ready, self.endpoint.response), (1, held))
        packet, ready = raw_read(self.endpoint)
        self.assertEqual((packet, ready), (held, 0))

    def test_request_during_held_response_cannot_deliver_another_command(self):
        raw_send(self.endpoint, encode_request(1, command=0))
        before, held = len(self.endpoint.delivered), self.endpoint.response
        raw_send(self.endpoint, encode_request(2, command=7))
        self.assertEqual((len(self.endpoint.delivered), self.endpoint.response), (before, held))
        self.assertEqual(raw_read(self.endpoint), (held, 0))

    def test_protocol_rejection_codes_and_clean_recovery(self):
        for packet, length, code in ((0xA710 << 144, 159, 1), (0xB710 << 144, 160, 2),
                (0xA715 << 144, 160, 3), ((0xA717 << 144) | 1, 160, 3)):
            before = len(self.endpoint.delivered)
            raw_send(self.endpoint, packet, length)
            response, ready = raw_read(self.endpoint)
            self.assertEqual((decode_response(response)[1], ready), (code, 0))
            self.assertEqual(len(self.endpoint.delivered), before)
        self.transport.edge(command=0)


if __name__ == '__main__':
    unittest.main()
