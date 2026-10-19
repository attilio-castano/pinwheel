"""Quad framing/recovery controls. The fixture is a link endpoint, not an engine oracle."""
import binascii
from dataclasses import replace
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from streaming_transport import (Code, Flags, Opcode, QuadTransport, Receipt, StreamHost,
    Request, StreamProtocolError, StreamTransportError, bits_left, byte_bits,
    checked_frame, command, crc16, decode_request, decode_response, jtag_bits)


class QuadFixture:
    """Only sampled framing, persistent exact-request replay and a callback.

    The callback represents command effects. No protocol execution, FIFO model,
    source program or typed circuit is used by these transport-only controls.
    """
    def __init__(self, respond=None):
        self.cycle = 0
        self.ready = False
        self.previous_cs, self.previous_sck = 1, 0
        self.mode, self.nibbles, self.read_index = None, [], 0
        self.response, self.cache = None, None
        self.effects, self.frames, self.reads = 0, [], []
        self.fail_at, self.corrupt_at = None, None
        self.corrupt_packet = None
        self.respond = respond or (lambda request: Receipt(request.sequence, Code.ACCEPTED,
            tag=0x12340001, flags=int(Flags.VALID)))

    def cold_reset(self):
        self.cycle += 2
        self.ready = False
        self.mode, self.cache, self.response = None, None, None
        self.previous_cs, self.previous_sck = 1, 0

    def tick(self, *, csn, sck, mosi):
        miso = 0
        if self.ready and not csn:
            packet = self.response.packet if self.corrupt_packet is None else self.corrupt_packet
            shift = 204 - 4 * self.read_index
            miso = (packet >> shift) & 15 if shift >= 0 else 0
        if self.previous_cs and not csn and not sck:
            self.mode = 'read' if self.ready else 'request'
            self.nibbles, self.read_index = [], 0
        if not csn and sck and not self.previous_sck:
            if self.mode == 'request':
                self.nibbles.append(mosi)
            elif self.mode == 'read':
                self.read_index += 1
        if not self.previous_cs and csn:
            if self.mode == 'request':
                packet = 0
                for nibble in self.nibbles:
                    packet = (packet << 4) | nibble
                self.frames.append(packet)
                if len(self.nibbles) == 44:
                    request = decode_request(packet)
                    if self.cache is not None and self.cache[0] == request.bytes:
                        self.response = self.cache[1]
                    else:
                        self.response = self.respond(request)
                        if self.response.code is Code.ACCEPTED:
                            self.effects += 1
                        if self.response.code in (Code.ACCEPTED, Code.BAD_PAYLOAD, Code.REJECTED):
                            self.cache = (request.bytes, self.response)
                    self.ready = True
            elif self.mode == 'read':
                self.reads.append(self.read_index)
                self.ready = self.read_index != 52
                self.corrupt_packet = None
            self.mode = None
        self.previous_cs, self.previous_sck = csn, sck
        self.cycle += 1
        if self.cycle == self.corrupt_at:
            miso ^= 1
        result = dict(miso=miso, ready=int(self.ready))
        if self.cycle == self.fail_at:
            self.fail_at = None
            raise OSError('Injected acknowledgement loss after an actual edge')
        return result


class CodecTests(unittest.TestCase):
    def test_ccitt_false_known_vector_and_independent_standard_library(self):
        self.assertEqual(crc16(b'123456789'), 0x29b1)
        for data in (b'', bytes(22), bytes(range(24)), b'\xff' * 24):
            self.assertEqual(crc16(data), binascii.crc_hqx(data, 0xffff))

    def test_exact_request_bit_positions_and_crc(self):
        request = command(0x1234, Opcode.EXCHANGE64, tag=0x56789abc,
            tx_offset=0xdef0, rx_ack=0x1357, data=0x2468ace013579bdf)
        body = bytes.fromhex('a72a123456789abcdef013572468ace013579bdf')
        # Header16 + sequence16 + tag32 + two offsets16 + data64 is20bytes.
        self.assertEqual(request.logical.to_bytes(20, 'big'), body)
        self.assertEqual(request.bytes, body + binascii.crc_hqx(body, 0xffff).to_bytes(2, 'big'))
        self.assertEqual(decode_request(request.packet), request)

    def test_control_layouts_zero_start_and_canonical_reservations(self):
        start = command(9, Opcode.START, expected_generation=0x1234, bit_count=0)
        self.assertEqual(start.payload, 0x1234 << 112)
        write = command(0, Opcode.WRITE, address=63, word=0x89abcdef12345678)
        self.assertEqual(write.payload, (63 << 122) | (0x89abcdef12345678 << 58))
        self.assertEqual(decode_request(write.packet), write)
        for fields in [dict(count=0), dict(count=65)]:
            with self.assertRaises(ValueError): command(0, Opcode.COMMIT, **fields)
        for request in [Request(0, Opcode.WRITE, 1), Request(0, Opcode.WARM_RESET, 1),
                        Request(0, Opcode.EXCHANGE0, 1), Request(0, Opcode.EXCHANGE32, 1)]:
            with self.assertRaises(StreamProtocolError): decode_request(request.packet)
        with self.assertRaises(ValueError): command(0, Opcode.START, bit_count=True)
        with self.assertRaises(ValueError): command(0, Opcode.START, reserved=1)

    def test_rx_right_alignment_and_tx_left_alignment(self):
        self.assertEqual(bits_left((True, False, True)), 5 << 61)
        reply = Receipt(0x3210, Code.ACCEPTED, data=5, tag=0x12340001,
            tx_accepted=4097, rx_start=4094, rx_valid=3,
            flags=int(Flags.VALID | Flags.RETAINED))
        self.assertEqual(decode_response(reply.packet, 0x3210), reply)
        self.assertEqual(reply.rx_bits, (True, False, True))
        self.assertEqual(reply.rx_end, 4097)
        self.assertEqual(reply.packet.bit_length(), 207)
        with self.assertRaises(StreamProtocolError): replace(reply, data=13)
        with self.assertRaises(StreamProtocolError): replace(reply, rx_start=65535)
        self.assertEqual(byte_bits(b'\x80', 1), (True,))
        self.assertEqual(byte_bits(b'\x01', 1, msb_first=False), (True,))
        with self.assertRaises(ValueError): byte_bits(b'\x01', 1)

    def test_all_single_bit_response_corruptions_are_detected(self):
        reply = Receipt(3, Code.ACCEPTED, tag=0x00010002,
            flags=int(Flags.VALID | Flags.BUSY), tx_free=4)
        for bit in range(208):
            with self.subTest(bit=bit), self.assertRaises(StreamProtocolError):
                decode_response(reply.packet ^ (1 << bit), 3)
        with self.assertRaises(StreamProtocolError): decode_response(reply.packet, 4)
        with self.assertRaises(StreamProtocolError): replace(reply, flags=128)
        with self.assertRaises(StreamProtocolError): replace(reply, flags=int(Flags.BUSY | Flags.RETAINED))

    def test_jtag_protocol_constructor_requires_a_real_last_bit(self):
        self.assertEqual(jtag_bits(b'\x01', 1), (True,))
        self.assertEqual(jtag_bits(b'\x01\x01', 9), (True,) + (False,) * 7 + (True,))
        with self.assertRaises(ValueError): jtag_bits(b'', 0)
        with self.assertRaises(ValueError): jtag_bits(b'\x80', 1)
        self.assertEqual(command(0, Opcode.START, bit_count=0).payload, 0)


class TransportTests(unittest.TestCase):
    def test_quad_nibble_chronology_and_phase_holds(self):
        for phase in (1, 2, 3):
            backend = QuadFixture()
            transport = QuadTransport(backend, phase_cycles=phase)
            receipt = transport.request(Opcode.START, expected_generation=0x1234, bit_count=4097)
            self.assertEqual(receipt.tag, 0x12340001)
            self.assertEqual(len(backend.frames), 1)
            self.assertEqual(backend.effects, 1)
            self.assertEqual(backend.reads, [52])
            self.assertEqual(transport.physical_edges, 192 * phase + 4)
            self.assertIsNone(transport.inflight)

    def test_lost_start_acknowledgement_recovers_held_response_once(self):
        backend = QuadFixture()
        transport = QuadTransport(backend)
        backend.fail_at = 90  # Request closes after one idle +88data edges.
        with self.assertRaises(StreamTransportError):
            transport.request(Opcode.START, expected_generation=0x1234, bit_count=32768)
        original = transport.inflight
        self.assertEqual(backend.effects, 1)
        reply = transport.recover()
        self.assertEqual(reply.sequence, original.sequence)
        self.assertEqual(backend.effects, 1)
        self.assertEqual(transport.request_frames, 1)
        self.assertEqual(transport.transactions, 1)

    def test_lost_close_allows_actual_response_publication_before_replay(self):
        class DelayedPublication(QuadFixture):
            publish_at = None
            def tick(self, **pins):
                before = self.effects
                try:
                    result = super().tick(**pins)
                finally:
                    if self.effects > before:
                        self.publish_at = self.cycle + 52
                if self.publish_at is not None and self.cycle < self.publish_at:
                    result['ready'] = 0
                return result
        backend = DelayedPublication()
        backend.fail_at = 90
        transport = QuadTransport(backend)
        with self.assertRaises(StreamTransportError): transport.request(Opcode.START, bit_count=8)
        transport.recover()
        self.assertEqual(backend.effects, 1)
        self.assertEqual(len(backend.frames), 1)
        self.assertEqual(transport.request_frames, 1)

    def test_partial_response_retains_receipt_and_does_not_repeat_effect(self):
        backend = QuadFixture()
        transport = QuadTransport(backend)
        backend.fail_at = 100
        with self.assertRaises(StreamTransportError):
            transport.request(Opcode.EXCHANGE32, tag=0x12340001,
                tx_offset=32, rx_ack=64, data=0xa5 << 56)
        transport.recover()
        self.assertGreaterEqual(len(backend.reads), 2)
        self.assertLess(backend.reads[0], 52)
        self.assertEqual(backend.reads[-1], 52)
        self.assertEqual(backend.effects, 1)
        self.assertEqual(transport.request_frames, 1)

    def test_corrupt_full_response_replays_exact_request_without_effects(self):
        backend = QuadFixture()
        transport = QuadTransport(backend)
        backend.corrupt_at = 95  # Corrupt a sampled pre-edge MISO nibble.
        with self.assertRaises(StreamTransportError):
            transport.request(Opcode.EXCHANGE32, tag=0x12340001,
                tx_offset=0, rx_ack=0, data=0xa5 << 56)
        original = transport.inflight.bytes
        transport.recover()
        self.assertEqual(backend.effects, 1)
        self.assertEqual(len(backend.frames), 2)
        self.assertEqual(backend.frames[0].to_bytes(22, 'big'), original)
        self.assertEqual(backend.frames[0], backend.frames[1])
        self.assertEqual(transport.transactions, 1)
        self.assertEqual(transport.request_frames, 2)

    def test_postedge_miso_mutation_cannot_pass_as_preedge_receipt(self):
        class WrongEdge(QuadFixture):
            def tick(self, **pins):
                result = super().tick(**pins)
                if not pins['csn'] and pins['sck'] and self.mode == 'read':
                    shift = 204 - 4 * self.read_index
                    result['miso'] = (self.response.packet >> shift) & 15 if shift >= 0 else 0
                return result
        transport = QuadTransport(WrongEdge())
        with self.assertRaises(StreamTransportError):
            transport.request(Opcode.START, bit_count=0)
        self.assertIsNotNone(transport.inflight)

    def test_semantic_offset_validation_failure_remains_recoverable(self):
        backend = QuadFixture()
        transport = QuadTransport(backend)
        attempts = []
        def validate(reply):
            attempts.append(reply)
            if len(attempts) == 1:
                raise StreamProtocolError('Injected inconsistent offset observation')
        with self.assertRaises(StreamTransportError):
            transport.request(Opcode.EXCHANGE0, tag=0x12340001, validate=validate)
        original = transport.inflight
        transport.recover()
        self.assertEqual(backend.effects, 1)
        self.assertEqual(backend.frames[0], backend.frames[1])
        self.assertEqual(attempts[0], attempts[1])
        self.assertEqual(original.sequence, attempts[1].sequence)

    def test_invalid_request_and_outstanding_command_refused_before_more_io(self):
        backend = QuadFixture()
        transport = QuadTransport(backend)
        with self.assertRaises(ValueError): transport.request(Opcode.COMMIT, count=0)
        self.assertEqual(backend.cycle, 0)
        backend.fail_at = 90
        with self.assertRaises(StreamTransportError): transport.request(Opcode.START, bit_count=0)
        before = backend.cycle
        with self.assertRaises(StreamProtocolError): transport.request(Opcode.WARM_RESET)
        self.assertEqual(backend.cycle, before)
        self.assertEqual(backend.effects, 1)

    def test_framing_rejection_keeps_exact_sequence_but_credit_rejection_completes(self):
        calls = []
        def respond(request):
            calls.append(request)
            code = Code.BAD_CRC if len(calls) == 1 else Code.REJECTED
            return Receipt(request.sequence, code, flags=int(Flags.REJECTED) if code is Code.REJECTED else 0)
        backend = QuadFixture(respond)
        transport = QuadTransport(backend)
        with self.assertRaises(StreamTransportError): transport.request(Opcode.START, bit_count=0)
        original = transport.inflight
        self.assertEqual(transport.recover().code, Code.REJECTED)
        self.assertIsNone(transport.inflight)
        self.assertEqual(calls, [original, original])
        self.assertEqual(transport.request(Opcode.START, bit_count=0).sequence, 1)

    def test_sequence_never_silently_wraps(self):
        backend = QuadFixture()
        transport = QuadTransport(backend)
        transport._sequence = 65535
        self.assertEqual(transport.request(Opcode.START, bit_count=0).sequence, 65535)
        before = backend.cycle
        with self.assertRaisesRegex(StreamProtocolError, 'sequence exhausted'):
            transport.request(Opcode.START, bit_count=0)
        self.assertEqual(before, backend.cycle)
        transport.cold_reset()
        self.assertEqual(transport.request(Opcode.START, bit_count=0).sequence, 0)

    def test_idle_edges_are_physical_and_validate_before_io(self):
        backend = QuadFixture()
        transport = QuadTransport(backend)
        self.assertIsNone(transport.idle(0))
        transport.idle(17)
        self.assertEqual(backend.cycle, 17)
        self.assertEqual(transport.physical_edges, 17)
        for bad in (-1, True, 1.5):
            with self.assertRaises(ValueError): transport.idle(bad)
        self.assertEqual(backend.cycle, 17)

    def test_well_formed_rejection_is_cached_for_exact_replay(self):
        calls = []
        def respond(request):
            calls.append(request)
            return Receipt(request.sequence, Code.REJECTED, flags=int(Flags.REJECTED))
        backend = QuadFixture(respond)
        transport = QuadTransport(backend)
        request = command(0, Opcode.START, bit_count=0)
        transport._send(request)
        first = transport._read(0)
        transport._send(request)
        self.assertEqual(transport._read(0), first)
        self.assertEqual(calls, [request])


class HostScopeTests(unittest.TestCase):
    def refused_simplex(self, *, transmit, receive):
        from streaming_compile import Instruction, lower, spi_image, validate_image
        image = spi_image()
        instructions = list(image.source.instructions)
        instructions[1] = Instruction('stream', replace(instructions[1].cell,
            transmit=transmit, receive=receive))
        simplex = lower(tuple(instructions), idle_levels=image.idle_levels, idle_enabled=image.idle_enabled)
        validate_image(simplex)  # Generic compiler still supports these cells.
        backend = QuadFixture()
        host = StreamHost(QuadTransport(backend), depth=2)
        with self.assertRaisesRegex(ValueError, 'duplex'):
            host.load(simplex)
        self.assertEqual(backend.cycle, 0)
        self.assertEqual(host._epoch, 0)

    def test_receive_only_image_refused_before_any_link_action(self):
        self.refused_simplex(transmit=False, receive=True)

    def test_transmit_only_image_refused_before_any_link_action(self):
        self.refused_simplex(transmit=True, receive=False)


if __name__ == '__main__':
    unittest.main()
