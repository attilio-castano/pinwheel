"""Buffered model admission, ownership, and independent resolved-wire targets."""
from dataclasses import FrozenInstanceError, replace
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from buffered_engine import (TARGET, BufferedEngine, BufferedInstruction, BufferedProgram,
                             BufferedWireSimulation, buffered_jtag, buffered_spi)
from buffered_peers import BufferedJTAGPeer, BufferedSPIPeer
from jtag_peers import TAP
from pad_io import PadDrive
from pinwheel_buffers import TransferError, TransferSlot
from pinwheel_host import Host, PAIRED_FORMAT


class ZeroPeer:
    def drive(self, cycle, pads, ui):
        return PadDrive(0, 3)


def start(program, payload, peer, *, rx_limit=None):
    bits = program.encode_tx(payload)
    rx_limit = program.rx_bits if rx_limit is None else rx_limit
    program.validate_transfer(bits, rx_limit)
    slot = TransferSlot(tx_capacity_bits=max(32, program.tx_bits),
                        rx_capacity_bits=max(32, rx_limit))
    identity = slot.begin(program.key, bits, rx_limit)
    engine = BufferedEngine(slot, identity, program)
    return slot, identity, BufferedWireSimulation(engine, peer)


class BufferedWireTests(unittest.TestCase):
    def test_four_spi_bytes_keep_cs_and_reuse_one_program_for_changing_data(self):
        program = buffered_spi()
        key = program.key
        for value in range(256):
            transmit = bytes((value, value ^ 0x96, 0, 255))
            receive = bytes((value ^ 0xa5, 0x53, 0x81, value ^ 255))
            peer = BufferedSPIPeer(transmit, receive)
            slot, identity, wire = start(program, transmit, peer)
            completion = wire.run(program.execution_edges)
            report = peer.check(completion.rx_bits)
            self.assertEqual(program.decode_rx(completion.rx_bits), receive)
            self.assertEqual((completion.tx_consumed_bits, len(completion.rx_bits),
                              wire.cycle, report['clock_edges']), (32, 32, 260, 64))
            self.assertEqual(slot.peek(identity), completion)
            self.assertEqual(program.key, key)

    def test_32_bit_jtag_scan_recovers_all_initial_tap_states(self):
        program = buffered_jtag()
        for state in TAP:
            for transmit in (0, 0xffffffff, 0x80000001, 0xa6531289):
                receive = transmit ^ 0x963cc35a
                with self.subTest(state=state, transmit=transmit):
                    peer = BufferedJTAGPeer(transmit, receive, initial_state=state)
                    slot, identity, wire = start(program, transmit.to_bytes(4, 'little'), peer)
                    completion = wire.run(program.execution_edges)
                    report = peer.check(completion.rx_bits)
                    self.assertEqual(program.decode_rx(completion.rx_bits), receive.to_bytes(4, 'little'))
                    self.assertEqual((report['clocks'], report['clock_edges'], wire.cycle), (43, 86, 348))
                    self.assertEqual((completion.tx_consumed_bits, len(completion.rx_bits)), (32, 32))
                    self.assertEqual(report['tap_states'][4], 'test_logic_reset')
                    slot.release(identity)

    def test_nonbyte_jtag_scan_has_thirteen_real_clocks_and_checked_padding(self):
        program = buffered_jtag(bit_count=13)
        for state in TAP:
            transmit, receive = 0x1234, 0x1569
            peer = BufferedJTAGPeer(transmit, receive, bit_count=13, initial_state=state)
            _, _, wire = start(program, transmit.to_bytes(2, 'little'), peer)
            completion = wire.run(program.execution_edges)
            report = peer.check(completion.rx_bits)
            self.assertEqual((report['sampled_bits'], report['clocks'], wire.cycle), (13, 24, 196))
            self.assertEqual(program.decode_rx(completion.rx_bits), b'\x69\x15')
        with self.assertRaisesRegex(ValueError, 'padding'):
            program.encode_tx(b'\x34\x92')

    def test_one_bit_jtag_scan_exits_on_its_only_data_clock(self):
        program = buffered_jtag(bit_count=1)
        peer = BufferedJTAGPeer(1, 0, bit_count=1)
        _, _, wire = start(program, b'\x01', peer)
        completion = wire.run(program.execution_edges)
        peer.check(completion.rx_bits)
        self.assertEqual(completion.rx_bits, (False,))
        self.assertEqual(wire.cycle, 100)

    def test_receive_delay_boundary_and_exact_duration(self):
        for period, delay in ((3, 0), (4, 1), (7, 4)):
            for program, payload, peer in (
                (buffered_spi(4, period), b'\xa6\x53\x81\x00',
                 BufferedSPIPeer(b'\xa6\x53\x81\x00', b'\x96\xa5\x55\x3c', period, delay)),
                (buffered_jtag(32, period), b'\x89\x12\x53\xa6',
                 BufferedJTAGPeer(0xa6531289, 0x963cc35a, half_cycles=period, tco=delay)),
            ):
                with self.subTest(protocol=program.protocol, period=period):
                    _, _, wire = start(program, payload, peer)
                    completion = wire.run(program.execution_edges)
                    peer.check(completion.rx_bits)
                    self.assertEqual(wire.cycle, program.execution_edges)
        for constructor, args in ((BufferedSPIPeer, (b'\x00', b'\x01')),
                                  (BufferedJTAGPeer, (0, 1))):
            with self.assertRaisesRegex(ValueError, 'Receive timing'):
                constructor(*args, half_cycles=4, tco=2)

    def test_host_wait_timeout_resumes_same_engine_without_releasing_buffers(self):
        program = buffered_spi()
        peer = BufferedSPIPeer(b'\xa6\x53\x81\x00', b'\x96\xa5\x55\x3c')
        slot, identity, wire = start(program, peer.transmit, peer)
        with self.assertRaisesRegex(TimeoutError, 'remain owned'):
            wire.run(11)
        self.assertEqual((slot.state, wire.cycle), ('running', 11))
        with self.assertRaises(TransferError):
            slot.release(identity)
        completion = wire.run(program.execution_edges - 11)
        peer.check(completion.rx_bits)
        self.assertEqual(slot.state, 'completed')
        self.assertEqual(wire.cycle, 260)

    def test_spi_capture_moved_late_keeps_valid_wires_but_fails_independent_reply(self):
        program = buffered_spi()
        operations = list(program.instructions)
        first_high = operations[1]
        operations[1:2] = [replace(first_high, duration=3, append_input=None),
                           replace(first_high, duration=1)]
        mutation = replace(program, instructions=tuple(operations))
        peer = BufferedSPIPeer(b'\xa6\x53\x81\x00', b'\x96\xa5\x55\x3c')
        _, _, wire = start(mutation, peer.transmit, peer)
        completion = wire.run(mutation.execution_edges)
        peer.check()  # Pin timing and framing remain valid.
        with self.assertRaisesRegex(RuntimeError, 'appended RX'):
            peer.check(completion.rx_bits)

    def test_spi_cs_release_at_byte_boundary_is_rejected(self):
        program = buffered_spi()
        operations = list(program.instructions)
        operations[16] = replace(operations[16], levels=4)
        mutation = replace(program, instructions=tuple(operations))
        peer = BufferedSPIPeer(b'\xa6\x53\x81\x00', b'\x96\xa5\x55\x3c')
        _, _, wire = start(mutation, peer.transmit, peer)
        with self.assertRaisesRegex(RuntimeError, 'CS asserted twice'):
            wire.run(mutation.execution_edges)

    def test_jtag_missing_last_bit_tms_exit_is_rejected(self):
        program = buffered_jtag()
        operations = list(program.instructions)
        for index in (18 + 2 * 31, 19 + 2 * 31):
            operations[index] = replace(operations[index], levels=operations[index].levels & ~4)
        mutation = replace(program, instructions=tuple(operations))
        _, _, wire = start(mutation, b'\x89\x12\x53\xa6', BufferedJTAGPeer(0xa6531289, 0x963cc35a))
        with self.assertRaisesRegex(RuntimeError, 'last-bit TMS'):
            wire.run(mutation.execution_edges)

    def test_jtag_wrong_wire_byte_order_is_rejected(self):
        mutation = replace(buffered_jtag(), wire_order='msb-per-byte')
        peer = BufferedJTAGPeer(0xa6531289, 0x963cc35a)
        _, _, wire = start(mutation, b'\x89\x12\x53\xa6', peer)
        wire.run(mutation.execution_edges)
        with self.assertRaisesRegex(RuntimeError, 'outgoing LSB-first'):
            peer.check()


class BufferedEngineTests(unittest.TestCase):
    def test_program_is_immutable_bound_to_all_operations_and_separate_from_chip_images(self):
        program = buffered_spi()
        self.assertEqual(program.target, TARGET)
        self.assertFalse(hasattr(program, 'upload_words'))
        self.assertEqual(program, buffered_spi())
        with self.assertRaises(FrozenInstanceError):
            program.idle_levels = 0
        for replacement in (dict(idle_levels=0), dict(protocol='changed'), dict(wire_order='lsb-per-byte'),
                            dict(instructions=(replace(program.instructions[0], duration=5),
                                               *program.instructions[1:]))):
            self.assertNotEqual(replace(program, **replacement).key, program.key)
        with self.assertRaisesRegex(ValueError, 'reference-model target'):
            replace(program, target='pinwheel-paired-v1')

    def test_existing_hardware_host_rejects_reference_program_before_any_io(self):
        class NoIO:
            def advance(self, *args, **kwargs):
                raise AssertionError('Reference program touched hardware transport')
        for host in (Host(NoIO()), Host(NoIO(), image_format=PAIRED_FORMAT)):
            with self.assertRaisesRegex(ValueError, 'image format'):
                host.upload(buffered_spi())

    def test_payload_and_reservation_admission_fail_before_ownership(self):
        program = buffered_spi()
        slot = TransferSlot()
        for payload in (b'', b'\x00', b'\x00' * 5, bytearray(4), True):
            with self.subTest(payload=payload), self.assertRaises(ValueError):
                program.encode_tx(payload)
            self.assertEqual(slot.state, 'free')
        for bits, limit in (((), 32), ((False,) * 31, 32), ((0,) * 32, 32),
                            ([False] * 32, 32), ((False,) * 32, 31), ((False,) * 32, True)):
            with self.subTest(limit=limit), self.assertRaises(ValueError):
                program.validate_transfer(bits, limit)
            self.assertEqual(slot.state, 'free')

    def test_engine_requires_matching_program_and_buffers(self):
        program = buffered_spi()
        for key, bit_count, rx_limit in ((program.key, 31, 32), (program.key, 32, 31), ('wrong', 32, 32)):
            slot = TransferSlot()
            identity = slot.begin(key, (False,) * bit_count, rx_limit)
            with self.assertRaises(ValueError):
                BufferedEngine(slot, identity, program)
            self.assertEqual(slot.state, 'running')
            self.assertEqual(slot._tx_consumed, 0)

    def test_shift_consumes_once_per_entry_and_keep_preserves_output_during_held_edges(self):
        program = BufferedProgram((BufferedInstruction('shift', 3, shift_pin=0),
                                   BufferedInstruction('keep', 4, levels=2, preserve=1),
                                   BufferedInstruction('halt')))
        slot = TransferSlot()
        identity = slot.begin(program.key, (True,), 0)
        engine = BufferedEngine(slot, identity, program)
        wire = BufferedWireSimulation(engine, ZeroPeer())
        completion = wire.run(7)
        self.assertEqual([entry.logical.levels for entry in wire.trace], [1, 1, 1, 3, 3, 3, 3, 0])
        self.assertEqual(completion.tx_consumed_bits, 1)
        self.assertEqual(completion.rx_bits, ())
        # No peripheral data clock has been defined by this generic program.
        self.assertEqual(wire.cycle, 7)

    def test_sample_is_preedge_second_register_and_appended_once(self):
        program = BufferedProgram((BufferedInstruction('drive', 2),
                                   BufferedInstruction('keep', 3, append_input=0),
                                   BufferedInstruction('halt')))
        slot = TransferSlot()
        identity = slot.begin(program.key, (), 1)
        engine = BufferedEngine(slot, identity, program)
        wire = BufferedWireSimulation(engine, ZeroPeer())
        completion = wire.run(5)
        # Input zero starts on fixture edge 1; on entry at edge 2 the old
        # second sampler register still contains the initial pullup one.
        self.assertEqual(completion.rx_bits, (True,))
        self.assertEqual(wire.cycle, 5)

    def test_engine_fault_and_timeout_freeze_partial_prefix_then_restore_idle(self):
        for outcome in ('fault', 'timeout'):
            program = BufferedProgram((BufferedInstruction('shift', 3, shift_pin=0),
                                       BufferedInstruction('keep', 1, preserve=1, append_input=0),
                                       BufferedInstruction('fault', outcome=outcome)), idle_levels=4)
            slot = TransferSlot()
            identity = slot.begin(program.key, (True,), 1)
            engine = BufferedEngine(slot, identity, program)
            wire = BufferedWireSimulation(engine, ZeroPeer())
            completion = wire.run(4)
            self.assertEqual((completion.outcome, completion.tx_consumed_bits, completion.rx_bits),
                             (outcome, 1, (False,)))
            self.assertEqual(engine.levels, 4)
            wire.step()
            self.assertEqual(slot.peek(identity), completion)
            with self.assertRaises(TransferError):
                slot.append_rx(identity, True)

    def test_runtime_tx_underflow_is_fault_not_a_fabricated_transmitted_count(self):
        program = BufferedProgram((BufferedInstruction('shift', 1, shift_pin=0),
                                   BufferedInstruction('shift', 1, shift_pin=0),
                                   BufferedInstruction('halt')))
        slot = TransferSlot()
        identity = slot.begin(program.key, (False, True), 0)
        engine = BufferedEngine(slot, identity, program)
        slot.take_tx(identity)  # Deliberate low-level cursor corruption fixture.
        engine.step(0)
        completion = slot.peek(identity)
        self.assertEqual((completion.outcome, completion.tx_consumed_bits, engine.cycle), ('fault', 2, 1))
        self.assertEqual(engine.levels, program.idle_levels)

    def test_runtime_rx_overflow_freezes_existing_prefix(self):
        program = BufferedProgram((BufferedInstruction('drive', 3),
                                   BufferedInstruction('keep', 1, append_input=0),
                                   BufferedInstruction('halt')))
        slot = TransferSlot()
        identity = slot.begin(program.key, (), 1)
        engine = BufferedEngine(slot, identity, program)
        slot.append_rx(identity, True)  # Deliberate low-level cursor corruption.
        for _ in range(3):
            engine.step(0)
        completion = slot.peek(identity)
        self.assertEqual((completion.outcome, completion.rx_bits), ('fault', (True,)))

    def test_reset_does_not_let_stale_engine_finish_another_transaction(self):
        program = buffered_spi()
        slot, identity, wire = start(program, b'\x00' * 4, ZeroPeer())
        slot.reset()
        next_identity = slot.begin(program.key, (False,) * 32, 32)
        with self.assertRaisesRegex(TransferError, 'Stale'):
            wire.run(program.execution_edges)
        self.assertNotEqual(identity, next_identity)
        self.assertEqual((slot.state, slot._tx_consumed), ('running', 0))

    def test_malformed_timed_programs_reject_at_construction(self):
        for item in (dict(kind='unknown'), dict(kind='shift'), dict(kind='drive', shift_pin=0),
                     dict(kind='keep', duration=0), dict(kind='keep', duration=True),
                     dict(kind='drive', preserve=1), dict(kind='keep', append_input=2),
                     dict(kind='halt', append_input=0), dict(kind='fault', outcome='complete')):
            with self.subTest(item=item), self.assertRaises(ValueError):
                BufferedInstruction(**item)
        for instructions in ((), [BufferedInstruction('halt')], (BufferedInstruction('drive'),),
                             (BufferedInstruction('halt'), BufferedInstruction('halt'))):
            with self.subTest(instructions=instructions), self.assertRaises(ValueError):
                BufferedProgram(instructions)


if __name__ == '__main__':
    unittest.main()
