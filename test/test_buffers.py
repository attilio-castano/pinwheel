"""Ownership, recovery, and host API contracts for finite buffered transfers."""
from copy import deepcopy
from dataclasses import FrozenInstanceError
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from pinwheel_buffers import (BufferFault, BufferedExecutionError, BufferedModelHost,
    HostWaitTimeout, TransferError, TransferId, TransferSlot)
from buffered_engine import BufferedInstruction, BufferedProgram, buffered_jtag, buffered_spi
from pad_io import PadDrive


class TransferOwnershipTests(unittest.TestCase):
    def test_preparation_copies_and_start_freezes_data(self):
        slot = TransferSlot(tx_capacity_bits=3, rx_capacity_bits=2)
        source = [True, False, True]
        identity = slot.prepare('program', source, 2, program_generation=7)
        source[:] = [False, True, False]
        with self.assertRaises(TransferError):
            slot.take_tx(identity)
        before = deepcopy(slot.__dict__)
        with self.assertRaises(TransferError):
            slot.start(identity, program_generation=8)
        self.assertEqual(before, slot.__dict__)
        slot.start(identity, program_generation=7)
        self.assertEqual([slot.take_tx(identity) for _ in range(3)], [True, False, True])
        self.assertEqual(slot.descriptor.program_generation, 7)
        with self.assertRaises(FrozenInstanceError):
            slot.descriptor.rx_limit = 9

    def test_rejected_admission_does_not_allocate_or_mutate(self):
        slot = TransferSlot(tx_capacity_bits=2, rx_capacity_bits=1)
        requests = [('p', (True,) * 3, 1, 0), ('p', (), 2, 0),
                    ('', (), 0, 0), ('p', (1,), 0, 0), ('p', (), True, 0),
                    ('p', (), 0, True)]
        for key, tx, rx, generation in requests:
            before = deepcopy(slot.__dict__)
            with self.subTest(request=(key, tx, rx, generation)), self.assertRaises(ValueError):
                slot.begin(key, tx, rx, program_generation=generation)
            self.assertEqual(before, slot.__dict__)
        identity = slot.begin('p', (), 0)
        self.assertEqual((identity.epoch, identity.sequence), (0, 1))

    def test_iterator_failure_is_not_partial_preparation(self):
        def broken():
            yield True
            raise RuntimeError('source failed')
        slot = TransferSlot()
        before = deepcopy(slot.__dict__)
        with self.assertRaisesRegex(RuntimeError, 'source failed'):
            slot.prepare('p', broken(), 0)
        self.assertEqual(before, slot.__dict__)

    def test_active_and_unread_owners_block_reuse(self):
        slot = TransferSlot()
        identity = slot.begin('p', (True,), 1)
        for phase in ('running', 'completed'):
            with self.subTest(phase=phase):
                before = deepcopy(slot.__dict__)
                with self.assertRaises(TransferError):
                    slot.begin('other', (), 0)
                self.assertEqual(before, slot.__dict__)
            if phase == 'running':
                with self.assertRaises(TransferError):
                    slot.release(identity)
                slot.complete(identity, 'fault')
        slot.release(identity)
        self.assertEqual(slot.state, 'free')

    def test_exact_bounds_reject_without_overwriting_prefix(self):
        slot = TransferSlot(tx_capacity_bits=2, rx_capacity_bits=2)
        identity = slot.begin('p', (False, True), 2)
        self.assertFalse(slot.take_tx(identity))
        self.assertTrue(slot.take_tx(identity))
        slot.append_rx(identity, True)
        slot.append_rx(identity, False)
        for operation in (lambda: slot.take_tx(identity),
                          lambda: slot.append_rx(identity, True)):
            before = deepcopy(slot.__dict__)
            with self.assertRaises(BufferFault):
                operation()
            self.assertEqual(before, slot.__dict__)
        slot.complete(identity, 'fault')
        raw = slot.peek(identity)
        self.assertEqual(raw.rx_bits, (True, False))
        self.assertEqual(raw.tx_consumed_bits, 2)

    def test_zero_length_and_zero_reservation(self):
        slot = TransferSlot(tx_capacity_bits=0, rx_capacity_bits=0)
        identity = slot.begin('p', (), 0)
        with self.assertRaises(BufferFault):
            slot.take_tx(identity)
        with self.assertRaises(BufferFault):
            slot.append_rx(identity, False)
        slot.complete(identity)
        self.assertEqual(slot.peek(identity).rx_bits, ())

    def test_completion_and_reads_are_immutable_until_matching_release(self):
        for outcome in ('complete', 'timeout', 'fault'):
            slot = TransferSlot()
            identity = slot.begin('p', (True, False), 3)
            slot.take_tx(identity)
            slot.append_rx(identity, False)
            slot.complete(identity, outcome)
            result = slot.peek(identity)
            self.assertIs(slot.peek(identity), result)
            for operation in (lambda: slot.take_tx(identity),
                              lambda: slot.append_rx(identity, True),
                              lambda: slot.complete(identity),
                              lambda: slot.start(identity),
                              lambda: slot.release(TransferId(identity.epoch, identity.sequence + 1))):
                before = deepcopy(slot.__dict__)
                with self.assertRaises(TransferError):
                    operation()
                self.assertEqual(before, slot.__dict__)
            slot.release(identity)
            successor = slot.begin('new', (False,), 0)
            self.assertNotEqual(identity, successor)
            self.assertEqual(result.rx_bits, (False,))
            self.assertEqual(result.program_key, 'p')
            with self.assertRaises(FrozenInstanceError):
                result.outcome = 'complete'

    def test_reset_and_reuse_never_accept_old_handles(self):
        for completed in (False, True):
            slot = TransferSlot()
            old = slot.begin('p', (True,), 1)
            if completed:
                slot.complete(old)
            slot.reset()
            new = slot.begin('p', (True,), 1)
            self.assertEqual(old.sequence, new.sequence)
            self.assertNotEqual(old.epoch, new.epoch)
            for operation in (slot.take_tx, slot.peek, slot.release, slot.start):
                before = deepcopy(slot.__dict__)
                with self.assertRaises(TransferError):
                    operation(old)
                self.assertEqual(before, slot.__dict__)

    def test_ids_reject_boolean_aliases_and_negative_fields(self):
        for epoch, sequence in ((True, 1), (0, True), (-1, 1), (0, -1), (0.0, 1), (0, 1.0)):
            with self.assertRaises(ValueError):
                TransferId(epoch, sequence)

    def test_handles_from_another_slot_cannot_access_or_release_storage(self):
        left, right = TransferSlot(), TransferSlot()
        first = left.begin('p', (), 0)
        second = right.begin('p', (), 0)
        self.assertEqual((first.epoch, first.sequence), (second.epoch, second.sequence))
        self.assertNotEqual(first.owner, second.owner)
        right.complete(second)
        for operation in (right.peek, right.release):
            before = deepcopy(right.__dict__)
            with self.assertRaises(TransferError):
                operation(first)
            self.assertEqual(before, right.__dict__)
        right.release(second)

    def test_adversarial_histories_preserve_data_bounds_and_identity(self):
        rng = random.Random(0x70696e)
        slot = TransferSlot(tx_capacity_bits=3, rx_capacity_bits=3)
        accepted = set()
        for _ in range(6000):
            descriptor = slot.descriptor
            current = descriptor.identity if descriptor else TransferId(0, 0)
            identity = current if rng.randrange(3) else TransferId(current.epoch, current.sequence + 1)
            command = rng.randrange(8)
            before = deepcopy(slot.__dict__)
            try:
                if command == 0:
                    new = slot.prepare('p', (False,) * rng.randrange(5), rng.randrange(5))
                    self.assertNotIn(new, accepted)
                    accepted.add(new)
                elif command == 1:
                    slot.start(identity)
                elif command == 2:
                    slot.take_tx(identity)
                elif command == 3:
                    slot.append_rx(identity, bool(rng.randrange(2)))
                elif command == 4:
                    slot.complete(identity, ('complete', 'timeout', 'fault')[rng.randrange(3)])
                elif command == 5:
                    slot.peek(identity)
                    self.assertEqual(before, slot.__dict__)
                elif command == 6:
                    slot.release(identity)
                else:
                    slot.reset()
            except (TransferError, ValueError):
                self.assertEqual(before, slot.__dict__)
            if slot.descriptor:
                self.assertLessEqual(slot.tx_length, 3)
                self.assertLessEqual(len(slot._rx), slot.rx_limit)
                self.assertLessEqual(slot.rx_limit, 3)
                self.assertLessEqual(slot._tx_consumed, slot.tx_length)
                self.assertEqual(slot.descriptor.identity.epoch, slot._epoch)
                self.assertLess(slot.descriptor.identity.sequence, slot._next_sequence)


class BufferedHostTests(unittest.TestCase):
    def test_submit_copies_mutable_host_buffers_before_execution(self):
        from buffered_peers import BufferedSPIPeer
        source = bytearray(b'\xa6\x53\xff\x00')
        peer = BufferedSPIPeer(bytes(source), b'\x96\xa5\x3c\x81')
        host = BufferedModelHost()
        pending = host.load(buffered_spi()).submit(tx=source, peer=peer)
        source[:] = bytes(4)
        pending.wait()
        result = pending.read()
        peer.check(result.raw_rx_bits)
        self.assertEqual(result.payload, b'\x96\xa5\x3c\x81')
        pending.release()

    def test_run_copies_result_before_release_and_survives_reuse(self):
        host = BufferedModelHost()
        loaded = host.load(buffered_spi())
        result = loaded.run(tx=b'\xa6\x53\xff\x00')
        self.assertEqual(result.payload, bytes(4))
        self.assertEqual(result.tx_consumed_bits, 32)
        self.assertEqual(result.rx_valid_bits, 32)
        self.assertEqual(host.slot.state, 'free')
        second = loaded.run(tx=b'\x00\xff\x53\xa6')
        self.assertNotEqual(result.identity, second.identity)
        self.assertEqual(result.payload, bytes(4))

    def test_host_timeout_carries_handle_for_continued_wait(self):
        host = BufferedModelHost()
        loaded = host.load(buffered_jtag())
        with self.assertRaises(HostWaitTimeout) as failure:
            loaded.run(tx=b'\xa6\x53\xff\x00', timeout_cycles=1)
        pending = failure.exception.pending
        self.assertEqual(host.slot.state, 'running')
        self.assertEqual(host.edges, 1)
        with self.assertRaises(TransferError):
            loaded.submit(tx=bytes(4))
        pending.wait()
        first = pending.read()
        self.assertEqual(pending.read(), first)
        self.assertEqual(host.slot.state, 'completed')
        pending.release()
        with self.assertRaises(TransferError):
            pending.read()

    def test_invalid_inputs_do_not_start_or_change_loaded_program(self):
        host = BufferedModelHost()
        loaded = host.load(buffered_spi())
        for operation in (lambda: loaded.run(tx=bytes(3)),
                          lambda: loaded.run(tx=bytes(4), rx_limit=31),
                          lambda: loaded.run(tx=bytes(4), rx_limit=33),
                          lambda: loaded.run(tx=bytes(4), timeout_cycles=True),
                          lambda: loaded.run(tx=bytes(4), peer=object()),
                          lambda: host.load(buffered_spi(byte_count=5))):
            before = deepcopy(host.slot.__dict__)
            with self.assertRaises(ValueError):
                operation()
            self.assertEqual(before, host.slot.__dict__)
            self.assertEqual(host.edges, 0)
        loaded.run(tx=bytes(4))

    def test_reload_reset_and_unread_results_protect_program_binding(self):
        host = BufferedModelHost()
        program = buffered_spi()
        old = host.load(program)
        current = host.load(program)
        with self.assertRaises(TransferError):
            old.submit(tx=bytes(4))
        pending = current.submit(tx=bytes(4))
        with self.assertRaises(TransferError):
            host.load(buffered_jtag())
        pending.wait()
        with self.assertRaises(TransferError):
            host.load(buffered_jtag())
        host.reset()
        for operation in (lambda: pending.wait(), pending.read, pending.release,
                          lambda: current.submit(tx=bytes(4))):
            with self.assertRaises(TransferError):
                operation()

    def test_decode_failure_preserves_the_unread_packet(self):
        host = BufferedModelHost()
        pending = host.load(buffered_spi()).submit(tx=bytes(4))
        pending.wait()
        original = host.slot.peek(pending.identity)
        with patch.object(BufferedProgram, 'decode_rx', side_effect=ValueError('decoder failed')):
            with self.assertRaisesRegex(ValueError, 'decoder failed'):
                pending.read()
        self.assertIs(host.slot.peek(pending.identity), original)
        self.assertEqual(pending.read().payload, bytes(4))
        pending.release()

    def test_incomplete_engine_success_is_not_decoded_as_success(self):
        host = BufferedModelHost()
        pending = host.load(buffered_spi()).submit(tx=bytes(4))
        host.slot.complete(pending.identity)
        with self.assertRaisesRegex(ValueError, 'declared TX'):
            pending.read()
        self.assertEqual(host.slot.state, 'completed')

    def test_terminal_failure_preserves_diagnostic_prefix(self):
        for outcome in ('fault', 'timeout'):
            program = BufferedProgram((BufferedInstruction('shift', duration=4, shift_pin=0),
                BufferedInstruction('keep', duration=4, append_input=0),
                BufferedInstruction('fault', outcome=outcome)))
            host = BufferedModelHost()
            result = host.load(program).run(tx=b'\x01')
            self.assertEqual(result.outcome, outcome)
            self.assertIsNone(result.payload)
            self.assertEqual(result.raw_rx_bits, (False,))
            self.assertEqual(result.rx_valid_bits, 1)
            self.assertEqual(result.tx_consumed_bits, 1)
            self.assertEqual(host.slot.state, 'free')

    def test_peer_setup_exception_has_recoverable_retained_failure(self):
        class BadPeer:
            def drive(self, cycle, pads, ui):
                raise RuntimeError('peer failed')
        host = BufferedModelHost()
        loaded = host.load(buffered_spi())
        with self.assertRaises(BufferedExecutionError) as failure:
            loaded.submit(tx=bytes(4), peer=BadPeer())
        pending = failure.exception.pending
        self.assertEqual(host.slot.state, 'completed')
        self.assertEqual(pending.read().outcome, 'fault')
        self.assertIsInstance(failure.exception.cause, RuntimeError)
        pending.release()
        loaded.run(tx=bytes(4))

    def test_invalid_initial_peer_reply_is_a_recoverable_fixture_failure(self):
        class InvalidPeer:
            def drive(self, cycle, pads, ui):
                return None
        host = BufferedModelHost()
        with self.assertRaises(BufferedExecutionError) as failure:
            host.load(buffered_spi()).submit(tx=bytes(4), peer=InvalidPeer())
        pending = failure.exception.pending
        self.assertEqual(pending.read().outcome, 'fault')
        pending.release()

    def test_final_observer_error_preserves_already_published_completion(self):
        program = buffered_spi()
        class FinalInvalidPeer:
            def drive(self, cycle, pads, ui):
                if cycle == program.execution_edges:
                    return None
                return PadDrive(0, 3)
        host = BufferedModelHost()
        pending = host.load(program).submit(tx=bytes(4), peer=FinalInvalidPeer())
        with self.assertRaises(BufferedExecutionError) as failure:
            pending.wait()
        self.assertEqual(failure.exception.pending.identity, pending.identity)
        self.assertIsInstance(failure.exception.cause, ValueError)
        self.assertEqual(pending.read().outcome, 'complete')
        self.assertEqual(host.slot.state, 'completed')
        # Engine testimony and validation of a final external observation are
        # separate. Rewriting this already published result would break retention.
        pending.release()

    def test_peer_runtime_exception_ends_with_a_recoverable_prefix(self):
        class BadPeer:
            def drive(self, cycle, pads, ui):
                if cycle == 20:
                    raise RuntimeError('peer later failed')
                return PadDrive(0, 3)
        host = BufferedModelHost()
        pending = host.load(buffered_spi()).submit(tx=bytes(4), peer=BadPeer())
        with self.assertRaises(BufferedExecutionError) as failure:
            pending.wait()
        self.assertEqual(host.edges, 20)
        self.assertEqual(failure.exception.pending.identity, pending.identity)
        result = pending.read()
        self.assertEqual(result.outcome, 'fault')
        self.assertGreater(result.rx_valid_bits, 0)
        self.assertLess(result.rx_valid_bits, 32)
        pending.release()

    def test_subclass_rejected_before_accepting_start(self):
        class UnsupportedProgram(BufferedProgram):
            pass
        program = buffered_spi()
        forged = UnsupportedProgram(program.instructions)
        host = BufferedModelHost()
        with self.assertRaises(ValueError):
            host.load(forged)
        self.assertEqual(host.slot.state, 'free')


if __name__ == '__main__':
    unittest.main()
