"""Reactive entry effects, compact counted fetch, and retained partial results."""
from dataclasses import FrozenInstanceError, replace
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from buffered_engine import (BufferedBlock, BufferedEngine, BufferedInstruction as I,
                             BufferedProgram, BufferedRepeat, BufferedSequence)
from pinwheel_buffers import (BufferedModelHost, HostWaitTimeout, TransferError,
                              TransferSlot)
from pad_io import PadDrive


def program(instructions, *, tx=0, rx=0, maximum=None, idle_levels=0, idle_enabled=7):
    return BufferedProgram((), schedule=BufferedBlock(tuple(instructions)),
                           declared_tx_bits=tx, declared_rx_bits=rx,
                           max_rx_bits=rx if maximum is None else maximum,
                           idle_levels=idle_levels, idle_enabled=idle_enabled)


def start(code, tx=(), *, rx_limit=None):
    limit = code.rx_reservation_bits if rx_limit is None else rx_limit
    slot = TransferSlot(tx_capacity_bits=max(32, len(tx)),
                        rx_capacity_bits=max(32, limit))
    identity = slot.begin(code.key, tx, limit)
    return slot, identity, BufferedEngine(slot, identity, code)


def sampled_step(engine, sampled):
    """Explicit pre-edge observation for semantic boundary tests only."""
    engine._second = sampled
    engine.step(sampled)


class HighPeer:
    def drive(self, cycle, pads, ui):
        return PadDrive(pullups=3)


class BufferedReactiveTests(unittest.TestCase):
    def test_counted_fetch_reuses_stored_body_and_reports_control_metadata(self):
        bit = BufferedBlock((I('shift', 2, shift_pin=0),
                             I('keep', 2, levels=2, preserve=1, append_input=0)))
        byte = BufferedRepeat(8, bit)
        body = BufferedRepeat(4, byte)
        code = BufferedSequence((body, BufferedBlock((I('halt'),))))
        p = BufferedProgram((), schedule=code, declared_tx_bits=32,
                            declared_rx_bits=32, max_rx_bits=32)
        self.assertEqual(p.storage(), dict(virtual_slots=65, instruction_words=3,
            control_nodes=4, stored_nodes=7, repeat_nodes=2, nesting=2,
            expanded_at_runtime=False, target='buffered-reference-v1'))
        self.assertIs(p.fetch(0), p.fetch(2))
        self.assertIs(p.fetch(0), p.fetch(16))
        self.assertEqual(p.locate(30)[1], (7, 1))
        self.assertIsNone(p.fetch(65))
        slot, identity, engine = start(p, tuple(bool(i % 3) for i in range(32)))
        for _ in range(128): engine.step(3)
        completion = slot.peek(identity)
        self.assertEqual((completion.outcome, completion.tx_consumed_bits,
                          len(completion.rx_bits)), ('complete', 32, 32))
        self.assertEqual(engine.samples, (False,) * 16)

    def test_self_branch_reenters_rx_append_and_holds_do_not_append(self):
        p = program((I('checked', 2, append_input=0, finish=0), I('halt')),
                    rx=2, idle_levels=4)
        slot, identity, engine = start(p)
        self.assertEqual(slot._rx, (True,))
        sampled_step(engine, 0)
        self.assertEqual(slot._rx, (True,))
        sampled_step(engine, 0)
        self.assertEqual((engine.pc, slot._rx), (0, (True, False)))
        sampled_step(engine, 3)
        self.assertEqual(slot._rx, (True, False))
        sampled_step(engine, 3)
        packet = slot.peek(identity)
        self.assertEqual((packet.outcome, packet.rx_bits), ('fault', (True, False)))
        self.assertEqual((engine.levels, engine.enabled), (4, 7))

    def test_branch_back_to_shift_consumes_only_on_entry(self):
        p = program((I('shift', 3, shift_pin=0), I('checked', finish=0), I('halt')),
                    tx=2, idle_levels=4)
        slot, identity, engine = start(p, (True, False))
        self.assertEqual((engine.levels, slot._tx_consumed), (1, 1))
        for _ in range(2): engine.step(3)
        self.assertEqual(slot._tx_consumed, 1)
        engine.step(3)
        self.assertEqual((engine.pc, slot._tx_consumed), (1, 1))
        engine.step(3)
        self.assertEqual((engine.pc, engine.levels, slot._tx_consumed), (0, 0, 2))
        for _ in range(4): engine.step(3)
        self.assertEqual(slot.peek(identity).outcome, 'fault')
        self.assertEqual(engine.levels, 4)

    def test_wait_ready_wins_on_last_budget_edge_and_does_not_consume_on_hold(self):
        p = program((I('wait', wait_input=0, budget=2),
                     I('shift', shift_pin=0), I('halt')), tx=1)
        slot, identity, engine = start(p, (True,))
        sampled_step(engine, 0)
        self.assertEqual((engine.mode, engine.remaining, slot._tx_consumed), ('waiting', 0, 0))
        sampled_step(engine, 1)
        self.assertEqual((engine.pc, slot._tx_consumed), (1, 1))
        engine.step(1)
        self.assertEqual(slot.peek(identity).outcome, 'complete')
        slot.release(identity)
        _, _, engine = start(p, (False,))
        sampled_step(engine, 0)
        sampled_step(engine, 0)
        self.assertEqual(engine.mode, 'timeout')

    def test_guard_fault_precedes_terminal_capture_and_successor_effects(self):
        p = program((I('checked', check_mask=1, check_value=1,
                       entry_capture=(1, 1), terminal_capture=(0, 0), append_input=1),
                     I('shift', shift_pin=0), I('halt')), tx=1, rx=1,
                    idle_levels=4, idle_enabled=0)
        slot, identity, engine = start(p, (False,))
        sampled_step(engine, 2)
        packet = slot.peek(identity)
        self.assertEqual((packet.outcome, packet.tx_consumed_bits, packet.rx_bits),
                         ('fault', 0, (True,)))
        self.assertEqual(engine.samples[:2], (False, True))
        self.assertEqual((engine.levels, engine.enabled), (4, 0))

    def test_terminal_capture_controls_branch_and_sequential_endpoint_is_dynamic(self):
        branch = I('checked', terminal_capture=(0, 3), finish=(3, None, 0))
        p = program((branch, I('halt')))
        slot, identity, engine = start(p)
        sampled_step(engine, 0)
        self.assertEqual((engine.pc, engine.samples[3]), (0, False))
        sampled_step(engine, 1)
        self.assertEqual(slot.peek(identity).outcome, 'complete')
        self.assertTrue(engine.samples[3])

    def test_qualify_resets_interval_and_rebudgets_after_ready_partial_edge(self):
        p = program((I('qualify', 3, check_mask=1, check_value=1, budget=2), I('halt')))
        slot, identity, engine = start(p)
        sampled_step(engine, 0)
        self.assertEqual((engine.remaining, engine.wait_left), (2, 0))
        sampled_step(engine, 1)
        self.assertEqual((engine.remaining, engine.wait_left), (1, 1))
        sampled_step(engine, 0)
        self.assertEqual((engine.remaining, engine.wait_left), (2, 0))
        sampled_step(engine, 1)
        sampled_step(engine, 1)
        sampled_step(engine, 1)
        self.assertEqual(slot.peek(identity).outcome, 'complete')
        slot.release(identity)
        slot, identity, engine = start(p)
        sampled_step(engine, 0)
        sampled_step(engine, 0)
        self.assertEqual(slot.peek(identity).outcome, 'timeout')

    def test_scratch_and_rx_are_distinct_and_capture_uses_pre_edge_second_sampler(self):
        p = program((I('drive', 2),
                     I('checked', entry_capture=(0, 5), append_input=1,
                       terminal_capture=(1, 6)), I('halt')), rx=1)
        slot, identity, engine = start(p)
        engine.step(0)                 # second is still initial 3
        engine.step(1)                 # entry sees pre-edge second == 3
        self.assertTrue(engine.samples[5])
        self.assertEqual(slot._rx, (True,))
        engine.step(3)                 # terminal sees pre-edge second == 0
        self.assertFalse(engine.samples[6])
        self.assertEqual(slot.peek(identity).rx_bits, (True,))

    def test_open_drain_shift_selects_enable_inversion_and_keep_preserves_it(self):
        p = program((I('shift', 2, enabled=1, shift_pin=1,
                       shift_enabled=True, shift_invert=True),
                     I('checked', 2, enabled=0, preserve_enabled=2), I('halt')), tx=1,
                    idle_enabled=0)
        for bit, pull in ((False, 3), (True, 1)):
            slot, identity, engine = start(p, (bit,))
            self.assertEqual((engine.levels, engine.enabled), (0, pull))
            engine.step(3); engine.step(3)
            self.assertEqual((engine.levels, engine.enabled), (0, pull & 2))
            engine.step(3); engine.step(3)
            self.assertEqual(slot.peek(identity).outcome, 'complete')

    def test_underflow_precedes_append_and_overflow_retains_successful_tx_consume(self):
        p = program((I('shift', shift_pin=0, append_input=0, entry_capture=(0, 2)),
                     I('checked', finish=0), I('halt')), tx=1, rx=0,
                    idle_levels=4)
        slot, identity, engine = start(p, (True,))
        packet = slot.peek(identity)
        self.assertEqual((packet.outcome, packet.tx_consumed_bits, packet.rx_bits), ('fault', 1, ()))
        self.assertTrue(engine.samples[2])
        self.assertEqual(engine.levels, 4)
        p = replace(p, max_rx_bits=1, declared_rx_bits=1)
        slot, identity, engine = start(p, (True,))
        self.assertEqual(slot._rx, (True,))
        engine.step(3); engine.step(0)
        packet = slot.peek(identity)
        self.assertEqual((packet.outcome, packet.tx_consumed_bits, packet.rx_bits),
                         ('fault', 1, (True,)))

    def test_maximum_rx_reservation_differs_from_success_exact_length(self):
        p = program((I('checked', append_input=0), I('halt')), rx=1, maximum=4)
        with self.assertRaisesRegex(ValueError, 'RX reservation'):
            p.validate_transfer((), 1)
        p.validate_transfer((), 4)
        with self.assertRaisesRegex(ValueError, 'complete program result'):
            p.decode_rx((True, False))
        self.assertEqual(p.decode_rx((True,)), b'\x01')

    def test_early_halt_cannot_publish_a_short_successful_payload(self):
        p = program((I('checked', append_input=0), I('halt')), rx=2)
        host = BufferedModelHost()
        pending = host.load(p).submit(tx=b'', peer=HighPeer())
        pending.wait(timeout_cycles=1)
        with self.assertRaisesRegex(ValueError, 'complete program result'):
            pending.read()
        retained = host.slot.peek(pending.identity)
        self.assertEqual((host.slot.state, retained.outcome, retained.rx_bits),
                         ('completed', 'complete', (True,)))
        self.assertIs(host.slot.peek(pending.identity), retained)
        pending.release()
        self.assertEqual(host.slot.state, 'free')

    def test_host_wait_timeout_retains_self_loop_until_explicit_engine_failure(self):
        p = program((I('checked', 2, finish=0), I('halt')))
        host = BufferedModelHost()
        loaded = host.load(p)
        pending = loaded.submit(tx=b'', peer=HighPeer())
        with self.assertRaises(HostWaitTimeout) as raised:
            pending.wait(timeout_cycles=7)
        self.assertIs(raised.exception.pending, pending)
        self.assertEqual(host.slot.state, 'running')
        with self.assertRaises(TransferError): pending.release()
        host._simulation.engine.fail('timeout')
        result = pending.read()
        self.assertEqual((result.outcome, result.payload), ('timeout', None))
        pending.release()
        self.assertEqual(host.slot.state, 'free')

    def test_reset_invalidates_reactive_engine_without_advancing_sampler_or_data(self):
        p = program((I('wait', budget=20), I('halt')))
        slot, _, engine = start(p)
        slot.reset()
        before = (engine.cycle, engine._first, engine._second, engine.samples)
        with self.assertRaises(TransferError): engine.step(0)
        self.assertEqual((engine.cycle, engine._first, engine._second, engine.samples), before)

    def test_program_key_binds_bounds_controls_and_schedule_metadata(self):
        p = program((I('checked', 2, check_mask=1, check_value=1), I('halt')))
        self.assertNotEqual(p.key, replace(p, max_rx_bits=1).key)
        self.assertNotEqual(p.key, replace(p, schedule=BufferedBlock((
            I('checked', 2, check_mask=2, check_value=2), I('halt')))).key)
        with self.assertRaises(FrozenInstanceError): p.max_rx_bits = 2
        with self.assertRaises(ValueError):
            BufferedRepeat(9, BufferedBlock((I('halt'),)))
        with self.assertRaises(ValueError):
            replace(p, schedule=BufferedRepeat(2, BufferedRepeat(2,
                BufferedRepeat(2, BufferedBlock((I('halt'),))))))
        with self.assertRaises(ValueError):
            replace(p, schedule=BufferedBlock((I('drive'),) * 129))
        with self.assertRaises(ValueError): p.execution_edges
        with self.assertRaises(ValueError):
            I('wait', entry_capture=(0, 0))
        with self.assertRaises(ValueError):
            replace(p, schedule=BufferedBlock((I('checked', 257), I('halt'))))

    def test_final_virtual_address_normalizes_both_branch_endpoints_before_entry(self):
        first = I('checked', entry_capture=(0, 0), finish=1023)
        last = I('checked', entry_capture=(0, 1), append_input=0,
                 finish=(0, 0, None))
        body = BufferedBlock((first,) + (I('drive'),) * 14 + (last,))
        code = BufferedRepeat(8, BufferedRepeat(8, body))
        p = BufferedProgram((), schedule=code, declared_tx_bits=0,
                            declared_rx_bits=1, max_rx_bits=1)
        self.assertEqual((code.span, code.nodes, code.nesting), (1024, 33, 2))
        slot, identity, engine = start(p)
        self.assertTrue(engine.samples[0])  # Valid selected branch target is zero.
        engine.step(3)
        packet = slot.peek(identity)
        self.assertEqual((packet.outcome, packet.tx_consumed_bits, packet.rx_bits),
                         ('fault', 0, ()))
        self.assertEqual(engine.samples[:2], (True, False))

        # An ordinary sequential finish remains representable at PC1023. Its
        # entry effects happen; fault occurs only when the final duration ends.
        body = replace(body, instructions=body.instructions[:-1] +
                       (replace(last, finish=None),))
        p = replace(p, schedule=BufferedRepeat(8, BufferedRepeat(8, body)))
        slot, identity, engine = start(p)
        engine.step(3)
        self.assertEqual((engine.pc, slot.state, slot._rx), (1023, 'running', (True,)))
        engine.step(3)
        self.assertEqual(slot.peek(identity).outcome, 'fault')


if __name__ == '__main__':
    unittest.main()
