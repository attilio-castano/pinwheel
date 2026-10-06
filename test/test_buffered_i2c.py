"""Reactive buffered I2C against a target that only observes resolved pads."""
from dataclasses import replace
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from buffered_engine import (BufferedBlock, BufferedEngine, BufferedInstruction,
                             BufferedProgram, BufferedRepeat, BufferedSequence,
                             BufferedWireSimulation)
from buffered_i2c import buffered_i2c_read, register_read_tx, run_witness
from buffered_i2c_peer import BufferedI2CReadPeer, BufferedI2CWireError
from pinwheel_buffers import (BufferedModelHost, HostWaitTimeout, TransferError,
                              TransferSlot)
from pinwheel_host import Host


REPLY = b'\x96\xa5\x55\x3c'


def start(program=None, peer=None, *, address=0x53, register=0xa6):
    program = program or buffered_i2c_read()
    peer = peer or BufferedI2CReadPeer(address, register, REPLY)
    slot = TransferSlot(tx_capacity_bits=32, rx_capacity_bits=max(32, program.rx_bits))
    identity = slot.begin(program.key, program.encode_tx(register_read_tx(address, register)),
                          program.rx_bits)
    wire = BufferedWireSimulation(BufferedEngine(slot, identity, program), peer)
    return slot, identity, wire, peer


def replace_part(program, index, part):
    pieces = list(program.schedule.parts)
    pieces[index] = part
    return replace(program, schedule=BufferedSequence(tuple(pieces)))


class BufferedI2CTests(unittest.TestCase):
    def test_four_byte_read_has_compact_bit_byte_loops_and_no_hardware_upload(self):
        program = buffered_i2c_read()
        self.assertEqual(program.instructions, ())
        self.assertEqual(program.storage(), dict(virtual_slots=270, instruction_words=50,
                         control_nodes=55, stored_nodes=105, repeat_nodes=6, nesting=2,
                         expanded_at_runtime=False, target='buffered-reference-v1'))
        self.assertEqual((program.tx_bits, program.rx_bits, program.rx_reservation_bits),
                         (24, 32, 32))
        with self.assertRaisesRegex(ValueError, 'explicit host wait horizon'):
            _ = program.execution_edges

        class NoIO:
            def advance(self, *args, **kwargs):
                raise AssertionError('Buffered I2C touched current hardware transport')
        with self.assertRaisesRegex(ValueError, 'image format'):
            Host(NoIO()).upload(program)

    def test_reuse_one_program_with_different_address_register_and_reply_bytes(self):
        host = BufferedModelHost()
        loaded = host.load(buffered_i2c_read())
        key = loaded.program_key
        payloads = (bytes(4), b'\xff' * 4, REPLY, b'\x80\x01\x55\xaa',
                    b'\x01\x02\x04\x08', b'\x10\x20\x40\x80')
        for address, register in ((0, 0), (0, 255), (127, 0), (127, 255), (0x53, 0xa6)):
            for reply in payloads:
                with self.subTest(address=address, register=register, reply=reply):
                    peer = BufferedI2CReadPeer(address, register, reply)
                    tx = bytearray(register_read_tx(address, register))
                    pending = loaded.submit(tx=tx, peer=peer)
                    tx[:] = bytes(3)  # the accepted control bytes were copied
                    pending.wait(timeout_cycles=10_000)
                    result = pending.read()
                    peer.check(result.raw_rx_bits)
                    self.assertEqual(result.payload, reply)
                    self.assertEqual((result.outcome, result.tx_consumed_bits,
                                      result.rx_valid_bits), ('complete', 24, 32))
                    self.assertEqual(loaded.program_key, key)
                    frozen = result
                    pending.release()
                    self.assertEqual(result, frozen)
                    self.assertEqual(host.slot.state, 'free')

    def test_each_reply_lane_exercises_every_byte_value(self):
        program = buffered_i2c_read()
        for lane in range(4):
            for value in range(256):
                reply = bytearray(REPLY)
                reply[lane] = value
                peer = BufferedI2CReadPeer(0x53, 0xa6, bytes(reply))
                _, _, wire, _ = start(program, peer)
                completion = wire.run(2000)
                peer.check(completion.rx_bits)
                self.assertEqual(program.decode_rx(completion.rx_bits), bytes(reply))
                self.assertEqual((wire.cycle, len(peer.bits), peer.starts), (993, 63, 2))

    def test_parameterized_receive_lengths_do_not_clock_padding(self):
        for count in (1, 2, 3, 4, 7, 8):
            reply = bytes((0x81 ^ (index * 23)) & 255 for index in range(count))
            result = run_witness(reply=reply)
            self.assertEqual((result['sampled_bits'], result['rx_valid_bits']),
                             (27 + 9 * count, 8 * count))
            self.assertLessEqual(result['storage']['stored_nodes'], 256)
            self.assertEqual(result['storage']['nesting'], 2)

    def test_all_control_nack_positions_stop_before_retaining_fault(self):
        for stage in range(3):
            ack = tuple(int(index == stage) for index in range(3))
            peer = BufferedI2CReadPeer(0x53, 0xa6, REPLY, ack)
            host = BufferedModelHost()
            pending = host.load(buffered_i2c_read()).submit(tx=register_read_tx(0x53, 0xa6),
                                                          peer=peer)
            pending.wait(timeout_cycles=2000)
            result = pending.read()
            report = peer.check(result.raw_rx_bits)
            self.assertEqual((result.outcome, result.payload, result.rx_valid_bits),
                             ('fault', None, 0))
            self.assertEqual((result.tx_consumed_bits, report['sampled_bits']),
                             (8 * (stage + 1), 9 * (stage + 1)))
            self.assertTrue(report['stopped'])
            self.assertEqual(report['starts'], 1 if stage < 2 else 2)
            with self.assertRaises(TransferError):
                pending.host.slot.append_rx(pending.identity, False)
            self.assertEqual(pending.read(), result)
            pending.release()

    def test_clock_stretching_preserves_complete_high_and_low_intervals(self):
        for H, stretch in ((3, 0), (3, 5), (4, 1), (4, 15), (7, 28), (4, 30)):
            result = run_witness(phase_cycles=H, wait_cycles=32, stretch_cycles=stretch)
            self.assertEqual(result['outcome'], 'complete')
            self.assertEqual((result['rx_valid_bits'], result['sampled_bits']), (32, 63))
            self.assertTrue(result['stopped'])
            self.assertEqual(result['stretch_events'], 65 if stretch else 0)
        # The ready observation on the final budget edge succeeds. One more
        # callback cycle of stretching yields a retained timeout instead.
        at_boundary = run_witness(wait_cycles=4, stretch_cycles=2)
        beyond_boundary = run_witness(wait_cycles=4, stretch_cycles=3)
        self.assertEqual((at_boundary['outcome'], beyond_boundary['outcome']),
                         ('complete', 'timeout'))
        self.assertFalse(beyond_boundary['stopped'])

    def test_initial_stuck_bus_prevents_start_and_reports_timeout(self):
        result = run_witness(initially_stuck=True)
        self.assertEqual((result['outcome'], result['starts'], result['sampled_bits'],
                          result['tx_consumed_bits'], result['rx_valid_bits']),
                         ('timeout', 0, 0, 0, 0))
        self.assertFalse(result['stopped'])
        self.assertTrue(result['clock_timeout'])

    def test_mid_read_clock_timeout_retains_exact_partial_prefix_and_no_stop(self):
        for clocks, expected_rx in ((27, 0), (37, 9), (54, 24), (62, 32)):
            result = run_witness(never_after_bits=clocks)
            self.assertEqual((result['outcome'], result['sampled_bits'], result['rx_valid_bits']),
                             ('timeout', clocks, expected_rx))
            expected = tuple(bool((byte >> bit) & 1) for byte in REPLY for bit in range(7, -1, -1))
            self.assertEqual(tuple(result['raw_rx_bits']), expected[:expected_rx])
            self.assertFalse(result['stopped'])
            self.assertTrue(result['immutable_completion'])
        host = BufferedModelHost()
        peer = BufferedI2CReadPeer(0x53, 0xa6, REPLY, never_after_bits=37)
        pending = host.load(buffered_i2c_read()).submit(tx=register_read_tx(0x53, 0xa6),
                                                       peer=peer)
        pending.wait(timeout_cycles=2000)
        result = pending.read()
        self.assertEqual((result.outcome, result.payload, result.rx_valid_bits),
                         ('timeout', None, 9))
        peer.check(result.raw_rx_bits, timeout=True)
        host.advance(3)
        self.assertEqual(pending.read(), result)
        self.assertEqual(host.slot.state, 'completed')
        pending.release()

    def test_missing_stop_due_to_sda_stuck_never_reports_success(self):
        result = run_witness(stop_sda_stuck=True)
        self.assertEqual((result['outcome'], result['sampled_bits'], result['rx_valid_bits']),
                         ('timeout', 63, 32))
        self.assertFalse(result['stopped'])
        self.assertTrue(result['bus_free_timeout'])

    def test_host_wait_budget_preserves_same_pending_read_and_resumes(self):
        host = BufferedModelHost()
        loaded = host.load(buffered_i2c_read())
        peer = BufferedI2CReadPeer(0x53, 0xa6, REPLY, stretch_cycles=5)
        pending = loaded.submit(tx=register_read_tx(0x53, 0xa6), peer=peer)
        with self.assertRaises(HostWaitTimeout) as caught:
            pending.wait(timeout_cycles=800)
        self.assertEqual(caught.exception.pending.identity, pending.identity)
        self.assertEqual(host.slot.state, 'running')
        with self.assertRaises(TransferError):
            pending.release()
        pending.wait(timeout_cycles=2000)
        result = pending.read()
        peer.check(result.raw_rx_bits)
        self.assertEqual(result.payload, REPLY)
        pending.release()

    def test_mutation_final_master_ack_is_rejected_by_wire_oracle(self):
        program = buffered_i2c_read()
        parts = program.schedule.parts
        final_read = parts[5]
        bad_ack = BufferedBlock(tuple(replace(item, enabled=item.enabled | 2)
                                      for item in final_read.parts[1].instructions))
        mutant = replace_part(program, 5, replace(final_read,
                              parts=(final_read.parts[0], bad_ack)))
        _, _, wire, _ = start(mutant)
        with self.assertRaisesRegex(BufferedI2CWireError, 'ACK/NACK order'):
            wire.run(2000)

    def test_mutation_repeated_start_omission_is_rejected(self):
        program = buffered_i2c_read()
        middle = program.schedule.parts[2]
        items = list(middle.instructions)
        items[3] = replace(items[3], enabled=0)  # no SDA falling START
        mutant = replace_part(program, 2, replace(middle, instructions=tuple(items)))
        _, _, wire, _ = start(mutant)
        with self.assertRaisesRegex(BufferedI2CWireError, 'repeated START'):
            wire.run(2000)

    def test_mutation_nack_bypasses_stop_cannot_pass_wire_check(self):
        program = buffered_i2c_read()
        # Fault cleanup keeps identical virtual geometry but immediately halts.
        fault_stop = program.schedule.parts[-1]
        items = (BufferedInstruction('fault'),) + fault_stop.instructions[1:]
        mutant = replace_part(program, len(program.schedule.parts) - 1,
                              replace(fault_stop, instructions=items))
        peer = BufferedI2CReadPeer(0x53, 0xa6, REPLY, (1, 0, 0))
        _, _, wire, _ = start(mutant, peer)
        with self.assertRaisesRegex(BufferedI2CWireError, 'STOP preparation'):
            wire.run(2000)
        self.assertEqual(wire.engine.slot.peek(wire.engine.identity).outcome, 'fault')

    def test_mutation_missing_rx_append_keeps_valid_wires_but_fails_result_oracle(self):
        program = buffered_i2c_read()
        final_read = program.schedule.parts[5]
        body = final_read.parts[0].body
        items = tuple(replace(item, append_input=None) for item in body.instructions)
        bad_bits = replace(final_read.parts[0], body=replace(body, instructions=items))
        mutant = replace_part(program, 5, replace(final_read,
                              parts=(bad_bits, final_read.parts[1])))
        _, _, wire, peer = start(mutant)
        completion = wire.run(2000)
        peer.check()  # framing, clocks, bytes and ACKs are independently valid
        self.assertEqual(len(completion.rx_bits), 24)
        with self.assertRaisesRegex(BufferedI2CWireError, 'appended RX'):
            peer.check(completion.rx_bits)

    def test_mutation_short_stop_setup_is_rejected(self):
        program = buffered_i2c_read()
        stop = program.schedule.parts[-2]
        items = list(stop.instructions)
        # Bypass readiness and shorten high hold: the sampler's normal wait
        # latency otherwise already supplies a legal four-cycle setup window.
        items[1] = BufferedInstruction('drive', 1, enabled=2)
        items[2] = replace(items[2], duration=1, check_mask=0, check_value=0)
        mutant = replace_part(program, len(program.schedule.parts) - 2,
                              replace(stop, instructions=tuple(items)))
        _, _, wire, _ = start(mutant)
        with self.assertRaisesRegex(BufferedI2CWireError, 'STOP high setup'):
            wire.run(2000)

    def test_mutation_short_tx_setup_is_rejected_by_resolved_wire_timing(self):
        program = buffered_i2c_read()
        byte_repeat = program.schedule.parts[1]
        bit_repeat = byte_repeat.body.parts[0]
        items = list(bit_repeat.body.instructions)
        items[0] = replace(items[0], duration=1)
        bad_bits = replace(bit_repeat, body=replace(bit_repeat.body, instructions=tuple(items)))
        bad_byte = replace(byte_repeat.body, parts=(bad_bits, byte_repeat.body.parts[1]))
        mutant = replace_part(program, 1, replace(byte_repeat, body=bad_byte))
        _, _, wire, _ = start(mutant)
        with self.assertRaisesRegex(BufferedI2CWireError, 'SDA setup interval'):
            wire.run(2000)

    def test_invalid_parameters_and_short_rx_reservation_fail_before_start(self):
        for args in (dict(byte_count=0), dict(byte_count=9), dict(byte_count=True),
                     dict(phase_cycles=2), dict(wait_cycles=3), dict(wait_cycles=257)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                buffered_i2c_read(**args)
        for args in ((128, 0), (-1, 0), (0, 256), (True, 0)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                register_read_tx(*args)
        host = BufferedModelHost()
        loaded = host.load(buffered_i2c_read())
        with self.assertRaises(ValueError):
            loaded.submit(tx=register_read_tx(0x53, 0xa6), rx_limit=31)
        self.assertEqual(host.slot.state, 'free')


if __name__ == '__main__':
    unittest.main()
