"""Resolved-wire controls for the independent I2C peer, without an engine model."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from pad_io import PadDrive, PadObservation
from streaming_ready_peers import StreamingI2cPeer, expected_rx, payloads
from streaming_ready_transport import pack_read, pack_write, project


class ResolvedBench:
    """An external open-drain bitbanger, not the source or typed controller."""
    def __init__(self, peer):
        self.peer, self.cycle, self.drive = peer, 0, PadDrive(links=3)
        self.pads = PadObservation(0, 0, 0, 255, 255)
        self.drive = peer.drive(0, self.pads)

    def step(self, scl_low, sda_low):
        self.cycle += 1
        wires = 255
        if scl_low or self.drive.enabled & 1: wires &= ~5
        if sda_low or self.drive.enabled & 2: wires &= ~10
        self.pads = PadObservation(0, 0, (4 if scl_low else 0) | (8 if sda_low else 0), wires, 255)
        self.pads.validate_drive(self.drive)
        self.drive = self.peer.drive(self.cycle, self.pads)
        return self.pads

    def hold(self, scl_low, sda_low, edges):
        for _ in range(edges): self.step(scl_low, sda_low)

    def transaction(self, *, first_low_extra=0, high_extra=0, abort_slot=None):
        peer, plan = self.peer, self.peer.plan
        self.hold(False, False, 3)
        self.hold(False, True, peer.low_cycles + peer.high_cycles)
        for index, bit in enumerate(plan.tx_bits):
            self.hold(True, not bit, peer.low_cycles + 1 + (first_low_extra if index == 0 else 0))
            if index == abort_slot:
                self.hold(False, not bit, peer.wait_budget + 2)
                self.hold(False, False, 3)
                return
            for _ in range(1000):
                if self.step(False, not bit).bit(0): break
            else: raise RuntimeError('Bitbanger did not observe resolved SCL HIGH')
            self.hold(False, not bit, peer.high_cycles - 1 + high_extra)
        self.hold(True, True, 2 * (peer.low_cycles + peer.high_cycles))
        for _ in range(1000):
            if self.step(False, True).bit(0): break
        else: raise RuntimeError('STOP did not observe SCL HIGH')
        self.hold(False, True, peer.high_cycles)
        self.hold(False, False, 2)


class ReadyPeerTests(unittest.TestCase):
    def test_independent_patterns_include_order_and_open_drain_extremes(self):
        write, read = payloads()
        self.assertEqual(len(write), 64)
        self.assertEqual(len(read), 64)
        self.assertEqual(write[:4], b'\x00\xff\x80\x01')
        self.assertNotEqual(write, read)

    def test_resolved_sixty_four_byte_read_and_write(self):
        write, read = payloads()
        for plan in (pack_write(0x52, write), pack_read(0x52, 64)):
            peer = StreamingI2cPeer(plan, read)
            bench = ResolvedBench(peer)
            bench.transaction(first_low_extra=10)
            raw = expected_rx(plan, read)
            result = peer.check(raw, require_host_stall=True)
            self.assertEqual(result['physical_data_rises'], 585)
            self.assertEqual(result['stop_preparation_rises'], 1)
            self.assertEqual(result['stop_count'], 1)
            self.assertTrue(project(plan, raw).payload_valid)

    def test_target_stretch_and_host_low_stall_have_distinct_evidence(self):
        write, read = payloads()
        plan = pack_read(0x52, 64)
        peer = StreamingI2cPeer(plan, read, profile='varying')
        bench = ResolvedBench(peer)
        bench.transaction(first_low_extra=20)
        result = peer.check(expected_rx(plan, read), require_host_stall=True)
        self.assertGreater(result['host_low_extra_edges'], 0)
        self.assertGreater(result['target_stretch_edges'], 0)
        self.assertTrue(any(record['slot'] == 585 for record in result['stretches']))
        self.assertTrue(all(record['stimulus'] == 'resolved fall timer' for record in result['stretches']))

    def test_last_poll_uses_only_declared_public_release_alignment(self):
        write, read = payloads()
        plan = pack_read(0x52, 64)
        peer = StreamingI2cPeer(plan, read, profile='lastpoll')
        bench = ResolvedBench(peer)
        bench.transaction()
        result = peer.check(expected_rx(plan, read))
        alignment = result['deadline_alignment']
        self.assertEqual(alignment['slot'], 11)
        self.assertEqual(alignment['release_callback'], alignment['master_release'] + 28)
        self.assertEqual(alignment['expected_stage2_ready'], alignment['expected_last_poll'])
        self.assertIn('no private state', alignment['access'])

    def test_timeout_has_50_captures_and_no_required_stop(self):
        write, read = payloads()
        plan = pack_read(0x52, 64)
        peer = StreamingI2cPeer(plan, read, profile='timeout')
        bench = ResolvedBench(peer)
        bench.transaction(abort_slot=50)
        raw = expected_rx(plan, read)[:50]
        result = peer.check(raw, fault=True)
        self.assertEqual(result['physical_data_rises'], 50)
        self.assertEqual(result['stop_count'], 0)
        self.assertEqual(len(project(plan, raw, fault=True).partial_data_bits), 5)
        with self.assertRaises(RuntimeError): peer.check(expected_rx(plan, read)[:51], fault=True)

    def test_address_nack_ignores_payload_but_preserves_all_raw_slots(self):
        write, read = payloads()
        for plan in (pack_read(0x52, 64), pack_write(0x52, write)):
            peer = StreamingI2cPeer(plan, read, address_ack=False)
            bench = ResolvedBench(peer)
            bench.transaction()
            raw = expected_rx(plan, read, address_ack=False)
            self.assertFalse(peer.check(raw)['payload_accepted'])
            result = project(plan, raw)
            self.assertFalse(result.payload_valid)
            self.assertEqual(result.data, b'')
            if plan.direction == 'write':
                self.assertTrue(all(raw[index] for index in range(8, 585, 9)))

    def test_wrong_data_and_high_stalls_are_distinguishing_failures(self):
        write, read = payloads()
        plan = pack_write(0x52, write)
        peer = StreamingI2cPeer(plan, read)
        bench = ResolvedBench(peer)
        with self.assertRaisesRegex(RuntimeError, 'HIGH phase'):
            bench.transaction(high_extra=8)
        peer = StreamingI2cPeer(plan, read)
        bench = ResolvedBench(peer)
        bench.hold(False, False, 3)
        bench.hold(False, True, 8)
        bench.hold(True, True, 5)  # Address MSB should be released1.
        with self.assertRaisesRegex(RuntimeError, 'slot 0'): bench.step(False, True)

    def test_high_phase_sda_glitch_and_push_pull_drive_refused(self):
        plan = pack_read(0x52, 1)
        peer = StreamingI2cPeer(plan, b'x')
        bench = ResolvedBench(peer)
        bench.hold(False, False, 2)
        bench.hold(False, True, 8)
        with self.assertRaisesRegex(RuntimeError, 'early STOP'): bench.step(False, False)
        peer = StreamingI2cPeer(plan, b'x')
        with self.assertRaisesRegex(RuntimeError, 'HIGH'):
            peer.drive(0, PadObservation(0, 4, 4, 255, 255))

    def test_short_low_cannot_claim_sampler_freshness(self):
        plan = pack_read(0x52, 1)
        for options in (dict(low_cycles=3), dict(wait_budget=2), dict(profile='lastpoll', deadline_slot=18)):
            with self.assertRaises(ValueError): StreamingI2cPeer(plan, b'x', **options)


if __name__ == '__main__': unittest.main()
