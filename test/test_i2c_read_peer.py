"""Pin-only I2C reference traces and negative controls for the read peer."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))

from i2c_read_peers import I2CReadPeer
from pad_io import PadDrive, PadObservation


class ResolvedFixture:
    """Resolve controller and target low/release commands without chip state.

    The controller schedule below is a direct protocol transaction: address,
    register, repeated START, read address, reply bytes and final NACK/STOP.
    It imports no compiler, instruction decoder or execution oracle.
    """
    def __init__(self, peer):
        self.peer = peer
        self.target = PadDrive(0, 0, links=3)
        self.cycle = 0

    def tick(self, enabled):
        scl = int(not ((enabled & 1) or (self.target.enabled & 1)))
        sda = int(not ((enabled & 2) or (self.target.enabled & 2)))
        wires = 0xf0 | scl | sda << 1 | scl << 2 | sda << 3
        observed = PadObservation(1, 0, enabled << 2, wires, 255)
        self.target = self.peer.drive(self.cycle, observed, 4)
        self.cycle += 1
        return observed

    def hold(self, enabled, duration=4):
        for _ in range(duration):
            self.tick(enabled)

    def high(self, sda_enable=0, duration=4):
        for _ in range(64):
            observed = self.tick(sda_enable)
            if observed.bit(0):
                break
        else:
            raise RuntimeError('Independent I2C controller could not observe released SCL')
        self.hold(sda_enable, duration - 1)

    def start(self, hold=4):
        self.hold(2, hold)

    def clock(self, bit=None, *, ack_drive=False):
        # None leaves SDA to the target. Zero drives low; one releases it.
        data = 2 if bit == 0 or ack_drive else 0
        self.hold(1 | data)
        self.high(data)

    def controller_byte(self, byte, *, drive_ack=False):
        for shift in range(7, -1, -1):
            self.clock((byte >> shift) & 1)
        self.clock(ack_drive=drive_ack)

    def repeated_start(self, setup=4):
        self.hold(1)
        self.high(duration=setup)
        self.start()

    def stop(self):
        self.hold(3)
        self.high(2)
        self.hold(0)


def transaction(peer, *, address=0x53, register=0xa6, initial_free=4,
                start_hold=4, repeated_setup=4, omit_stop=False, drive_address_ack=False):
    fixture = ResolvedFixture(peer)
    fixture.hold(0, initial_free)
    fixture.start(start_hold)
    fixture.controller_byte(address << 1, drive_ack=drive_address_ack)
    if peer.ack_bits[0]:
        fixture.stop()
        return fixture
    fixture.controller_byte(register)
    if peer.ack_bits[1]:
        fixture.stop()
        return fixture
    fixture.repeated_start(repeated_setup)
    fixture.controller_byte((address << 1) | 1)
    if not peer.ack_bits[2]:
        for index in range(len(peer.payload_bytes)):
            for _ in range(8):
                fixture.clock()
            fixture.clock(int(index == len(peer.payload_bytes) - 1))
    if not omit_stop:
        fixture.stop()
    return fixture


class I2CReadPinPeer(unittest.TestCase):
    def test_one_and_two_byte_reads_resolve_target_bytes_and_controller_acks(self):
        for payload in ((0x96,), (0x96, 0x3c), (0, 255), (255, 0)):
            peer = I2CReadPeer(0x53, 0xa6, payload)
            transaction(peer)
            wire = peer.check()
            self.assertEqual(wire['clock_count'], 27 + 9 * len(payload))
            self.assertEqual(wire['starts'], 2)
            self.assertEqual(wire['observed_bits'][35], int(len(payload) == 1))
            self.assertEqual(wire['observed_bits'][-1], 1)
            for index, byte in enumerate(payload):
                self.assertEqual(wire['observed_bits'][27 + 9*index:35 + 9*index],
                                 [(byte >> bit) & 1 for bit in range(7, -1, -1)])

    def test_every_first_nack_stops_before_later_prefix_or_payload(self):
        for count in (1, 2):
            for stage in range(3):
                ack_bits = tuple(int(index == stage) for index in range(3))
                peer = I2CReadPeer(0x53, 0xa6, (0x96, 0x3c)[:count], ack_bits)
                transaction(peer)
                wire = peer.check()
                self.assertEqual(wire['clock_count'], 9 * (stage + 1))
                self.assertEqual(wire['starts'], 1 if stage < 2 else 2)
                self.assertEqual(wire['observed_bits'][-1], 1)

    def test_clock_stretching_is_observed_on_real_resolved_lines(self):
        peer = I2CReadPeer(0x53, 0xa6, (0x96, 0x3c), stretch_cycles=3)
        transaction(peer)
        wire = peer.check()
        self.assertEqual(wire['clock_count'], 45)
        self.assertGreater(wire['stretch_events'], 45)

    def test_wrong_address_and_missing_stop_are_rejected(self):
        peer = I2CReadPeer(0x53, 0xa6, (0x96,))
        transaction(peer, address=0x52)
        with self.assertRaisesRegex(RuntimeError, 'wire bytes'):
            peer.check()
        peer = I2CReadPeer(0x53, 0xa6, (0x96, 0x3c))
        transaction(peer, omit_stop=True)
        with self.assertRaisesRegex(RuntimeError, 'wire bytes'):
            peer.check()

    def test_controller_driving_a_target_owned_ack_is_rejected(self):
        peer = I2CReadPeer(0x53, 0xa6, (0x96,))
        with self.assertRaisesRegex(RuntimeError, 'target-owned ACK/data'):
            transaction(peer, drive_address_ack=True)

    def test_short_initial_bus_free_and_start_hold_are_rejected(self):
        peer = I2CReadPeer(0x53, 0xa6, (0x96,))
        with self.assertRaisesRegex(RuntimeError, 'START setup interval'):
            transaction(peer, initial_free=1)
        peer = I2CReadPeer(0x53, 0xa6, (0x96,))
        with self.assertRaisesRegex(RuntimeError, 'START hold'):
            transaction(peer, start_hold=1)

    def test_short_repeated_start_setup_is_rejected(self):
        peer = I2CReadPeer(0x53, 0xa6, (0x96,))
        with self.assertRaisesRegex(RuntimeError, 'START setup interval'):
            transaction(peer, repeated_setup=1)

    def test_active_high_drive_and_initial_stuck_clock(self):
        peer = I2CReadPeer(0x53, 0xa6, (0x96,))
        with self.assertRaisesRegex(RuntimeError, 'only low/release'):
            peer.drive(0, PadObservation(1, 8, 8, 255, 255), 4)
        peer = I2CReadPeer(0x53, 0xa6, (0x96,), scl_stuck=True)
        fixture = ResolvedFixture(peer)
        fixture.hold(0, 20)
        wire = peer.check(timeout=True)
        self.assertEqual(wire['clock_count'], 0)
        self.assertEqual(wire['starts'], 0)

    def test_guard_clock_loss_interrupts_the_declared_wire_prefix(self):
        peer = I2CReadPeer(0x53, 0xa6, (0x96,), fault_after_rises=1, fault_delay_cycles=2)
        fixture = ResolvedFixture(peer)
        fixture.hold(0)
        fixture.start()
        fixture.clock(1)  # First MSB of the address/write byte.
        fixture.hold(0, 8)
        wire = peer.check(fault=True)
        self.assertEqual(wire['clock_count'], 1)
        self.assertFalse(wire['stopped'])


if __name__ == '__main__':
    unittest.main()
