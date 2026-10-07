"""Pin-only TAP fixtures and mutations; no engine/compiler expected trace."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from jtag_peers import JTAGPeer, TAP
from pad_io import PadObservation


def scan_trace(transmit, half_cycles=4):
    # A target-driven test recipe, independent of Pinwheel's program encoding.
    controls = [(1, 0)] * 5 + [(0, 0), (1, 0), (0, 0), (0, 0)]
    controls += [(int(k == 7), (transmit >> k) & 1) for k in range(8)]
    controls += [(1, 0), (0, 0)]
    trace = []
    for tms, tdi in controls:
        trace += [tdi | (tms << 2)] * half_cycles
        trace += [tdi | 2 | (tms << 2)] * half_cycles
    return trace + [0] * (half_cycles + 1)


def feed(peer, trace, *, enabled=0x1c, unknown_at=None):
    external = 0
    history = []
    samples = 0
    scan_rises = {peer.half_cycles * (19 + 2 * k): k for k in range(8)}
    for cycle, level in enumerate(trace):
        history.append(external)
        physical = level << 2
        observation = PadObservation(1, physical, enabled,
            physical | external | 2, 0xfe if cycle == unknown_at else 255)
        drive = peer.drive(cycle, observation, 4)
        if cycle in scan_rises:
            # The fixture models the two-register package sampling boundary.
            samples |= history[max(0, cycle - 2)] << scan_rises[cycle]
        external = (drive.levels & 1) if drive.enabled & 1 else 1
    return samples


class JTAGPinPeerTests(unittest.TestCase):
    def test_all_payloads_have_delayed_lsb_reply_and_exact_scan(self):
        for byte in range(256):
            received = byte ^ 0x96
            peer = JTAGPeer(byte, received)
            samples = feed(peer, scan_trace(byte))
            result = peer.check(samples)
            self.assertEqual(samples, received)
            self.assertEqual((result['clocks'], result['clock_edges'],
                              result['execution_edges']), (19, 38, 156))
            self.assertEqual(peer.tdo_bits, [(received >> k) & 1 for k in range(8)])
            self.assertEqual(result['tap_states'][4], 'test_logic_reset')

    def test_five_reset_clocks_recover_every_initial_tap_state(self):
        for state in TAP:
            with self.subTest(state=state):
                peer = JTAGPeer(0xa6, 0x53, initial_state=state)
                peer.check(feed(peer, scan_trace(0xa6)))

    def test_boundary_receive_delay_contract(self):
        for period, delay in ((3, 0), (4, 1), (7, 4)):
            peer = JTAGPeer(0xa6, 0x69, half_cycles=period, tco=delay)
            peer.check(feed(peer, scan_trace(0xa6, period)))
        with self.assertRaisesRegex(ValueError, 'receive timing'):
            JTAGPeer(0xa6, 0x69, half_cycles=4, tco=2)

    def test_wrong_navigation_and_missing_final_exit_are_rejected(self):
        for phase in (6, 16):
            trace = scan_trace(0xa6)
            # Corrupt the selected full clock's TMS without changing its period.
            for cycle in range(8 * phase, 8 * (phase + 1)):
                trace[cycle] ^= 4
            with self.subTest(phase=phase), self.assertRaisesRegex(RuntimeError, 'TMS sequence'):
                feed(JTAGPeer(0xa6, 0x53), trace)

    def test_msb_first_transmit_is_rejected(self):
        reversed_byte = int(f'{0xa6:08b}'[::-1], 2)
        peer = JTAGPeer(0xa6, 0x53)
        feed(peer, scan_trace(reversed_byte))
        with self.assertRaisesRegex(RuntimeError, 'outgoing byte/LSB-first'):
            peer.check()

    def test_wrong_capture_slot_and_extra_capture_bits_are_rejected(self):
        peer = JTAGPeer(0xa6, 0x53)
        samples = feed(peer, scan_trace(0xa6))
        for bad in (samples ^ 1, int(f'{samples:08b}'[::-1], 2), samples | 0x100, True):
            with self.subTest(samples=bad), self.assertRaisesRegex(RuntimeError, 'capture slots'):
                peer.check(bad)

    def test_wrong_clock_spacing_and_high_phase_control_changes_are_rejected(self):
        trace = scan_trace(0xa6)
        trace[12] = trace[11]  # Extend a high half period by one edge.
        with self.assertRaisesRegex(RuntimeError, 'half-period timing'):
            feed(JTAGPeer(0xa6, 0x53), trace)
        trace = scan_trace(0xa6)
        trace[77] ^= 1  # Change TDI inside the first scan bit's high period.
        with self.assertRaisesRegex(RuntimeError, 'low-clock phase'):
            feed(JTAGPeer(0xa6, 0x53), trace)

    def test_resolved_contention_and_released_controller_pad_are_rejected(self):
        with self.assertRaisesRegex(RuntimeError, 'Unknown resolved pad 0'):
            feed(JTAGPeer(0xa6, 0x53), scan_trace(0xa6), unknown_at=76)
        with self.assertRaisesRegex(RuntimeError, 'drive TDI2/TCK3/TMS4|driven TMS'):
            feed(JTAGPeer(0xa6, 0x53), scan_trace(0xa6), enabled=0x18)

    def test_truncated_scan_and_short_final_hold_are_rejected(self):
        for count in (80, 155):
            peer = JTAGPeer(0xa6, 0x53)
            feed(peer, scan_trace(0xa6)[:count])
            with self.subTest(count=count), self.assertRaisesRegex(RuntimeError, 'final idle hold'):
                peer.check()

    def test_additional_clock_after_completed_scan_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, 'additional clock'):
            feed(JTAGPeer(0xa6, 0x53), scan_trace(0xa6) + [2])

    def test_invalid_bytes_timing_and_state_fail_before_observation(self):
        for byte in (-1, 256, True, '1'):
            with self.assertRaises(ValueError):
                JTAGPeer(byte, 0x53)
            with self.assertRaises(ValueError):
                JTAGPeer(0xa6, byte)
        for settings in ({'half_cycles': 0}, {'half_cycles': True}, {'tco': -1},
                         {'tco': True}, {'initial_state': 'unknown'}):
            with self.assertRaises(ValueError):
                JTAGPeer(0xa6, 0x53, **settings)


if __name__ == '__main__':
    unittest.main()
