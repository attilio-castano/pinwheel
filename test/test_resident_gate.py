"""Independent pin-oracle controls; real RTL acceptance lives in the gate."""
from pathlib import Path
import runpy
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))

from pad_io import PadObservation
from resident_peers import ResidentSPIPeer, ResidentUARTPeer


def pads(levels, status=1, enabled=0x1c):
    return PadObservation(status, levels << 2, enabled, (levels << 2) | 3, 255)


def uart_symbols(byte, period):
    return [bit for bit in (0, *((byte >> k) & 1 for k in range(8)), 1)
            for _ in range(period)]


def feed_uart(peer, trace):
    for cycle, bit in enumerate(trace):
        peer.drive(cycle, pads(4 | bit), 4)
    peer.drive(len(trace), pads(5, status=0), 4)


def feed_spi(peer, byte, *, duplicate_clock=False):
    for cycle in range(69):
        if cycle == 68:
            level = 4
        else:
            at = cycle + int(duplicate_clock and cycle >= 15)
            clock = (at // 4) % 2 if at < 64 else 0
            slot = min(cycle // 8, 7)
            mosi = (byte >> (7 - slot)) & 1 if cycle < 64 else 0
            level = mosi | clock << 1
        peer.drive(cycle, pads(level, status=int(cycle < 68)), 4)


class ResidentPinOracles(unittest.TestCase):
    def test_uart_all_values_have_exact_frame_duration(self):
        for byte in range(256):
            peer = ResidentUARTPeer(byte)
            feed_uart(peer, uart_symbols(byte, 4))
            result = peer.check()
            self.assertEqual(result['execution_edges'], 40)
            self.assertEqual(result['finished_at'] - result['started_at'], 40)

    def test_uart_changed_payload_is_rejected(self):
        peer = ResidentUARTPeer(0xa6)
        with self.assertRaisesRegex(RuntimeError, 'pin waveform'):
            feed_uart(peer, uart_symbols(0x53, 4))

    def test_uart_shift_on_hold_is_rejected(self):
        trace = uart_symbols(0xa6, 4)
        trace[5] ^= 1  # A retained data symbol changes after one held edge.
        with self.assertRaisesRegex(RuntimeError, 'pin waveform'):
            feed_uart(ResidentUARTPeer(0xa6), trace)

    def test_uart_incomplete_frame_and_released_drive_are_rejected(self):
        peer = ResidentUARTPeer(0xa6)
        for cycle, bit in enumerate(uart_symbols(0xa6, 4)[:20]):
            peer.drive(cycle, pads(4 | bit), 4)
        with self.assertRaisesRegex(RuntimeError, 'complete frame'):
            peer.check()
        with self.assertRaisesRegex(RuntimeError, 'output enables'):
            peer.drive(20, pads(5, enabled=0), 4)

    def test_uart_busy_extending_past_stop_is_rejected(self):
        peer = ResidentUARTPeer(0xa6)
        for cycle, bit in enumerate(uart_symbols(0xa6, 4)):
            peer.drive(cycle, pads(4 | bit), 4)
        with self.assertRaisesRegex(RuntimeError, 'busy exceeded'):
            peer.drive(40, pads(5, status=1), 4)

    def test_spi_all_values_and_high_phase_decoys(self):
        for byte in range(256):
            peer = ResidentSPIPeer(byte, byte ^ 255)
            feed_spi(peer, byte)
            result = peer.check()
            self.assertEqual(result['clock_edges'], 16)
            self.assertEqual(result['high_phase_decoy_edges'], 32)
            self.assertTrue(result['within_receive_timing_contract'])

    def test_spi_wrong_payload_and_clock_spacing_are_rejected(self):
        peer = ResidentSPIPeer(0xa6, 0x96)
        feed_spi(peer, 0x53)
        with self.assertRaisesRegex(RuntimeError, 'outgoing byte'):
            peer.check()
        peer = ResidentSPIPeer(0xa6, 0x96)
        feed_spi(peer, 0xa6, duplicate_clock=True)
        with self.assertRaisesRegex(RuntimeError, 'clock spacing'):
            peer.check()

    def test_invalid_peer_payloads_fail_before_observation(self):
        for value in (-1, 256, True, '1'):
            with self.assertRaises(ValueError):
                ResidentUARTPeer(value)


class ResidentSerialOracle(unittest.TestCase):
    def test_partial_start_has_exact_prefix_and_no_frame_completion(self):
        namespace = runpy.run_path(str(ROOT/'scripts/check-resident-programs.py'))
        send_partial_start = namespace['send_partial_start']

        class SerialRecorder:
            phase_cycles = 2
            ui = 4

            def __init__(self):
                self.observations = []

            def advance(self, cycles):
                self.observations.append((self.ui, cycles))

        for bits in (0, 7, 8, 64, 71):
            host = SerialRecorder()
            send_partial_start(host, 0xa6, bits)
            self.assertEqual(host.observations[-1], (4 | (host.ui & ~7), 4))
            clocks = [ui for ui, _ in host.observations[:-1] if ui & 1]
            expected = (5 << 64) | 0xa6
            self.assertEqual([ui >> 1 & 1 for ui in clocks],
                             [(expected >> shift) & 1 for shift in range(71, 71 - bits, -1)])
        for bits in (-1, 72, True):
            with self.assertRaises(ValueError):
                send_partial_start(SerialRecorder(), 0xa6, bits)


if __name__ == '__main__':
    unittest.main()
