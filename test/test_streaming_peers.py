"""Independent physical-edge target controls; no program or controller oracle."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from pad_io import PadDrive, PadObservation
from streaming_peers import StreamingJTAGPeer, StreamingSPIPeer


class Wires:
    def __init__(self, peer):
        self.peer, self.cycle, self.drive = peer, 0, PadDrive()

    def hold(self, levels, count):
        for _ in range(count):
            self.cycle += 1
            wires = (levels << 2) | (self.drive.levels & 3)
            pads = PadObservation(0, levels << 2, 7 << 2, wires, 255)
            pads.validate_drive(self.drive)
            self.drive = self.peer.drive(self.cycle, pads)


def spi_wave(peer, *, stall=0, high_extra=0, wrong_data=False):
    wires = Wires(peer)
    wires.hold(4, 4)
    wires.hold(0, 4)
    for index, bit in enumerate(peer.expected):
        value = int(bit) ^ int(wrong_data and index == 3)
        wires.hold(value, 5 + (stall if index == 4 else 0))
        wires.hold(value | 2, 4 + high_extra)
    wires.hold(int(peer.expected[-1]) if peer.expected else 0, 6)
    wires.hold(4, 5)
    return wires


def jtag_wave(peer, *, stall=0, high_extra=0, wrong_last=False):
    wires = Wires(peer)
    profile = [1] * 5 + [0, 1, 0, 0] + [0] * (peer.bit_count - 1) + [1, 1, 0]
    if wrong_last:
        profile[peer.bit_count + 8] = 0
    for index, tms in enumerate(profile):
        tdi = (peer.transmit >> (index - 9)) & 1 if 9 <= index < peer.bit_count + 9 else 0
        levels = (tms << 2) | tdi
        wires.hold(levels, 5 + (stall if index == 11 else 0))
        wires.hold(levels | 2, 4 + high_extra)
    wires.hold(0, 6)
    return wires


class StreamingPeerTests(unittest.TestCase):
    def test_spi_accepts_low_stalls_and_checks_all_bytes(self):
        peer = StreamingSPIPeer(b'\x96\xa5', b'\x3c\xc3')
        spi_wave(peer, stall=37)
        result = peer.check(peer.reply, require_stall=True)
        self.assertEqual(result['bits'], 16)
        self.assertEqual(result['high_phase_edges'], [4])
        self.assertEqual(result['low_extra_edges'], 37)
        self.assertEqual(result['low_max_edges'], 42)

    def test_spi_rejects_high_stall_data_mutation_and_wrong_receive(self):
        with self.assertRaisesRegex(RuntimeError, 'high phase'):
            spi_wave(StreamingSPIPeer(b'\xa5', b'\x96'), high_extra=1)
        peer = StreamingSPIPeer(b'\xa5', b'\x96')
        spi_wave(peer, wrong_data=True)
        with self.assertRaisesRegex(RuntimeError, 'transmitted data'):
            peer.check(peer.reply)
        peer = StreamingSPIPeer(b'\xa5', b'\x96')
        spi_wave(peer)
        with self.assertRaisesRegex(RuntimeError, 'received data'):
            peer.check(tuple(not bit for bit in peer.reply))

    def test_zero_length_spi_has_no_data_clocks(self):
        peer = StreamingSPIPeer(b'', b'')
        spi_wave(peer)
        self.assertEqual(peer.check(())['clock_edges'], 0)

    def test_jtag_nonbyte_last_bit_and_low_stall(self):
        peer = StreamingJTAGPeer(0x196a5, 0x13cc3, 17)
        jtag_wave(peer, stall=53)
        expected = tuple(bool((peer.receive >> bit) & 1) for bit in range(17))
        result = peer.check(expected, require_stall=True)
        self.assertEqual(result['bits'], 17)
        self.assertEqual(result['clock_edges'], 56)
        self.assertEqual(result['high_phase_edges'], [4])
        self.assertEqual(result['capture_count'], 1)
        self.assertEqual(result['update_count'], 1)

    def test_jtag_rejects_high_stall_and_last_tms_mutation(self):
        with self.assertRaisesRegex(RuntimeError, 'high phase'):
            jtag_wave(StreamingJTAGPeer(1, 0, 1), high_extra=1)
        with self.assertRaisesRegex(RuntimeError, 'last-bit TMS'):
            jtag_wave(StreamingJTAGPeer(0x96, 0xa5, 8), wrong_last=True)
        with self.assertRaises(ValueError): StreamingJTAGPeer(0, 0, 0)

    def test_long_nonbyte_peer_uses_one_shift_and_one_update(self):
        bits = 4097
        tx = (int.from_bytes(bytes(range(256)) * 2 + b'\x01', 'little')) & ((1 << bits) - 1)
        rx = ((1 << bits) - 1) ^ tx
        peer = StreamingJTAGPeer(tx, rx, bits)
        jtag_wave(peer, stall=29)
        result = peer.check(tuple(bool((rx >> bit) & 1) for bit in range(bits)), require_stall=True)
        self.assertEqual(result['clocks'], bits + 11)
        self.assertEqual(peer.updated, tx)


if __name__ == '__main__':
    unittest.main()
