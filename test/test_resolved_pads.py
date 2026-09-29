"""Exercise real Verilog pad resolution and independent SPI peer rejection."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from pad_io import PadDrive, PadObservation
from pad_peers import SPIPeer, spi_result_bytes
from pinwheel_host import Pins
from pinwheel_sim import Simulation


def observation(levels, enabled=7):
    # Fully observed fixture wires, with independent MISO high on pad0.
    return PadObservation(0, levels << 2, enabled << 2, (levels << 2) | 3, 255)


def exercise_peer(peer, corrupt=None):
    tx = [(byte >> k) & 1 for byte in peer.transmit for k in range(7, -1, -1)]
    for phase in range(2 * len(tx) + 1):
        clock = peer.cpol ^ (phase & 1)
        index = min(phase // 2 if not peer.cpha else max(0, (phase - 1) // 2), len(tx) - 1)
        bit = tx[index] ^ int(corrupt == 'data')
        levels = bit | clock << 1
        for tick in range(peer.half_cycles):
            drive = peer.drive(phase * peer.half_cycles + tick, observation(levels), 0)
            if drive.enabled != 1 or drive.links != 0:
                raise RuntimeError('SPI peer drove more than dedicated MISO0')
    peer.drive((2 * len(tx) + 1) * peer.half_cycles,
               observation(4 | peer.cpol << 1), 0)


class SPIWireChecks(unittest.TestCase):
    def test_all_modes_and_both_byte_counts_accept_specification_waveforms(self):
        for mode in range(4):
            for count in (1, 2):
                with self.subTest(mode=mode, count=count):
                    peer = SPIPeer(mode, (0xa6, 0x53)[:count], (0x96, 0x3c)[:count])
                    exercise_peer(peer)
                    self.assertEqual(peer.check()['sampled_bits'], 8 * count)

    def test_wrong_wire_data_and_early_chip_select_fail(self):
        peer = SPIPeer()
        exercise_peer(peer, corrupt='data')
        with self.assertRaisesRegex(RuntimeError, 'outgoing byte'):
            peer.check()
        peer = SPIPeer()
        peer.drive(0, observation(0), 0)
        peer.drive(4, observation(4), 0)
        with self.assertRaisesRegex(RuntimeError, 'outgoing byte'):
            peer.check()

    def test_wrong_idle_polarity_and_missing_output_ownership_fail(self):
        for peer, pads, message in [(SPIPeer(2), observation(0), 'CPOL'),
                                    (SPIPeer(), observation(0, 4), 'must drive')]:
            with self.subTest(message=message), self.assertRaisesRegex(RuntimeError, message):
                peer.drive(0, pads, 0)

    def test_sample_decode_is_msb_first_and_retains_byte_order(self):
        self.assertEqual(spi_result_bytes(0x69, 1), (0x96,))
        self.assertEqual(spi_result_bytes(0x3c69, 2), (0x96, 0x3c))
        for samples, count in [(1 << 8, 1), (1 << 16, 2), (-1, 1), (0, 3)]:
            with self.subTest(samples=samples, count=count), self.assertRaises(ValueError):
                spi_result_bytes(samples, count)


class PhysicalPadContract(unittest.TestCase):
    def test_old_map_cannot_be_masked_into_a_plausible_logical_interface(self):
        with self.assertRaisesRegex(RuntimeError, 'five-pad'):
            PadObservation(0, 1, 7, 255, 255).logical

    def test_same_value_driver_overlap_and_linked_push_pull_high_fail(self):
        with self.assertRaisesRegex(RuntimeError, 'DUT-owned'):
            PadObservation(0, 4, 4, 255, 255).validate_drive(PadDrive(4, 4))
        with self.assertRaisesRegex(RuntimeError, 'open-drain'):
            PadObservation(0, 4, 4, 255, 255).validate_drive(PadDrive(1, 1, links=1))


class ActualResolvedBridge(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.iverilog = ROOT / 'build/tools/oss-cad-suite/bin/iverilog'
        cls.vvp = ROOT / 'build/tools/oss-cad-suite/bin/vvp'
        if not cls.iverilog.is_file() or not cls.vvp.is_file():
            raise unittest.SkipTest('Pinned Icarus tools unavailable')

    def simulate(self, legacy=False):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        source = root / 'dut.sv'
        mask = 7 if legacy else 28
        source.write_text('module tt_um_pinwheel(input clk,input [7:0] ui_in,uio_in, '
            'input ena,rst_n,output [7:0] uo_out,uio_out,uio_oe); '
            f'assign uio_out=ui_in & 8\'d{mask}; assign uio_oe=8\'d{mask}; '
            'assign uo_out=uio_in; endmodule\n')
        executable = root / 'bridge.vvp'
        result = subprocess.run([str(self.iverilog), '-g2012', '-s', 'host_bridge', '-o',
            str(executable), str(source), str(ROOT / 'test/host_bridge.sv')],
            capture_output=True, text=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return Simulation(self.vvp, executable)

    def test_resolved_inputs_and_physical_output_decode(self):
        with self.simulate() as simulation:
            self.assertEqual(simulation.advance(20, 1), Pins(247, 5, 7))
            self.assertEqual(simulation.observation.levels, 20)
            self.assertEqual(simulation.observation.enabled, 28)
            self.assertEqual(simulation.observation.bit(0), 1)

    def test_linked_open_drain_low_overrides_pullups(self):
        with self.simulate() as simulation:
            simulation._advance(0, PadDrive(0, 3, links=3), 1, 1)
            self.assertEqual(simulation.observation.wires & 15, 0)

    def test_opposing_and_same_value_driver_ownership_fail_in_verilog(self):
        for level in (0, 4):
            with self.subTest(level=level), self.simulate() as simulation:
                with self.assertRaisesRegex(RuntimeError, 'Unknown/contention|DUT-owned'):
                    simulation._advance(4, PadDrive(level, 4), 1, 1)

    def test_linked_push_pull_high_and_floating_inputs_fail_in_verilog(self):
        for ui, drive, message in [(4, PadDrive(0, 0, links=1), 'open-drain'),
                                   (0, PadDrive(pullups=0), 'Unknown/contention')]:
            with self.subTest(message=message), self.simulate() as simulation:
                with self.assertRaisesRegex(RuntimeError, message):
                    simulation._advance(ui, drive, 1, 1)

    def test_old_mosi_pad_cannot_also_receive_different_miso(self):
        # Old MOSI0 drives zero while external MISO0 drives one: a real conflict.
        with self.simulate(legacy=True) as simulation:
            with self.assertRaisesRegex(RuntimeError, 'Unknown/contention'):
                simulation._advance(4, PadDrive(1, 1), 1, 1)


if __name__ == '__main__':
    unittest.main()
