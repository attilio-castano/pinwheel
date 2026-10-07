"""Physical pin parsing, timing, ownership and subprocess boundaries."""
from dataclasses import asdict
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from buffered_sram_serial_rtl import (BufferedSramSerialRTL, OBSERVATION_WIDTHS,
                                       PIN_WIDTHS, SerialPinSnapshot)
from pad_io import PadDrive, PadObservation

CAD = ROOT / 'build/tools/oss-cad-suite/bin'


class SerialPinBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory(prefix='pinwheel-serial-pins-')
        self.addCleanup(self.folder.cleanup)

    def backend(self, source=None, **options):
        if source is None:
            source = '''import sys
for line in sys.stdin:
    fields = list(map(int, line.split()))
    print('SRAM_SERIAL 1 0 0 0 0 255 255 3', flush=True)
'''
        path = Path(self.folder.name) / 'pin_pipe.py'
        path.write_text(source)
        simulation = BufferedSramSerialRTL(Path(sys.executable), path, **options)
        self.addCleanup(simulation.close)
        return simulation

    def test_tick_records_only_pins_and_public_pad_observations(self):
        actual = SerialPinSnapshot(1, 0, 0, 0, 0, 255, 255, 3)
        sink = []
        simulation = self.backend(record_sink=sink.append)
        result = simulation.tick(csn=0, sck=1, mosi=1)
        self.assertEqual(result, asdict(actual))
        self.assertEqual(simulation.cycle, 1)
        self.assertEqual(simulation.observation, PadObservation(0, 0, 0, 255, 255))
        record = simulation.records[0]
        self.assertEqual(set(record), {'cycle', 'pins', 'drive', 'observation'})
        self.assertEqual(record['pins'], dict(initialize=0, csn=0, sck=1, mosi=1))
        self.assertEqual(record['drive'], asdict(PadDrive()))
        self.assertEqual(record['observation'], asdict(actual))
        self.assertEqual(sink, [record])

    def test_cold_reset_uses_two_physical_edges_at_idle_serial_pins(self):
        simulation = self.backend()
        simulation.cold_reset()
        self.assertEqual(simulation.cycle, 2)
        self.assertEqual([r['pins'] for r in simulation.records], [
            dict(initialize=1, csn=1, sck=0, mosi=0),
            dict(initialize=0, csn=1, sck=0, mosi=0)])

    def test_invalid_pin_values_fail_before_any_process_input(self):
        simulation = self.backend()
        valid = dict(initialize=0, csn=1, sck=0, mosi=0)
        for name in PIN_WIDTHS:
            for value in (-1, 2, True, 0.0, None, '0'):
                with self.subTest(name=name, value=value):
                    with self.assertRaisesRegex(ValueError, 'pin width'):
                        simulation.tick(**dict(valid, **{name: value}))
        with self.assertRaises(TypeError):
            simulation.tick(csn=1, sck=0, mosi=0, command=3)
        self.assertEqual(simulation.cycle, 0)
        self.assertEqual(list(simulation.records), [])

    def test_snapshot_rejects_every_unrepresentable_pin_value(self):
        valid = asdict(SerialPinSnapshot(1, 0, 0, 0, 0, 255, 255, 3))
        for name, width in OBSERVATION_WIDTHS.items():
            for value in (-1, 1 << width, True, 0.0):
                with self.subTest(name=name, value=value):
                    with self.assertRaisesRegex(ValueError, 'pin width'):
                        SerialPinSnapshot(**dict(valid, **{name: value}))

    def test_malformed_unknown_and_extra_observations_close_process(self):
        for tokens in ('x 0 0 0 0 255 255 3', '0 0 0 0 0 255 255',
                       '0 0 0 0 0 255 255 3 0', '2 0 0 0 0 255 255 3',
                       '0 0 0 0 0 0 0 0'):
            with self.subTest(tokens=tokens):
                simulation = self.backend("import sys\nfor line in sys.stdin:\n"
                    + "    print('SRAM_SERIAL " + tokens + "', flush=True)\n")
                with self.assertRaisesRegex(RuntimeError, 'Malformed'):
                    simulation.tick(csn=1, sck=0, mosi=0)
                self.assertIsNotNone(simulation.process.poll())
                self.assertEqual(simulation.cycle, 0)
                with self.assertRaisesRegex(RuntimeError, 'closed'):
                    simulation.tick(csn=1, sck=0, mosi=0)

    def test_pre_edge_reset_release_cannot_hide_existing_output_ownership(self):
        simulation = self.backend()
        simulation.observation = PadObservation(1, 4, 4, 255, 255)
        for drive, message in ((PadDrive(enabled=4), 'DUT-owned'),
                               (PadDrive(links=1), 'open-drain')):
            with self.subTest(drive=drive):
                with self.assertRaisesRegex(RuntimeError, message):
                    simulation.tick(csn=1, sck=0, mosi=0, initialize=1, drive=drive)
        self.assertEqual(simulation.cycle, 0)

    def test_new_driver_can_resolve_a_previously_unused_unknown_pad(self):
        simulation = self.backend()
        simulation.observation = PadObservation(0, 0, 0, 3, 3)
        result = simulation.tick(csn=1, sck=0, mosi=0, drive=PadDrive(32, 32))
        self.assertEqual(result['known'], 255)

    def test_peer_receives_only_post_edge_pads_and_physical_cycle_count(self):
        simulation = self.backend()

        class Peer:
            def __init__(self):
                self.calls = []

            def drive(self, cycle, pads, ui):
                self.calls.append((cycle, pads, ui))
                return PadDrive(1, 1)

        peer = Peer()
        simulation.device = peer
        for _ in range(4):
            simulation.tick(csn=1, sck=0, mosi=0)
        self.assertEqual([call[0] for call in peer.calls], list(range(5)))
        self.assertTrue(all(type(call[1]) is PadObservation and call[2] == 0 for call in peer.calls))
        self.assertTrue(all(r['drive'] == asdict(PadDrive(1, 1)) for r in simulation.records))

    def test_bounded_records_and_complete_sink_keep_all_physical_edges(self):
        sink = []
        simulation = self.backend(record_limit=2, record_sink=sink.append)
        for _ in range(5):
            simulation.tick(csn=1, sck=0, mosi=0)
        self.assertEqual([r['cycle'] for r in simulation.records], [4, 5])
        self.assertEqual([r['cycle'] for r in sink], [1, 2, 3, 4, 5])

    def test_timeout_and_eof_fail_closed_without_a_completed_edge(self):
        for source, error in (("import sys, time\nfor line in sys.stdin:\n    time.sleep(1)\n", TimeoutError),
                              ("import sys\nsys.exit(0)\n", RuntimeError)):
            with self.subTest(error=error):
                simulation = self.backend(source, timeout_seconds=0.05)
                with self.assertRaises(error):
                    simulation.tick(csn=1, sck=0, mosi=0)
                self.assertIsNotNone(simulation.process.poll())
                self.assertEqual(simulation.cycle, 0)

    def test_close_is_idempotent_and_context_manager_reaps_child(self):
        simulation = self.backend()
        with simulation:
            simulation.tick(csn=1, sck=0, mosi=0)
        simulation.close()
        self.assertIsNotNone(simulation.process.poll())
        self.assertTrue(simulation.process.stdin.closed)
        self.assertTrue(simulation.process.stdout.closed)

    def test_options_and_peer_drive_types_fail_before_use(self):
        for value in (True, 0, -1, float('nan'), float('inf')):
            with self.subTest(timeout=value):
                with self.assertRaises(ValueError):
                    BufferedSramSerialRTL(Path('missing'), Path('missing'), timeout_seconds=value)
        for value in (True, -1, 1.5):
            with self.subTest(limit=value):
                with self.assertRaises(ValueError):
                    BufferedSramSerialRTL(Path('missing'), Path('missing'), record_limit=value)
        with self.assertRaises(TypeError):
            BufferedSramSerialRTL(Path('missing'), Path('missing'), record_sink=1)
        simulation = self.backend()
        with self.assertRaises(TypeError):
            simulation.device = object()
        with self.assertRaises(TypeError):
            simulation.tick(csn=1, sck=0, mosi=0, drive={})


class SerialBridgeRTLTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not all((CAD / tool).is_file() for tool in ('iverilog', 'vvp')):
            raise unittest.SkipTest('Pinned Icarus is required for serial bridge timing')

    def setUp(self):
        self.folder = tempfile.TemporaryDirectory(prefix='pinwheel-serial-bridge-')
        self.addCleanup(self.folder.cleanup)
        source = Path(self.folder.name) / 'public_stub.sv'
        source.write_text('''module pinwheel_buffered_shared_branches_sram_serial(
  input clk, initialize, csn, sck, mosi, input [1:0] raw_inputs,
  output miso, ready, output reg busy, output reg [2:0] levels, enabled);
  reg q;
  assign miso = initialize ? 1'b0 : q;
  assign ready = q;
  always @(posedge clk) begin
    if (initialize) begin q <= 0; busy <= 0; levels <= 0; enabled <= 0; end
    else begin q <= ~q; busy <= sck; levels <= mosi ? 7 : 0;
      enabled <= csn ? 0 : 7; end
  end
endmodule
''')
        self.executable = Path(self.folder.name) / 'bridge.vvp'
        result = subprocess.run([str(CAD / 'iverilog'), '-g2012',
            '-s', 'buffered_sram_serial_host_bridge', '-o', str(self.executable),
            str(source), str(ROOT / 'physical/buffered_sram_serial_host_bridge.sv')],
            capture_output=True, text=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_miso_is_pre_edge_and_ready_pads_are_post_edge(self):
        with BufferedSramSerialRTL(CAD / 'vvp', self.executable) as simulation:
            simulation.cold_reset()
            result = simulation.tick(csn=0, sck=1, mosi=1,
                                     drive=PadDrive(2, 3))
            self.assertEqual((result['miso'], result['ready']), (1, 0))
            self.assertEqual((result['busy'], result['levels'], result['enabled']), (1, 7, 7))
            self.assertEqual(result['edge_inputs'], 2)
            self.assertEqual(result['wires'] & 31, 30)
            self.assertEqual(simulation.cycle, 3)

    def test_bridge_rejects_extra_truncated_unknown_and_out_of_range_pin_lines(self):
        for line in ('1 1 0 0 0 0 0 255 extra\n', '1 1 0 0 0 0 0\n',
                     'x 1 0 0 0 0 0 255\n', '1 2 0 0 0 0 0 255\n',
                     '1 1 0 0 0 256 0 255\n', '4294967297 1 0 0 0 0 0 255\n'):
            with self.subTest(line=line):
                result = subprocess.run([str(CAD / 'vvp'), str(self.executable)],
                    input=line, capture_output=True, text=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('Malformed buffered SRAM serial pin input', result.stdout)

    def test_bridge_rejects_unknown_protocol_input_and_pre_edge_output_overlap(self):
        cases = [('1 1 0 0 0 0 0 0\n', 'Unknown pre-edge'),
                 ('1 1 0 0 0 0 0 255\n0 0 0 0 0 0 0 255\n'
                  '1 1 0 0 0 4 0 255\n', 'pre-edge buffered serial DUT-owned')]
        for lines, message in cases:
            with self.subTest(message=message):
                result = subprocess.run([str(CAD / 'vvp'), str(self.executable)],
                    input=lines, capture_output=True, text=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stdout)


if __name__ == '__main__':
    unittest.main()
