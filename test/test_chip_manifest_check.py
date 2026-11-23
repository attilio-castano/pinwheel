"""The chip-manifest checker must reject drifted copies, not just accept today's.

Uses the Lean-emitted manifest; run `python3 -B scripts/check-chip-manifest.py
--emit` once first (or this test emits it when missing).
"""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('check_chip_manifest', ROOT / 'scripts/check-chip-manifest.py')
C = importlib.util.module_from_spec(spec)
spec.loader.exec_module(C)
import streaming_ready_wrapper as W


def load_manifest():
    if not C.DEFAULT_MANIFEST.exists():
        C.emit_manifest(C.DEFAULT_MANIFEST)
    return json.loads(C.DEFAULT_MANIFEST.read_text())


class ChipManifestCheck(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = load_manifest()
        cls.info = (ROOT / 'info.yaml').read_text()
        cls.wrapper = W.tt_source(cls.manifest['depth'])
        cls.sdc = (ROOT / 'physical/streaming-tt.sdc').read_text()

    def fields(self, report):
        return {(row['copy'], row['field']) for row in report.mismatches}

    def test_current_repository_agrees(self):
        report, _ = C.run(self.manifest)
        self.assertEqual(report.mismatches, [])
        self.assertGreater(len(report.rows), 50)

    def test_swapped_info_labels(self):
        text = self.info.replace('ui[0]: "Host CSn"', 'ui[0]: "Host SCK"')
        report = C.Report()
        C.check_info_yaml(report, self.manifest, text)
        self.assertEqual(self.fields(report), {('info.yaml', 'pinout ui[0]')})

    def test_wrong_info_tiles(self):
        report = C.Report()
        C.check_info_yaml(report, self.manifest, self.info.replace('tiles: "8x4"', 'tiles: "6x4"'))
        self.assertEqual(self.fields(report), {('info.yaml', 'tiles')})

    def test_swapped_wrapper_inputs(self):
        text = self.wrapper.replace('.csn(ui_in[0]), .sck(ui_in[1])', '.csn(ui_in[1]), .sck(ui_in[0])')
        self.assertNotEqual(text, self.wrapper)
        report = C.Report()
        C.check_wrapper(report, self.manifest, text)
        self.assertEqual({field for _, field in self.fields(report)}, {'input wiring'})

    def test_wrapper_drives_a_zero_output(self):
        text = self.wrapper.replace("{2'b0, busy, ready, miso}", "{2'b10, busy, ready, miso}")
        self.assertNotEqual(text, self.wrapper)
        report = C.Report()
        C.check_wrapper(report, self.manifest, text)
        self.assertEqual({field for _, field in self.fields(report)}, {'zero outputs'})

    def test_wrapper_reordered_mosi(self):
        text = self.wrapper.replace('.mosi({ui_in[7:5], ui_in[2]})', '.mosi({ui_in[2], ui_in[7:5]})')
        self.assertNotEqual(text, self.wrapper)
        report = C.Report()
        C.check_wrapper(report, self.manifest, text)
        self.assertEqual({field for _, field in self.fields(report)}, {'input wiring'})

    def test_changed_clock_target(self):
        manifest = copy.deepcopy(self.manifest)
        manifest['targets']['clock_period_ns'] = 25
        report = C.Report()
        config = json.loads((ROOT / 'physical/streaming-tt.json').read_text())
        C.check_physical_config(report, manifest, 'config', config, 'baseline')
        self.assertEqual(self.fields(report), {('config', 'CLOCK_PERIOD')})

    def test_unexplained_footprint_fails(self):
        report = C.Report()
        config = json.loads((ROOT / 'physical/streaming-tt.json').read_text())
        C.check_physical_config(report, self.manifest, 'config', config)
        self.assertEqual(self.fields(report), {('config', 'FP_DEF_TEMPLATE tiles')})

    def test_sdc_unknown_port(self):
        report = C.Report()
        C.check_sdc(report, self.manifest, self.sdc.replace('{ui_in[*] uio_in[*]', '{ui_in[*] uio_bad[*]'))
        self.assertEqual({field for _, field in self.fields(report)}, {'input uio_bad[*]'})

    def test_state_literal_count(self):
        report = C.Report()
        hits = C.check_state_literals(report, self.manifest, [('a.py', 'x = 6039\ny = 16039\nz = 6039.5'),
                                                               ('b.py', 'nothing')])
        self.assertEqual(hits, {'a.py': 1})

    def test_can_clock_contract(self):
        can = (ROOT / 'scripts/streaming_ready_can.py').read_text()
        report = C.Report()
        C.check_program_clocks(report, self.manifest, [('scripts/streaming_ready_can.py', can)])
        self.assertEqual(report.mismatches, [])
        self.assertEqual({row['field'] for row in report.rows if row['kind'] == 'ok'}, {'CORE_HZ'})
        changed = can.replace('CORE_HZ = 4_000_000', 'CORE_HZ = 8_000_000')
        self.assertNotEqual(changed, can)
        report = C.Report()
        C.check_program_clocks(report, self.manifest, [('scripts/streaming_ready_can.py', changed)])
        self.assertEqual(self.fields(report), {('scripts/streaming_ready_can.py', 'CORE_HZ')})

    def test_uncontracted_clock_warns(self):
        report = C.Report()
        C.check_program_clocks(report, self.manifest, [('scripts/demo.py', 'CORE_HZ = 60_000_000\n'),
                                                       ('scripts/slow.py', 'CORE_HZ = 1_000_000\n')])
        self.assertEqual(report.mismatches, [])
        reasons = {row['copy']: row['reason'] for row in report.rows if row['kind'] == 'warning'}
        self.assertIn('exceeds the 50 MHz target', reasons['scripts/demo.py'])
        self.assertNotIn('exceeds', reasons['scripts/slow.py'])

    def test_can_script_rejects_unproved_clock(self):
        source = (ROOT / 'scripts/streaming_ready_can.py').read_text()
        changed = source.replace('CORE_HZ = 4_000_000', 'CORE_HZ = 50_000_000')
        with self.assertRaisesRegex(ValueError, '32 core clocks per bit'):
            exec(compile(changed, 'streaming_ready_can.py', 'exec'), {'__name__': 'can_variant'})

    def test_ethernet_clock_contract(self):
        path = 'scripts/streaming_ready_ethernet.py'
        source = (ROOT / path).read_text()
        report = C.Report()
        C.check_program_clocks(report, self.manifest, [(path, source)])
        self.assertEqual(report.mismatches, [])
        contract = {row['program']: row for row in self.manifest['program_clocks']}['ethernet_sni_tx']
        self.assertEqual((contract['core_hz'], contract['within_target']), (60000000, False))
        self.assertTrue(contract['contract'].endswith('StreamingEthernetClock.phyClock'))
        changed = source.replace('CORE_HZ = 60_000_000', 'CORE_HZ = 50_000_000')
        with self.assertRaisesRegex(ValueError, 'six core clocks per bit'):
            exec(compile(changed, 'streaming_ready_ethernet.py', 'exec'), {'__name__': 'ethernet_variant'})

    def test_ps2_clock_contract(self):
        path = 'scripts/streaming_ready_ps2.py'
        source = (ROOT / path).read_text()
        report = C.Report()
        C.check_program_clocks(report, self.manifest, [(path, source)])
        self.assertEqual([row['kind'] for row in report.rows], ['ok'])
        contract = {row['program']: row for row in self.manifest['program_clocks']}['ps2_receive']
        self.assertEqual((contract['core_hz'], contract['within_target']), (4000000, True))
        changed = source.replace('CORE_HZ = 4_000_000\n', 'CORE_HZ = 8_000_000\n', 1)
        self.assertNotEqual(changed, source)
        with self.assertRaisesRegex(ValueError, '4 MHz core clock'):
            exec(compile(changed, 'streaming_ready_ps2.py', 'exec'), {'__name__': 'ps2_variant'})

    def test_over_target_contract_warns(self):
        report, _ = C.run(self.manifest)
        warnings = {(row['copy'], row['field']) for row in report.rows if row['kind'] == 'warning'}
        self.assertIn(('manifest program_clocks', 'ethernet_sni_tx'), warnings)

    def test_verilog_bits(self):
        widths = {'miso': 4, 'busy': 1}
        self.assertEqual(C.verilog_bits("{2'b0, busy, miso[3:2]}", widths),
                         [('miso', 2), ('miso', 3), ('busy', 0), ('0', None), ('0', None)])
        with self.assertRaises(ValueError):
            C.verilog_bits('miso + 1', widths)


if __name__ == '__main__':
    unittest.main()
