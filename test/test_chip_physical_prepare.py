"""Chip staging must bind the comparison and every macro view before a run."""
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('prepare_chip', SCRIPTS / 'prepare-chip-physical.py')
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)
import physical_floorplan


class ChipPreparation(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.base = self.root / 'build/physical'
        self.upstream = self.base / 'upstream'
        for name in ['tools', 'scripts', 'physical', 'test', 'comparison/hybrid',
                     'build/physical/upstream/macro']:
            (self.root / name).mkdir(parents=True)
        for name in ['physical/chip.json', 'physical/chip.sdc', 'test/sram_chip.sv',
                     'scripts/prepare-chip-physical.py', 'comparison/hybrid/chip.sv']:
            (self.root / name).write_text('fixture')
        macro = prepare.MACRO
        views = [f'{kind}/{macro}.{kind}' for kind in ['lef', 'gds', 'cdl']]
        views += [f'verilog/{macro}.v']
        views += [f'lib/{macro}_{corner}.lib' for corner in
                  ['typ_1p20V_25C', 'slow_1p08V_125C', 'fast_1p32V_m55C']]
        entries = []
        for relative in views:
            text = 'pinned ' + relative
            if relative.endswith('.v'):
                text = f'// original license\n`celldefine\nmodule {macro} ();\n// ---- Simulation-only check:\n'
            file = self.upstream / 'macro' / Path(relative).name
            file.write_text(text)
            entries.append(dict(path='ihp-sg13g2/libs.ref/sg13g2_sram/' + relative,
                                sha=prepare.blob(file.read_bytes())))
        tree = self.upstream / 'pdk-tree.json'
        tree.write_text(json.dumps(dict(sha='fixture-revision', truncated=False, tree=entries)))
        template = self.upstream / 'tt_block_6x4_pgvdd.def'
        template.write_text('official pins fixture')
        lock = dict(pdk_revision='fixture-revision', pdk_tree_sha256=prepare.sha(tree),
                    support_revision='fixture-support', allocation=dict(tt_def_template='template.def',
                    tt_def_template_sha256=prepare.sha(template)))
        (self.root / 'tools/physical-toolchain.json').write_text(json.dumps(lock))
        self.comparison = self.root / 'comparison/report.json'
        self.comparison.write_text(json.dumps(dict(
            source_sha256={'test/sram_chip.sv': prepare.sha(self.root / 'test/sram_chip.sv')},
            variants=dict(hybrid=dict(artifacts=dict(chip=dict(
                rtl_sha256=prepare.sha(self.root / 'comparison/hybrid/chip.sv'))))))))
        self.out = self.base / 'candidate'

    def invoke(self, extra=()):
        with patch.object(prepare, 'ROOT', self.root), patch.object(prepare, 'BASE', self.base), \
             patch.object(prepare, '__file__', str(self.root / 'scripts/prepare-chip-physical.py')), \
             patch.object(sys, 'argv', ['prepare', '--comparison', str(self.comparison), '--design', 'candidate', *extra]), \
             patch.object(prepare.urllib.request, 'urlopen', side_effect=AssertionError('Unexpected network')):
            prepare.main()

    def test_complete_input_set_is_frozen_and_identified(self):
        self.invoke()
        receipt = json.loads((self.out / 'inputs.json').read_text())
        self.assertEqual(receipt['profile'], 'chip')
        for name, digest in receipt['files_sha256'].items():
            self.assertEqual(prepare.sha(self.out / name), digest)
        self.assertEqual(len(receipt['files_sha256']), 14)
        header = (self.out / 'macro' / (prepare.MACRO + '.bb.v')).read_text()
        self.assertIn('original license', header)
        self.assertIn('(* blackbox *)', header)
        self.assertNotIn('Simulation-only', header)
        self.assertEqual(receipt['validation_receipt_sha256'], prepare.sha(self.comparison))

    def test_macro_experiment_preserves_base_and_other_inputs(self):
        config = {'DIE_AREA': [0, 0, 100, 100], 'CLOCK_PERIOD': 20,
                  'MACROS': {'ram': {'lef': ['dir::ram.lef'], 'instances': {
                      'memory': {'location': [10, 20], 'orientation': 'N'}}}}}
        base = self.root / 'physical/chip.json'
        base.write_text(json.dumps(config))
        placements = {'memory': {'location': [10, 20], 'orientation': 'FS'}}
        path = self.root / 'placement.json'
        path.write_text(json.dumps(placements))
        self.invoke(['--macro-placement', str(path)])
        self.assertEqual(json.loads(base.read_text()), config)
        self.assertEqual(json.loads((self.out / 'core.json').read_text()),
                         physical_floorplan.apply_placement(config, placements))
        receipt = json.loads((self.out / 'inputs.json').read_text())
        self.assertEqual(receipt['macro_placement'], placements)
        for name, digest in receipt['files_sha256'].items():
            self.assertEqual(prepare.sha(self.out / name), digest)
        for name in ['design.sv', 'sram_chip.sv', 'core.sdc', 'tt_block_6x4_pgvdd.def']:
            self.assertEqual(prepare.sha(self.out / name), receipt['files_sha256'][name])

    def test_macro_experiment_rejects_unrelated_or_malformed_changes(self):
        config = {'DIE_AREA': [0, 0, 100, 100],
                  'MACROS': {'ram': {'instances': {'memory': {}}}}}
        good = {'location': [10, 20], 'orientation': 'FS'}
        bad = [None, {}, {'new-memory': good}, {'memory': {**good, 'lef': []}},
               {'memory': {**good, 'orientation': 'SIDEWAYS'}}]
        bad += [{'memory': {**good, 'location': v}} for v in
                [[True, 0], [float('nan'), 0], [float('inf'), 0], [100, 0], [-1, 0], [0], '0,0']]
        for placements in bad:
            with self.subTest(placements=placements), self.assertRaises(ValueError):
                physical_floorplan.apply_placement(config, placements)

    def test_changed_source_rtl_or_macro_fails_before_creating_design(self):
        for name, message in [
            ('test/sram_chip.sv', 'Stale comparison source'),
            ('comparison/hybrid/chip.sv', 'Changed validated hybrid RTL'),
            (f'build/physical/upstream/macro/{prepare.MACRO}.gds', 'Modified input'),
        ]:
            file = self.root / name
            original = file.read_bytes()
            file.write_bytes(original + b'changed')
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, message):
                self.invoke()
            self.assertFalse(self.out.exists())
            file.write_bytes(original)

    def test_placement_exclusions_are_frozen_without_changing_other_controls(self):
        config = {'DIE_AREA': [0, 0, 100, 100], 'CLOCK_PERIOD': 20}
        base = self.root / 'physical/chip.json'
        base.write_text(json.dumps(config))
        path = self.root / 'exclusions.json'
        regions = [[10, 20, 30, 40]]
        path.write_text(json.dumps(regions))
        self.invoke(['--placement-exclusions', str(path)])
        self.assertEqual(json.loads(base.read_text()), config)
        self.assertEqual(json.loads((self.out / 'core.json').read_text()),
                         {**config, 'FP_OBSTRUCTIONS': regions})
        receipt = json.loads((self.out / 'inputs.json').read_text())
        self.assertEqual(receipt['placement_exclusions'], regions)
        self.assertEqual(receipt['files_sha256']['placement-exclusions.json'],
                         prepare.sha(self.out / 'placement-exclusions.json'))

    def test_exclusions_reject_invalid_geometry(self):
        config = {'DIE_AREA': [0, 0, 100, 100]}
        for regions in [None, [], {}, [[0, 0, 0, 5]], [[5, 5, 4, 9]],
                        [[-1, 0, 5, 5]], [[0, 0, 101, 5]], [[True, 0, 5, 5]],
                        [[0, 0, float('nan'), 5]], [[0, 0, float('inf'), 5]], [[0, 1, 2]]]:
            with self.subTest(regions=regions), self.assertRaises(ValueError):
                physical_floorplan.apply_exclusions(config, regions)

    def test_exclusion_check_detects_straddling_cells_rows_and_missing_blockages(self):
        rect = [10, 20, 30, 40]
        context = dict(die=[0, 0, 100, 100], instances={}, rows=[],
                       placement_blockages=[dict(bbox=rect, soft=False)])
        self.assertTrue(physical_floorplan.exclusion_report(context, [rect])['clear'])
        for change in [dict(instances={'buffer': {'bbox': [9, 22, 11, 25]}}),
                       dict(rows=[{'bbox': [0, 22, 100, 25]}]),
                       dict(placement_blockages=[]),
                       dict(placement_blockages=[dict(bbox=rect, soft=True)])]:
            with self.subTest(change=change):
                self.assertFalse(physical_floorplan.exclusion_report({**context, **change}, [rect])['clear'])
        context['instances'] = {'touching': {'bbox': [0, 20, 10, 40]}}
        self.assertTrue(physical_floorplan.exclusion_report(context, [rect])['clear'])

    def test_bad_download_is_never_installed(self):
        file = self.upstream / 'missing.lib'
        with patch.object(prepare.urllib.request, 'urlopen', return_value=io.BytesIO(b'wrong')):
            with self.assertRaisesRegex(RuntimeError, 'Unpinned download'):
                prepare.fetch_checked(file, 'https://example.invalid/pinned.lib', lambda b: b == b'expected', True)
        self.assertFalse(file.exists())

    def test_missing_view_without_fetch_does_not_use_network(self):
        with patch.object(prepare.urllib.request, 'urlopen', side_effect=AssertionError('Unexpected network')):
            with self.assertRaisesRegex(RuntimeError, 'use --fetch'):
                prepare.fetch_checked(self.upstream / 'missing.lib', '', lambda _: True, False)


if __name__ == '__main__':
    unittest.main()
