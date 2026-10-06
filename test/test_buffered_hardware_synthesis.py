"""Negative boundaries for saved buffered resource and local PDK evidence."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import buffered_hardware_synthesis as synthesis


def fixture(mapped=False):
    kind = 'sg13cmos5l_dfrbpq_1' if mapped else '$_DFF_P_'
    module = dict(cells={'state': dict(type=kind, connections={'Q': [9], 'D': [8]})},
        netnames={name: dict(bits=['0'] * 32) for name in
                  ['r_tx_data', 'r_rx_data', *[f'r_word{row}' for row in range(128)]]})
    module['netnames']['r_written'] = dict(bits=['0'] * 128)
    module['netnames']['r_tx_data']['bits'][0] = 9
    return dict(modules={synthesis.TOP: module, kind: dict(attributes={'area': '48.9888'})})


class SavedResourcesTests(unittest.TestCase):
    def test_saved_state_and_area_census(self):
        generic = synthesis.resource_metrics(fixture())
        mapped = synthesis.resource_metrics(fixture(True), mapped=True)
        self.assertEqual((generic['cells'], generic['physical_state_bits']), (1, 1))
        self.assertEqual(generic['named_storage']['tx']['physical_state_bits'], 1)
        self.assertEqual(generic['named_storage']['program_bank']['logical_bits'], 4096)
        self.assertEqual(mapped['standard_cell_area_um2'], 48.9888)
        self.assertEqual(mapped['sequential_area_um2'], 48.9888)

    def test_aliased_or_constant_saved_state_is_rejected(self):
        data = fixture()
        data['modules'][synthesis.TOP]['cells']['alias'] = deepcopy(
            data['modules'][synthesis.TOP]['cells']['state'])
        with self.assertRaisesRegex(ValueError, 'Aliased'):
            synthesis.resource_metrics(data)
        data = fixture()
        data['modules'][synthesis.TOP]['cells']['state']['connections']['Q'] = ['0']
        with self.assertRaisesRegex(ValueError, 'Invalid saved'):
            synthesis.resource_metrics(data)

    def test_unmapped_cells_or_missing_liberty_area_are_rejected(self):
        for kind in ('$mux', '$_AND_'):
            data = fixture(True)
            data['modules'][synthesis.TOP]['cells']['unmapped'] = dict(
                type=kind, connections={'Y': [12]})
            with self.assertRaisesRegex(ValueError, 'Unmapped cell'):
                synthesis.resource_metrics(data, mapped=True)
        data = fixture(True)
        del data['modules']['sg13cmos5l_dfrbpq_1']['attributes']['area']
        with self.assertRaises(KeyError):
            synthesis.resource_metrics(data, mapped=True)

    def test_unnormalized_sequential_forms_are_rejected(self):
        for kind in ('$dff', '$adff', '$sdff', '$_DFFE_PP_'):
            data = fixture()
            data['modules'][synthesis.TOP]['cells']['state']['type'] = kind
            with self.assertRaisesRegex(ValueError, 'Normalize all'):
                synthesis.resource_metrics(data)

    def test_corrupt_pdk_source_is_rejected_before_staging(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'tools').mkdir()
            pdk = root / 'source'
            (pdk / 'lib').mkdir(parents=True)
            (pdk / 'verilog').mkdir()
            library = b'fixture liberty'
            (pdk / 'lib' / synthesis.LIBRARY).write_bytes(library)
            models = {name: hashlib.sha256(name.encode()).hexdigest()
                      for name in synthesis.MODEL_SHA256}
            for name in models:
                (pdk / 'verilog' / name).write_text(name)
            manifest = dict(commit=synthesis.MODEL_REVISION, files=[dict(
                name=synthesis.LIBRARY, sha256=hashlib.sha256(library).hexdigest())])
            (root / 'tools/technology-library.json').write_text(json.dumps(manifest))
            destination = root / 'staged'
            with patch.object(synthesis, 'ROOT', root), patch.object(synthesis, 'MODEL_SHA256', models):
                synthesis.stage_pdk(destination, pdk)
                staged = {path.name: path.read_bytes() for path in destination.iterdir()}
                corrupt = pdk / 'verilog' / next(iter(models))
                corrupt.write_text('corrupt model')
                with self.assertRaisesRegex(ValueError, 'Unpinned local'):
                    synthesis.stage_pdk(root / 'another', pdk)
                self.assertFalse((root / 'another').exists())
                self.assertEqual(staged, {path.name: path.read_bytes()
                                         for path in destination.iterdir()})

    def test_existing_staged_pdk_is_preserved_on_hash_mismatch(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'tools').mkdir()
            pdk = root / 'source'
            (pdk / 'lib').mkdir(parents=True)
            (pdk / 'verilog').mkdir()
            library = b'fixture liberty'
            (pdk / 'lib' / synthesis.LIBRARY).write_bytes(library)
            models = {name: hashlib.sha256(name.encode()).hexdigest()
                      for name in synthesis.MODEL_SHA256}
            for name in models:
                (pdk / 'verilog' / name).write_text(name)
            manifest = dict(commit=synthesis.MODEL_REVISION, files=[dict(
                name=synthesis.LIBRARY, sha256=hashlib.sha256(library).hexdigest())])
            (root / 'tools/technology-library.json').write_text(json.dumps(manifest))
            destination = root / 'staged'
            destination.mkdir()
            (destination / synthesis.LIBRARY).write_bytes(b'preserve this mismatch')
            with patch.object(synthesis, 'ROOT', root), patch.object(synthesis, 'MODEL_SHA256', models):
                with self.assertRaisesRegex(ValueError, 'Preserve and inspect'):
                    synthesis.stage_pdk(destination, pdk)
            self.assertEqual((destination / synthesis.LIBRARY).read_bytes(), b'preserve this mismatch')


if __name__ == '__main__':
    unittest.main()
