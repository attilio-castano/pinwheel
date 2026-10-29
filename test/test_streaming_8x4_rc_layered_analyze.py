"""HOST analytic slope/ground/coupling controls; no field solve."""
from decimal import Decimal as D
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('layered_analyze', Path(__file__).resolve().parents[1] / 'scripts/streaming_8x4_rc_layered_analyze.py')
A = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(A)
GSPEC = importlib.util.spec_from_file_location('layered_geometry_units', Path(__file__).resolve().parents[1] / 'scripts/streaming_8x4_rc_layered_geometry.py')
G = importlib.util.module_from_spec(GSPEC); GSPEC.loader.exec_module(G)

POLICY = {'maximum_length_slope_difference': '.05', 'maximum_ground_extension_difference': '.02',
          'maximum_BEM_reference_difference': '.10'}


def finite(slope=None):
    slope = slope or [[D('2e-10'), D('-.5e-10')], [D('-.5e-10'), D('2e-10')]]
    end = [[D('1e-16'), D('-.2e-16')], [D('-.2e-16'), D('1e-16')]]
    return {(length, extent): [[str(x * D(length) * D('1e-6') + e) for x, e in zip(row, erow)]
                              for row, erow in zip(slope, end)]
            for length, extent in [('10', '20'), ('20', '20'), ('30', '20'), ('20', '30'), ('30', '30')]}


class AnalyzeTests(unittest.TestCase):
    def test_independent_unit_readback_requires_every_vertex_and_reference(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); old = root / 'physical'; current = root / 'emitted'
            old.mkdir(); current.mkdir(); (old / 'manifest.json').write_text('{}')
            (old / 'probe').mkdir(); (current / 'probe').mkdir()
            source = {'panel.qui': 'Q W1 .5 0 0  1 0 0  1 1 0  .5 1 0\n',
                      'geometry.lst': 'C panel.qui 4.1 0 0 0\nD panel.qui 1 2 0 0 0 .5 .5 .5\n'}
            emitted, unit = G.normalize_s20(source)
            for name, text in source.items():
                (old / 'probe' / name).write_text(text)
                (current / 'probe' / name).write_text(emitted[name])
            (current / 'manifest.json').write_text(json.dumps({'physical_SI_source_owner': str(old),
                'physical_source_manifest_sha256': A.E.sha(old / 'manifest.json')}))
            (current / 'probe' / 'unit-map.json').write_text(json.dumps(unit))
            self.assertTrue(A.check_unit_witness(current, 'probe')['retained_SI_and_emitted_S20_readback_exact'])
            unit['all_coordinate_and_reference_witnesses'].pop()
            (current / 'probe' / 'unit-map.json').write_text(json.dumps(unit))
            with self.assertRaisesRegex(ValueError, 'coordinate unit witness'):
                A.check_unit_witness(current, 'probe')

    def test_fine_mesh_leaf_cannot_impersonate_a_coarse_batch_job(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / 'report.json').write_text(json.dumps({'mesh': '0.0000431745'}))
            with self.assertRaisesRegex(ValueError, 'leaf mesh differs'):
                A.read_native({}, 'unused', {}, '0.000383703', path, path, path)

    def test_analytic_end_term_cancels_and_full_matrix_matches(self):
        reference = [[2e-10, -.5e-10], [-.5e-10, 2e-10]]
        result = A.compare_case(POLICY, ['W1', 'W2'], finite(), reference)
        self.assertTrue(result['passed'])
        self.assertEqual(D(result['length_slope_relative_difference']), 0)

    def test_matching_diagonal_cannot_hide_wrong_coupling(self):
        reference = [[2e-10, -.3e-10], [-.3e-10, 2e-10]]
        self.assertFalse(A.compare_case(POLICY, ['W1', 'W2'], finite(), reference)['passed'])

    def test_extension_slope_gate_separate_from_end_term(self):
        value = finite()
        value['30', '30'] = [[str(D(x) * D('1.02')) for x in row] for row in value['30', '30']]
        result = A.compare_case(POLICY, ['W1', 'W2'], value, [[2e-10, -.5e-10], [-.5e-10, 2e-10]])
        self.assertGreater(D(result['ground_extension_relative_difference']), D('.02'))
        self.assertFalse(result['passed'])

    def test_nonphysical_slope_rejected(self):
        with self.assertRaises(ValueError):
            A.compare_case(POLICY, ['W1', 'W2'], finite([[D('2e-10'), D('.5e-10')], [D('.5e-10'), D('2e-10')]]),
                           [[2e-10, -.5e-10], [-.5e-10, 2e-10]])


if __name__ == '__main__':
    unittest.main()
