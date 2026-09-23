import importlib.util
from pathlib import Path
import sys
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('guides', SCRIPTS / 'report-routing-guides.py')
guides = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guides)


class RoutingGuides(unittest.TestCase):
    def test_geometry_units_and_unique_net_counts(self):
        parsed = guides.parse_guides('a\n(\n0 0 2000 1000 Metal4\n0 0 2000 1000 Metal4\n)\n'
                                     'b\n(\n2000 0 3000 1000 Metal4\n)\n', 1000)
        context = {'instances': {'ram': {'macro': True, 'bbox': [0, 0, 2, 1]}},
                   'nets': {'a': {'terminals': [{'instance': 'ram'}]}, 'b': {'terminals': []}}}
        self.assertEqual(guides.summarize(parsed, context)['overlapping_guides'],
                         {'Metal4': {'rectangles': 2, 'nets': 1, 'macro_connected_nets': 1}})
        # Merely touching the boundary does not count as overlap.
        self.assertFalse(guides.overlaps(parsed[2]['bbox'], [0, 0, 2, 1]))

    def test_rejects_truncated_invalid_or_unknown_geometry(self):
        for text in ['', 'a\n(\n)', 'a\n(\n0 0 1 1 Metal4', 'a\n0 0 1 1 Metal4',
                     'a\n(\n0 0 0 1 Metal4\n)', 'a\n(\n0 nan 1 1 Metal4\n)']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                guides.parse_guides(text, 1000)
        with self.assertRaisesRegex(ValueError, 'missing'):
            guides.summarize([{'net': 'unknown'}], {'instances': {}, 'nets': {}})


if __name__ == '__main__':
    unittest.main()
