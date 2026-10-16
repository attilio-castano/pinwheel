import importlib.util
from pathlib import Path
from decimal import Decimal
import unittest

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('qualification_worker', HERE / 'worker.py')
worker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(worker)

class Metrics:
    def keys(self): return ['timing__setup__ws', 'count']
    def __getitem__(self, key): return {'timing__setup__ws': Decimal('-7.4530588255016905'), 'count': 369}[key]
    def __str__(self): return '<Metrics wrapper, not JSON>'

class Serialization(unittest.TestCase):
    def test_explicit_mapping_keeps_numeric_values(self):
        actual = worker.plain(dict(Metrics()))
        self.assertIsInstance(actual, dict)
        self.assertIsInstance(actual['timing__setup__ws'], float)
        self.assertEqual(actual['count'], 369)
    def test_unmaterialized_wrapper_fails_closed(self):
        with self.assertRaisesRegex(TypeError, 'Unsupported native'):
            worker.plain(Metrics())
    def test_nonfinite_metric_rejected(self):
        with self.assertRaises(ValueError): worker.plain({'value': float('nan')})

if __name__ == '__main__': unittest.main()
