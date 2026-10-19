"""Independent coverage and refusal checks for finite kernel proof producers."""
from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from streaming_tt_finite import finite_forall


def declared_chunks(source):
    matches = re.findall(r'private theorem witness_bounded_chunk_\d+ : ∀ offset : Fin (\d+), '
                         r'\(\(⟨(\d+) \+ offset.val,.*?\)\.val < \d+ :=', source)
    return [(int(start), int(width)) for width, start in matches]


def exact_cover(source, size):
    chunks = declared_chunks(source)
    covered = [index for start, width in chunks for index in range(start, start + width)]
    return covered == list(range(size)) and all(1 <= width <= 128 for _, width in chunks)


class FiniteKernelProducer(unittest.TestCase):
    def source(self, size):
        return finite_forall('witness', size, lambda index: f'({index}).val < {size}')

    def test_all_indices_covered_once_including_tail(self):
        for size in (1, 127, 128, 129, 257, 6039):
            with self.subTest(size=size):
                source = self.source(size)
                self.assertTrue(exact_cover(source, size))
                self.assertIn(f'theorem witness : ∀ index : Fin {size}, (index).val < {size}', source)
                self.assertEqual(source.count('have witness := witness_bounded_chunk_'),
                                 len(declared_chunks(source)))
        self.assertEqual(declared_chunks(self.source(6039))[-1], (6016, 23))

    def test_coverage_oracle_rejects_omission_duplicate_and_shift(self):
        source = self.source(257)
        lines = source.splitlines()
        first = next(line for line in lines if 'private theorem witness_bounded_chunk_0 ' in line)
        last = next(line for line in lines if 'private theorem witness_bounded_chunk_2 ' in line)
        self.assertFalse(exact_cover(source.replace(last, ''), 257))
        self.assertFalse(exact_cover(source + '\n' + first, 257))
        self.assertFalse(exact_cover(source.replace('⟨256 + offset.val', '⟨255 + offset.val'), 257))

    def test_empty_domain_is_explicit_and_inputs_are_bounded(self):
        source = self.source(0)
        self.assertIn('exact Fin.elim0 index', source)
        self.assertNotIn('private theorem', source)
        for size in (-1, True, 1.5, '6039'):
            with self.subTest(size=size), self.assertRaises(ValueError):
                self.source(size)
        for width in (0, -1, 257, True):
            with self.subTest(width=width), self.assertRaises(ValueError):
                finite_forall('witness', 1, lambda index: 'True', chunk_width=width)
        for name in ('', 'x y', 'x\naxiom bad : False'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                finite_forall(name, 1, lambda index: 'True')


if __name__ == '__main__':
    unittest.main()
