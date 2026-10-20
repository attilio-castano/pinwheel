"""Compiler-lift and missing/altered long-workload refusal controls."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_compile import spi_image, jtag_image
from streaming_uart_legacy_cases import ready_image, check_legacy_cases, SCHEMA, WORKLOADS


def receipt():
    rows = [dict(passed=True, protocol=protocol, bits=bits, depth=2, fault=None,
        start_count=1, owner_tag=65537, image_words=list(ready_image(protocol).words),
        physical_edges=bits+1000, trace=dict(edges=bits+1000, bytes=(bits+1000)*20, sha256='a'*64), exchange_rx_max=32,
        release=dict(code=0, tag=65537, flags=1, tx_accepted=0, rx_valid=0, rx_queued=0)) for protocol, bits in WORKLOADS]
    return dict(schema=SCHEMA, passed=True, depth=2, cases=rows,
        physical_edges=sum(row['physical_edges'] for row in rows))


class LiftedWorkloads(unittest.TestCase):
    def test_exact_qualified_words_and_idle_are_preserved(self):
        for name, old in [('spi', spi_image()), ('jtag', jtag_image())]:
            new = ready_image(name)
            self.assertEqual(new.words, old.words)
            self.assertEqual((new.idle_levels, new.idle_enabled), (old.idle_levels, old.idle_enabled))
        with self.assertRaises(ValueError): ready_image('uart')

    def test_both_long_single_start_workloads_required(self):
        good = receipt()
        check_legacy_cases(good)
        for field, value in [('bits', 32), ('start_count', 1024), ('owner_tag', 65538),
                ('depth', 4), ('fault', 'partial_read'), ('passed', False)]:
            bad = deepcopy(good)
            bad['cases'][0][field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError): check_legacy_cases(bad)
        bad = deepcopy(good)
        bad['cases'].pop()
        with self.assertRaises(RuntimeError): check_legacy_cases(bad)

    def test_trace_program_storage_and_release_cannot_be_omitted(self):
        good = receipt()
        for field, value in [('image_words', [2]), ('trace', {}), ('exchange_rx_max', 64),
                ('release', {}), ('release', dict(flags=4)), ('physical_edges', 0)]:
            bad = deepcopy(good)
            bad['cases'][0][field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError): check_legacy_cases(bad)
        bad = deepcopy(good)
        bad['physical_edges'] += 1
        with self.assertRaises(RuntimeError): check_legacy_cases(bad)

    def test_independent_release_recheck_requires_accepted_matching_free_valid_slot(self):
        good = receipt()
        for field, value in [('code', 5), ('tag', 65538), ('flags', 0), ('flags', 5),
                ('tx_accepted', 1), ('rx_valid', 1), ('rx_queued', 1)]:
            bad = deepcopy(good)
            bad['cases'][0]['release'][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(RuntimeError): check_legacy_cases(bad)
        for field, value in [('bytes', 1), ('sha256', 'not-a-hash')]:
            bad = deepcopy(good)
            bad['cases'][0]['trace'][field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError): check_legacy_cases(bad)


if __name__ == '__main__': unittest.main()
