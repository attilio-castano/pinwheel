from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_lef_format as L


FIXTURE = '''VERSION 5.8 ;
UNITS
  DATABASE MICRONS 1000 ;
END UNITS
MACRO example
  FOREIGN example 0 0 ;
  SIZE 1289.28 BY 710.64 ;
  PIN data[0]
    DIRECTION INPUT ;
    USE SIGNAL ;
    PORT
      LAYER Metal4 ;
      RECT 187.05 709.64 187.35 710.64 ;
    END
  END data[0]
  OBS
    LAYER Metal1 ;
    RECT -0.1 0 1.001 2.2 ;
  END
END example
END LIBRARY
'''


class FormatTests(unittest.TestCase):
    def test_exact_geometry_and_noncoordinate_text(self):
        derived, summary = L.canonicalize(FIXTURE)
        self.assertIn('SIZE 1289.280 BY 710.640 ;', derived)
        self.assertIn('RECT -0.100 0.000 1.001 2.200 ;', derived)
        self.assertIn('VERSION 5.8 ;', derived)
        self.assertIn('DATABASE MICRONS 1000 ;', derived)
        self.assertEqual(summary['pins'], ['data[0]'])
        self.assertEqual(L.model(FIXTURE)['signature'], L.model(derived)['signature'])
        self.assertEqual(L.validate_equivalence(FIXTURE, derived), summary)

    def test_unchanged_official_fp3_parser_requires_three_digits(self):
        # Exact arithmetic used by the pinned official parse_fp3 implementation.
        def official(value):
            ip, fp = value.split('.')
            return int(ip + fp[:3].rjust(3, '0'))
        self.assertEqual(official('1289.28'), 1289028)
        self.assertEqual(official('1289.280'), 1289280)
        self.assertEqual(official('710.640'), 710640)
        derived, _ = L.canonicalize(FIXTURE)
        for line in derived.splitlines():
            words = line.split()
            if words and words[0] in L.FIELDS:
                for index in L.FIELDS[words[0]]:
                    self.assertEqual(official(words[index]), int(L.coordinate(words[index])*1000))

    def test_actual_native_double_space_rect_is_compatible_without_geometry_change(self):
        raw = FIXTURE.replace('RECT 187.05', 'RECT  187.05')
        official_rect = re.compile(r'RECT (\S+) (\S+) (\S+) (\S+) ;')
        self.assertIsNone(official_rect.match('RECT  187.05 709.64 187.35 710.64 ;'))
        derived, summary = L.canonicalize(raw)
        self.assertEqual(summary['whitespace_changed_statements'], 1)
        self.assertIsNotNone(official_rect.fullmatch('RECT 187.050 709.640 187.350 710.640 ;'))
        self.assertIn('RECT 187.050 709.640 187.350 710.640 ;', derived)
        L.validate_equivalence(raw, derived)

    def test_geometry_tabs_negative_coordinates_indent_and_nongeometry_bytes(self):
        raw = FIXTURE.replace('    RECT -0.1 0 1.001 2.2 ;',
            '\t  RECT\t-0.1\t0\t1.001\t2.2\t;  ').replace('VERSION 5.8', 'VERSION\t5.8')
        derived, _ = L.canonicalize(raw)
        self.assertIn('\t  RECT -0.100 0.000 1.001 2.200 ;\n', derived)
        self.assertIn('VERSION\t5.8 ;\n', derived)
        L.validate_equivalence(raw, derived)
        for mutated in (derived.replace('VERSION\t5.8', 'VERSION 5.8'),
                derived.replace('\t  RECT', '  RECT')):
            with self.assertRaises(ValueError): L.validate_equivalence(raw, mutated)

    def test_geometry_mutations_refused(self):
        derived, _ = L.canonicalize(FIXTURE)
        for changed in (derived.replace('1289.280', '1289.281'),
                derived.replace('187.050', '187.051'), derived.replace('2.200', '2.201')):
            with self.assertRaises(ValueError): L.validate_equivalence(FIXTURE, changed)

    def test_pin_type_layer_membership_mutations_refused(self):
        derived, _ = L.canonicalize(FIXTURE)
        for changed in (derived.replace('data[0]', 'data[1]'), derived.replace('INPUT', 'OUTPUT'),
                derived.replace('SIGNAL', 'POWER'), derived.replace('Metal4', 'Metal3'),
                derived.replace('VERSION 5.8', 'VERSION 5.7')):
            with self.assertRaises(ValueError): L.validate_equivalence(FIXTURE, changed)

    def test_no_rounding_nonfinite_or_exponent(self):
        for raw in ('0.0001', 'NaN', 'Infinity', '1e-3', '.1', '0.1234', '1' * 30):
            with self.assertRaises(ValueError): L.coordinate(raw)
        for raw in ('0', '-0.125', '1.0000', '1289.28'):
            L.coordinate(raw)

    def test_duplicate_pin_or_macro_refused(self):
        for changed in (FIXTURE.replace('  OBS', '  PIN data[0]\n  END data[0]\n  OBS'),
                FIXTURE.replace('MACRO example', 'MACRO extra\nMACRO example')):
            with self.assertRaises(ValueError): L.canonicalize(changed)

    def test_deterministic_format_idempotence_and_unknown_geometry(self):
        derived, _ = L.canonicalize(FIXTURE)
        self.assertEqual(L.canonicalize(derived)[0], derived)
        with self.assertRaises(ValueError): L.validate_equivalence(FIXTURE, derived.replace('187.050', '187.05'))
        with self.assertRaises(ValueError): L.canonicalize(FIXTURE.replace('RECT ', 'POLYGON ', 1))

    def test_reversed_or_malformed_statement_refused(self):
        for changed in (FIXTURE.replace('187.05 709.64 187.35 710.64', '188 709.64 187.35 710.64'),
                FIXTURE.replace('1289.28 BY 710.64', '1289.28 BY 710.64 1'),
                FIXTURE.replace('1289.28 BY', '1289.28 AND')):
            with self.assertRaises(ValueError): L.canonicalize(changed)


if __name__ == '__main__': unittest.main()
