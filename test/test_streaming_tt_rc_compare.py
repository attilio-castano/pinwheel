"""Arithmetic, malformed-input and provenance controls for a host-only RC review."""
from copy import deepcopy
from decimal import Decimal, localcontext
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_tt_rc_compare as C


def itf_text():
    dielectric = {'fox': '.4', 'nitride': '.05', 'dummyOx': '.59', 'ox1': '.96',
                  'ox2': '1.03', 'ox3': '1.03', 'ox4': '1.34'}
    text = 'TECHNOLOGY = sg13cmos5l\n'
    for name, thickness in dielectric.items():
        text += f'DIELECTRIC {name} {{ THICKNESS={thickness} ER=4.1 }}\n'
    for name in C.METALS:
        thick, width, space, rpsq = ('.42', '.16', '.18', '.110') if name == 'Metal1' else (
            ('2', '1.64', '1.64', '.018') if name == 'TopMetal1' else ('.49', '.2', '.21', '.088'))
        text += f'CONDUCTOR {name} {{ THICKNESS={thick} WMIN={width} SMIN={space} RPSQ={rpsq} }}\n'
    return text


def process_text():
    lines = []
    for index, name in enumerate(C.METALS, 1):
        gap, thick, width, space, rho = ('1.04', '.42', '.16', '.18', '.0462') if index == 1 else (
            ('.85', '2', '1.64', '1.64', '.036') if index == 5 else ('.54', '.49', '.2', '.21', '.0431'))
        lines += [f'CONDUCTOR {name} {{ distance {gap} thickness {thick} min_width {width} min_spacing {space} resistivity {rho} }}',
                  f'DIELECTRIC d{index} {{ epsilon 4.1 thickness {gap} next_met {index} }}']
    return '\n'.join(lines)


class StackTests(unittest.TestCase):
    def test_surface_reference_and_intermetal_overlap_produce_540_not_516(self):
        rows = C.itf_metal_geometry(C.parse_stack(itf_text()))
        self.assertEqual([rows[name]['bottom_um'] for name in C.METALS],
                         list(map(Decimal, ['1.04', '2', '3.03', '4.06', '5.40'])))
        self.assertEqual(rows['TopMetal1']['top_um'], Decimal('7.40'))

    def test_comments_string_fields_and_decimal_exponents_are_data(self):
        parsed = C.parse_stack('$ copyright\nVIA Via1 { FROM=Metal1 TO=Metal2 AREA=3.61e-2 RPV=9 } # note')
        self.assertEqual(parsed['VIA', 'Via1']['AREA'], Decimal('.0361'))
        self.assertEqual(parsed['VIA', 'Via1']['FROM'], 'Metal1')

    def test_malformed_duplicate_nonfinite_or_unknown_fields_refuse(self):
        for text in ['CONDUCTOR M { distance 1 distance 2 }', 'CONDUCTOR M { distance 1 } CONDUCTOR M { distance 1 }',
                     'CONDUCTOR M { distance NaN }', 'CONDUCTOR M { distance -1 }',
                     'CONDUCTOR M { distance 1; }', 'CONDUCTOR M { unknown 1 }',
                     'CONDUCTOR M { distance 1', 'DIELECTRIC d { next_met 1.5 }', '',
                     'TECHNOLOGY = other CONDUCTOR M { distance 1 }']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                C.parse_stack(text)

    def test_rho_rounding_is_recorded_as_difference_not_silent_match(self):
        itf, process = C.parse_stack(itf_text()), C.parse_stack(process_text())
        rows = C.compare_corner(itf, process, 'TYP', C.itf_metal_geometry(itf))
        self.assertTrue(rows[0]['matches_itf']['rho_exact'])
        self.assertFalse(rows[1]['matches_itf']['rho_exact'])
        self.assertEqual(rows[1]['rho_difference_ohm_um'], Decimal('-.00002'))
        self.assertTrue(all(all(value for key, value in row['matches_itf'].items() if key != 'rho_exact') for row in rows))

    def test_corner_gap_fit_is_distinguished_from_unchanged_itf_geometry(self):
        itf, process = C.parse_stack(itf_text()), C.parse_stack(process_text())
        process['CONDUCTOR', 'Metal1']['distance'] = Decimal('1.241')
        process['DIELECTRIC', 'd1']['thickness'] = Decimal('1.24128')
        with localcontext() as context:
            context.prec = 50
            rows = C.compare_corner(itf, process, 'MIN', C.itf_metal_geometry(itf))
        self.assertFalse(rows[0]['matches_itf']['gap'])
        self.assertEqual(rows[0]['dielectric_sum_minus_declared_gap_um'], Decimal('.00028'))
        self.assertEqual(rows[0]['plate_fit']['scale_ratio'], '37/31')
        self.assertLess(abs(rows[0]['plate_fit']['stored_minus_expected_gap_um']), Decimal('.0003'))

    def test_width_delta_geometry_and_nonpositive_bias_refuse(self):
        itf, process = C.parse_stack(itf_text()), C.parse_stack(process_text())
        process['CONDUCTOR', 'Metal1']['width_delta'] = Decimal('-.064')
        rows = C.compare_corner(itf, process, 'MIN', C.itf_metal_geometry(itf))
        self.assertEqual(rows[0]['draft_process']['solver_wire_width_um_at_minimum_drawn_width'], Decimal('.096'))
        self.assertEqual(rows[0]['draft_process']['solver_spacing_um_at_minimum_drawn_spacing'], Decimal('.244'))
        process['CONDUCTOR', 'Metal1']['width_delta'] = Decimal('-.16')
        with self.assertRaises(ValueError):
            C.compare_corner(itf, process, 'MIN', C.itf_metal_geometry(itf))

    def test_metal_membership_order_is_not_inferred_from_names(self):
        itf, process = C.parse_stack(itf_text()), C.parse_stack(process_text())
        first = process.pop(('CONDUCTOR', 'Metal1'))
        process['CONDUCTOR', 'Metal1'] = first
        with self.assertRaisesRegex(ValueError, 'order'):
            C.compare_corner(itf, process, 'TYP', C.itf_metal_geometry(itf))


class IntakeTests(unittest.TestCase):
    def make_intake(self, base):
        for producer in ('fetch.py', 'fetch-rules.py'):
            (base / producer).write_text('not executable source\n')
        documents = []
        for filename, schema, count, producer in [('report.json', 'pinwheel.rc-upstream-source-intake.v1', 18, 'fetch.py'),
                                                  ('rules-intake.json', 'pinwheel.rc-draft-rules-intake.v1', 3, 'fetch-rules.py')]:
            rows = []
            for index in range(count):
                pr = 1251 if filename == 'report.json' and index < 3 else 1237
                path = filename + '/' + str(index)
                data = ('frozen input ' + str(index)).encode()
                local = base / ('pr' + str(pr)) / path
                local.parent.mkdir(parents=True, exist_ok=True)
                local.write_bytes(data)
                rows.append({'pr': pr, 'path': path, 'bytes': len(data), 'commit': C.COMMITS[pr],
                             'sha256': C.sha256(data), 'git_blob_sha1': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
                             'url': 'https://raw.githubusercontent.com/IHP-GmbH/IHP-Open-PDK/' + C.COMMITS[pr] + '/' + path})
            document = {'schema': schema, 'qualified': False, 'native_executed': False, 'files': rows,
                        'producer_sha256': C.sha256((base / producer).read_bytes())}
            (base / filename).write_text(json.dumps(document))
            documents.append(document)
        return documents

    def test_all21_blob_and_producer_hashes_checked_without_execution(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            self.make_intake(base)
            intakes, files = C.checked_intake(base)
            self.assertEqual(len(files), 21)
            self.assertEqual(len(intakes), 2)
            (base / 'pr1251/report.json/0').write_text('tampered')
            with self.assertRaisesRegex(ValueError, 'hash/size'):
                C.checked_intake(base)

    def test_membership_path_commit_url_blob_and_qualified_controls(self):
        for mutation in ('duplicate', 'escape', 'commit', 'url', 'blob', 'qualified', 'producer'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                base = Path(temporary)
                documents = self.make_intake(base)
                document = deepcopy(documents[0])
                row = document['files'][0]
                if mutation == 'duplicate': document['files'][1] = row
                if mutation == 'escape': row['path'] = '../escaped'
                if mutation == 'commit': row['commit'] = '0' * 40
                if mutation == 'url': row['url'] += '?other'
                if mutation == 'blob': row['git_blob_sha1'] = '0' * 40
                if mutation == 'qualified': document['qualified'] = True
                if mutation == 'producer': (base / 'fetch.py').write_text('changed')
                (base / 'report.json').write_text(json.dumps(document))
                with self.assertRaises(ValueError): C.checked_intake(base)

    def test_duplicate_json_key_refuses(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON'):
            json.loads('{"a": 1, "a": 2}', object_pairs_hook=C.unique_object)


class RulesInventoryTests(unittest.TestCase):
    def rules(self):
        text = 'LayerCount 5\nCorners 1 : TYP\n'
        for index in range(1, 6):
            text += (f'Metal {index} RESOVER\nWIDTH Table 1 entries: .2\n'
                     f'Metal {index} RESOVER 0\nDIST count 2 width .2\n'
                     '0 0 0 .0004\n0 .2 0 .0004\nEND DIST\n'
                     f'Metal {index} OVER1\nWIDTH Table 0 entries: \n')
        return text

    def test_width_coverage_and_synthetic_resistance_rows_are_inventory_only(self):
        inventory = C.inventory_rules(self.rules(), 'TYP')
        self.assertEqual(len(inventory['empty_width_tables']), 5)
        self.assertEqual(inventory['widths_um_by_metal_index']['1'], [Decimal('.2')])
        self.assertEqual(inventory['first_resover_grid_by_metal_index']['1']['rows'], 2)
        self.assertIn('not full', inventory['scope'])

    def test_missing_wrong_count_nonuniform_negative_width_or_wrong_corner_refuse(self):
        text = self.rules()
        for changed in (text.replace('DIST count 2', 'DIST count 3', 1),
                        text.replace('0 .2 0 .0004', '0 .2 0 .0005', 1),
                        text.replace('WIDTH Table 1 entries: .2', 'WIDTH Table 2 entries: .2', 1),
                        text.replace('WIDTH Table 1 entries: .2', 'WIDTH Table 1 entries: -.2', 1),
                        text.replace('Corners 1 : TYP', 'Corners 1 : MIN'),
                        text.replace('Metal 1 RESOVER 0', 'Metal 6 RESOVER 0')):
            with self.subTest(changed=changed[:80]), self.assertRaises(ValueError):
                C.inventory_rules(changed, 'TYP')


if __name__ == '__main__':
    unittest.main()
