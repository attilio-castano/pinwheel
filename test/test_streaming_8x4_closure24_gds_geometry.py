"""Portable exact8x4 geometry/custody controls; no CAD or ignored evidence."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_gds_geometry as G


class Points(list):
    def tolist(self):
        return list(self)


class Polygon:
    def __init__(self, box, layer=50, datatype=2):
        x, y, x2, y2 = box
        self.points = Points([[x, y], [x, y2], [x2, y2], [x2, y]])
        self.layer, self.datatype = layer, datatype

    def bounding_box(self):
        return ([min(p[0] for p in self.points), min(p[1] for p in self.points)],
                [max(p[0] for p in self.points), max(p[1] for p in self.points)])

    def area(self):
        points = self.points + self.points[:1]
        return abs(sum(a[0]*b[1]-b[0]*a[1] for a, b in zip(points, points[1:])))/2


def pins():
    return {name: dict(bounds_um=[2+i*10, 709.64, 2.3+i*10, 710.64],
                       center_um=[2.15+i*10, 710.14])
            for i, name in enumerate(sorted(G.A.public_names()))}


def geometry():
    expected = pins()
    polygons = [Polygon(G.EXPECTED_BOUNDS, 189, 4)] + [
        Polygon(row['bounds_um']) for row in expected.values()]
    labels = [SimpleNamespace(text=name, layer=50, texttype=25, origin=row['center_um'])
              for name, row in expected.items()]
    top = SimpleNamespace(name=G.V.Q.TOP, labels=labels,
                          bounding_box=lambda: [[0.0, 0.0], [1724.16, 710.64]],
                          get_polygons=lambda **kw: polygons)
    return top, polygons, expected


def template():
    lines = ['UNITS DISTANCE MICRONS 1000 ;', 'DIEAREA ( 0 0 ) ( 1724160 710640 ) ;']
    lines += [f'ROW ROW_{i} CoreSite 2880 {3780+i*3780} '+
              ('N' if i % 2 == 0 else 'FS')+' DO 3580 BY 1 STEP 480 0 ;'
              for i in range(186)]
    lines += ['PINS 43 ;']
    for i, name in enumerate(sorted(G.A.public_names())):
        direction = 'INPUT' if name in {'clk', 'ena', 'rst_n'} or name.startswith(('ui_in[', 'uio_in[')) else 'OUTPUT'
        lines += [f'- {name} + NET {name} + DIRECTION {direction} + USE SIGNAL',
                  '+ PORT', '+ LAYER Metal4 ( 0 0 ) ( 300 1000 )',
                  f'+ PLACED ( {2000+i*10000} 709640 ) N ;']
    return '\n'.join(lines+['END PINS'])+'\n'


class GeometryControls(unittest.TestCase):
    def test_exact8x4_passes_but_old6x4_boundary_never_passes(self):
        top, polygons, expected = geometry()
        result = G.measure(top, polygons, expected)
        self.assertTrue(result['exact_top_bbox_8x4'])
        self.assertTrue(result['exact_rectangular_prBoundary_189_4'])
        self.assertTrue(result['all43_exact_Metal4_pin_rectangles_and_50_25_labels'])
        polygons[0] = Polygon([0, 0, 1289.28, 710.64], 189, 4)
        self.assertFalse(G.measure(top, polygons, expected)['exact_rectangular_prBoundary_189_4'])

    def test_boundary_must_be_one_exact_rectangle_with_no_outside_bbox(self):
        for mutate in ('duplicate', 'wrong_layer', 'nonrectangle', 'outside'):
            top, polygons, expected = geometry()
            if mutate == 'duplicate':polygons.append(Polygon(G.EXPECTED_BOUNDS, 189, 4))
            elif mutate == 'wrong_layer':polygons[0].datatype = 0
            elif mutate == 'nonrectangle':polygons[0].points.insert(1, [0.001, 100])
            else:top.bounding_box = lambda: [[0, 0], [1724.161, 710.64]]
            result = G.measure(top, polygons, expected)
            self.assertFalse(result['exact_top_bbox_8x4'] and result['exact_rectangular_prBoundary_189_4'])

    def test_each_public_rectangle_is_exact_unique_and_on_pin_purpose(self):
        for mutate in ('missing', 'duplicate', 'large_covering', 'wrong_purpose'):
            top, polygons, expected = geometry()
            if mutate == 'missing':polygons.pop(1)
            elif mutate == 'duplicate':polygons.append(deepcopy(polygons[1]))
            elif mutate == 'large_covering':polygons[1] = Polygon([1, 709, 3, 710.64])
            else:polygons[1].datatype = 0
            self.assertFalse(G.measure(top, polygons, expected)['all43_exact_Metal4_pin_rectangles_and_50_25_labels'])
        top, polygons, expected = geometry()
        polygons.append(Polygon([1000, 10, 1002.1, 700]))  # legitimate extra PG pin geometry
        self.assertTrue(G.measure(top, polygons, expected)['all43_exact_Metal4_pin_rectangles_and_50_25_labels'])

    def test_labels_require_exact_name_layer_purpose_center_and_uniqueness(self):
        for mutate in ('missing', 'duplicate', 'wrong_layer', 'wrong_purpose', 'wrong_center'):
            top, polygons, expected = geometry()
            if mutate == 'missing':top.labels.pop()
            elif mutate == 'duplicate':top.labels.append(deepcopy(top.labels[0]))
            elif mutate == 'wrong_layer':top.labels[0].layer = 49
            elif mutate == 'wrong_purpose':top.labels[0].texttype = 2
            else:top.labels[0].origin = [0, 0]
            self.assertFalse(G.measure(top, polygons, expected)['all43_exact_Metal4_pin_rectangles_and_50_25_labels'])
        top, polygons, expected = geometry();expected.pop(next(iter(expected)))
        with self.assertRaises(ValueError):G.measure(top, polygons, expected)

    def test_gds_units_precision_and_unique_top_are_not_assumed(self):
        top, polygons, expected = geometry()
        lib = SimpleNamespace(unit=1e-6, precision=1e-9, cells=[top], top_level=lambda: [top])
        fake = SimpleNamespace(read_gds=lambda _: lib)
        with patch.dict(sys.modules, {'gdstk': fake}):
            self.assertEqual(G.load_measurement('unused.gds', expected)['cells'], 1)
            for key, value in [('unit', 1e-3), ('precision', 1e-6)]:
                old = getattr(lib, key);setattr(lib, key, value)
                with self.assertRaises(ValueError):G.load_measurement('unused.gds', expected)
                setattr(lib, key, old)
            lib.top_level = lambda: [top, top]
            with self.assertRaises(ValueError):G.load_measurement('unused.gds', expected)


class CustodyControls(unittest.TestCase):
    def test_certified_template_uses8x4_allocation_hash_and_complete_pins(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);inputs = root/'inputs';inputs.mkdir()
            template_path = inputs/'tt_block_8x4_pgvdd.def';template_path.write_text(template())
            allocation = inputs/'allocation.json'
            row = dict(schema='pinwheel.streaming-8x4-allocation.v1', tiles='8x4', die_dbu=list(G.A.DIE),
                       core_dbu=list(G.A.CORE), dbu_per_micron=1000, public_pin_count=43,
                       template_sha256=G.S.sha(template_path))
            allocation.write_text(json.dumps(row));base = {'input_sha256': {
                'allocation.json': G.S.sha(allocation), 'tt_block_8x4_pgvdd.def': G.S.sha(template_path)}}
            with patch.object(G.A, 'ALLOCATION', allocation):
                result = G.certified_template(root, base);self.assertEqual(len(result[2]), 43)
                template_path.write_text(template().replace('1724160', '1289280'))
                row['template_sha256'] = G.S.sha(template_path);allocation.write_text(json.dumps(row))
                base['input_sha256'] = {'allocation.json': G.S.sha(allocation), 'tt_block_8x4_pgvdd.def': G.S.sha(template_path)}
                with self.assertRaises(ValueError):G.certified_template(root, base)
                template_path.write_text(template());base['input_sha256']['tt_block_8x4_pgvdd.def'] = '0'*64
                with self.assertRaises(ValueError):G.certified_template(root, base)

    def test_runtime_requires_exact_precheck_and_sealed_import_payload(self):
        lock = {'python_version_prefix': '3.12.', 'precheck_python_packages': {'gdstk': '0.9.52', 'numpy': '1.26.4'}}
        row = dict(python_version='3.12.14 example', gdstk_version='0.9.52', packages=lock['precheck_python_packages'],
                   flags=dict(optimize=0, no_user_site=1, dont_write_bytecode=True),
                   library_payload_sha256={'/runtime/gdstk.py': 'a'*64, '/runtime/numpy.py': 'b'*64},
                   actual_package_imports={'gdstk': {'path': '/runtime/gdstk.py', 'sha256': 'a'*64},
                                           'numpy': {'path': '/runtime/numpy.py', 'sha256': 'b'*64}})
        G.validate_runtime(row, lock)
        for key, value in [('python_version', '3.13.5'), ('gdstk_version', '0.9.53'),
                           ('packages', {'gdstk': '0.9.52'}), ('library_payload_sha256', {})]:
            bad = deepcopy(row);bad[key] = value
            with self.assertRaises(ValueError):G.validate_runtime(bad, lock)
        for key, value in [('optimize', 1), ('no_user_site', 0), ('dont_write_bytecode', False)]:
            bad = deepcopy(row);bad['flags'][key] = value
            with self.assertRaises(ValueError):G.validate_runtime(bad, lock)
        bad = deepcopy(row);bad['actual_package_imports']['gdstk']['path'] = '/outside/fake.py'
        with self.assertRaises(ValueError):G.validate_runtime(bad, lock)
        bad = deepcopy(row);bad['actual_package_imports'] = {}
        with self.assertRaises(ValueError):G.validate_runtime(bad, lock)

    def test_same_target_gds_authority_and_raw_streamout_hash_are_joined(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);viewdir = root/'views';viewdir.mkdir();basepath = root/'base';basepath.mkdir()
            flow = root/'flow';flow.mkdir()
            for p in [viewdir/'report.json', viewdir/'preparation.json', viewdir/'design.gds',
                      root/'final.odb', root/'physical.json', root/'state.json', root/'allocation.json',
                      root/'template.def', basepath/'preparation.json', flow/'resolved.json']:
                p.write_text('{}')
            (root/'tools').mkdir();(root/'tools/streaming-tt-signoff.json').write_text('{}')
            target = {'actual_odb': G.bound(root/'final.odb'), 'physical_report': G.bound(root/'physical.json'),
                      'physical_state': G.bound(root/'state.json')}
            view = dict(target=target, physical_candidate={'actual': 'same'},
                        artifact_sha256={'design.gds': G.S.sha(viewdir/'design.gds')})
            prep = dict(prepared=str(basepath), source_flow=str(flow))
            base = dict(input_sha256={'exact': 'sealed'}, pdk_identity={'complete': 'sealed'})
            stream = dict(source_odb_sha256=target['actual_odb']['sha256'],
                          generated_files_sha256={'design.gds': G.S.sha(viewdir/'design.gds')})
            (viewdir/'native-report.json').write_text(json.dumps(stream))
            with patch.object(G, 'ROOT', root),patch.object(G.V, 'closed_views', return_value=(view, prep)),\
                    patch.object(G.V.P, 'verify', return_value=base),\
                    patch.object(G, 'certified_template', return_value=(root/'allocation.json', root/'template.def', pins())):
                result = G.authority(viewdir/'report.json')
                self.assertEqual(result['input_bindings']['selected_ODB'], target['actual_odb'])
                self.assertEqual(result['complete_view_artifact_sha256'], view['artifact_sha256'])
                stream['source_odb_sha256'] = '0'*64;(viewdir/'native-report.json').write_text(json.dumps(stream))
                with self.assertRaisesRegex(ValueError, 'same-target'):G.authority(viewdir/'report.json')
                stream['source_odb_sha256'] = target['actual_odb']['sha256']
                (viewdir/'native-report.json').write_text(json.dumps(stream));(viewdir/'design.gds').write_text('changed')
                with self.assertRaisesRegex(ValueError, 'same-target'):G.authority(viewdir/'report.json')

    def test_source_closure_requires_immutable_commit_and_exact_current_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);(root/'producer.py').write_text('exact\n')
            with patch.object(G, 'ROOT', root),patch.object(G, 'dependency_closure', return_value={'files': ['producer.py']}),\
                    patch.object(G.subprocess, 'check_output', return_value=b'exact\n'):
                result = G.source_identity('a'*40)
                self.assertEqual(result['sha256']['producer.py'], G.S.sha(root/'producer.py'))
                with self.assertRaises(ValueError):G.source_identity('HEAD')
                (root/'producer.py').write_text('changed\n')
                with self.assertRaisesRegex(ValueError, 'Commit the exact'):G.source_identity('a'*40)

    def test_output_is_fresh_campaign_owned_and_outside_views_tree(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve();campaign = root/G.V.Q.T.PG.CAMPAIGN
            campaign.mkdir(parents=True);views = campaign/'views';views.mkdir()
            with patch.object(G, 'ROOT', root):
                self.assertEqual(G.output_path(campaign/'geometry.json', views/'report.json'), campaign/'geometry.json')
                for output in (views/'geometry.json', root/'outside.json'):
                    with self.assertRaises(ValueError):G.output_path(output, views/'report.json')
                old = campaign/'old.json';old.write_text('{}')
                with self.assertRaises(ValueError):G.output_path(old, views/'report.json')

    def test_measurement_preserves_failed_geometry_and_rechecks_all_boundaries(self):
        top, polygons, expected = geometry()
        measured = dict(geometry=G.measure(top, polygons, expected))
        authority = dict(input_bindings={'GDS': {'path': '/actual.gds'}}, pins=expected)
        source = dict(commit='frozen', sha256={})
        with patch.object(G, 'authority', return_value=authority),patch.object(G, 'source_identity', return_value=source),\
                patch.object(G, 'observe_runtime', return_value={'sealed': True}),patch.object(G, 'load_measurement', return_value=measured):
            row = G.build('/views.json');self.assertTrue(row['passed']);self.assertFalse(row['physical_acceptance'])
            measured['geometry']['exact_top_bbox_8x4'] = False
            row = G.build('/views.json');self.assertTrue(row['observation_completed']);self.assertFalse(row['passed'])
        changed = deepcopy(authority);changed['input_bindings']['GDS']['path'] = '/changed.gds'
        with patch.object(G, 'authority', side_effect=[authority, changed]),patch.object(G, 'source_identity', return_value=source),\
                patch.object(G, 'observe_runtime', return_value={'sealed': True}),patch.object(G, 'load_measurement', return_value=measured):
            with self.assertRaisesRegex(ValueError, 'target/input/PDK/source changed'):G.build('/views.json')
        with patch.object(G, 'authority', return_value=authority),patch.object(G, 'source_identity', return_value=source),\
                patch.object(G, 'observe_runtime', side_effect=[{'sealed': 1}, {'sealed': 2}]),patch.object(G, 'load_measurement', return_value=measured):
            with self.assertRaisesRegex(ValueError, 'import payload changed'):G.build('/views.json')

    def test_verifier_reuses_original_commit_and_never_promotes_claims(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve();campaign = root/G.V.Q.T.PG.CAMPAIGN;campaign.mkdir(parents=True)
            path = campaign/'geometry.json';views = campaign/'views/report.json'
            row = dict(schema=G.SCHEMA, HOST_only=True, physical_acceptance=False, passed=False,
                       authority={'views_report': {'path': str(views)}}, source={'commit': 'original'})
            path.write_text(json.dumps(row))
            with patch.object(G, 'ROOT', root),patch.object(G, 'build', return_value=row) as build:
                self.assertFalse(G.verify(path)['passed']);build.assert_called_once_with(str(views), 'original')
                bad = deepcopy(row);bad['physical_acceptance'] = True;path.write_text(json.dumps(bad))
                with self.assertRaises(ValueError):G.verify(path)
                path.write_text(json.dumps(row));different = deepcopy(row);different['passed'] = True
                with patch.object(G, 'build', return_value=different):
                    with self.assertRaisesRegex(ValueError, 'does not rederive'):G.verify(path)


if __name__ == '__main__':
    unittest.main()
