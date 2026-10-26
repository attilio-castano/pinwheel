"""HOST-only exact 8x4 GDS boundary/public-pin observation of closed views.

This never launches CAD or grants official precheck, connectivity, DRC, model,
timing or tapeout acceptance. Read/verify with the pinned precheck interpreter.
"""
import argparse
from collections import Counter
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import re
import subprocess
import sys

import streaming_8x4_closure24_signoff_execute as V
import streaming_8x4_geometry as A
import streaming_tt_signoff as S
from streaming_tt_intake import dependency_closure

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 'pinwheel.closure24-exact-gds-geometry.v1'
ENTRIES = ('scripts/streaming_8x4_closure24_gds_geometry.py',
           'physical/streaming_8x4/allocation.json', 'tools/streaming-tt-signoff.json')
EXPECTED_BOUNDS = [0.0, 0.0, 1724.16, 710.64]
TOLERANCE_UM = 0.000001


def near(left, right):
    return len(left) == len(right) and all(abs(a-b) <= TOLERANCE_UM for a, b in zip(left, right))


def bound(path):
    path = S.regular(path)
    return dict(path=str(path), sha256=S.sha(path))


def source_identity(commit=None):
    commit = commit or subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                                               text=True, timeout=30).strip()
    S.require(re.fullmatch(r'[0-9a-f]{40}', commit) is not None, 'Use exact immutable producer commit')
    closure = dependency_closure(ROOT, ENTRIES)
    sources = {}
    for name in closure['files']:
        S.regular(ROOT/name)
        data = subprocess.check_output(['git', 'show', commit+':'+name], cwd=ROOT, timeout=30)
        S.require(hashlib.sha256(data).hexdigest() == S.sha(ROOT/name),
                  'Commit the exact GDS observation producer first: '+name)
        sources[name] = S.sha(ROOT/name)
    return dict(commit=commit, closure=closure, sha256=sources)


def certified_template(prepared, base):
    prepared = Path(prepared).resolve()
    allocation = S.regular(prepared/'inputs/allocation.json')
    template = S.regular(prepared/'inputs/tt_block_8x4_pgvdd.def')
    S.require(base['input_sha256'].get('allocation.json') == S.sha(allocation) == S.sha(A.ALLOCATION),
              'Certified/current 8x4 allocation differs')
    manifest = S.read(allocation)
    S.require(manifest.get('schema') == 'pinwheel.streaming-8x4-allocation.v1' and
              manifest.get('tiles') == '8x4' and manifest.get('die_dbu') == list(A.DIE) and
              manifest.get('dbu_per_micron') == 1000 and manifest.get('public_pin_count') == 43 and
              manifest.get('core_dbu') == list(A.CORE) and
              base['input_sha256'].get('tt_block_8x4_pgvdd.def') == S.sha(template) ==
              manifest.get('template_sha256'), 'Certified official 8x4 template differs')
    # The existing strict pure 8x4 parser checks rows, die, all exact public
    # names/directions, Metal4, coordinates, dimensions and orientations.
    pins = A.template_pins(template.read_text())
    return allocation, template, {
        name: dict(bounds_um=[x/1000 for x in box],
                   center_um=[(box[0]+box[2])/2000, (box[1]+box[3])/2000])
        for name, box in sorted(pins.items())}


def authority(views_path):
    views_path = S.regular(views_path)
    views, preparation = V.closed_views(views_path)
    prepared = Path(preparation['prepared']).resolve()
    base = V.P.verify(prepared)
    allocation, template, pins = certified_template(prepared, base)
    target = views['target']
    gds = S.regular(views_path.parent/'design.gds')
    stream = S.read(views_path.parent/'native-report.json')
    S.require(stream['source_odb_sha256'] == target['actual_odb']['sha256'] and
              stream['generated_files_sha256']['design.gds'] == S.sha(gds) ==
              views['artifact_sha256']['design.gds'], 'GDS is not the closed same-target streamout')
    paths = dict(views_report=views_path, views_preparation=views_path.parent/'preparation.json',
                 GDS=gds, streamout_report=views_path.parent/'native-report.json',
                 selected_ODB=target['actual_odb']['path'], physical_report=target['physical_report']['path'],
                 physical_state=target['physical_state']['path'], original_preparation=prepared/'preparation.json',
                 allocation=allocation, official_8x4_template=template,
                 resolved_configuration=Path(preparation['source_flow'])/'resolved.json',
                 tool_lock=ROOT/'tools/streaming-tt-signoff.json')
    bindings = {name: bound(path) for name, path in paths.items()}
    S.require(bindings['selected_ODB']['sha256'] == target['actual_odb']['sha256'], 'Selected ODB changed')
    return dict(views_report=bindings['views_report'], target=target,
                physical_candidate=views['physical_candidate'], input_bindings=bindings,
                complete_view_artifact_sha256=views['artifact_sha256'],
                certified_base_input_sha256=base['input_sha256'],
                certified_PDK_identity=base['pdk_identity'], pins=pins)


def validate_runtime(row, lock):
    S.require(lock['python_version_prefix'] == '3.12.' and
              row['python_version'].startswith('3.12.') and
              row['gdstk_version'] == lock['precheck_python_packages']['gdstk'] == '0.9.52' and
              row['packages'] == lock['precheck_python_packages'] and
              row['flags'] == dict(optimize=0, no_user_site=1, dont_write_bytecode=True),
              'Use pinned precheck Python3.12/gdstk0.9.52 and isolated unoptimized -B imports')
    S.require(set(row['actual_package_imports']) == {'gdstk', 'numpy'} and
        row['library_payload_sha256'] and all(
        row['library_payload_sha256'].get(item['path']) == item['sha256']
        for item in row['actual_package_imports'].values()), 'Imported package is outside sealed runtime payload')


def observe_runtime():
    import gdstk
    import numpy
    lock = S.read(ROOT/'tools/streaming-tt-signoff.json')
    aliases = {}
    declared = Path(sys.executable).absolute()
    link = declared
    seen = set()
    while link.is_symlink():
        S.require(str(link) not in seen, 'Cyclic interpreter alias')
        seen.add(str(link))
        aliases[str(link)] = dict(target=os.readlink(link), resolved=str(link.resolve()))
        link = (link.parent/os.readlink(link)).absolute()
    executable = S.regular(declared.resolve())
    roots = sorted({str((Path(prefix)/'lib').resolve()) for prefix in (sys.prefix, sys.base_prefix)})
    payload = {}
    for root in roots:
        payload.update(S.inventory(root, aliases=aliases))
    row = dict(python_version=sys.version, declared_executable=str(declared), executable=bound(executable),
               prefixes=dict(prefix=sys.prefix, base_prefix=sys.base_prefix), library_roots=roots,
               flags=dict(optimize=sys.flags.optimize, no_user_site=sys.flags.no_user_site,
                          dont_write_bytecode=sys.dont_write_bytecode),
               gdstk_version=gdstk.__version__,
               packages={name: importlib.metadata.version(name) for name in lock['precheck_python_packages']},
               actual_package_imports={name: bound(module.__file__) for name, module in
                                       [('gdstk', gdstk), ('numpy', numpy)]},
               library_payload_sha256=payload, runtime_aliases=aliases)
    validate_runtime(row, lock)
    return row


def rectangle(polygon, expected):
    bounds = [*polygon.bounding_box()[0], *polygon.bounding_box()[1]]
    corners = [[expected[0], expected[1]], [expected[0], expected[3]],
               [expected[2], expected[3]], [expected[2], expected[1]]]
    points = polygon.points.tolist()
    return (near(bounds, expected) and len(points) == 4 and
            all(sum(near(point, corner) for point in points) == 1 for corner in corners) and
            abs(polygon.area()-(expected[2]-expected[0])*(expected[3]-expected[1])) <= TOLERANCE_UM)


def measure(top, polygons, pins):
    S.require(set(pins) == A.public_names(), 'Not all43 official public pins')
    boundaries = [p for p in polygons if (p.layer, p.datatype) == (189, 4)]
    pin_shapes = [p for p in polygons if (p.layer, p.datatype) == (50, 2)]
    bbox = top.bounding_box()
    top_bbox = [*bbox[0], *bbox[1]] if bbox is not None else []
    rows = []
    for name, pin in sorted(pins.items()):
        labels = [label for label in top.labels if label.text == name]
        matches = [p for p in pin_shapes if rectangle(p, pin['bounds_um'])]
        rows.append(dict(name=name, expected=pin, label_count=len(labels),
                         exact_label=(len(labels) == 1 and labels[0].layer == 50 and
                                      labels[0].texttype == 25 and near(labels[0].origin, pin['center_um'])),
                         exact_pin_rectangle=len(matches) == 1, exact_rectangle_count=len(matches)))
    return dict(exact_top_bbox_8x4=near(top_bbox, EXPECTED_BOUNDS), top_bbox_um=top_bbox,
                exact_rectangular_prBoundary_189_4=(len(boundaries) == 1 and rectangle(boundaries[0], EXPECTED_BOUNDS)),
                prBoundary_polygons=[dict(bounds_um=[*p.bounding_box()[0], *p.bounding_box()[1]],
                                         area_um2=p.area(), vertices=p.points.tolist()) for p in boundaries],
                all43_exact_Metal4_pin_rectangles_and_50_25_labels=(len(rows) == 43 and
                    all(row['exact_label'] and row['exact_pin_rectangle'] for row in rows)),
                pins=rows, top_labels=[dict(text=l.text, layer=l.layer, texttype=l.texttype,
                                           origin=list(l.origin)) for l in top.labels],
                direct_polygon_inventory={str(pair): count for pair, count in
                                          sorted(Counter((p.layer, p.datatype) for p in polygons).items())},
                direct_pin_purpose_polygon_count=len(pin_shapes),
                additional_power_pin_geometry_not_inferred_as_public_signal_pins=True)


def load_measurement(path, pins):
    import gdstk
    library = gdstk.read_gds(path)
    tops = library.top_level()
    S.require(library.unit == 1e-6 and library.precision == 1e-9,
              'Unexpected GDS coordinate unit/precision')
    S.require(len(tops) == 1 and tops[0].name == V.Q.TOP, 'GDS top is absent/ambiguous/wrong')
    top = tops[0]
    geometry = measure(top, top.get_polygons(apply_repetitions=True, include_paths=True, depth=0), pins)
    return dict(unit=library.unit, precision=library.precision, cells=len(library.cells),
                top_level_cells=[cell.name for cell in tops], geometry=geometry)


def build(views_path, producer_commit=None):
    inputs = authority(views_path)
    producer = source_identity(producer_commit)
    before = observe_runtime()
    measured = load_measurement(inputs['input_bindings']['GDS']['path'], inputs['pins'])
    after = observe_runtime()
    S.require(before == after, 'Executable/import payload changed during GDS observation')
    S.require(authority(views_path) == inputs and source_identity(producer['commit']) == producer,
              'Closed target/input/PDK/source changed during GDS observation')
    geometry = measured['geometry']
    passed = all(geometry[key] for key in ('exact_top_bbox_8x4', 'exact_rectangular_prBoundary_189_4',
                                         'all43_exact_Metal4_pin_rectangles_and_50_25_labels'))
    return dict(schema=SCHEMA, HOST_only=True, native_executed=False, observation_completed=True,
                passed=passed, source=producer, authority=inputs, runtime_before=before, runtime_after=after,
                inputs_source_runtime_unchanged=True, measured=measured,
                official_nine_check_precheck_completed=False, routed_connectivity_proved=False,
                DRC_passed=False, physical_acceptance=False, model_qualified=False,
                qualified_timing=False, tapeout_ready=False,
                boundary='Exact actual8x4 GDS boundary/public signal-pin geometry only. Official9, route connectivity, device/antenna/DRC/LVS/PG/model/timing acceptance remain separate.')


def output_path(path, views_report):
    path = V.Q.owned(path, ROOT)
    S.require(not path.exists() and path.parent.is_dir(), 'Preserve earlier geometry output; parent must exist')
    S.require(not path.resolve().is_relative_to(Path(views_report).resolve().parent),
              'Keep geometry receipt outside immutable final views tree')
    return path


def verify(path):
    path = S.regular(path)
    V.Q.owned(path, ROOT)
    row = S.read(path)
    S.require(row.get('schema') == SCHEMA and row.get('HOST_only') is True and
              row.get('physical_acceptance') is False, 'Wrong typed HOST geometry receipt')
    S.require(not path.is_relative_to(Path(row['authority']['views_report']['path']).resolve().parent),
              'Geometry receipt is inside immutable final views tree')
    actual = build(row['authority']['views_report']['path'], row['source']['commit'])
    S.require(actual == row, 'GDS geometry/input/source/runtime receipt does not rederive')
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    read = sub.add_parser('read')
    read.add_argument('--views-report', type=Path, required=True)
    read.add_argument('--output', type=Path, required=True)
    check = sub.add_parser('verify')
    check.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    if args.action == 'verify':
        row = verify(args.report)
    else:
        path = output_path(args.output, args.views_report)
        row = build(args.views_report)
        with path.open('x') as stream:
            json.dump(row, stream, sort_keys=True, indent=2, allow_nan=False)
            stream.write('\n')
    print(json.dumps(dict(observation_completed=True, passed=row['passed'], physical_acceptance=False)))
    return 0 if row['passed'] else 2


if __name__ == '__main__':
    raise SystemExit(main())
