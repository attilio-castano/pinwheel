"""HOST-only frozen eight-case nominal all-layer follow-on preparation.

No field operator, solver, CAD process or recovered executable runs here.
Existing M1 files remain immutable; both closed batch universes are fixed now.
"""
import argparse
import ast
import copy
from decimal import Decimal
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_process as P
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_layered_plan as M
import streaming_8x4_rc_layered_geometry as G
import streaming_8x4_rc_all_layers_reference as F
from streaming_tt_rc_compare import itf_metal_geometry

SCHEMA = 'pinwheel.streaming-8x4-rc-all-layers-plan.v1'
M1_REFERENCE_HASH = '185bac5e2f4346aeb03ebda83b827e7fb0336ffbc51c8a0a46f24b4b72aa910c'
M1_NATIVE_HASH = '6ea3613a03b2c29b8706da76d02e5a4f67ae2f5dc6ff55ddfe5cc1e27b418cc4'
BATCHES = {
    'first5': ['TYP-Metal2-self', 'TYP-Metal3-self', 'TYP-Metal4-self',
               'TYP-Metal1-Metal2-centered', 'TYP-Metal2-Metal3-centered'],
    'remaining3': ['TYP-TopMetal1-self', 'TYP-Metal3-Metal4-centered', 'TYP-Metal4-TopMetal1-centered'],
}
LENGTH_EXTENSIONS = [('10', '20'), ('20', '20'), ('30', '20'), ('20', '30'), ('30', '30')]
NEW_SOURCES = ['streaming_8x4_rc_all_layers_reference.py', 'streaming_8x4_rc_all_layers_plan.py',
               'streaming_8x4_rc_all_layers_execute.py', 'streaming_8x4_rc_all_layers_analyze.py']


def case_universe(itf):
    heights = itf_metal_geometry(itf); layers = M.materials(itf)
    def row(metal, index):
        data = heights[metal]; half = data['minimum_width_um'] / 2
        return {'name': 'W' + str(index), 'layer': metal,
                'width_um': str(data['minimum_width_um']),
                'bounds_um': list(map(str, (-half, half, data['bottom_um'], data['top_um'])))}
    definitions = {}
    for metal in P.METALS[1:]:
        definitions['TYP-' + metal + '-self'] = [row(metal, 1)]
    for lo, hi in zip(P.METALS, P.METALS[1:]):
        definitions['TYP-' + lo + '-' + hi + '-centered'] = [row(lo, 1), row(hi, 2)]
    result = []
    for batch, names in BATCHES.items():
        for name in names:
            geometry = definitions[name]
            result.append({'name': name, 'batch': batch, 'corner': 'TYP', 'role': 'new_nominal_only',
                           'layer_geometry': geometry,
                           'rectangles': [{k: v for k, v in r.items() if k in ('name', 'bounds_um')} for r in geometry],
                           'epsilon_layers': layers})
    P.need(len(result) == len(definitions) == 8, 'All-layer universe membership differs')
    return result


def operator_derivation():
    old = Path(__file__).with_name('streaming_8x4_rc_layered_reference.py')
    new = Path(F.__file__)
    def body(path):
        text = path.read_text(); function = next(n for n in ast.parse(text).body if isinstance(n, ast.FunctionDef) and n.name == 'solve')
        return '\n'.join(text.splitlines()[function.body[0].lineno - 1:function.end_lineno])
    original, adapted = body(old), body(new)
    P.need(original == adapted, 'All-layer FVM equation/operator body differs')
    return {'source_path': old.name, 'source_sha256': P.sha(old), 'adapted_path': new.name,
            'adapted_sha256': P.sha(new), 'solve_body_sha256': hashlib.sha256(original.encode()).hexdigest(),
            'solve_body_byte_identical': True,
            'changes': ['linear axis subdivision emits strict interior knots only; original anchors retained',
                        'default/explicit node admission 40000 to 65000; equation and numerical tolerances unchanged']}


def reference_storage_budget():
    """Conservative source-count estimate; no operator or large allocation runs."""
    nodes = 65000; memory = 2147483648
    total = nodes * 4096 * 4 + 268435456 + 134217728
    P.need(total < memory, 'Reference structural storage budget has insufficient headroom')
    return {'maximum_nodes': nodes, 'maximum_undirected_edges_per_node': 2,
            'maximum_neighbor_entries_per_node': 4, 'maximum_conductors_and_RHS_vectors': 2,
            'CG_simultaneous_vector_budget': 10,
            'object_storage_budget_bytes_per_node': 4096,
            'allocator_and_transient_factor': 4,
            'interpreter_and_worker_reserve_bytes': 268435456, 'scratch_bytes': 134217728,
            'conservative_total_bytes': total, 'cgroup_memory_bytes': memory,
            'headroom_bytes': memory - total, 'measured_RSS': False,
            'source_count_basis': 'rectangular nearest-neighbor graph; edges<=2N, neighbors<=4N; partition/potential dictionaries and construction temporaries O(N); at most two conductors; CG list comprehensions do not retain iteration history',
            'object_estimate_basis': 'conservatively charge independent int/float/tuple/list references even when shared, plus partition/potential maps and ten full float-vector buffers; 4096B/node is above these CPython64-bit object counts, then quadrupled',
            'limitations': 'structural admission estimate, not a formal RSS bound or timing guarantee; actual1CPU2GiB/no-extra-swap/120s enforcement is mandatory',
            'operator_source_sha256': P.sha(F.__file__),
            'CG_source_sha256': P.sha(Path(__file__).with_name('streaming_8x4_rc_reference.py'))}


def grid_inventory(cases):
    rows = []
    for case in cases:
        for step in ('.04', '.02'):
            for extent in ('16', '32'):
                limit = float(extent); xa, ya = {-limit, limit}, {0., limit}
                for r in case['rectangles']:
                    x0, x1, y0, y1 = map(float, r['bounds_um']); xa.update((x0, x1)); ya.update((y0, y1))
                for slab in case['epsilon_layers']:
                    for y in map(float, slab[:2]):
                        if 0 < y < limit:
                            ya.add(y)
                xs, ys = F._axis(sorted(xa), float(step)), F._axis(sorted(ya), float(step))
                P.need(set(xa) <= set(xs) and set(ya) <= set(ys), 'All-layer grid anchor admission differs')
                rows.append({'case': case['name'], 'batch': case['batch'], 'step_um': step, 'extent_um': extent,
                             'nodes': len(xs) * len(ys), 'nx': len(xs), 'ny': len(ys),
                             'within_reviewed_50000_node_cap': len(xs) * len(ys) <= 50000,
                             'within_reviewed_65000_node_cap': len(xs) * len(ys) <= 65000,
                             'minimum_dx_um': min(b - a for a, b in zip(xs, xs[1:])),
                             'minimum_dy_um': min(b - a for a, b in zip(ys, ys[1:])),
                             'exact_material_and_conductor_anchors_present': True})
    P.need(len(rows) == 32, 'All-layer grid expected membership differs')
    return rows


def physical_files(emitted):
    unit = json.loads(emitted['unit-map.json']); source = {}
    witness = {(r['file'], r['line']): r for r in unit['all_coordinate_and_reference_witnesses']}
    for name, value in emitted.items():
        if name == 'unit-map.json':
            continue
        lines = []
        for index, line in enumerate(value.splitlines(), 1):
            fields = line.split(); row = witness.get((name, index))
            if row:
                positions = range(2, 14) if fields[0] == 'Q' else range(7, 10)
                for position, number in zip(positions, row['SI_m']):
                    fields[position] = G.token(Fraction(number))
                lines.append(' '.join(fields))
            else:
                lines.append(line.replace('raw coordinates=2**20 * SI metres', 'coordinates SI meters'))
        source[name] = '\n'.join(lines) + '\n'
        P.need(hashlib.sha256(source[name].encode()).hexdigest() == unit['SI_files_sha256'][name],
               'Reconstructed exact physical SI authority differs')
    return source


def prepare(intake, m1_reference, m1_native, runtime, output):
    P.need(not output.exists() and output.parent.is_dir(), 'All-layer preparation owner must be fresh')
    P.need(P.sha(m1_reference) == M1_REFERENCE_HASH and P.sha(m1_native) == M1_NATIVE_HASH,
           'Frozen M1 prerequisite plan identities differ')
    original_ref = json.loads(m1_reference.read_text()); original_native = json.loads(m1_native.read_text())
    frozen = dict(original_ref['producers_sha256'], **original_native['producers_sha256'])
    frozen['streaming_8x4_rc_layered_analyze.py'] = P.sha(Path(__file__).with_name('streaming_8x4_rc_layered_analyze.py'))
    for name, value in frozen.items():
        P.need(P.sha(Path(__file__).with_name(name)) == value, 'Frozen M1 producer differs before preparation')
    texts, _ = P.verify_intake(intake); itf = P.parse_stack(texts['itf_typ']); cases = case_universe(itf)
    grids = grid_inventory(cases); derivation = operator_derivation()
    policy = copy.deepcopy(original_native['protocol'])
    policy['maximum_reference_nodes'] = 65000
    policy['material_geometry_convention'] = 'exact merged TYP ITF routing heights; each conductor embedded in its following oxide; full passivation/air stack'
    policy['process_corner_scope'] = 'new nominal TYP cases only; no held-out range or corner envelope qualification'
    for kind, memory, scratch, calls in (('reference', 2147483648, 134217728, 32), ('native', 6442450944, 536870912, 200)):
        policy[kind + '_resources'] = {'cpus': 1, 'memory_bytes': memory, 'scratch_bytes': scratch,
                                       'seconds_per_call': 120, 'maximum_calls': calls,
                                       'work_seconds': 1800, 'outer_seconds': 1860, 'root_go_required': True}
    output.mkdir(); geometry = output / 'geometry'; physical = output / 'physical-SI'
    geometry.mkdir(); physical.mkdir(); baseline = output / 'baseline-M1'; baseline.mkdir()
    (baseline / 'reference-plan.json').write_bytes(m1_reference.read_bytes())
    (baseline / 'native-plan.json').write_bytes(m1_native.read_bytes())
    (output / 'itf-typ.txt').write_bytes(texts['itf_typ'].encode())
    generated = []; si_rows = []
    for case in cases:
        for length, extension in LENGTH_EXTENSIONS:
            name = case['name'] + '-L' + length + '-E' + extension
            normalized, certificate = G.from_plan(case, length, extension)
            si = physical_files(normalized); destination = geometry / name; destination.mkdir()
            si_destination = physical / name; si_destination.mkdir()
            for filename, text in normalized.items():
                (destination / filename).write_text(text)
            for filename, text in si.items():
                (si_destination / filename).write_text(text)
            (destination / 'geometry-certificate.json').write_text(json.dumps(certificate, indent=2) + '\n')
            si_rows.append({'case': name, 'files': E.tree(si_destination)})
            generated.append({'name': name, 'case': case['name'], 'batch': case['batch'],
                              'length_um': length, 'extension_um': extension,
                              'coordinate_unit_m': G.COORDINATE_UNIT_M,
                              'matrix_names': ['g' + str(i + 1) + '_' + n for i, n in enumerate(certificate['conductors'])],
                              'files': E.tree(destination)})
    (physical / 'manifest.json').write_text(json.dumps({'schema': 'pinwheel.streaming-8x4-all-layers-SI-authority.v1',
        'field_solver_executed': False, 'cases': si_rows}, indent=2) + '\n')
    (geometry / 'manifest.json').write_text(json.dumps({'schema': 'pinwheel.streaming-8x4-all-layers-geometry.v1',
        'field_solver_executed': False, 'physical_SI_source_owner': str(physical.resolve()),
        'physical_source_manifest_sha256': P.sha(physical / 'manifest.json'), 'cases': generated}, indent=2) + '\n')
    producers = dict(frozen)
    for name in NEW_SOURCES:
        producers[name] = P.sha(Path(__file__).with_name(name))
    batches = {name: {'case_names': names, 'reference_calls': 4 * len(names), 'native_calls': 25 * len(names),
                      'prior_closed_batch_required': None if name == 'first5' else 'first5',
                      'all_case_grids_within_node_admission': all(r['within_reviewed_65000_node_cap'] for r in grids if r['batch'] == name)}
               for name, names in BATCHES.items()}
    result = {'schema': SCHEMA, 'qualified': False, 'model_qualified': False, 'execution_admitted': False,
              'native_executed': False, 'reference_executed': False, 'cases': cases, 'geometry_cases': generated,
              'batches': batches, 'protocol': policy, 'FVM_derivation': derivation,
              'BEM_geometry_source_sha256': P.sha(G.__file__), 'producer_sha256': producers,
              'frozen_M1_producers_sha256': frozen, 'M1_reference_plan_sha256': M1_REFERENCE_HASH,
              'M1_native_plan_sha256': M1_NATIVE_HASH,
              'M1_complete_pass_required_before_any_numerical_execution': True,
              'process_intake_manifest_sha256': P.sha(intake / 'manifest.json'),
              'ITF_TYP_sha256': P.sha(output / 'itf-typ.txt'),
              'geometry_manifest_sha256': P.sha(geometry / 'manifest.json'),
              'physical_SI_manifest_sha256': P.sha(physical / 'manifest.json'),
              'runtime': E.tree(runtime), 'solver_sha256': E.P.SOLVER_SHA256,
              'grid_inventory': grids, 'maximum_actual_grid_nodes': max(r['nodes'] for r in grids),
              'reference_structural_storage_admission': reference_storage_budget(),
              'scope': 'eight new nominal self/centered-parallel adjacent-layer cases only; held-outs/corners/orthogonal/diagonal/shielding/final consumer coverage remain open'}
    P.need(P.sha(runtime / 'bin/FasterCap') == E.P.SOLVER_SHA256, 'Wrong all-layer solver runtime')
    for name, value in frozen.items():
        P.need(P.sha(Path(__file__).with_name(name)) == value, 'Frozen M1 producer changed during preparation')
    (output / 'plan.json').write_text(json.dumps(result, indent=2) + '\n')
    return {'plan': str(output / 'plan.json'), 'plan_sha256': P.sha(output / 'plan.json'),
            'physical_cases': len(cases), 'geometry_cases': len(generated), 'FVM_grids': len(grids),
            'maximum_actual_grid_nodes': result['maximum_actual_grid_nodes'], 'field_solver_executed': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('intake', 'm1-reference', 'm1-native', 'runtime', 'output'):
        p.add_argument('--' + name, type=Path, required=True)
    a = p.parse_args(); print(json.dumps(prepare(a.intake, a.m1_reference, a.m1_native, a.runtime, a.output), indent=2))


if __name__ == '__main__':
    main()
