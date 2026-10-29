"""Frozen finite-wire RC pilot contracts; no solver is launched by this module.

This is a new experiment, not a repair of historical receipts.  A successful
pilot is neither a qualified process model nor routed-design signoff.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
import math
import re
import struct


SCHEMA = 'pinwheel.streaming-8x4-rc-pilot.v1'
EPS0 = Decimal('8.8541878128e-12')
SOURCE_PINS = {
    'tt_support': 'd66cf179e7bc4d296362ab7e2e3b344dc3c4f665',
    'tt_gds_action': '3412659307918422f3f0727917cf9b499aaca588',
    'ihp_draft_1237': 'ffdafdbb4abb17316fa0ffd221ea99c0475c4734',
    'ihp_dev_observed_20261022': '7c783c7c56086511be93bb2097bee656a26148bd',
    'fastercap_source': 'b42179a8fdd25ab42fe45527282b4a738d7e7f87',
}
SOLVER_SHA256 = 'b78b4938eb3e301653cee76808de12a5c37a5c567477f247b535a8319a1037d1'
NUM = r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'


def need(value, message):
    if not value:
        raise ValueError(message)


def number(value):
    need(type(value) in (str, int, Decimal), 'Numeric value must be an exact decimal token')
    token = str(value)
    need(len(token) <= 80 and re.fullmatch(NUM, token), 'Invalid/nonfinite decimal token')
    result = Decimal(token)
    need(result.is_finite() and abs(result) <= Decimal('1e100'), 'Unbounded decimal value')
    return result


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def digest(value):
    return hashlib.sha256(value).hexdigest()


def frozen_protocol():
    """Predeclare all cases and tolerances before new numerical measurements.

    Historical U selected the first three mesh values.  They are training data,
    so the wider wire is explicitly held out and cannot tune these thresholds.
    The final two levels are an a-priori halving continuation of the third.
    """
    return {
        'schema': SCHEMA,
        'source_pins': SOURCE_PINS,
        'solver_sha256': SOLVER_SHA256,
        'scope': 'finite uniform-dielectric wire pilot and independent 2D reference',
        'qualified': False,
        'draft_model_promoted': False,
        'training': {'width_um': '0.16', 'source': 'failed historical aspect-U trace'},
        'held_out': {'width_um': '0.32', 'tuning_permitted': False},
        'geometry': {
            'gap_um': '1.04', 'thickness_um': '0.42', 'epsilon_r': '4.1',
            'wire_lengths_um': ['10', '20', '30'],
            'ground_margin_um': '20', 'ground_thickness_um': '0.4',
            'coordinate_unit_m': '0.000001', 'maximum_panel_aspect': '4',
            'maximum_initial_quads': 8192,
        },
        'manual_solver': {
            'mesh_ladder': ['0.000383703', '0.000248446', '0.000172698',
                            '0.000086349', '0.0000431745'],
            'interaction_ratio': '1', 'gmres_tolerance': '0.0005',
            'galerkin': True, 'automatic_iteration': False,
            'all_warnings_fatal': True,
            'reason': 'avoid the auto initial m=1e32 coarse-link pass without making later passes dense',
        },
        'acceptance': {
            'maximum_matrix_asymmetry_relative': '0.01',
            'maximum_cellwise_mesh_change': '0.02',
            'consecutive_mesh_pairs_required': 2,
            'maximum_length_slope_change': '0.05',
            'maximum_independent_reference_relative_error': '0.10',
            'maximum_reference_mesh_change': '0.02',
            'maximum_reference_domain_change': '0.02',
            'maximum_native_ground_extension_change': '0.02',
            'missing_native_ground_extension_is_failure': True,
            'complete_expected_membership_required': True,
            'held_out_tuning_forbidden': True,
        },
        'reference': {
            'method': 'independent nonuniform Cartesian finite-volume Laplace/energy',
            'mesh_steps_um': ['0.04', '0.02'],
            'domain_extents_um': ['16', '32'],
            'epsilon_layers': [['0', '1000', '4.1']],
            'residual_relative_tolerance': '0.000000001',
            'maximum_cg_iterations': 3000,
            'maximum_nodes': 30000,
            'limitations': 'empirical mesh/domain stability is not a rigorous discretization error enclosure',
        },
        'native_ground_extension': {
            'widths_um': ['0.16', '0.32'], 'wire_lengths_um': ['20', '30'],
            'margin_um': '30', 'use_same_accepted_mesh_policy': True,
        },
        'resource_request': {
            'cpus': 1, 'memory_bytes': 6442450944,
            'scratch_limit_bytes': 4294967296,
            'solver_seconds_per_call': 120,
            'maximum_solver_calls': 55,
            'root_go_required': True,
        },
        'limits': [
            'uniform epsilon benchmark does not validate layered CMOS5L dielectric accuracy',
            'no resistance, via, diagonal, multilayer or process-corner qualification',
            'no extraction consumer/table coverage, SPEF or routed timing acceptance',
            'no historical failed receipt is promoted',
        ],
    }


def validate_protocol(plan):
    need(plan == frozen_protocol(), 'Pilot protocol differs from the predeclared experiment')
    return digest(canonical(plan))


def f32_token(value):
    rounded = struct.unpack('>f', struct.pack('>f', float(value)))[0]
    need(math.isfinite(rounded), 'Nonfinite binary32 coordinate')
    return format(rounded, '.17g')


def box_panels(name, bounds, counts):
    """Outward, conforming surface tiling with one shared knot set per axis."""
    need(re.fullmatch(r'[A-Z][A-Z0-9_]*', name), 'Invalid conductor name')
    need(len(bounds) == len(counts) == 3, 'Three box axes required')
    knots = []
    for (lo, hi), count in zip(bounds, counts):
        lo, hi = Fraction(lo), Fraction(hi)
        need(lo < hi and type(count) is int and 1 <= count <= 128, 'Invalid box extent/count')
        values = [f32_token(lo + (hi - lo) * i / count) for i in range(count + 1)]
        need(len(set(values)) == len(values), 'Binary32 knot collapse')
        knots.append(values)
    rows = ['* closed outward box ' + name]
    for axis in range(3):
        u, v = [i for i in range(3) if i != axis]
        for side in (0, 1):
            # The ordered (u,v) basis has +normal for axes 0 and 2, - for 1.
            reverse = ((1 if axis != 1 else -1) != (-1 if side == 0 else 1))
            for i in range(counts[u]):
                for j in range(counts[v]):
                    corners = [(i, j), (i + 1, j), (i + 1, j + 1), (i, j + 1)]
                    if reverse:
                        corners.reverse()
                    coords = []
                    for a, b in corners:
                        point = ['0'] * 3
                        point[axis] = knots[axis][-1 if side else 0]
                        point[u], point[v] = knots[u][a], knots[v][b]
                        coords.extend(point)
                    rows.append('Q ' + name + ' ' + ' '.join(coords))
    return ('\n'.join(rows) + '\n').encode('ascii')


def finite_wire_files(plan, width_um, length_um, margin_um=None):
    validate_protocol(plan)
    g = plan['geometry']
    width, length = number(width_um), number(length_um)
    need(str(width_um) in ('0.16', '0.32') and str(length_um) in ('10', '20', '30'),
         'Geometry is outside declared case membership')
    margin = number(margin_um if margin_um is not None else g['ground_margin_um'])
    need(margin in (Decimal('20'), Decimal('30')), 'Undeclared ground extension')
    gap, thick, ground_thick = map(number, (g['gap_um'], g['thickness_um'], g['ground_thickness_um']))
    bounds = {
        'GND_SUB': ((-margin - width / 2, margin + width / 2), (-ground_thick, 0), (-margin, length + margin)),
        'SIGNAL': ((-width / 2, width / 2), (gap, gap + thick), (0, length)),
    }
    files = {'geometry.lst': ('* units: one coordinate = 1 um\nC ground.qui 4.1 0 0 0\nC signal.qui 4.1 0 0 0\n').encode()}
    mesh = {}
    for name, box in bounds.items():
        dims = [number(str(b - a)) for a, b in box]
        minimum = min(dims)
        counts = [max(1, math.ceil(float(d / (4 * minimum)))) for d in dims]
        quads = 2 * sum(counts[i] * counts[j] for i, j in ((0, 1), (0, 2), (1, 2)))
        mesh[name] = {'counts': counts, 'quads': quads,
                      'requested_bounds_um': [[str(x) for x in pair] for pair in box]}
        files['ground.qui' if name == 'GND_SUB' else 'signal.qui'] = box_panels(name, box, counts)
    need(sum(x['quads'] for x in mesh.values()) <= g['maximum_initial_quads'], 'Initial panel cap exceeded')
    certificate = {
        'schema': 'pinwheel.streaming-8x4-rc-geometry.v1',
        'protocol_sha256': validate_protocol(plan), 'coordinate_unit_m': g['coordinate_unit_m'],
        'width_um': str(width_um), 'length_um': str(length_um), 'margin_um': str(margin),
        'epsilon_r': g['epsilon_r'], 'mesh': mesh,
        'input_sha256': {k: digest(v) for k, v in files.items()},
        'qualification': False,
    }
    files['certificate.json'] = canonical(certificate) + b'\n'
    return files


def matrix_physics(names, matrix, asymmetry_limit=Decimal('0.01')):
    need(names and len(set(names)) == len(names) and len(matrix) == len(names), 'Matrix membership differs')
    n = len(names)
    need(all(len(row) == n for row in matrix), 'Nonsquare matrix')
    a = [[number(x) for x in row] for row in matrix]
    scale = max(abs(x) for row in a for x in row)
    need(scale > 0, 'Zero capacitance matrix')
    maximum = Decimal(0)
    for i in range(n):
        need(a[i][i] > 0 and sum(a[i]) >= 0, 'Nonpositive diagonal/negative Maxwell row sum')
        for j in range(n):
            if i != j:
                need(a[i][j] <= 0, 'Positive Maxwell off-diagonal')
                denominator = max(abs(a[i][j]), abs(a[j][i]), scale * Decimal('1e-12'))
                maximum = max(maximum, abs(a[i][j] - a[j][i]) / denominator)
    need(maximum <= asymmetry_limit, 'Matrix reciprocity exceeds declared tolerance')
    # Positive definiteness of the symmetric part; no numerical package or fit.
    with localcontext() as context:
        context.prec = 50
        lower = [[Decimal(0)] * n for _ in range(n)]
        for i in range(n):
            for j in range(i + 1):
                value = (a[i][j] + a[j][i]) / 2 - sum(lower[i][k] * lower[j][k] for k in range(j))
                if i == j:
                    need(value > 0, 'Matrix symmetric energy form is not positive definite')
                    lower[i][j] = value.sqrt()
                else:
                    lower[i][j] = value / lower[j][j]
    return {'maximum_reciprocity_relative_error': str(maximum), 'positive_definite_symmetric_part': True}


def parse_manual_log(log, expected_names, mesh, gmres_tolerance, interaction_ratio='1'):
    need(type(log) is str and len(log) <= 8 * 1024 * 1024, 'Invalid solver log size/type')
    need(not re.search(r'(?im)^\s*(?:warning|error|fatal)\b|segmentation fault|killed|timeout', log),
         'Warning/failure marker anywhere in solver log')
    need('Auto calculation' not in log and 'Auto option overrides' not in log,
         'Automatic run cannot enter the manual-mesh experiment')
    def one(pattern, value, description):
        found = re.findall(pattern, log, flags=re.M)
        need(len(found) == 1 and number(found[0]) == number(value), 'Missing/different ' + description)
    one(r'^Mesh refinement \(-m\):\s*(' + NUM + r')\s*$', mesh, 'manual mesh')
    one(r'^Solution scheme \(-g\): Galerkin, GMRES tolerance \(-t\):\s*(' + NUM + r')\s*$',
        gmres_tolerance, 'Galerkin/GMRES selection')
    one(r'^Potential interaction coefficient to mesh refinement ratio \(-d\):\s*(' + NUM + r')\s*$',
        interaction_ratio, 'interaction ratio')
    lines = log.splitlines()
    starts = [i for i, line in enumerate(lines) if line.startswith('Dimension')]
    need(len(starts) == 1, 'Manual run must contain exactly one complete matrix')
    start = starts[0]
    n = len(expected_names)
    need(lines[start].split() == ['Dimension', str(n), 'x', str(n)], 'Wrong matrix dimension')
    names, matrix = [], []
    for line in lines[start + 1:start + 1 + n]:
        fields = line.split()
        need(len(fields) == n + 1, 'Incomplete/extra matrix cells')
        names.append(fields[0]); matrix.append([number(x) for x in fields[1:]])
    need(names == expected_names, 'Wrong/duplicate/reordered matrix names')
    physics = matrix_physics(names, matrix)
    # The pinned Native writer appends a human-readable integer decomposition.
    # Accept exactly that complete footer and check it against the numeric time;
    # do not accept a truncated prefix or arbitrary trailing text.
    times = re.findall(r'^Total time:\s*(' + NUM + r')s \((\d+) days, (\d+) hours, (\d+) mins, (\d+) s\)\s*$',
                       log, flags=re.M)
    need(len(times) == 1 and number(times[0][0]) >= 0, 'Missing/duplicate terminal time')
    seconds, days, hours, minutes, remainder = times[0]
    days, hours, minutes, remainder = map(int, (days, hours, minutes, remainder))
    need(hours < 24 and minutes < 60 and remainder < 60 and
         int(number(seconds)) == ((days * 24 + hours) * 60 + minutes) * 60 + remainder,
         'Inconsistent terminal duration decomposition')
    need(log.find('Total time:') > log.find('Dimension'), 'Terminal time precedes matrix')
    return {'names': names, 'matrix': [[str(x) for x in row] for row in matrix],
            'solver_seconds': seconds, 'physics': physics, 'mesh': str(mesh),
            'qualified': False, 'manual_solve_only': True}


def cellwise_change(first, second):
    need(first['names'] == second['names'], 'Matrix name/order mismatch')
    a = [[number(x) for x in row] for row in first['matrix']]
    b = [[number(x) for x in row] for row in second['matrix']]
    need(len(a) == len(b) and all(len(x) == len(y) for x, y in zip(a, b)), 'Matrix dimension mismatch')
    scale = max(abs(x) for row in b for x in row)
    return max(abs(x - y) / max(abs(y), scale * Decimal('1e-12'))
               for r, s in zip(a, b) for x, y in zip(r, s))


def admit_mesh_sequence(plan, results):
    validate_protocol(plan)
    ladder = plan['manual_solver']['mesh_ladder']
    need(3 <= len(results) <= len(ladder), 'At least three successive declared meshes required')
    need([x['mesh'] for x in results] == ladder[:len(results)], 'Skipped/reordered/undeclared mesh')
    changes = [cellwise_change(a, b) for a, b in zip(results, results[1:])]
    bound = number(plan['acceptance']['maximum_cellwise_mesh_change'])
    required = plan['acceptance']['consecutive_mesh_pairs_required']
    need(all(x <= bound for x in changes[-required:]), 'Cellwise mesh stability failed')
    return {'mesh_stability_passed': True, 'changes': [str(x) for x in changes],
            'qualified': False, 'error_bound_proved': False}


def layered_parallel_plate_per_area(layers):
    """Exact one-dimensional SI reference, C/A = eps0 / sum(thickness/er)."""
    need(layers, 'No dielectric layers')
    terms = []
    for thickness_m, er in layers:
        d, epsilon = number(thickness_m), number(er)
        need(d > 0 and epsilon > 0, 'Nonpositive dielectric thickness/permittivity')
        terms.append(d / epsilon)
    return EPS0 / sum(terms)
