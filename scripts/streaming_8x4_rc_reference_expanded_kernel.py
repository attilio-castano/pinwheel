# New E32/64,70k admission adapter; frozen source5a21e1a89b942e770557850319b48592ec04f5bfa420be81fd42fe8843138e03
# Only domain guard/default node admission differ; all remaining solve/axis bytes match after exact normalization.
"""Separately admitted all-layer FVM adaptation of the frozen M1 operator.

This extends the frozen one-conductor reference with distinct terminal labels
and one unit excitation per conductor. No FasterCap geometry/kernel is reused.
No numerical solve occurs at import or plan preparation. Error enclosures are
not claimed: mesh/domain/held-out comparisons remain mandatory.
"""
import math
import time

from streaming_8x4_rc_reference import _cg, _graded, _layer_integral
from streaming_8x4_rc_protocol import EPS0, need


def _axis(anchors, step):
    values = set(anchors)
    for a, b in zip(anchors, anchors[1:]):
        need(b > a, 'Repeated/reversed FVM anchor')
        if b - a <= 1:
            n = math.ceil((b - a) / step)
            values.update(a + (b - a) * i / n for i in range(1, n))
        else:
            middle = (a + b) / 2
            left = _graded(a, middle, step)
            values.update(left)
            # Original anchors already supply a and b; left supplies the exact
            # middle. Reflect interior points only. Recomputing b as a+b-a can
            # differ by one ulp and introduce a nearly zero dielectric cell.
            values.update(a + b - x for x in left[1:-1])
    result = sorted(values)
    need(set(anchors) <= set(result) and all(b - a > 1e-8 for a, b in zip(result, result[1:])),
         'Reference grid has a near-duplicate/sliver interval or missing exact anchor')
    return result


def solve(rectangles, layers, extent, step, tolerance=1e-9,
          maximum_iterations=6000, maximum_nodes=70000):
    started = time.monotonic()
    need(1 <= len(rectangles) <= 2 and extent in (32.0, 64.0) and step in (.04, .02),
         'Undeclared layered reference geometry/mesh/domain')
    names = [r['name'] for r in rectangles]
    need(len(set(names)) == len(names), 'Duplicate reference conductor label')
    xa, ya = {-extent, extent}, {0.0, extent}
    for r in rectangles:
        x0, x1, y0, y1 = r['bounds_um']
        need(-extent < x0 < x1 < extent and 0 < y0 < y1 < extent, 'Invalid reference conductor bounds')
        need(step <= min(x1 - x0, y1 - y0) / 2, 'Reference conductor underresolved')
        xa.update((x0, x1)); ya.update((y0, y1))
    for bottom, top, er in layers:
        need(math.isfinite(er) and er > 0, 'Invalid reference ER')
        for y in (bottom, top):
            if 0 < y < extent:
                ya.add(y)
    xs, ys = _axis(sorted(xa), step), _axis(sorted(ya), step)
    nx, ny = len(xs), len(ys)
    need(nx * ny <= maximum_nodes, 'Layered FVM total node cap exceeded')
    _layer_integral(layers, 0, extent)
    terminal, unknown = {}, {}
    for j, y in enumerate(ys):
        for i, x in enumerate(xs):
            point = j * nx + i
            matches = [k for k, r in enumerate(rectangles) if
                       r['bounds_um'][0] - 1e-12 <= x <= r['bounds_um'][1] + 1e-12 and
                       r['bounds_um'][2] - 1e-12 <= y <= r['bounds_um'][3] + 1e-12]
            need(len(matches) <= 1, 'Overlapping/touching reference conductors')
            if i in (0, nx - 1) or j in (0, ny - 1):
                terminal[point] = -1
            elif matches:
                terminal[point] = matches[0]
            else:
                unknown[point] = len(unknown)
    diagonal, neighbors, edges = [0.0] * len(unknown), [[] for _ in unknown], []
    boundary_rhs = [[0.0] * len(unknown) for _ in rectangles]
    def edge(a, b, conductance):
        need(math.isfinite(conductance) and conductance > 0, 'Invalid layered edge conductance')
        edges.append((a, b, conductance))
        for left, right in ((a, b), (b, a)):
            if left in unknown:
                k = unknown[left]; diagonal[k] += conductance
                if right in unknown:
                    neighbors[k].append((unknown[right], conductance))
                elif terminal[right] >= 0:
                    boundary_rhs[terminal[right]][k] += conductance
    for j in range(1, ny - 1):
        lo, hi = (ys[j - 1] + ys[j]) / 2, (ys[j] + ys[j + 1]) / 2
        face_er = _layer_integral(layers, lo, hi)
        for i in range(nx - 1):
            edge(j * nx + i, j * nx + i + 1, face_er / (xs[i + 1] - xs[i]))
    for i in range(1, nx - 1):
        dual_width = (xs[i + 1] - xs[i - 1]) / 2
        for j in range(ny - 1):
            inverse_integral = _layer_integral(layers, ys[j], ys[j + 1], inverse=True)
            edge(j * nx + i, (j + 1) * nx + i, dual_width / inverse_integral)
    matrix = [[0.0] * len(names) for _ in names]; excitations = []; potentials = []
    for excitation in range(len(names)):
        values, iterations, residual = _cg(diagonal, neighbors, boundary_rhs[excitation], tolerance, maximum_iterations)
        potential = {p: float(k == excitation) for p, k in terminal.items()}
        potential.update({p: values[k] for p, k in unknown.items()})
        need(min(potential.values()) >= -1e-7 and max(potential.values()) <= 1 + 1e-7,
             'Layered reference maximum principle failed')
        charge = [0.0] * len(names)
        for a, b, g in edges:
            for left, right in ((a, b), (b, a)):
                if left in terminal and terminal[left] >= 0 and terminal.get(right) != terminal[left]:
                    charge[terminal[left]] += g * (potential[left] - potential[right])
        energy = sum(g * (potential[a] - potential[b]) ** 2 for a, b, g in edges)
        need(energy > 0 and abs(energy - charge[excitation]) / energy <= 1e-7,
             'Layered reference terminal energy/flux failed')
        for measured in range(len(names)):
            matrix[measured][excitation] = float(EPS0) * charge[measured]
        excitations.append({'name': names[excitation], 'true_residual_relative': residual,
                            'cg_iterations': iterations, 'energy_flux_relative_error': abs(energy - charge[excitation]) / energy})
        potentials.append(potential)
    for i, row in enumerate(matrix):
        need(row[i] > 0 and all(x <= 1e-25 for j, x in enumerate(row) if i != j) and sum(row) > 0,
             'Layered Maxwell signs/row sums failed')
    if len(names) == 2:
        reciprocity = abs(matrix[0][1] - matrix[1][0]) / max(abs(matrix[0][1]), abs(matrix[1][0]))
        need(reciprocity <= 1e-7 and matrix[0][0] * matrix[1][1] > matrix[0][1] * matrix[1][0],
             'Layered Maxwell reciprocity/positive energy failed')
        cross_energy = float(EPS0) * sum(g * (potentials[0][a] - potentials[0][b]) *
                                              (potentials[1][a] - potentials[1][b]) for a, b, g in edges)
        need(abs(cross_energy - matrix[0][1]) / abs(matrix[0][1]) <= 1e-7,
             'Layered cross-energy/terminal flux identity failed')
    else:
        reciprocity = 0.0
    return {'schema': 'pinwheel.streaming-8x4-rc-layered-reference.v1', 'qualified': False,
            'continuum_error_enclosure': False, 'names': names, 'rectangles': rectangles,
            'epsilon_layers': layers, 'extent_um': extent, 'mesh_step_um': step,
            'matrix_F_per_m': matrix, 'ground_C_F_per_m': [sum(row) for row in matrix],
            'coupling_C_F_per_m': -matrix[0][1] if len(names) == 2 else None,
            'excitations': excitations, 'reciprocity_relative_error': reciprocity,
            'nodes': nx * ny, 'unknown_nodes': len(unknown), 'wall_seconds': time.monotonic() - started,
            'scope': 'finite grounded 2D box; dielectric interfaces explicit; empirical mesh/domain gates still required'}
