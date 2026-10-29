"""Independent two-dimensional finite-volume electrostatic reference.

Solves div(epsilon grad V)=0 on a nonuniform Cartesian graph with a rectangular
wire at one volt and a grounded outer boundary.  It shares no mesher, kernel or
matrix parser with FasterCap.  Mesh/domain comparisons are empirical stability
checks, not certified continuum error bounds.  No solver runs at import.
"""
import math
import time

from streaming_8x4_rc_protocol import EPS0, need


def _graded(start, stop, step, growth=1.22):
    need(start < stop and step > 0 and 1 < growth <= 1.5, 'Invalid graded interval')
    result = [float(start)]
    while result[-1] + step < stop:
        result.append(result[-1] + step)
        step *= growth
        need(len(result) < 200, 'Reference interval node cap')
    result.append(float(stop))
    return result


def wire_axes(width, gap, thickness, extent, step):
    need(0 < width and 0 < gap and 0 < thickness and extent > 4 * (gap + thickness)
         and 0 < step <= min(width, thickness) / 2, 'Invalid reference geometry/mesh')
    half = width / 2
    side = _graded(half, extent, step)
    inside_x = [(-half + width * i / math.ceil(width / step))
                for i in range(math.ceil(width / step) + 1)]
    xs = sorted(set([-x for x in side] + inside_x + side))
    below = [gap - x for x in _graded(0, gap, step)]
    inside_y = [(gap + thickness * i / math.ceil(thickness / step))
                for i in range(math.ceil(thickness / step) + 1)]
    above = [gap + thickness + x for x in _graded(0, extent - gap - thickness, step)]
    ys = sorted(set(below + inside_y + above))
    return xs, ys


def _layer_integral(layers, lo, hi, inverse=False):
    need(hi > lo, 'Nonpositive dielectric integration interval')
    total, covered = 0.0, 0.0
    for bottom, top, er in layers:
        overlap = max(0.0, min(hi, top) - max(lo, bottom))
        if overlap:
            need(er > 0 and math.isfinite(er), 'Invalid dielectric permittivity')
            total += overlap / er if inverse else overlap * er
            covered += overlap
    need(abs(covered - (hi - lo)) <= 1e-11 * max(1.0, hi - lo),
         'Dielectric layers overlap or do not cover the reference domain')
    return total


def _cg(diagonal, neighbors, rhs, tolerance, maximum_iterations):
    size = len(rhs)
    def apply(vector):
        return [diagonal[i] * vector[i] - sum(g * vector[j] for j, g in neighbors[i])
                for i in range(size)]
    dot = lambda a, b: sum(x * y for x, y in zip(a, b))
    x, residual = [0.0] * size, list(rhs)
    rhs_norm2 = dot(rhs, rhs)
    need(rhs_norm2 > 0, 'Empty reference excitation')
    z = [r / d for r, d in zip(residual, diagonal)]
    direction, old = list(z), dot(residual, z)
    relative = 1.0
    for iteration in range(1, maximum_iterations + 1):
        product = apply(direction)
        denominator = dot(direction, product)
        need(denominator > 0 and math.isfinite(denominator), 'Reference operator lost positive definiteness')
        alpha = old / denominator
        x = [a + alpha * b for a, b in zip(x, direction)]
        residual = [a - alpha * b for a, b in zip(residual, product)]
        relative = math.sqrt(dot(residual, residual) / rhs_norm2)
        need(math.isfinite(relative), 'Nonfinite reference residual')
        if relative <= tolerance:
            # Recompute the true residual rather than trusting only its recurrence.
            actual = [a - b for a, b in zip(rhs, apply(x))]
            actual_relative = math.sqrt(dot(actual, actual) / rhs_norm2)
            need(actual_relative <= tolerance, 'Reference true residual does not meet tolerance')
            return x, iteration, actual_relative
        z = [r / d for r, d in zip(residual, diagonal)]
        new = dot(residual, z)
        beta = new / old
        direction = [a + beta * b for a, b in zip(z, direction)]
        old = new
    raise ValueError('Reference CG iteration allowance exhausted; last relative residual ' + str(relative))


def solve_wire(width, gap, thickness, extent, step, layers=((0.0, 1000.0, 4.1),),
               tolerance=1e-9, maximum_iterations=3000, maximum_nodes=30000):
    started = time.monotonic()
    xs, ys = wire_axes(width, gap, thickness, extent, step)
    nx, ny = len(xs), len(ys)
    need(nx * ny <= maximum_nodes, 'Reference total node cap exceeded')
    # Epsilon interfaces are grid lines, preventing silently unresolved layers.
    for bottom, top, _ in layers:
        for y in (bottom, top):
            if 0 < y < extent:
                ys.append(y)
    ys = sorted(set(ys)); ny = len(ys)
    need(nx * ny <= maximum_nodes, 'Reference total node cap exceeded after dielectric interfaces')
    fixed, unknown = {}, {}
    for j, y in enumerate(ys):
        for i, x in enumerate(xs):
            point = j * nx + i
            if i in (0, nx - 1) or j in (0, ny - 1):
                fixed[point] = 0.0
            elif abs(x) <= width / 2 + 1e-12 and gap - 1e-12 <= y <= gap + thickness + 1e-12:
                fixed[point] = 1.0
            else:
                unknown[point] = len(unknown)
    diagonal = [0.0] * len(unknown)
    rhs = [0.0] * len(unknown)
    neighbors = [[] for _ in unknown]
    edges = []
    def edge(a, b, conductance):
        need(conductance > 0 and math.isfinite(conductance), 'Invalid reference edge conductance')
        edges.append((a, b, conductance))
        for left, right in ((a, b), (b, a)):
            if left in unknown:
                k = unknown[left]
                diagonal[k] += conductance
                if right in unknown:
                    neighbors[k].append((unknown[right], conductance))
                else:
                    rhs[k] += conductance * fixed[right]
    for j in range(1, ny - 1):
        lo, hi = (ys[j - 1] + ys[j]) / 2, (ys[j] + ys[j + 1]) / 2
        face_er = _layer_integral(layers, lo, hi)
        for i in range(nx - 1):
            edge(j * nx + i, j * nx + i + 1, face_er / (xs[i + 1] - xs[i]))
    for i in range(1, nx - 1):
        dual_width = (xs[i + 1] - xs[i - 1]) / 2
        for j in range(ny - 1):
            series_gap = _layer_integral(layers, ys[j], ys[j + 1], inverse=True)
            edge(j * nx + i, (j + 1) * nx + i, dual_width / series_gap)
    values, iterations, residual = _cg(diagonal, neighbors, rhs, tolerance, maximum_iterations)
    potential = dict(fixed)
    potential.update({point: values[index] for point, index in unknown.items()})
    need(min(potential.values()) >= -1e-7 and max(potential.values()) <= 1 + 1e-7,
         'Reference discrete maximum principle failed')
    # For one volt, C'=2U=eps0*sum_edges(g*(Va-Vb)^2).
    energy_coefficient = sum(g * (potential[a] - potential[b]) ** 2 for a, b, g in edges)
    # An independent terminal-flux sum checks the energy identity and indexing.
    terminal_flux = 0.0
    for a, b, g in edges:
        if fixed.get(a) == 1.0 and fixed.get(b) != 1.0:
            terminal_flux += g * (1.0 - potential[b])
        elif fixed.get(b) == 1.0 and fixed.get(a) != 1.0:
            terminal_flux += g * (1.0 - potential[a])
    need(energy_coefficient > 0 and abs(terminal_flux - energy_coefficient) / energy_coefficient <= 1e-7,
         'Reference terminal flux/energy identity failed')
    return {
        'schema': 'pinwheel.streaming-8x4-rc-independent-reference.v1',
        'width_um': width, 'gap_um': gap, 'thickness_um': thickness,
        'extent_um': extent, 'mesh_step_um': step,
        'epsilon_layers': [list(x) for x in layers],
        'capacitance_per_length_F_per_m': float(EPS0) * energy_coefficient,
        'energy_flux_relative_error': abs(terminal_flux - energy_coefficient) / energy_coefficient,
        'true_residual_relative': residual, 'cg_iterations': iterations,
        'nodes': nx * ny, 'unknown_nodes': len(unknown),
        'wall_seconds': time.monotonic() - started,
        'qualified': False, 'continuum_error_enclosure': False,
        'scope': 'finite grounded-box 2D reference; mesh/domain extrapolation still required',
    }
