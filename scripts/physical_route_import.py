"""Reject saved-route imports that silently change routing resource accounting.

Unchanged route geometry and unchanged timing do not establish unchanged router
state. A no-edit control must also preserve every saved capacity/usage entry.
This module compares evidence; it does not initialize or repair OpenROAD.
"""
from collections import Counter
import math
import re


def parse_segments(text):
    """Parse OpenROAD's native write_segments format, retaining multiplicity."""
    result = {}
    name = None
    opened = False
    for line in text.splitlines():
        words = line.split()
        if not words:
            continue
        if name is None:
            if len(words) != 1 or not re.fullmatch(r'[A-Za-z0-9_./\[\]$-]+', words[0]):
                raise ValueError('Invalid route net name')
            name = words[0]
            if name in result:
                raise ValueError('Repeated route net')
            result[name] = []
        elif not opened:
            if words != ['(']:
                raise ValueError('Missing route opening delimiter')
            opened = True
        elif words == [')']:
            if not result[name]:
                raise ValueError('Empty route')
            name = None
            opened = False
        else:
            if len(words) != 6:
                raise ValueError('Invalid route segment')
            try:
                x, y, xx, yy = [int(words[k]) for k in (0, 1, 3, 4)]
            except ValueError as error:
                raise ValueError('Invalid segment coordinate') from error
            layer, other = words[2], words[5]
            if any(not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', v) for v in (layer, other)):
                raise ValueError('Invalid segment layer')
            if (layer != other and (x, y) != (xx, yy)) or (layer == other and x != xx and y != yy):
                raise ValueError('Non-Manhattan route segment')
            result[name].append(tuple(sorted(((x, y, layer), (xx, yy, other)))))
    if name is not None or not result:
        raise ValueError('Incomplete or empty segment export')
    return {name: sorted(segments) for name, segments in result.items()}


def compare_routes(before, after, clock_nets):
    clocks = set(clock_nets)
    if not clocks or not clocks <= set(before):
        raise ValueError('Missing source clock routes')
    changed = sorted(name for name in before.keys() | after.keys()
                     if before.get(name) != after.get(name))
    return dict(equal=not changed, source_nets=len(before), imported_nets=len(after),
                source_segments=sum(map(len, before.values())), clock_nets=len(clocks),
                changed_nets=changed, changed_clock_nets=sorted(clocks & set(changed)))


def _grid(grid):
    axes = [grid[k] for k in ('grid_x', 'grid_y')]
    for axis in axes:
        if (len(axis) < 2 or any(type(v) is not int for v in axis)
                or any(b <= a for a, b in zip(axis, axis[1:]))):
            raise ValueError('Invalid grid coordinates')
    if not grid['layers']:
        raise ValueError('Missing routing layers')
    nx, ny = map(len, axes)
    for layer in grid['layers'].values():
        for key in ('capacity', 'usage'):
            matrix = layer[key]
            if (len(matrix) != nx or any(len(col) != ny for col in matrix)
                    or any(type(v) not in (int, float) or not math.isfinite(v)
                           or v < 0 or v != int(v) for col in matrix for v in col)):
                raise ValueError('Incomplete or invalid grid accounting')
        overflow = sum(max(0, layer['usage'][x][y] - layer['capacity'][x][y])
                       for x in range(nx) for y in range(ny))
        if (layer['total_capacity'] != sum(map(sum, layer['capacity']))
                or layer['total_usage'] != sum(map(sum, layer['usage']))
                or layer['overflow'] != overflow):
            raise ValueError('Grid summary disagrees with complete arrays')
    return axes


def compare_grids(before, after):
    a, b = _grid(before), _grid(after)
    if a != b or before['layers'].keys() != after['layers'].keys():
        return dict(equal=False, coordinates_and_layers_equal=False, layers={})
    layers = {}
    for name in sorted(before['layers']):
        row = {}
        for key in ('capacity', 'usage'):
            old, new = before['layers'][name][key], after['layers'][name][key]
            changes = [[x, y, int(old[x][y]), int(new[x][y])]
                       for x in range(len(old)) for y in range(len(old[x]))
                       if old[x][y] != new[x][y]]
            row[key] = dict(changed_entries=len(changes), changes=changes,
                            net_change=sum(v[3] - v[2] for v in changes),
                            delta_counts=dict(Counter(str(v[3] - v[2]) for v in changes)))
        row['source_overflow'] = before['layers'][name]['overflow']
        row['imported_overflow'] = after['layers'][name]['overflow']
        layers[name] = row
    return dict(equal=all(not v[k]['changed_entries'] for v in layers.values()
                          for k in ('capacity', 'usage')),
                coordinates_and_layers_equal=True, layers=layers)


def control_verdict(routes, grid, *, physical_identity, measurements_equal):
    checks = dict(routes=routes['equal'], resource_accounting=grid['equal'],
                  physical_identity=physical_identity, measurements=measurements_equal)
    if any(type(value) is not bool for value in checks.values()):
        raise ValueError('Control checks must be explicit booleans')
    return dict(status='passed' if all(checks.values()) else 'rejected', checks=checks,
                candidate_admitted=all(checks.values()),
                failures=[name for name, ok in checks.items() if not ok])
