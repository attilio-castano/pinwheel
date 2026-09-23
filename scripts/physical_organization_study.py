"""Conditional timing and replication budgets for organization studies.

Use exact, matched saved paths. These calculations freeze data delays, clock
uncertainty and reconvergence corrections; they neither run STA nor certify a
clock change. Physical qualification stays with the existing route intake.
"""
from collections import defaultdict
import math

from physical_organization import area
from physical_distribution import CHAIN_CELLS
from tiled_chip import FF


def _finite(value):
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
        raise ValueError('Require a finite numeric measurement')
    return value


def timing_budget(comparison, specification, floor_ns):
    """Derive slack obligations, preserving clock identity and check direction.

    For setup, slack changes by capture_shift - launch_shift - data_shift;
    for hold the signs reverse. A common shift at the same physical clock pin
    cancels. Only one-sided bounds supported by the selected path are returned.
    """
    floor_ns = _finite(floor_ns)
    if floor_ns < 0 or specification['delay'] not in ('min', 'max'):
        raise ValueError('Invalid timing floor or check direction')
    sense = 1 if specification['delay'] == 'max' else -1
    for label in ('before', 'after'):
        path = comparison[label]
        for key in ('arrival_ns', 'required_ns', 'slack_ns', 'launch_clock_ns'):
            _finite(path[key])
        if path['capture_clock_ns'] is not None:
            _finite(path['capture_clock_ns'])
        slack = sense * (path['required_ns'] - path['arrival_ns'])
        if abs(slack - path['slack_ns']) > 1e-5:
            raise ValueError('Slack disagrees with arrival, requirement or check direction')
        data = [r[label] for r in comparison['data_arc_deltas']]
        identity = [{k: row[k] for k in ('pin', 'edge', 'cell')} for row in data]
        if identity != specification['expected_data_path']:
            raise ValueError('Changed matched data path')
    expected = specification['expected_data_path']
    if (not expected or expected[0]['pin'] != specification['source'] or
            expected[-1]['pin'] != specification['sink']):
        raise ValueError('Mismatched path boundaries')

    coefficients = defaultdict(int)
    clock_endpoints = []
    for kind, sign in (('launch_clock', -sense), ('capture_clock', sense)):
        arcs = comparison['clock_arc_deltas'][kind]
        for arc in arcs:
            if any(arc['before'][k] != arc['after'][k] for k in ('pin', 'edge', 'cell')):
                raise ValueError('Changed matched clock path')
        endpoint_kind = specification['source_kind' if kind == 'launch_clock' else 'sink_kind']
        if endpoint_kind not in ('pin', 'port') or bool(arcs) != (endpoint_kind == 'pin'):
            raise ValueError('Missing clock path or unexpected clock on package boundary')
        if arcs:
            pin = arcs[-1]['after']['pin']
            clock_endpoints.append(pin)
            if pin.rsplit('/', 1)[0] != specification['source' if kind == 'launch_clock' else 'sink'].rsplit('/', 1)[0]:
                raise ValueError('Clock path ends at a different instance')
            for label in ('before', 'after'):
                arrival = _finite(arcs[-1][label]['arrival_ns'])
                if abs(arrival - comparison[label][kind + '_ns']) > 1e-5:
                    raise ValueError('Clock arrival disagrees with matched path')
            coefficients[pin] += sign
    coefficients = {pin: value for pin, value in coefficients.items() if value}
    before, after = comparison['before'], comparison['after']
    slack, margin = after['slack_ns'], after['slack_ns'] - floor_ns
    # Replace the saved launch/required-time environment, retaining AFTER data
    # delay. Required time includes hold-cell and CPPR terms, not only skew.
    restored_arrival = after['arrival_ns'] - after['launch_clock_ns'] + before['launch_clock_ns']
    restored_slack = sense * (before['required_ns'] - restored_arrival)
    bounds = {}
    if len(coefficients) == 1:
        pin, coefficient = next(iter(coefficients.items()))
        bounds[pin] = dict(lower_ns=-margin if coefficient == 1 else None,
                          upper_ns=margin if coefficient == -1 else None)
    return dict(check='setup' if sense == 1 else 'hold', floor_ns=floor_ns,
                slack_ns=slack, meets_zero_slack=slack >= 0, meets_retained_floor=margin >= 0,
                margin_to_floor_ns=margin, required_slack_gain_ns=max(0, -margin),
                clock_shift_coefficients=coefficients, isolated_clock_shift_bounds_ns=bounds,
                common_clock_shift_cancels=len(clock_endpoints) == 2 and not coefficients,
                restored_saved_clock_environment_slack_ns=restored_slack,
                restored_environment_meets_floor=restored_slack >= floor_ns,
                restored_environment_remaining_deficit_ns=max(0, floor_ns - restored_slack),
                complete_clock_window=False, physical_qualification=False,
                assumptions='One matched path only. Data delays and timing corrections held fixed for shift bounds. '
                'Replay uses BEFORE launch and required time with AFTER data delay, including saved required-time corrections. '
                'Other paths, opposite checks and physical clock realizability remain untested.')


def replication_cost(context, library, instance, corners, copies=1):
    """Exact cell footprint and extra upstream input capacitance for gate copies.

    A copy receives the same inputs and drives a disjoint consumer group. No
    placement or distribution tree is assigned here. Wires and output timing
    remain unknown; the calculation deliberately exposes the upstream cost.
    """
    if type(copies) is not int or copies < 1:
        raise ValueError('Require a positive extra-copy count')
    if not corners or len(set(corners)) != len(corners):
        raise ValueError('Require distinct measured corners')
    info = context['instances'][instance]
    if info['macro'] or info['cell'] in CHAIN_CELLS | {FF}:
        raise ValueError('Replicate only combinational logic, not state or transport')
    terms = [(net, t) for net, row in context['nets'].items()
             if row['type'] not in ('POWER', 'GROUND') for t in row['terminals']
             if t['instance'] == instance]
    inputs = [(net, t['pin']) for net, t in terms if t['direction'] == 'INPUT']
    outputs = [(net, t['pin']) for net, t in terms if t['direction'] == 'OUTPUT']
    if (not inputs or len(outputs) != 1 or len(inputs) + len(outputs) != len(terms) or
            any(context['nets'][net]['type'] != 'SIGNAL' for net, _ in terms)):
        raise ValueError('Require one combinational signal output and only signal inputs')
    footprint = area(info['bbox_dbu'], context['dbu_per_micron'])
    if _finite(footprint) <= 0:
        raise ValueError('Require a positive cell footprint')
    loads = {}
    for corner in corners:
        totals = defaultdict(lambda: dict(rise=0.0, fall=0.0))
        for net, pin in inputs:
            caps = library.capacitance_edges(corner, info['cell'], pin)
            for edge in ('rise', 'fall'):
                cap = _finite(caps[edge][1])
                if cap < 0:
                    raise ValueError('Require nonnegative pin capacitance')
                totals[net][edge] += cap * copies
        loads[corner] = {net: max(edges.values()) for net, edges in totals.items()}
    return dict(instance=instance, cell=info['cell'], extra_copies=copies,
                output_net=outputs[0][0], inputs=[dict(net=n, pin=p) for n, p in inputs],
                extra_cell_area_um2=copies * footprint,
                extra_upstream_pin_capacitance_pf=loads,
                extra_wire_capacitance_pf=None, legal_placement_qualified=False,
                timing_qualified=False, source_netlist_changed=False)
