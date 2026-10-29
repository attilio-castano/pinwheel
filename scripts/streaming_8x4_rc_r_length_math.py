"""Separate R-study slope/heldout diagnostics; old absolute audits are retained."""
from decimal import Decimal as D, localcontext
import re

import streaming_8x4_rc_r_length_geometry as G

C, need = G.N.C, G.need
POLICIES = ('baseline_rules', 'width_aware_LEF')
JOBS = [(c, p) for c in ('MIN', 'TYP', 'MAX') for p in POLICIES]


def relative(a, b):
    a, b = D(a), D(b); need(b > 0, 'Positive declared R reference required')
    return abs(a / b - 1)


def intervals(text, values):
    """Reparse every raw resistor; %g has six significant digits by default."""
    names = {}; blocks = re.findall(r'^\*NAME_MAP\s*\n(.*?)(?=^\*(?:PORTS|D_NET)\b)', text, re.M | re.S)
    if blocks:
        for line in blocks[0].splitlines():
            if line.strip():
                key, name = line.split(); names[key] = name
    result = {}
    for token, _, body in re.findall(r'^\*D_NET\s+(\S+)\s+(' + C.P.NUM + r')\s*\n(.*?)^\*END\s*$', text, re.M | re.S):
        prefix, sep, rest = token.partition(':'); name = names.get(prefix, prefix) + sep + rest
        need(name in values and name not in result, 'Raw interval net membership differs')
        sections = re.findall(r'^\*RES\s*\n(.*)\Z', body, re.M | re.S); need(len(sections) == 1, 'Raw interval RES section differs')
        center = D(0); uncertainty = D(0); count = 0; factor = D(values[name]['R_unit_ohm'])
        for line in sections[0].splitlines():
            if not line.strip(): continue
            match = re.fullmatch(r'\s*\d+\s+\S+\s+\S+\s+(' + C.P.NUM + r')\s*', line)
            need(match is not None, 'Unsupported raw interval resistor')
            value = D(match[1]); need(value.is_finite() and value >= 0, 'Invalid raw interval resistor')
            half = D(0) if value == 0 else D('0.5') * (D(10) ** (value.adjusted() - 5))
            center += value * factor; uncertainty += half * factor; count += 1
        need(center == D(values[name]['R_ohm']) and count == values[name]['edges'], 'Independent raw interval sum differs')
        result[name] = dict(center_ohm=str(center), half_width_ohm=str(uncertainty),
            lower_ohm=str(center - uncertainty), upper_ohm=str(center + uncertainty), edges=count,
            serialization_rounding_only=True, physical_error_enclosure=False)
    need(set(result) == set(values), 'Complete raw interval universe required')
    return result


def wire_rows(plan, job):
    values = job['values']; bounds = job['rounding_intervals']; result = []
    families = [r for r in G.rows() if r['via'] is None and r['name'].endswith('_L50')]
    with localcontext() as context:
        context.prec = 50
        for row in families:
            family = row['name'][:-4]; layer, _, width = row['segments'][0]
            rs = [D(values[family + '_L' + n]['R_ohm']) for n in ('50', '100', '150')]
            slopes = [(rs[i + 1] - rs[i]) / 50 for i in range(2)]
            need(all(s > 0 for s in slopes), 'Nonpositive measured R slope')
            sheet = D(plan['corners'][job['corner']]['wire_sheet_R'][layer])
            physical_target = sheet / D(width)
            policy_width = C.WIDTHS[layer] if job['policy'] == 'baseline_rules' else D(width)
            policy_target = sheet / policy_width
            physical_errors = [relative(s, physical_target) for s in slopes]
            policy_errors = [relative(s, policy_target) for s in slopes]
            linearity = relative(slopes[0], slopes[1])
            lo, hi = ([D(bounds[family + '_L' + n][k]) for n in ('50', '100', '150')]
                for k in ('lower_ohm', 'upper_ohm'))
            predicted = [2 * lo[1] - hi[0], 2 * hi[1] - lo[0]]
            heldout = max(predicted[0], lo[2]) <= min(predicted[1], hi[2])
            result.append(dict(family=family, layer=layer, width_um=width,
                lengths_um=['50', '100', '150'], total_R_ohm=list(map(str, rs)),
                adjacent_slopes_ohm_per_um=list(map(str, slopes)),
                ITF_width_aware_slope_ohm_per_um=str(physical_target),
                ITF_width_aware_relative_errors=list(map(str, physical_errors)),
                ITF_width_aware_slope_gate_passed=max(physical_errors) <= D('.001'),
                source_policy_slope_ohm_per_um=str(policy_target),
                source_policy_relative_errors=list(map(str, policy_errors)),
                source_policy_slope_gate_passed=max(policy_errors) <= D('.001'),
                slope_relative_difference=str(linearity), linearity_gate_passed=linearity <= D('.001'),
                intercepts_ohm=[str(2 * rs[0] - rs[1]), str(3 * rs[1] - 2 * rs[2])],
                predicted_150um_rounding_interval_ohm=list(map(str, predicted)),
                actual_150um_rounding_interval_ohm=[str(lo[2]), str(hi[2])],
                heldout_150um_rounding_gate_passed=heldout,
                diagnostic_controls_passed=max(policy_errors) <= D('.001') and linearity <= D('.001') and heldout))
    need(len(result) == 7, 'Complete seven-width-family analysis required')
    return result


def measurements(plan, jobs):
    need([(j['corner'], j['policy']) for j in jobs] == JOBS, 'Complete ordered six-call R study required')
    results = []; absolute = []; via = []
    for job in jobs:
        observations = wire_rows(plan, job)
        absolute.append(dict(corner=job['corner'], policy=job['policy'], **job['absolute_audit']))
        vias = job['absolute_audit']['vias']; need([v['name'] for v in vias] == list(C.VIA_FIXTURES), 'Complete five actual named-via controls required')
        via.append(dict(corner=job['corner'], policy=job['policy'], controls=vias, passed=all(v['passed'] is True for v in vias)))
        results.append(dict(corner=job['corner'], policy=job['policy'], widths=observations))
    ratios = []
    index = {(r['corner'], r['policy']): {v['family']: v for v in r['widths']} for r in results}
    for corner, policy in JOBS:
        rows = index[corner, policy]
        for layer in ('Metal1', 'Metal2'):
            wide, default = rows[layer + '_wide'], rows[layer]
            values = [D(a) / D(b) for a, b in zip(wide['adjacent_slopes_ohm_per_um'], default['adjacent_slopes_ohm_per_um'])]
            target = D(1) if policy == 'baseline_rules' else D('.5')
            ratios.append(dict(corner=corner, policy=policy, layer=layer, wide_to_default_ratios=list(map(str, values)),
                source_hypothesis=str(target), passed=all(relative(v, target) <= D('.001') for v in values)))
    controls = all(w['diagnostic_controls_passed'] for r in results for w in r['widths']) and all(r['passed'] for r in via + ratios)
    return dict(length_width_diagnostic_controls_passed=controls, per_job=results, measured_named_vias=via,
        wide_to_default_slope_ratios=ratios, absolute_audits=absolute,
        new_absolute_wire_controls=sum(len(r['wires']) for r in absolute),
        new_absolute_wire_failures=sum(w['passed'] is False for r in absolute for w in r['wires']),
        original_17net_absolute_wire_failures=72, original_17net_via_difference_passes=30,
        original_17net_experiment_passed=False, original_absolute_thresholds_unchanged=True,
        model_qualified=False, capacitance_qualified=False, full_width_range_qualified=False,
        physical_error_enclosure=False, scope='Fixed three-length R consumer study only; original absolute failures remain failed.')
