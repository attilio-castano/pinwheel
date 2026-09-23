"""Evaluate measured distribution budgets after an exact additive buffer edit.

This quantitative gate does not establish functional identity, legal placement,
power binding or whole-chip routing. Those remain independently checked receipts.
Unlike the saved-checkpoint comparison, new branches and changed pin loads are
expected; every old and new connection must be measured in every declared corner.
"""
from collections import Counter
import math


COUNTS = ('timing__setup_vio__count', 'timing__hold_vio__count',
          'design__max_fanout_violation__count', 'design__max_slew_violation__count',
          'design__max_cap_violation__count')


def finite(value):
    return type(value) in (int, float) and math.isfinite(value)


def qualify_candidate(contract, before, after, plan, measurements, timing,
                      source_area, candidate_area):
    """Reject incomplete evidence; report measured budget failures without relaxing them."""
    reserve, area_cap = contract['reserve_fraction'], contract['max_added_area_fraction']
    if (not finite(reserve) or not 0 < reserve < 1 or
            not finite(area_cap) or not 0 < area_cap <= .01):
        raise ValueError('Invalid distribution reserve or area budget')
    if (before['source_database_sha256'] != contract['source_database_sha256'] or
            plan['source_database']['sha256'] != contract['source_database_sha256'] or
            before['scope'] != contract['scope'] or after['scope'] != contract['scope']):
        raise ValueError('Changed distribution source or scope')
    old = {r['net'] for r in before['connections']}
    records = {r['net']:r for r in after['connections']}
    added_entries = [stage['new_net'] for op in plan['operations'] for stage in op.get('stages', [op])]
    added = set(added_entries)
    selected = {op['net'] for op in plan['operations']}
    if (len(old) != len(before['connections']) or len(records) != len(after['connections']) or
            len(added) != len(added_entries) or len(selected) != len(plan['operations']) or
            not selected <= old or selected != set(contract['selected_nets']) or
            old & added or set(records) != old | added):
        raise ValueError('Missing, duplicate or unexpected covered/added connection')
    floors = contract['timing_floors_ns']
    corners = set(floors)
    if (not corners or set(measurements) != corners or set(timing) != corners or
            any(set(rows) != set(records) for rows in measurements.values())):
        raise ValueError('Missing distribution connection or measurement corner')
    for limits in floors.values():
        if (set(limits) != {'setup','hold'} or
                any(not finite(v) or v <= 0 for v in limits.values())):
            raise ValueError('Invalid positive setup/hold floor')
    if (not finite(source_area) or not finite(candidate_area) or
            not 0 < source_area <= candidate_area):
        raise ValueError('Invalid measured instance area')

    output, paths_positive, electrical_met = [], True, True
    for name, record in sorted(records.items()):
        rows, failing, below = {}, False, False
        for corner in sorted(corners):
            row = measurements[corner][name]
            if (row['drivers'] != 1 or row['loads'] != len(record['consumers']) + len(record['ports']) or
                    row['capacitance']['pin'] != record['driver']):
                raise ValueError('Measurement does not match the candidate driver or consumers')
            if row['slew']['pin'] not in {record['driver'], *record['consumers'], *record['ports']}:
                raise ValueError('Measured transition belongs to another connection')
            margins = {}
            for kind in ['capacitance','slew','fanout']:
                value = row[kind]
                if (any(not finite(value[k]) for k in ['actual','limit','slack']) or
                        value['actual'] < 0 or value['limit'] <= 0 or
                        value['verdict'] not in {'MET','VIOLATED'}):
                    raise ValueError('Invalid electrical measurement')
                met = value['verdict'] == 'MET' and value['slack'] >= 0 and value['actual'] <= value['limit']
                electrical_met &= met
                failing |= not met
                if kind != 'fanout':
                    fraction = (value['limit'] - value['actual']) / value['limit']
                    margins[kind] = dict(pin=value['pin'], limit=value['limit'], actual=value['actual'],
                        reserve_fraction=fraction, remaining_budget=value['limit']-value['actual'])
                    below |= fraction < reserve
            if set(row['paths']) != {'min','max'}:
                raise ValueError('Missing min/max connection path')
            for path in row['paths'].values():
                if not finite(path['slack_ns']) or path['verdict'] not in {'MET','VIOLATED'}:
                    raise ValueError('Invalid connection path')
                paths_positive &= path['slack_ns'] > 0 and path['verdict'] == 'MET'
            rows[corner] = dict(margins, setup_ns=row['paths']['max']['slack_ns'],
                                hold_ns=row['paths']['min']['slack_ns'])
        output.append(dict(net=name, families=record['families'], added=name in added,
            verdict='failing' if failing else 'below_trial_reserve' if below else 'within_trial_reserve',
            corners=rows))

    slack_checks, counts = {}, {}
    for corner in sorted(corners):
        values = timing[corner]
        counts[corner] = {k:values[k] for k in COUNTS}
        if any(type(v) is not int or v < 0 for v in counts[corner].values()):
            raise ValueError('Missing or invalid whole-chip violation count')
        slack_checks[corner] = {}
        for kind, floor in floors[corner].items():
            actual = values['timing__'+kind+'__ws']
            if not finite(actual):
                raise ValueError('Missing finite whole-chip slack')
            slack_checks[corner][kind] = dict(actual_ns=actual, floor_ns=floor, passed=actual >= floor)
    gates = dict(all_connections_within_reserve=all(r['verdict']=='within_trial_reserve' for r in output),
        whole_chip_timing_floors=all(v['passed'] for row in slack_checks.values() for v in row.values()),
        whole_chip_violation_counts_zero=all(v==0 for row in counts.values() for v in row.values()),
        measured_electrical_limits_met=electrical_met, measured_paths_positive=paths_positive,
        added_area_within_budget=candidate_area-source_area <= source_area*area_cap)
    return dict(quantitative_gates_passed=all(gates.values()), gates=gates,
        reserve_fraction=reserve, counts=dict(Counter(r['verdict'] for r in output)), connections=output,
        connection_corner_records=len(records)*len(corners),
        min_max_path_summaries=2*len(records)*len(corners),
        timing=slack_checks, whole_chip_violation_counts=counts,
        area=dict(source_um2=source_area, candidate_um2=candidate_area,
            added_um2=candidate_area-source_area, added_fraction=(candidate_area-source_area)/source_area,
            budget_um2=source_area*area_cap),
        boundary='Fixed experimental budgets on coarse estimates. Functional identity, physical legality, power binding and fresh whole-chip routing require separate evidence.')
