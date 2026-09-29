"""Explicit all-corner timing/electrical checks, independent of flow exit status.

The caller owns artifact identity, extraction mode and corner qualification.
A passing result here does not establish those premises or layout acceptance.
"""
import math


def assess_timing(metrics, corners):
    if not isinstance(metrics, dict):
        raise ValueError('Expected corner metrics as a dictionary')
    if (not isinstance(corners, (list, tuple)) or not corners
            or any(not isinstance(c, str) or not c for c in corners)
            or len(set(corners)) != len(corners)):
        raise ValueError('Expected a nonempty, unique list of required corners')
    fields = {
        'setup_ns': 'timing__setup__ws',
        'hold_ns': 'timing__hold__ws',
        'setup_violations': 'timing__setup_vio__count',
        'hold_violations': 'timing__hold_vio__count',
        'capacitance_violations': 'design__max_cap_violation__count',
        'slew_violations': 'design__max_slew_violation__count',
        'fanout_violations': 'design__max_fanout_violation__count',
    }
    rows, failures = {}, []
    for corner in corners:
        row = {}
        for label, metric in fields.items():
            key = metric + '__corner:' + corner
            value = metrics.get(key)
            if (type(value) not in (int, float) or not math.isfinite(value)
                    or (label.endswith('_violations') and (value < 0 or value != int(value)))):
                raise ValueError('Missing or invalid required corner metric: ' + key)
            row[label] = value
            violates = value < 0 if label.endswith('_ns') else value != 0
            if violates:
                failures.append(dict(corner=corner, measure=label, value=value))
        rows[corner] = row
    return dict(status='rejected' if failures else 'passed', corners=rows,
                failures=failures,
                boundary='Requires separately validated artifact, parasitics and corner definitions; no layout or physical qualification.')
