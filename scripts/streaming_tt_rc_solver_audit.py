"""Prepared host-only gate for future FasterCap execution receipts and logs.

No solver or downloaded script is launched here.  A future trusted, bounded
runner must supply fresh process/input/log bindings.  Passing this gate is only
numerical-log admission; it is never model calibration or physical signoff.
The grammar has synthetic tests, but has not been exercised on a native run.
"""
from datetime import datetime
from decimal import Decimal, localcontext
import hashlib
import re


NUM = r'[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?'


def require(value, message):
    if not value:
        raise ValueError(message)


def numeric(token):
    require(re.fullmatch(NUM, token) is not None, 'Nonfinite/nonnumeric solver value')
    result = Decimal(token)
    require(result.is_finite(), 'Nonfinite solver value')
    return result


def utc_time(value):
    result = datetime.fromisoformat(value.replace('Z', '+00:00'))
    require(result.tzinfo is not None and result.utcoffset().total_seconds() == 0, 'Execution times must be UTC')
    return result


def admit_run(log, receipt, expected, expected_names, accuracy):
    """Reject failed/stale/incomplete runs before admitting the terminal matrix.

    Expected input/solver/runner digests and run ID must come from a separately
    frozen job plan, not from the execution receipt being tested.  This pure
    function cannot establish the truth of an externally supplied process receipt.
    """
    require(receipt.get('schema') == 'pinwheel.rc-solver-execution.v1', 'Wrong execution receipt schema')
    for key in ('input_sha256', 'solver_sha256', 'runner_sha256'):
        require(re.fullmatch(r'[0-9a-f]{64}', expected[key]) and receipt.get(key) == expected[key],
                'Missing/stale execution binding: ' + key)
    require(re.fullmatch(r'[A-Za-z0-9_-]{12,128}', expected['run_id']) and receipt.get('run_id') == expected['run_id'],
            'Missing/stale run ID')
    require(type(receipt.get('exit_code')) is int and receipt['exit_code'] == 0, 'Solver did not exit successfully')
    require(receipt.get('timed_out') is False and receipt.get('process_tree_reaped') is True,
            'Timed-out/unreaped solver cannot be admitted')
    require(receipt.get('log_sha256') == hashlib.sha256(log.encode()).hexdigest(), 'Log content binding mismatch')
    started, ended = utc_time(receipt['started_utc']), utc_time(receipt['ended_utc'])
    require(utc_time(expected['not_before_utc']) <= started <= ended <= utc_time(expected['not_after_utc']),
            'Stale/out-of-window solver execution')
    require(numeric(str(receipt['wire_length_um'])) == numeric(str(expected['wire_length_um'])) > 0,
            'Wrong solver wire length')
    require(isinstance(accuracy, Decimal) and accuracy.is_finite() and 0 < accuracy < 1,
            'Invalid requested convergence accuracy')
    require(expected_names and len(expected_names) == len(set(expected_names)) and
            all(isinstance(name, str) and name and not re.search(r'\s', name) for name in expected_names),
            'Invalid planned matrix names')
    dimension = len(expected_names)
    current, names, remaining, norm, total_time, iterations = None, [], 0, None, None, 0
    for line in log.splitlines():
        require(not re.search(r'(?i)killed after|timeout(?:expired)?|segmentation fault|fatal error', line),
                'Failure marker in solver log')
        if line.startswith('Dimension'):
            match = re.fullmatch(r'Dimension\s+(\d+)\s+x\s+(\d+)\s*', line)
            require(match is not None and tuple(map(int, match.groups())) == (dimension, dimension),
                    'Unexpected matrix dimensions')
            require(remaining == 0 and (current is None or norm is not None) and total_time is None,
                    'Truncated matrix/iteration or multiple jobs in one log')
            current, names, remaining, norm = [], [], dimension, None
        elif remaining:
            fields = line.split()
            require(len(fields) == dimension + 1, 'Truncated/extra matrix cells')
            names.append(fields[0])
            current.append([numeric(value) for value in fields[1:]])
            remaining -= 1
            if remaining == 0:
                require(names == expected_names, 'Wrong/duplicate/reordered matrix names')
        elif line.startswith('Weighted Frobenius'):
            match = re.fullmatch(r'Weighted Frobenius[^\n]*:\s*(' + NUM + r')\s*', line)
            require(current is not None and norm is None and total_time is None and match is not None,
                    'Unbound/duplicate solver convergence metric')
            norm = numeric(match.group(1))
            require(norm >= 0, 'Negative solver convergence metric')
            iterations += 1
        elif line.startswith('Total time'):
            match = re.fullmatch(r'Total time:?\s+(' + NUM + r')s\s*', line)
            require(current is not None and norm is not None and total_time is None and match is not None,
                    'Missing/duplicate/unbound solver terminal time')
            total_time = numeric(match.group(1))
            require(total_time >= 0, 'Negative solver terminal time')
    require(current is not None and remaining == 0 and norm is not None and total_time is not None,
            'Incomplete terminal solver matrix/metric/footer')
    require(norm <= accuracy, 'Terminal solver convergence exceeds requested accuracy')
    return {'names': names, 'matrix': current, 'frobenius_relative_change': norm, 'iterations': iterations,
            'solver_seconds': total_time, 'run_id': expected['run_id'],
            'qualified': False, 'calibrated': False, 'numerical_log_admission_only': True}


def admit_pair(log1, receipt1, expected1, log2, receipt2, expected2, expected_names, accuracy):
    require(expected1['run_id'] != expected2['run_id'] and expected1['input_sha256'] != expected2['input_sha256'],
            'Length pair must have distinct fresh jobs and geometry inputs')
    require(all(expected1[key] == expected2[key] for key in ('solver_sha256', 'runner_sha256')),
            'Length pair solver/runner mismatch')
    length1, length2 = numeric(str(expected1['wire_length_um'])), numeric(str(expected2['wire_length_um']))
    require(0 < length1 < length2, 'Invalid wire-length pair')
    first = admit_run(log1, receipt1, expected1, expected_names, accuracy)
    second = admit_run(log2, receipt2, expected2, expected_names, accuracy)
    with localcontext() as context:
        context.prec = 50
        difference = [[(b - a) / (length2 - length1) for a, b in zip(row1, row2)]
                      for row1, row2 in zip(first['matrix'], second['matrix'])]
    return {'names': list(expected_names), 'matrix_difference_per_um': difference, 'runs': [first, second],
            'qualified': False, 'calibrated': False, 'end_effect_cancellation_validated': False,
            'note': 'Two converged matrices do not establish linear length scaling, dielectric accuracy or model calibration.'}
