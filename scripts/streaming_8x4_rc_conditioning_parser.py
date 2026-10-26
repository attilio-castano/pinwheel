"""Strict, fixed-profile conditioning readback; raw observations confer no pass."""
import re
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_solver_diagnostic_parser as Q

MESHES = ['0.000383703', '0.000248446', '0.000172698', '0.000086349', '0.0000431745']
PROFILES = ('layered-m1-two-call', 'uniform-development-five-mesh')


def branches(profile):
    P.need(profile in PROFILES, 'Undeclared conditioning profile')
    if profile == PROFILES[0]:
        return [dict(id='jacobi-d1', preconditioner='jacobi', flags=[], interaction_ratio='1', mesh=MESHES[0]),
                dict(id='jacobi-d025', preconditioner='jacobi', flags=[], interaction_ratio='0.25', mesh=MESHES[0])]
    return [dict(id='two-level-d025-m' + str(i), preconditioner='two-level-128', flags=['-pn', '-ps128'],
                 interaction_ratio='0.25', mesh=mesh) for i, mesh in enumerate(MESHES)]


def argv(branch, profile):
    P.need(branch in branches(profile), 'Undeclared conditioning branch')
    return ['/solver/runtime/bin/FasterCap', '-b', 'geometry.lst', '-g', '-m' + branch['mesh'],
            '-t0.0005', '-d' + branch['interaction_ratio']] + branch['flags']


def parse(log, names, branch, profile, unit):
    P.need(branch in branches(profile) and type(log) is str and len(log) <= 8 * 1024 * 1024,
           'Wrong conditioning branch/log')
    P.need(not re.search(r'(?i)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout', log),
           'Warning/failure marker anywhere in conditioning solver log')
    expected = 'Jacobi' if branch['preconditioner'] == 'jacobi' else 'Two-levels, two-levels preconditioner dimension (-ps): 128'
    P.need(re.findall(r'^Precond Type\(s\) \(-p\):\s*([^\r\n]*?)\s*$', log, re.M) == [expected],
           'Actual conditioning preconditioner differs/mixed/duplicated')
    numeric = P.parse_manual_log(log, names, branch['mesh'], '0.0005', branch['interaction_ratio'])
    expected_unit = '0.00000095367431640625' if profile == PROFILES[0] else '0.000001'
    P.need(unit == expected_unit, 'Wrong fixed physical coordinate unit')
    numeric['matrix_F'] = [[str(P.number(x) * P.number(unit)) for x in row] for row in numeric['matrix']]
    traces = re.findall(r'^GMRES Iteration:\s*([^\r\n]*)$', log, re.M)
    P.need(len(traces) <= len(names), 'Extra conditioning GMRES excitation trace')
    lengths = []
    for text in traces:
        P.need(re.fullmatch(r'\d+(?:\s+\d+)*\s*', text) is not None, 'Unsupported GMRES trace grammar')
        values = list(map(int, text.split()))
        P.need(0 < len(values) <= 1000 and values == list(range(len(values))), 'Skipped/reordered/excess GMRES trace')
        lengths.append(len(values))
    numeric.update(actual_preconditioner=branch['preconditioner'], interaction_ratio=branch['interaction_ratio'],
                   GMRES_iteration_trace_lengths=lengths, independent_true_residual_enclosure=False,
                   model_qualified=False)
    return numeric


def observations(log, names):
    """Keep printed evidence even on a failed branch, without qualifying it."""
    result = dict(Q.failure_evidence(log), numeric_acceptance=False)
    result['counts'] = {label: re.findall(pattern, log, re.M) for label, pattern in {
        'refined_panels': r'^Number of panels after refinement: (\d+)\s*$',
        'links': r'^Number of links: (\d+) ',
        'input_panels': r'^Number of input panels to solver engine: (\d+)\s*$'}.items()}
    result['GMRES_trace_lengths'] = [len(s.split()) for s in re.findall(r'^GMRES Iteration:\s*([^\r\n]*)$', log, re.M)]
    starts = [i for i, line in enumerate(log.splitlines()) if line.startswith('Dimension')]
    result['raw_matrix'] = None
    if len(starts) == 1:
        lines = log.splitlines(); start = starts[0]; n = len(names)
        rows = [line.split() for line in lines[start + 1:start + 1 + n]]
        if lines[start].split() == ['Dimension', str(n), 'x', str(n)] and len(rows) == n and all(len(r) == n + 1 for r in rows) and [r[0] for r in rows] == names:
            try:
                matrix = [[str(P.number(x)) for x in r[1:]] for r in rows]
                result['raw_matrix'] = {'names': names, 'matrix': matrix,
                    'printed_row_sums': [str(sum(P.number(x) for x in row)) for row in matrix],
                    'physics_passed': False, 'scope': 'printed values only; no acceptance or error enclosure'}
            except (ValueError, TypeError): pass
    return result


def aggregate(profile, rows):
    expected = branches(profile)
    P.need(len(rows) == len(expected) and [r['branch'] for r in rows] == expected, 'Incomplete/reordered conditioning packet')
    numeric_passed = all(r['passed'] is True for r in rows)
    result = {'all_numeric_branches_passed': numeric_passed, 'mesh_stability_passed': False,
              'mesh_changes': None, 'mesh_error': None, 'passed': numeric_passed}
    if profile == PROFILES[1]:
        result['passed'] = False
        if numeric_passed:
            values = [r['numeric'] for r in rows]
            result['mesh_changes'] = [str(P.cellwise_change(a, b)) for a, b in zip(values, values[1:])]
            try:
                accepted = P.admit_mesh_sequence(P.frozen_protocol(), values)
                result['mesh_stability_passed'] = accepted['mesh_stability_passed']; result['passed'] = True
            except ValueError as error: result['mesh_error'] = str(error)
        else: result['mesh_error'] = 'Incomplete strict numeric five-mesh sequence'
    return result
