"""Strict HOST parser for the fixed four-branch development diagnostic.

This reuses the frozen matrix/footer/physics parser and additionally binds the
actual preconditioner and interaction factor. No warning or nonconverged result
can become a numeric pass, including when FasterCap exits zero.
"""
import re
import streaming_8x4_rc_protocol as P

MESH = '0.000383703'
GMRES = '0.0005'
BRANCHES = [
    {'id': 'jacobi-d1', 'preconditioner': 'jacobi', 'flags': [], 'interaction_ratio': '1'},
    {'id': 'two-level-d1', 'preconditioner': 'two-level-128', 'flags': ['-pn', '-ps128'], 'interaction_ratio': '1'},
    {'id': 'jacobi-d025', 'preconditioner': 'jacobi', 'flags': [], 'interaction_ratio': '0.25'},
    {'id': 'two-level-d025', 'preconditioner': 'two-level-128', 'flags': ['-pn', '-ps128'], 'interaction_ratio': '0.25'},
]


def argv(branch):
    P.need(branch in BRANCHES, 'Undeclared numerical diagnostic branch')
    return ['/solver/runtime/bin/FasterCap', '-b', 'geometry.lst', '-g', '-m' + MESH,
            '-t' + GMRES, '-d' + branch['interaction_ratio']] + branch['flags']


def parse(log, names, branch, coordinate_unit):
    P.need(type(log) is str and len(log) <= 8 * 1024 * 1024 and branch in BRANCHES,
           'Invalid diagnostic log/branch')
    P.need(not re.search(r'(?i)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout', log),
           'Warning/failure marker anywhere in diagnostic solver log')
    choices = re.findall(r'^Precond Type\(s\) \(-p\):\s*([^\r\n]*?)\s*$', log, re.M)
    expected = 'Jacobi' if branch['preconditioner'] == 'jacobi' else 'Two-levels, two-levels preconditioner dimension (-ps): 128'
    P.need(choices == [expected], 'Actual preconditioner differs/mixed/duplicated')
    numeric = P.parse_manual_log(log, names, MESH, GMRES, branch['interaction_ratio'])
    P.need(coordinate_unit == '0.000001', 'Exact failed uniform-geometry unit differs')
    numeric['matrix_F'] = [[str(P.number(x) * P.number(coordinate_unit)) for x in row] for row in numeric['matrix']]
    traces = re.findall(r'^GMRES Iteration:\s*([^\r\n]*)$', log, re.M)
    P.need(len(traces) <= len(names), 'Extra GMRES excitation trace')
    lengths = []
    for text in traces:
        P.need(re.fullmatch(r'\d+(?:\s+\d+)*\s*', text) is not None, 'Unsupported GMRES trace grammar')
        values = list(map(int, text.split()))
        P.need(0 < len(values) <= 1000 and values == list(range(len(values))), 'Skipped/reordered/excess GMRES iteration trace')
        lengths.append(len(values))
    # The source can return before printing a trace if its preconditioned initial
    # guess already meets the internal target. No missing trace is fabricated.
    numeric.update(actual_preconditioner=branch['preconditioner'], interaction_ratio=branch['interaction_ratio'],
                   GMRES_iteration_trace_lengths=lengths, independent_true_residual_enclosure=False,
                   model_qualified=False)
    return numeric


def failure_evidence(log):
    return {'warning_or_error_lines': [line for line in log.splitlines()
        if re.search(r'(?i)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout', line)],
        'nonconvergence_reports': [list(values) for values in re.findall(
            r'Error: not converging after (\d+) iterations, norm of the residual is (\S+), while targeting (\S+)', log)],
        'rounded_residual_text_is_not_a_convergence_proof': True}
