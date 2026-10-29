"""Fixed residual×interaction experiment; unchanged complete-matrix physics."""
import re
import streaming_8x4_model24_contract as K
P,I=K.P,K.I


def branches():
    return [dict(id='baseline',gmres_tolerance='0.0005',interaction_ratio='0.25'),
        dict(id='residual-only',gmres_tolerance='0.000001',interaction_ratio='0.25'),
        dict(id='interaction-only',gmres_tolerance='0.0005',interaction_ratio='0.125'),
        dict(id='residual-and-interaction',gmres_tolerance='0.000001',interaction_ratio='0.125')]


def argv(branch):
    P.need(branch in branches(),'Undeclared model24 conditioning branch')
    return ['/solver/runtime/bin/FasterCap','-b','geometry.lst','-g','-m'+K.MESH,
        '-t'+branch['gmres_tolerance'],'-d'+branch['interaction_ratio'],'-f0']


def parse(log,roles,branch,exit_code,timed_out,memory_guard):
    P.need(branch in branches() and type(log) is str and len(log)<=8*1024*1024,'Wrong conditioning branch/log')
    P.need(type(exit_code) is int and exit_code==0 and timed_out is False and memory_guard is False,
        'Native exit/timeout/memory guard failed; no last-iteration fallback')
    names=K.role_names(roles)
    P.need(not re.search(r'(?i)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout',log),
        'Warning/failure marker anywhere in model24 conditioning solver log')
    P.need(I.mode_observed(log),'Explicit actual f0 required')
    P.need(re.findall(r'^Precond Type\(s\) \(-p\):\s*([^\r\n]*?)\s*$',log,re.M)==['Jacobi'],
        'Actual conditioning preconditioner differs/mixed/duplicated')
    numeric=P.parse_manual_log(log,names,K.MESH,branch['gmres_tolerance'],branch['interaction_ratio'])
    numeric['matrix_F']=[[str(P.number(x)*P.number(K.UNIT)) for x in row] for row in numeric['matrix']]
    traces=re.findall(r'^GMRES Iteration:\s*([^\r\n]*)$',log,re.M)
    P.need(len(traces)<=len(names),'Extra conditioning excitation trace');lengths=[]
    for text in traces:
        P.need(re.fullmatch(r'\d+(?:\s+\d+)*\s*',text) is not None,'Unsupported GMRES trace')
        values=list(map(int,text.split()));P.need(0<len(values)<=1000 and values==list(range(len(values))),
            'Skipped/reordered/excess GMRES trace');lengths.append(len(values))
    indices=[i for i,r in enumerate(roles) if r['role']=='signal'];matrix=numeric['matrix_F']
    signals=[[P.number(matrix[i][j]) for j in indices] for i in indices];ground=[sum(r) for r in signals]
    P.need(all(v>0 for v in ground),'Grounded signal-submatrix row sums must be positive')
    return dict(numeric=numeric,ordered_conductor_roles=roles,signal_names=[roles[i]['name'] for i in indices],
        signal_matrix_F=[[str(x) for x in row] for row in signals],ground_F=list(map(str,ground)),
        GMRES_iteration_trace_lengths=lengths,independent_true_residual_enclosure=False,
        complete_full_matrix_checked=True,grounded_roles_are_not_counted_as_signal_targets=True,
        physical_C_equals_raw_times_coordinate_unit_once=True,model_qualified=False)


def aggregate(jobs):
    expected=[dict(index=c*4+b,case=c,branch=r) for c in range(2) for b,r in enumerate(branches())]
    P.need(len(jobs)==8 and all(all(row[k]==wanted[k] for k in wanted) for row,wanted in zip(jobs,expected)),
        'Complete ordered eight-call factorial required; no successful subset')
    return [dict(branch=b,both_geometries_passed=all(jobs[c*4+i]['numeric_passed'] is True for c in range(2)))
        for i,b in enumerate(branches())]
