"""Fail-closed model24 generation contracts; no native work occurs here."""
from decimal import Decimal as D
import hashlib
import json
import re

import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_conditioning_parser as C
import streaming_8x4_rc_incore as I

need=P.need
SCHEMA='pinwheel.streaming-8x4-model24.v1'
COVERAGE=('resistance','ground_capacitance','coupling_capacitance','via_resistance',
    'dielectric_interfaces','layer_coverage','width_spacing_range','consumer_units_and_semantics')
MESH='0.000383703'
UNIT='0.00000095367431640625'


def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()
def digest(value):return hashlib.sha256(canonical(value)).hexdigest()


def policy():
    return dict(schema=SCHEMA,maximum_calls=1,seconds_per_leaf=120,work_seconds=150,outer_seconds=180,
        cpu=1,memory_bytes=6442450944,tmpfs_bytes=536870912,no_extra_swap=True,
        memory_preempt_fraction='0.95',memory_poll_seconds='0.25',manual_mesh=MESH,
        coordinate_unit_m=UNIT,galerkin=True,gmres_tolerance='0.0005',interaction_ratio='0.25',
        preconditioner='Jacobi',out_of_core_ratio='0',all_warnings_fatal=True,
        no_last_complete_iteration_fallback=True,no_implicit_retry=True,
        purpose='one full-stack two-signal source/role/unit/strict-terminal and runtime-cost smoke',
        smoke_is_not_mesh_length_boundary_or_independent_accuracy_qualification=True,
        model_qualified=False,qualified_timing=False,census_applicability_passed=False)


def solver_argv():
    return ['/solver/runtime/bin/FasterCap','-b','geometry.lst','-g','-m'+MESH,'-t0.0005','-d0.25','-f0']


def role_names(roles):
    need(type(roles) is list and len(roles)>=2,'Complete conductor-role inventory required')
    names=[];ids=[]
    for index,row in enumerate(roles,1):
        need(set(row)=={'ordinal','name','role','matrix_name','origin'} and row['ordinal']==index
            and re.fullmatch(r'[A-Z][A-Z0-9_]*',row['name']) is not None
            and row['role'] in ('ground','signal') and row['matrix_name']=='g'+str(index)+'_'+row['name']
            and type(row['origin']) is str and row['origin'],'Explicit conductor role/name/position differs')
        names.append(row['matrix_name']);ids.append(row['name'])
    need(len(names)==len(set(names)) and len(ids)==len(set(ids))
        and any(r['role']=='ground' for r in roles) and any(r['role']=='signal' for r in roles),
        'Duplicate or absent signal/ground role')
    return names


def parse_terminal(raw,roles,exit_code,timed_out,memory_guard):
    """Every process failure wins over every printed matrix, including exit zero warnings."""
    need(type(exit_code) is int and exit_code==0 and timed_out is False and memory_guard is False,
        'Native exit/timeout/memory guard failed; no last-iteration fallback')
    names=role_names(roles)
    need(I.mode_observed(raw),'Explicit actual -f0 header required; no implicit OOC fallback')
    branch=C.branches(C.PROFILES[0])[1]
    numeric=C.parse(raw,names,branch,C.PROFILES[0],UNIT)
    indices=[i for i,r in enumerate(roles) if r['role']=='signal']
    matrix=[[P.number(x) for x in row] for row in numeric['matrix_F']]
    signals=[[matrix[i][j] for j in indices] for i in indices]
    ground=[sum(row) for row in signals]
    need(all(v>0 for v in ground),'Grounded signal-submatrix row sums must be positive')
    return dict(numeric=numeric,ordered_conductor_roles=roles,
        signal_names=[roles[i]['name'] for i in indices],
        signal_matrix_F=[[str(x) for x in row] for row in signals],ground_F=list(map(str,ground)),
        complete_full_matrix_checked=True,grounded_roles_are_not_counted_as_signal_targets=True,
        physical_C_equals_raw_times_coordinate_unit_once=True,model_qualified=False)


def length_difference(first,second,first_length_um,second_length_um):
    """No positional zip truncation or permutation may enter a generated coefficient."""
    need(first['ordered_conductor_roles']==second['ordered_conductor_roles']
        and first['signal_names']==second['signal_names'],'Length matrices role/name/order differs')
    a,b=first['signal_matrix_F'],second['signal_matrix_F'];n=len(first['signal_names'])
    need(len(a)==len(b)==n and all(len(row)==n for row in a+b),'Length matrix dimensions differ')
    delta=P.number(second_length_um)-P.number(first_length_um)
    need(delta>0,'Strictly ordered distinct wire lengths required')
    matrix=[[(P.number(b[i][j])-P.number(a[i][j]))/(delta*D('1e-6')) for j in range(n)] for i in range(n)]
    P.matrix_physics(first['signal_names'],matrix)
    return dict(signal_names=first['signal_names'],matrix_F_per_m=[[str(x) for x in row] for row in matrix],
        ground_F_per_m=[str(sum(row)) for row in matrix],no_end_effect_error_enclosure=True)


def completion_manifest(expected,rows,source_bindings,corner_bindings):
    """Only a complete, exact, source/corner-bound universe can reach table assembly."""
    need(type(expected) is list and expected and all(type(x) is str and x for x in expected)
        and len(expected)==len(set(expected)),'Nonempty unique predeclared case universe required')
    need(type(rows) is list and [r['case_id'] for r in rows]==expected,'Missing/reordered/duplicate/foreign generation case')
    need(set(corner_bindings)=={'MIN','TYP','MAX'} and source_bindings,
        'Complete explicit corner/source binding required')
    for key,value in source_bindings.items():need(re.fullmatch(r'[0-9a-f]{64}',value) is not None,'Invalid source hash')
    for corner,row in corner_bindings.items():
        need(row['label']==corner and all(re.fullmatch(r'[0-9a-f]{64}',row[k]) for k in ('process_sha256','consumer_policy_sha256')),
            'Corner label/process/consumer-policy identity differs')
    for row in rows:
        need(row['corner'] in corner_bindings and row['source_bindings']==source_bindings
            and row['corner_binding']==corner_bindings[row['corner']]
            and row['terminal_passed'] is True and row['inputs_unchanged'] is True
            and row['role_identity_passed'] is True and row['strict_numeric_passed'] is True,
            'Failed, stale, unbound or untyped result cannot enter generation manifest')
        need(re.fullmatch(r'[0-9a-f]{64}',row['raw_receipt_sha256']) is not None,'Missing raw case receipt')
    return dict(schema='pinwheel.streaming-8x4-model24-generation-completion.v1',
        complete_declared_membership=True,case_ids=expected,source_bindings=source_bindings,
        corner_bindings=corner_bindings,rows=rows,model_qualified=False,
        complete_generation_is_not_independent_validation=True)


def qualification_requirements():
    return dict(coverage={name:dict(coverage_complete=False,status='pending_census_bound_protocol_and_independent_measurement') for name in COVERAGE},
        two_successive_BEM_matrix_change='0.02',FVM_mesh_change='0.02',FVM_domain_change='0.02',
        length_slope_change='0.05',ground_extension_change='0.02',consumer_independent_C_error='0.10',
        existing_absolute_R_and_via_gate='0.001',old_failures_remain_failed=True,
        heldout_values_not_available_to_training=True,postroute_census_join_required=True,
        prior_seen_cases_are_development_or_regression_only=True,
        full_PDK_qualification=False,model_qualified=False,qualified_timing=False)
