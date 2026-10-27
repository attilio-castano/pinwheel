"""Portable reference-reader inputs, not numerical or historical authority.

Geometry is a compact projection of the eight-case nominal plan whose SHA256 is
37628d053afaf9fd2987bcd7917873cabec76932a9fa4597c190e65391c43f12.
The fixed grid shapes below are independent expected values from the retained
preparations. No production generator, solver or ignored file is called here.
Matrices and resource counters are synthetic controls, never measured results.
"""
import copy


EPSILON_LAYERS = [
    ['0', '0.4', '3.95'], ['0.4', '0.45', '6.5'], ['0.45', '1.04', '4.1'],
    ['1.04', '2.000', '4.1'], ['2.000', '3.030', '4.1'], ['3.030', '4.060', '4.1'],
    ['4.060', '5.400', '4.1'], ['5.400', '8.900', '4.1'],
    ['8.900', '9.300', '6.6'], ['9.300', '1000', '1'],
]
METALS = {
    'Metal1': ('0.16', ['-0.08', '0.08', '1.04', '1.460']),
    'Metal2': ('0.2', ['-0.1', '0.1', '2.000', '2.490']),
    'Metal3': ('0.2', ['-0.1', '0.1', '3.030', '3.520']),
    'Metal4': ('0.2', ['-0.1', '0.1', '4.060', '4.550']),
    'TopMetal1': ('1.64', ['-0.82', '0.82', '5.400', '7.400']),
}
CASE_LAYOUTS = [
    ('TYP-Metal2-self', 'first5', ['Metal2']),
    ('TYP-Metal3-self', 'first5', ['Metal3']),
    ('TYP-Metal4-self', 'first5', ['Metal4']),
    ('TYP-Metal1-Metal2-centered', 'first5', ['Metal1', 'Metal2']),
    ('TYP-Metal2-Metal3-centered', 'first5', ['Metal2', 'Metal3']),
    ('TYP-TopMetal1-self', 'remaining3', ['TopMetal1']),
    ('TYP-Metal3-Metal4-centered', 'remaining3', ['Metal3', 'Metal4']),
    ('TYP-Metal4-TopMetal1-centered', 'remaining3', ['Metal4', 'TopMetal1']),
]
ORIGINAL_SHAPES = [
    (86, 174), (98, 186), (103, 287), (119, 299),
    (86, 174), (98, 186), (103, 287), (119, 299),
    (86, 180), (98, 192), (103, 301), (119, 313),
    (87, 175), (99, 187), (105, 287), (121, 299),
    (86, 187), (98, 199), (103, 319), (119, 331),
    (95, 175), (111, 187), (117, 273), (129, 285),
    (86, 193), (98, 205), (103, 333), (119, 345),
    (118, 194), (134, 206), (175, 319), (187, 331),
]
EXPANDED_SHAPES = [
    (98, 186), (114, 196), (119, 299), (131, 307),
    (98, 186), (114, 196), (119, 299), (131, 307),
    (98, 192), (114, 202), (119, 313), (131, 321),
    (99, 187), (115, 197), (121, 299), (133, 307),
    (98, 199), (114, 209), (119, 331), (131, 339),
    (111, 187), (123, 197), (129, 285), (145, 293),
    (98, 205), (114, 215), (119, 345), (131, 353),
    (134, 206), (146, 216), (187, 331), (203, 339),
]
DERIVATION = {
    'source_path': 'streaming_8x4_rc_layered_reference.py',
    'source_sha256': '42f2f43590d023d4a5f42826d7ac70b875108ca761d521436e96aef35830b5c9',
    'adapted_path': 'streaming_8x4_rc_all_layers_reference.py',
    'adapted_sha256': '5a21e1a89b942e770557850319b48592ec04f5bfa420be81fd42fe8843138e03',
    'solve_body_sha256': 'a01b8ac269355e2e29d9f023258483ae72e312095c2a2f1d11b88996b82b3476',
    'solve_body_byte_identical': True,
    'changes': ['linear axis subdivision emits strict interior knots only; original anchors retained',
                'default/explicit node admission 40000 to 65000; equation and numerical tolerances unchanged'],
}


def reference_plan(expanded=False):
    cases = []
    for name, batch, metals in CASE_LAYOUTS:
        geometry = [dict(name='W' + str(i + 1), layer=metal,
                         width_um=METALS[metal][0], bounds_um=list(METALS[metal][1]))
                    for i, metal in enumerate(metals)]
        cases.append(dict(name=name, batch=batch, corner='TYP', role='new_nominal_only',
                          layer_geometry=geometry,
                          rectangles=[dict(name=r['name'], bounds_um=list(r['bounds_um'])) for r in geometry],
                          epsilon_layers=copy.deepcopy(EPSILON_LAYERS)))
    extents = ('32', '64') if expanded else ('16', '32')
    shapes = EXPANDED_SHAPES if expanded else ORIGINAL_SHAPES
    inventory = []
    for case in cases:
        for step in ('.04', '.02'):
            for extent in extents:
                nx, ny = shapes[len(inventory)]
                inventory.append(dict(case=case['name'], step_um=step, extent_um=extent,
                                      nodes=nx * ny, nx=nx, ny=ny))
    protocol = dict(maximum_cg_iterations=6000, true_residual_relative_tolerance='1e-9',
                    energy_flux_relative_tolerance='1e-7', reciprocity_relative_tolerance='1e-7',
                    maximum_reference_mesh_change='.02', maximum_reference_domain_change='.02',
                    reference_mesh_steps_um=['.04', '.02'], reference_domain_extents_um=list(extents),
                    maximum_reference_nodes=70000 if expanded else 65000)
    return dict(cases=cases, protocol=protocol, grid_inventory=inventory,
                FVM_derivation=copy.deepcopy(DERIVATION),
                storage_admission=dict(object_storage_budget_bytes_per_node=4096,
                    allocator_and_transient_factor=4, interpreter_and_worker_reserve_bytes=268435456,
                    scratch_bytes=134217728, measured_RSS=False))


def reference_rows(plan):
    """Synthetic passing reader controls for the independently specified grids."""
    rows = []
    for index, grid in enumerate(plan['grid_inventory']):
        job = dict(case=grid['case'], step=grid['step_um'], extent=grid['extent_um'])
        case = next(c for c in plan['cases'] if c['name'] == job['case'])
        n = len(case['rectangles'])
        matrix = [[1e-10]] if n == 1 else [[2e-10, -1e-10], [-1e-10, 2e-10]]
        kernel = dict(schema='pinwheel.streaming-8x4-rc-layered-reference.v1',
            qualified=False, continuum_error_enclosure=False, names=[r['name'] for r in case['rectangles']],
            rectangles=[dict(name=r['name'], bounds_um=list(map(float, r['bounds_um']))) for r in case['rectangles']],
            epsilon_layers=[list(map(float, r)) for r in case['epsilon_layers']],
            mesh_step_um=float(job['step']), extent_um=float(job['extent']), matrix_F_per_m=matrix,
            ground_C_F_per_m=[sum(r) for r in matrix], coupling_C_F_per_m=None if n == 1 else 1e-10,
            excitations=[dict(name=r['name'], true_residual_relative=1e-10, cg_iterations=40,
                             energy_flux_relative_error=1e-9) for r in case['rectangles']],
            nodes=grid['nodes'], unknown_nodes=grid['nodes'] - 100,
            reciprocity_relative_error=0., wall_seconds=1.)
        rows.append(dict(index=index, job=job, resource_feasible=True, numeric_passed=True, kernel_row=kernel))
    return rows


def cgroup_snapshot():
    return dict(memory_current=1000, memory_peak=2000, memory_max=2147483648, memory_swap_max=0,
                pids_max=128, cpu_max='100000 100000', memory_events=dict(max=0, oom=0, oom_kill=0),
                memory_events_local=dict(max=0, oom=0, oom_kill=0))
