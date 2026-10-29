"""Freeze actual ITF M1 self/coupling reference cases before measurement."""
import argparse
from decimal import Decimal
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_process as P


def materials(itf):
    y = Decimal(0); rows = []
    for name in ('fox', 'nitride', 'dummyOx', 'ox1', 'ox2', 'ox3', 'ox4', 'oxTopMetal1', 'nitTop'):
        layer = itf['DIELECTRIC', name]; top = y + layer['THICKNESS']
        rows.append([str(y), str(top), str(layer['ER'])]); y = top
    P.need(itf['DIELECTRIC', 'air']['ER'] == 1, 'Unexpected external ITF air')
    rows.append([str(y), '1000', '1'])
    return rows


def rectangles(itf, width, spacing=None):
    width = Decimal(width)
    gap = sum(itf['DIELECTRIC', n]['THICKNESS'] for n in ('fox', 'nitride', 'dummyOx'))
    top = gap + itf['CONDUCTOR', 'Metal1']['THICKNESS']
    if spacing is None:
        xs = [(-width / 2, width / 2)]
    else:
        half_gap = Decimal(spacing) / 2
        xs = [(-half_gap - width, -half_gap), (half_gap, half_gap + width)]
    return [{'name': 'W' + str(i + 1), 'bounds_um': list(map(str, (x0, x1, gap, top)))} for i, (x0, x1) in enumerate(xs)]


def prepare(intake, output):
    P.need(not output.exists() and output.parent.is_dir(), 'Layered preparation must be fresh')
    texts, _ = P.verify_intake(intake)
    cases = []
    for corner, width, spacing, role in (
        ('TYP', '.16', None, 'development'), ('TYP', '.32', None, 'held_out_width'),
        ('TYP', '.16', '.18', 'development_coupling'), ('TYP', '.16', '.36', 'held_out_spacing'),
        ('MIN', '.16', '.18', 'untuned_corner'), ('MAX', '.16', '.18', 'untuned_corner')):
        itf = P.parse_stack(texts['itf_' + corner.lower()])
        name = corner + '-w' + width + ('-self' if spacing is None else '-s' + spacing)
        cases.append({'name': name, 'corner': corner, 'width_um': width, 'spacing_um': spacing,
                      'role': role, 'rectangles': rectangles(itf, width, spacing), 'epsilon_layers': materials(itf)})
    controls = {
        'series_planar_exact': {'layers': [['0', '.4', '3.95'], ['.4', '.45', '6.5'], ['.45', '1.04', '4.1']],
                               'formula': 'C/A = epsilon0 / sum(d_i/er_i), with d_i converted um to m once',
                               'relative_tolerance': '1e-12'},
        'uniform_limit': {'case': 'TYP-w.16-self', 'epsilon_layers': [['0', '1000', '4.1']],
                          'reference': 'frozen plan04 independent FVM w0.16-h0.02-E32',
                          'reference_F_per_m': '8.536226390196693e-11', 'relative_tolerance': '.02',
                          'mesh_step_um': '.02', 'extent_um': '32'},
        'coordinate_scale': {'physical_coordinate_unit': 'um', 'FVM_result_unit': 'F/m',
                             'FasterCap_geometry_coordinate_unit': 'm', 'FasterCap_raw_matrix_unit': 'F'},
    }
    source_names = ['streaming_8x4_rc_layered_plan.py', 'streaming_8x4_rc_layered_reference.py',
                    'streaming_8x4_rc_reference.py', 'streaming_8x4_rc_protocol.py',
                    'streaming_8x4_rc_process.py', 'streaming_tt_rc_compare.py',
                    'streaming_8x4_rc_layered_run.py']
    parent = Path(__file__).parent
    protocol = {
        'reference_mesh_steps_um': ['.04', '.02'], 'reference_domain_extents_um': ['16', '32'],
        'maximum_reference_nodes': 40000, 'maximum_cg_iterations': 6000,
        'minimum_reference_grid_interval_um': '1e-8', 'exact_material_interface_anchors_required': True,
        'true_residual_relative_tolerance': '1e-9', 'energy_flux_relative_tolerance': '1e-7',
        'reciprocity_relative_tolerance': '1e-7', 'maximum_reference_mesh_change': '.02',
        'maximum_reference_domain_change': '.02', 'maximum_BEM_reference_difference': '.10',
        'maximum_successive_BEM_matrix_change': '.02', 'required_successive_changes': 2,
        'maximum_length_slope_difference': '.05', 'maximum_ground_extension_difference': '.02',
        'native_mesh_ladder': ['0.000383703', '0.000248446', '0.000172698', '0.000086349', '0.0000431745'],
        'native_interaction_ratio': '1', 'native_gmres_tolerance': '0.0005',
        'native_lengths_um': ['10', '20', '30'], 'native_ground_extension_um': ['20', '30'],
        'native_extension_cases': 'all three lengths at E20; L20 and L30 at E30',
        'all_native_warnings_fatal': True, 'full_matrix_name_membership_and_physics_required': True,
        'held_out_no_tuning': True, 'process_corner_scope': 'merged ITF geometry and ER only; draft effective linewidth/corner fit is not presumed equivalent',
        'material_geometry_convention': 'fox+nitride+dummyOx below M1; M1 embeds in ox1; above nitTop is air',
        'reference_boundary': 'grounded outer 2D box [-E,E]x[0,E]; mesh/domain comparisons required',
        'native_boundary': 'finite ground slab and explicit finite layered prism/air boundary; independent length and boundary comparisons required',
        'reference_resources': {'cpus': 1, 'memory_bytes': 2147483648, 'scratch_bytes': 134217728,
                                'seconds_per_call': 120, 'maximum_calls': 25, 'work_seconds': 1800,
                                'outer_seconds': 1860, 'root_go_required': True},
        'native_resources': {'cpus': 1, 'memory_bytes': 6442450944, 'scratch_bytes': 536870912,
                             'seconds_per_call': 120, 'maximum_calls': 150, 'work_seconds': 3600,
                             'outer_seconds': 3660, 'root_go_required': True},
    }
    result = {'schema': 'pinwheel.streaming-8x4-rc-layered-plan.v1', 'qualified': False, 'model_qualified': False,
              'native_executed': False, 'reference_executed': False,
              'process_intake_manifest_sha256': P.sha(Path(intake) / 'manifest.json'),
              'source_pins': P.consumer_protocol(), 'cases': cases, 'controls': controls, 'protocol': protocol,
              'producers_sha256': {name: P.sha(parent / name) for name in source_names},
              'qualification_limits': ['M1-only self/lateral C; no vertical, upper-metal, diagonal or shielding coverage',
                                        'mesh/domain empirical stability is not a rigorous continuum error enclosure',
                                        'no full RC model or final extracted timing promotion from this pilot']}
    output.mkdir(); (output / 'plan.json').write_text(json.dumps(result, indent=2) + '\n')
    return {'prepared': str(output), 'plan_sha256': P.sha(output / 'plan.json'), 'reference_executed': False}


def main():
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--intake', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True); args = p.parse_args()
    print(json.dumps(prepare(args.intake, args.output), indent=2))


if __name__ == '__main__':
    main()
