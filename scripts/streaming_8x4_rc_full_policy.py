"""Fresh complete-universe d.25 policies; no historical schema substitution."""
import argparse
import ast
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_conditioning as C
import streaming_8x4_rc_layered_analyze as L
import streaming_8x4_rc_analyze as U

PROFILES = ('layered-m1-jacobi-d025', 'uniform-two-level-d025')
NEW = ('streaming_8x4_rc_full_policy.py', 'streaming_8x4_rc_full_execute.py', 'streaming_8x4_rc_full_readback.py')
# The original FVM receipts record this host identity. It remains literal inside
# /rc-source mounts; deriving it from __file__ would invent a different authority.
ROOT = Path('/Users/attiliocastano/.codex/worktrees/dc52/pinwheel')
REFS = {
    PROFILES[0]: {'plan': '185bac5e2f4346aeb03ebda83b827e7fb0336ffbc51c8a0a46f24b4b72aa910c',
        'report': 'f5a4f60659bd1241dc1796cce695dc3f84d1901b26e5b6bf4d828bdbe8ffc252',
        'resource': '498a148c62f4bd80b8601ac5c591f2fed6cffcdf8dc2246d9f662efc3d535407',
        'proposal': 'eacf1ba4eb5f2bf7a8d2cb0df447b1be9f830e56e37851bcbf28e90ccd28d932'},
    PROFILES[1]: {'plan': C.D.BASELINE_HASH,
        'report': '202d7a972c2b899c2bd7551748180cc29470d239e2e08154591484b5ddefb7d4',
        'resource': 'a1d52992591a2e4effc8e198308ff55337b9a0b3cf066db0175c915c7b441f24',
        'proposal': 'f222ba52f24546442c9e800a9f45df63e678de11cc7f4f69a700a1063106f3a8'}}


def policy(profile):
    P.need(profile in PROFILES, 'Undeclared complete-universe profile')
    layered = profile == PROFILES[0]; work = 3600 if layered else 1800
    return {'schema': 'pinwheel.streaming-8x4-rc-full-native-policy.v1', 'profile': profile,
        'interaction_ratio': '0.25', 'gmres_tolerance': '0.0005', 'scheme': 'Galerkin',
        'preconditioner': 'jacobi' if layered else 'two-level-128', 'preconditioner_flags': [] if layered else ['-pn', '-ps128'],
        'mesh_ladder': C.Q.MESHES, 'maximum_calls': 150 if layered else 55,
        'physical_cases': 6 if layered else 11, 'finite_geometries': 30 if layered else 11,
        'coordinate_policy': 'all cases S20' if layered else 'original U S20; ten finite wires 1e-6m',
        'seconds_per_leaf': 120, 'work_seconds': work, 'outer_seconds': work + 60,
        'cpus': 1, 'memory_bytes': 6442450944, 'scratch_bytes': 536870912, 'pids': 128, 'no_extra_swap': True,
        'warnings_fatal': True, 'maximum_numeric_matrix_asymmetry_relative': '0.01',
        'maximum_cellwise_mesh_change': '0.02', 'consecutive_mesh_pairs_required': 2,
        'maximum_length_slope_change': '0.05', 'maximum_ground_extension_change': '0.02',
        'maximum_independent_reference_difference': '0.10', 'no_adaptive_subset_or_retry': True,
        'numeric_failure_policy': 'stop and preserve incomplete prefix; no partial limited-pilot authority',
        'reference_authority': 'exact original plan, raw results and resource receipt retained without relabeling',
        'root_go_required': True, 'model_qualified': False, 'qualified_timing': False,
        'continuum_error_enclosure': False}


def case_unit(profile, name):
    P.need(profile in PROFILES, 'Undeclared case-unit profile')
    return '0.00000095367431640625' if profile == PROFILES[0] or name == 'historical_U_new_manual' else '0.000001'


def source_closure():
    """Follow local explicit imports, including imports in function bodies."""
    pending = list(NEW) + ['streaming_8x4_rc_layered_native.py', 'streaming_8x4_rc_layered_geometry.py', 'streaming_8x4_rc_layered_plan.py',
        'streaming_8x4_rc_reference_run.py', 'streaming_8x4_acceptance_resources.py',
        'streaming_8x4_acceptance.py', 'streaming_tt_resources.py']; done = {}
    while pending:
        name = pending.pop()
        if name in done: continue
        path = Path(__file__).with_name(name); tree = ast.parse(path.read_text())
        done[name] = E.sha(path)
        for node in ast.walk(tree):
            modules = [x.name for x in node.names] if isinstance(node, ast.Import) else ([node.module] if isinstance(node, ast.ImportFrom) and node.module else [])
            for module in modules:
                if module.startswith('streaming_') and '.' not in module:
                    local = module + '.py'
                    P.need(Path(__file__).with_name(local).is_file(), 'Missing local explicit producer dependency')
                    pending.append(local)
    return dict(sorted(done.items()))


def write(path, row):
    C.write(path, row)


def input_files(owner):
    return {n: row for n, row in E.tree(owner).items() if n != 'plan.json'}


def reference_join(inputs, profile):
    fixed = REFS[profile]; base = inputs / 'reference'
    for name, key in [('plan.json', 'plan'), ('results/report.json', 'report'), ('resource.json', 'resource'), ('proposal.json', 'proposal')]:
        P.need(E.sha(base / name) == fixed[key], 'Exact original FVM authority changed: ' + key)
    original = json.loads((base / 'plan.json').read_text()); proposal = json.loads((base / 'proposal.json').read_text())
    resource = json.loads((base / 'resource.json').read_text()); boundary = resource['campaign_boundary']
    P.need(proposal['plan_sha256'] == fixed['plan'] and resource['argv'] == proposal['argv']
        and resource['timeout_seconds'] == proposal['timeout_seconds'] and resource['status'] == 'completed' and resource['exit_code'] == 0
        and resource['cleanup_confirmed'] is True and resource['inputs_unchanged'] is True
        and resource['owned_processes_remaining'] == [] and resource['cleanup_errors'] == []
        and boundary['schema'] == 'pinwheel.streaming-8x4-resource-boundary.v1'
        and boundary['campaign_kind'] == 'rc_experiment'
        and boundary['shared_lease']['heavy_lock'] == str(ROOT / 'build/streaming-tt-resources/heavy.lock')
        and boundary['wrapper_sha256'] == E.sha(Path(__file__).with_name('streaming_8x4_acceptance_resources.py'))
        and boundary['inherited_supervisor_sha256'] == resource['supervisor_sha256'] == E.sha(Path(__file__).with_name('streaming_tt_resources.py')),
        'Original FVM command/resource/shared-lock cleanup differs')
    if profile == PROFILES[0]: P.need(resource['containers_remaining'] == [], 'Original FVM container residue')
    else:
        P.need('containers_remaining' not in resource and resource['kind'] == 'host'
            and resource['cleanup_scope'] == 'spawned_controller_and_observed_children' and proposal['argv'][0] != 'docker',
            'Historical HOST-only FVM cleanup scope differs')
    seals = resource['input_sha256']
    P.need(seals[proposal['plan_path']] == fixed['plan']
        and any(pin == fixed['proposal'] for pin in seals.values()), 'Original FVM resource lacks plan/proposal seals')
    for n, value in original['producers_sha256'].items():
        P.need(E.sha(Path(__file__).with_name(n)) == value and seals[str(ROOT / 'scripts' / n)] == value,
               'Original FVM producer/resource seal differs')
    if profile == PROFILES[0]:
        plan, report = L.read_reference(base / 'plan.json', fixed['plan'], base / 'results')
        return {'reference_plan_sha256': fixed['plan'], 'reference_report_sha256': fixed['report'],
            'reference_resource_sha256': fixed['resource'], 'reference_calls': 25, 'analysis': report['analysis']}
    report = json.loads((base / 'results/report.json').read_text())
    P.need(report['plan_sha256'] == fixed['plan']
        and all(report['producer_sha256'].get(n) == original['producers_sha256'][n] for n in ('streaming_8x4_rc_protocol.py', 'streaming_8x4_rc_reference.py')),
        'Original uniform FVM plan/producer authority differs')
    return {'reference_plan_sha256': fixed['plan'], 'reference_report_sha256': fixed['report'],
        'reference_resource_sha256': fixed['resource'], 'reference_calls': 8,
        'analysis': U.reference_stability(original, report)}


def prepare(profile, baseline, cases, runtime, reference_plan, reference_results, reference_resource, reference_proposal, output):
    layered = profile == PROFILES[0]; baseline_hash = C.BASELINES[C.Q.PROFILES[0 if layered else 1]]['hash']
    P.need(E.sha(baseline) == baseline_hash and not output.exists() and output.parent.is_dir(), 'Wrong original/fresh full policy owner')
    old = json.loads(baseline.read_text()); p = policy(profile)
    P.need(len(old['cases']) == p['finite_geometries'] and E.tree(runtime) == old['runtime']
        and E.sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256, 'Wrong original universe/runtime')
    if layered:
        P.need(E.sha(cases / 'manifest.json') == old['geometry_manifest_sha256'], 'Wrong original full S20 geometry')
        units = [L.check_unit_witness(cases, c['name']) for c in old['cases']]
    else:
        P.validate_protocol(old['protocol']); units = []
    for c in old['cases']:
        P.need(E.tree(cases / c['name']) == c['files'] and c['coordinate_unit_m'] == case_unit(profile, c['name']), 'Original full geometry/unit differs')
    output.mkdir(); (output / 'baseline').mkdir(); (output / 'geometry').mkdir(); (output / 'reference').mkdir()
    shutil.copyfile(baseline, output / 'baseline/native-plan.json')
    for c in old['cases']: shutil.copytree(cases / c['name'], output / 'geometry' / c['name'])
    if layered: shutil.copyfile(cases / 'manifest.json', output / 'baseline/geometry-manifest.json')
    shutil.copyfile(reference_plan, output / 'reference/plan.json'); shutil.copytree(reference_results, output / 'reference/results')
    shutil.copyfile(reference_resource, output / 'reference/resource.json'); shutil.copyfile(reference_proposal, output / 'reference/proposal.json')
    result = {'schema': 'pinwheel.streaming-8x4-rc-full-policy-plan.v1', 'profile': profile,
        'qualified': False, 'model_qualified': False, 'qualified_timing': False, 'native_executed': False,
        'old_native_plan_sha256': baseline_hash, 'policy': p, 'cases': old['cases'], 'original_protocol': old['protocol'],
        'runtime': old['runtime'], 'solver_sha256': P.SOLVER_SHA256,
        'original_geometry_owner': str(cases.resolve()), 'unit_witnesses': units,
        'reference_join': reference_join(output, profile), 'producer_sha256': source_closure(), 'files': input_files(output)}
    write(output / 'plan.json', result); verify(output, E.sha(output / 'plan.json')); return result


def verify(inputs, plan_hash):
    P.need(E.sha(inputs / 'plan.json') == plan_hash, 'New full-policy plan hash differs')
    plan = json.loads((inputs / 'plan.json').read_text()); profile = plan['profile']; p = policy(profile)
    old_hash = C.BASELINES[C.Q.PROFILES[0 if profile == PROFILES[0] else 1]]['hash']
    P.need(plan['schema'] == 'pinwheel.streaming-8x4-rc-full-policy-plan.v1'
        and all(plan[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'native_executed'))
        and plan['policy'] == p and plan['old_native_plan_sha256'] == old_hash
        and E.sha(inputs / 'baseline/native-plan.json') == old_hash and input_files(inputs) == plan['files']
        and source_closure() == plan['producer_sha256'], 'New full-policy scope/producer/input custody differs')
    old = json.loads((inputs / 'baseline/native-plan.json').read_text())
    P.need(plan['cases'] == old['cases'] and plan['original_protocol'] == old['protocol']
        and len(plan['cases']) == p['finite_geometries'] and plan['runtime'] == old['runtime']
        and plan['solver_sha256'] == old['solver_sha256'] == P.SOLVER_SHA256
        and all(plan['producer_sha256'][n] == value for n, value in old['producers_sha256'].items()),
        'Original complete universe/policy/producer/runtime differs')
    for c in plan['cases']:
        P.need(E.tree(inputs / 'geometry' / c['name']) == c['files'] and c['coordinate_unit_m'] == case_unit(profile, c['name']), 'Copied full geometry/unit differs')
    if profile == PROFILES[0]:
        P.need(E.sha(inputs / 'baseline/geometry-manifest.json') == old['geometry_manifest_sha256']
            and len(plan['unit_witnesses']) == 30 and all(u['retained_SI_and_emitted_S20_readback_exact'] is True for u in plan['unit_witnesses']),
            'Full S20 manifest/witness membership differs')
    else: P.validate_protocol(old['protocol'])
    P.need(reference_join(inputs, profile) == plan['reference_join'], 'Original FVM readback/resource authority differs')
    return plan


def jobs(plan):
    return [{'case': c['name'], 'mesh': m} for c in plan['cases'] for m in plan['policy']['mesh_ladder']]


def solver_argv(policy_row, mesh):
    P.need(mesh in policy_row['mesh_ladder'], 'Undeclared full-policy mesh')
    return ['/solver/runtime/bin/FasterCap', '-b', 'geometry.lst', '-g', '-m' + mesh, '-t0.0005', '-d0.25'] + policy_row['preconditioner_flags']


def proposal(inputs, plan_hash, runtime, parent, require_fresh=True):
    inputs, runtime, parent = (x.resolve() for x in (inputs, runtime, parent)); plan = verify(inputs, plan_hash)
    name = 'rc-full-' + plan['profile'] + '-01'; p = plan['policy']
    P.need(E.tree(runtime) == plan['runtime'] and parent.is_dir() and (not require_fresh or not (parent / name).exists()), 'Full proposal runtime/fresh output differs')
    argv = ['docker', 'run', '--name', 'pinwheel-8x4-' + name, '--rm', '--pull', 'never', '--network', 'none', '--read-only',
        '--cpus', '1', '--memory', '6g', '--memory-swap', '6g', '--pids-limit', '128', '--tmpfs', '/tmp:rw,nosuid,noexec,size=536870912',
        '--mount', f'type=bind,src={Path(__file__).resolve().parent},dst=/rc-source,readonly',
        '--mount', f'type=bind,src={inputs},dst=/rc-inputs,readonly', '--mount', f'type=bind,src={runtime},dst=/solver/runtime,readonly',
        '--mount', f'type=bind,src={parent},dst=/rc-output-parent',
        '--entrypoint', '/nix/store/lqn6mbgzzdrqq2qkwddcmxj9z6amdd86-python3-3.13.13/bin/python3', C.D.IMAGE,
        '-I', '-B', '/rc-source/streaming_8x4_rc_full_execute.py', '--inputs', '/rc-inputs', '--plan-sha256', plan_hash,
        '--runtime', '/solver/runtime', '--output', '/rc-output-parent/' + name]
    return {'schema': 'pinwheel.streaming-8x4-rc-full-policy-command-proposal.v1', 'profile': plan['profile'],
        'root_go_required': True, 'admitted': False, 'native_executed': False, 'model_qualified': False, 'qualified_timing': False,
        'plan_path': str(inputs / 'plan.json'), 'plan_sha256': plan_hash, 'runtime_path': str(runtime), 'output_name': name,
        'container_name': 'pinwheel-8x4-' + name, 'timeout_seconds': p['outer_seconds'], 'policy': p,
        'producer_sha256': plan['producer_sha256'], 'argv': argv}


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare'); q.add_argument('--profile', choices=PROFILES, required=True)
    for n in ('baseline', 'cases', 'runtime', 'reference-plan', 'reference-results', 'reference-resource', 'reference-proposal', 'output'):
        q.add_argument('--' + n, type=Path, required=True)
    for action in ('verify', 'proposal'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action == 'proposal': q.add_argument('--runtime', type=Path, required=True); q.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.action == 'prepare':
        result = prepare(a.profile, a.baseline, a.cases, a.runtime, a.reference_plan, a.reference_results, a.reference_resource, a.reference_proposal, a.output)
        print(json.dumps({'plan_sha256': E.sha(a.output / 'plan.json'), 'maximum_calls': result['policy']['maximum_calls'], 'native_executed': False}, indent=2))
    elif a.action == 'verify': print(json.dumps({'verified': bool(verify(a.inputs, a.plan_sha256)), 'native_executed': False}))
    else:
        result = proposal(a.inputs, a.plan_sha256, a.runtime, a.output.parent); write(a.output, result); print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
