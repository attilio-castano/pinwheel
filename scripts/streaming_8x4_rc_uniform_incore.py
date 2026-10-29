"""Fresh complete55 uniform -f0 authority; no historical receipt rewriting."""
import argparse
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_incore as G
import streaming_8x4_rc_incore_readback as GR

W, X, F, P, E = G.W, G.X, G.F, G.P, G.E
C = W.C
ROOT = W.ROOT
CAMPAIGN = ROOT / 'build/campaigns/8x4-20261022-01'
UNIFORM = '1981b870525ef5253da1cb78612976ebe18306392f1bfe6480cffef7575c82ff'
PROBE_PLAN = '53393b5c1e68ee4ad3c619dc4622dbb27ca2f3bfbe298dd57565eb1222fb53b6'
PROBE_PROPOSAL = 'ac8dbd09ae5450f9e285fd944a887bbf634862814993b3c7cf9d692c5e17c589'
PROBE_RESOURCE = '80ed9b0d475abd0f1420701e671bcc130bbe4dc2a2d8b2090c3729737109e2fb'
PROBE_RUN = 'c9a26b0f034ffec39fed2e94e3962eff83032a41c2f19d36a59b95efe5eb212e'
PROBE_READBACK = '72d75a4624fb8fb357d9fa96fd3d2bf5a6f560afb6cbc9b5a764babdc0d6713a'
NEW = ('streaming_8x4_rc_uniform_incore.py', 'streaming_8x4_rc_uniform_incore_execute.py', 'streaming_8x4_rc_uniform_incore_readback.py')
OUTPUT = 'rc-uniform-incore-full-01'


def write(path, value): W.write(path, value)


def sources():
    return dict(G.sources(), **{n: E.sha(Path(__file__).with_name(n)) for n in NEW})


def policy():
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-policy.v1', maximum_calls=55,
        original_profile=W.PROFILES[1], only_solver_delta=['-f0'], work_seconds=1800, outer_seconds=1860,
        seconds_per_leaf=120, next_leaf_reserve_seconds=130, cpus=1, memory_bytes=6442450944,
        no_extra_swap=True, pids=128, scratch_bytes=536870912, memory_preempt_fraction='0.95',
        memory_poll_seconds='0.25', mandatory_actual_f_header='0', peak_scope=G.policy()['peak_scope'],
        capture=G.policy()['capture'], stop_on_first_numeric_failure=True,
        stop_suffix_on_resource_or_custody_failure=True, all_55_fresh_required=True, no_cache_reuse=True,
        mathematical_gates_unchanged=True, root_go_required=True, model_qualified=False, qualified_timing=False,
        scope='Complete original uniform finite-wire pilot only; no layered M1 or full-model promotion')


def parent(inputs):
    owner = inputs / 'probe-preparation/original-1/preparation'; plan = W.verify(owner, UNIFORM)
    P.need(plan['profile'] == W.PROFILES[1] and len(W.jobs(plan)) == 55
        and plan['policy'] == W.policy(W.PROFILES[1]), 'Only exact original55-call uniform parent admitted')
    return owner, plan


def probe_join(inputs):
    """New relocation intake; original serialized claims and paths stay literal."""
    prepared = inputs / 'probe-preparation'; probe = G.verify(prepared, PROBE_PLAN)
    paths = {'proposal.json': PROBE_PROPOSAL, 'resource.json': PROBE_RESOURCE,
        'readback.json': PROBE_READBACK, G.OUTPUT + '/report.json': PROBE_RUN}
    for name, pin in paths.items(): P.need(E.sha(inputs / name) == pin, 'Exact passed resource-probe evidence changed')
    proposal = json.loads((inputs / 'proposal.json').read_text()); resource = json.loads((inputs / 'resource.json').read_text())
    report = json.loads((inputs / G.OUTPUT / 'report.json').read_text()); readback = json.loads((inputs / 'readback.json').read_text())
    original_plan = str(CAMPAIGN / 'rc-incore-preparation-02/plan.json')
    original_proposal = str(CAMPAIGN / 'rc-incore-command-proposal-02.json')
    original_resource = str(ROOT / 'build/streaming-tt-resources/8x4-rc-incore-two-leaf-01/report.json')
    b = resource['campaign_boundary']; seals = resource['input_sha256']
    P.need(proposal['plan_path'] == original_plan and proposal['plan_sha256'] == PROBE_PLAN
        and resource['schema'] == 'pinwheel.streaming-tt-resource-job.v1'
        and resource['argv'] == proposal['argv'] and resource['timeout_seconds'] == 330
        and resource['status'] == 'completed' and type(resource['exit_code']) is int and resource['exit_code'] == 0
        and resource['cleanup_confirmed'] is True and resource['inputs_unchanged'] is True
        and resource['owned_processes_remaining'] == [] and resource['containers_remaining'] == [] and resource['cleanup_errors'] == []
        and b['schema'] == 'pinwheel.streaming-8x4-resource-boundary.v1' and b['campaign_root'] == str(ROOT)
        and b['campaign_kind'] == 'rc_experiment' and b['shared_lease']['heavy_lock'] == str(ROOT / 'build/streaming-tt-resources/heavy.lock')
        and b['wrapper_sha256'] == E.sha(Path(__file__).with_name('streaming_8x4_acceptance_resources.py'))
        and b['inherited_supervisor_sha256'] == resource['supervisor_sha256'] == E.sha(Path(__file__).with_name('streaming_tt_resources.py'))
        and seals[original_plan] == PROBE_PLAN and seals[original_proposal] == PROBE_PROPOSAL
        and all(seals[str(ROOT / 'scripts' / n)] == h == E.sha(Path(__file__).with_name(n)) for n, h in probe['producer_sha256'].items()),
        'Original resource-probe literal command/input/source/cleanup authority differs')
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-incore-execution.v1' and report['plan_sha256'] == PROBE_PLAN
        and report['policy'] == G.policy() and all(report[k] is True for k in ('measurement_packet_completed', 'resource_feasible', 'numeric_passed', 'passed', 'inputs_runtime_unchanged'))
        and all(report[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed', 'qualified_timing'))
        and [j['leaf_index'] for j in report['jobs']] == [0, 1], 'Resource probe did not close both actual leaves')
    leaves = [GR.leaf(prepared, PROBE_PLAN, i, inputs / G.OUTPUT / ('job-' + str(i).zfill(3))) for i in range(2)]
    P.need(readback['schema'] == 'pinwheel.streaming-8x4-rc-incore-independent-readback.v1'
        and readback['plan_sha256'] == PROBE_PLAN and readback['leaves'] == leaves
        and all(readback[k] is True for k in ('measurement_packet_completed', 'resource_feasible', 'numeric_passed'))
        and all(readback[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed', 'qualified_timing'))
        and readback['resource_cleanup_join']['resource_report'] == dict(path=original_resource, sha256=PROBE_RESOURCE),
        'Passed probe raw mode/matrix/cgroup reopening or literal original path claim differs')
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-probe-relocation-intake.v1',
        original_plan_sha256=PROBE_PLAN, original_proposal_sha256=PROBE_PROPOSAL,
        original_resource_sha256=PROBE_RESOURCE, original_run_sha256=PROBE_RUN, original_readback_sha256=PROBE_READBACK,
        all_original_bytes_and_path_claims_unchanged=True, two_resource_points_reopened=True,
        probe_is_not_full55_mathematical_authority=True, no_probe_result_reused_as_fresh_measurement=True)


def prepare(campaign, runtime, output):
    P.need(campaign.resolve() == CAMPAIGN and not output.exists() and output.parent.is_dir(), 'Fresh exact-campaign uniform owner required')
    # Admission first uses the original owners and exact original reader.
    pp = campaign / 'rc-incore-command-proposal-02.json'; q = json.loads(pp.read_text())
    reopened = GR.readback(campaign / 'rc-incore-preparation-02', PROBE_PLAN, campaign / 'rc-native-outputs' / G.OUTPUT,
        runtime, ROOT / 'build/streaming-tt-resources/8x4-rc-incore-two-leaf-01/report.json', pp)
    P.need(reopened == json.loads((campaign / 'rc-incore-independent-readback-01.json').read_text()), 'Original probe reader differs')
    output.mkdir(); shutil.copytree(campaign / 'rc-incore-preparation-02', output / 'probe-preparation')
    shutil.copytree(campaign / 'rc-native-outputs' / G.OUTPUT, output / G.OUTPUT)
    for source, name in [(pp, 'proposal.json'), (campaign / 'rc-incore-independent-readback-01.json', 'readback.json'),
        (ROOT / 'build/streaming-tt-resources/8x4-rc-incore-two-leaf-01/report.json', 'resource.json')]: shutil.copyfile(source, output / name)
    _, old = parent(output); evidence = probe_join(output)
    P.need(E.tree(runtime) == old['runtime'] and str(runtime.resolve()) == q['runtime_path'], 'Original exact runtime owner/bytes differ')
    files = W.input_files(output)
    P.need(len(files) <= 1600 and sum(r.get('bytes', 0) for r in files.values()) <= 24 * 1024 ** 2, 'Uniform HOST intake exceeds fixed budget')
    row = dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-plan.v1', qualified=False, model_qualified=False,
        qualified_timing=False, native_executed=False, root_go_required=True, policy=policy(),
        original_uniform_plan_sha256=UNIFORM, original_uniform_plan=old, cases=old['cases'], runtime=old['runtime'],
        source_probe_intake=evidence, producer_sha256=sources(), files=files, all55_must_be_fresh=True)
    write(output / 'plan.json', row); verify(output, E.sha(output / 'plan.json')); return row


def verify(inputs, digest):
    P.need(E.sha(inputs / 'plan.json') == digest, 'New uniform in-core plan hash differs')
    row = json.loads((inputs / 'plan.json').read_text()); _, old = parent(inputs)
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-uniform-incore-full-plan.v1'
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'native_executed'))
        and row['root_go_required'] is True and row['policy'] == policy() and row['original_uniform_plan_sha256'] == UNIFORM
        and row['original_uniform_plan'] == old and row['cases'] == old['cases'] and row['runtime'] == old['runtime']
        and row['source_probe_intake'] == probe_join(inputs) and row['producer_sha256'] == sources()
        and row['files'] == W.input_files(inputs) and row['all55_must_be_fresh'] is True,
        'New uniform full55 scope/geometry/units/reference/source/probe/custody differs')
    return row


def jobs(plan): return W.jobs(plan['original_uniform_plan'])


def geometry(inputs, case): return inputs / 'probe-preparation/original-1/preparation/geometry' / case['name']


def solver_argv(plan, mesh): return W.solver_argv(plan['original_uniform_plan']['policy'], mesh) + ['-f0']


def proposal(inputs, digest, runtime, parent, require_fresh=True):
    inputs, runtime, parent = (p.resolve() for p in (inputs, runtime, parent)); plan = verify(inputs, digest)
    old = json.loads((inputs / 'probe-preparation/original-1/proposal.json').read_text())
    P.need(E.tree(runtime) == plan['runtime'] and str(runtime) == old['runtime_path'] and parent.is_dir()
        and (not require_fresh or not (parent / OUTPUT).exists()), 'Uniform in-core exact runtime/fresh output differs')
    command = list(old['argv']); replacements = {old['container_name']: 'pinwheel-8x4-' + OUTPUT,
        'type=bind,src=' + str(Path(old['plan_path']).parent) + ',dst=/rc-inputs,readonly': 'type=bind,src=' + str(inputs) + ',dst=/rc-inputs,readonly',
        '/rc-source/streaming_8x4_rc_full_execute.py': '/rc-source/streaming_8x4_rc_uniform_incore_execute.py',
        UNIFORM: digest, '/rc-output-parent/' + old['output_name']: '/rc-output-parent/' + OUTPUT}
    for before, after in replacements.items(): P.need(command.count(before) == 1, 'Uniform command identity token differs'); command[command.index(before)] = after
    mounted_parent = next(s.split('src=', 1)[1].split(',dst=', 1)[0] for s in command if 'dst=/rc-output-parent' in s)
    P.need(Path(mounted_parent).resolve() == parent, 'Original uniform output mount differs')
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-command-proposal.v1', root_go_required=True,
        admitted=False, native_executed=False, model_qualified=False, qualified_timing=False,
        plan_path=str(inputs / 'plan.json'), plan_sha256=digest, runtime_path=str(runtime), output_name=OUTPUT,
        container_name='pinwheel-8x4-' + OUTPUT, timeout_seconds=1860, policy=policy(), producer_sha256=sources(), argv=command)


def launch_reopen(proposal_path, command):
    python = '/opt/homebrew/opt/python@3.13/bin/python3.13'; tag = '8x4-' + OUTPUT
    resource = ROOT / 'build/streaming-tt-resources' / tag / 'report.json'
    argv = [python, '-B', str(ROOT / 'scripts/streaming_8x4_acceptance_resources.py'), '--campaign-root', str(ROOT),
        '--kind', 'solver', '--tag', tag, '--timeout-seconds', '1860', '--rss-mib', '4096',
        '--container-name', command['container_name'], '--input', str(proposal_path.resolve()), '--input', command['plan_path']]
    for name in sorted(command['producer_sha256']): argv += ['--input', str(ROOT / 'scripts' / name)]
    argv += ['--', *command['argv']]
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-launch-reopen-proposal.v1', root_go_required=True,
        native_executed=False, resource_supervisor_argv=argv, required_resource_report=str(resource),
        HOST_readback_argv=[python, '-B', str(ROOT / 'scripts/streaming_8x4_rc_uniform_incore_readback.py'),
            '--inputs', str(Path(command['plan_path']).parent), '--plan-sha256', command['plan_sha256'],
            '--directory', str(CAMPAIGN / 'rc-native-outputs' / OUTPUT), '--runtime', command['runtime_path'],
            '--resource-report', str(resource), '--command-proposal', str(proposal_path.resolve()),
            '--output', str(CAMPAIGN / 'rc-uniform-incore-full-independent-readback-01.json')],
        HOST_only_after_actual_terminal_and_Root_signal=True, model_qualified=False, qualified_timing=False)


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare')
    for n in ('campaign', 'runtime', 'output'): q.add_argument('--' + n, type=Path, required=True)
    for action in ('verify', 'proposal'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action == 'proposal':
            for n in ('runtime', 'output', 'launch-reopen'): q.add_argument('--' + n, type=Path, required=True)
    a = p.parse_args()
    if a.action == 'prepare': prepare(a.campaign, a.runtime, a.output); result = dict(plan_sha256=E.sha(a.output / 'plan.json'), native_executed=False)
    elif a.action == 'verify': result = dict(verified=bool(verify(a.inputs, a.plan_sha256)), native_executed=False)
    else:
        result = proposal(a.inputs, a.plan_sha256, a.runtime, CAMPAIGN / 'rc-native-outputs'); write(a.output, result)
        write(a.launch_reopen, launch_reopen(a.output, result))
    print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
