"""New after-failure fixed uniform count97 -> extra-fine-f0 point study."""
import argparse
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_uniform_incore as U
import streaming_8x4_rc_uniform_incore_execute as UX
import streaming_8x4_rc_uniform_incore_readback as UR
import streaming_8x4_rc_ooc as C
P, E, ROOT = U.P, U.E, U.ROOT
B = U.CAMPAIGN
NEW = ('streaming_8x4_rc_uniform_extra.py', 'streaming_8x4_rc_uniform_extra_readback.py')
FULL_PLAN = '66e9852784c67b01156dfa9f649434ce8190bd9922a268cb8e4a388f6af03b63'
FULL_READBACK = '81547850af1c84bcb4a8398f80c19a9c5e5ba30e1fd89a02faed6b57df717d2f'
FULL_RESOURCE = '9fed81ec9d976959dc04fbbf2c5e38095dc269b8870aedc61d9ef427eb4c91a4'
BASE_COMMAND = 'c53f1df433110492053d6748301be32dd31f5ff3ef1eb4476d016c0f9b23df27'
CASE = 'wire_w0p32_L20_M30'
MESH = '0.00002158725'
OUTPUT = 'rc-uniform-extra-fine-01'
CONTAINER = 'pinwheel-8x4-' + OUTPUT
STAGES = ['count97', 'solve']


def write(path, row): U.write(path, row)


def sources():
    return dict(sorted(dict(U.sources(), **C.sources(), **{n: E.sha(Path(__file__).with_name(n)) for n in NEW}).items()))


def policy():
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-policy.v1', stages=STAGES, maximum_calls=2,
        case=CASE, extra_mesh=MESH, count_ratio='1000000000000', count_expected_exit=97, solve_ratio='0',
        coordinate_unit_m='0.000001', preconditioner='two-level-128', gmres_tolerance='0.0005', interaction_ratio='0.25',
        cpus=1, memory_bytes=6442450944, no_extra_swap=True, pids=128, tmpfs_bytes=536870912,
        seconds_per_leaf=120, work_seconds=270, outer_seconds=330, next_leaf_reserve_seconds=130,
        memory_preempt_fraction='0.95', poll_seconds='0.25', scratch_threshold_bytes=17179869184,
        scratch_threshold_is_hard_quota=False, disk_reserve_bytes=12884901888,
        count97_not_numerical_success=True, no_retry_or_fallback=True, maximum_matrix_change='0.02',
        exact_source_count_memory_admission_required=True, original55_failure_unchanged=True,
        full55_limited_pilot_passed=False, model_qualified=False, qualified_timing=False, root_go_required=True,
        scope='New fixed extra-fine point after complete55 failure; no old55 pass or extended-universe authority')


def original(inputs):
    owner = inputs / 'full55-preparation'; plan = U.verify(owner, FULL_PLAN)
    path = inputs / 'full55-readback.json'; P.need(E.sha(path) == FULL_READBACK, 'Exact complete55 failed readback differs')
    row = json.loads(path.read_text()); resource = inputs / 'full55-resource.json'
    P.need(E.sha(resource) == FULL_RESOURCE and row['new_policy_plan']['sha256'] == FULL_PLAN
        and all(row[k] is True for k in ('measurement_packet_completed', 'resource_feasible', 'numeric_passed'))
        and row['limited_uniform_finite_wire_pilot_passed'] is False and row['model_qualified'] is False
        and row['raw_readback']['analysis']['passed'] is False
        and [r['case'] for r in row['raw_readback']['analysis']['mesh_results'] if not r['passed']] == [CASE],
        'Original55 must remain the complete independently closed mesh failure')
    P.need(E.sha(inputs / 'base-command.json') == BASE_COMMAND, 'Original resource-command authority differs')
    case = next(c for c in plan['cases'] if c['name'] == CASE)
    P.need(case['coordinate_unit_m'] == policy()['coordinate_unit_m'], 'Original finite-wire unit differs')
    prior = []
    for i in (48, 49):
        job = U.jobs(plan)[i]
        P.need(job['case'] == CASE, 'Exact prior case membership differs')
        leaf = UR.leaf(owner, FULL_PLAN, plan, job, inputs / 'previous' / ('job-' + str(i).zfill(3)))
        P.need(leaf == row['raw_readback']['leaves'][i] and leaf['numeric_passed'] and leaf['resource_feasible'],
            'Original selected raw leaf/current source custody differs')
        prior.append(leaf)
    P.need(P.cellwise_change(prior[0]['numeric'], prior[1]['numeric']) <= P.number('.02'), 'Prior final mesh pair differs')
    return plan, case, prior


def ownership(plan, digest):
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-scratch-owner.v1', plan_sha256=digest,
        scratch_host_path=plan['scratch_host_path'], stages=STAGES, ephemeral_solver_scratch_only=True)


def verify_owner(root, plan, digest, fresh=False):
    P.need(root.is_dir() and not root.is_symlink() and (root / 'owner.json').is_file()
        and not (root / 'owner.json').is_symlink() and json.loads((root / 'owner.json').read_text()) == ownership(plan, digest),
        'Uniform extra scratch owner differs')
    P.need({p.name for p in root.iterdir()} <= ({'owner.json'} if fresh else {'owner.json', *STAGES})
        and all(p.is_dir() and not p.is_symlink() for p in root.iterdir() if p.name != 'owner.json'),
        'Foreign/aliased uniform extra scratch stage')


def memory_admission(count, peak):
    n, links = count['panels'], count['links']
    P.need(type(n) is int and n > 0 and type(links) is int and links > 0 and type(peak) is int and peak >= 0,
        'Actual count/peak memory admission data invalid')
    terms = dict(observed_count_probe_cumulative_peak_bytes=peak,
        complete_rounded_link_buffers_bytes=((links + 1048575) // 1048576) * 1048576 * 16,
        two_worst_1001_vector_arrays_bytes=2 * 1001 * n * 8, work_vectors_bytes=24 * n * 8,
        Hessenberg_reserve_bytes=8016000, two_maximum_SUPER_matrices_bytes=2 * 4096 ** 2 * 8,
        additional_untracked_reserve_bytes=536870912)
    total = sum(terms.values())
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-count-memory-admission.v1', actual_counts=count,
        terms=terms, planning_total_bytes=total, strict_ceiling_bytes=6442450944 * 95 // 100,
        admitted=total < 6442450944 * 95 // 100, no_assumed_mesh_growth_factor=True,
        not_a_proven_malloc_or_RSS_bound=True, source_estimate_function_sha256=E.sha(Path(U.G.__file__)))


def prepare(campaign, runtime, output):
    campaign, runtime, output = (p.resolve() for p in (campaign, runtime, output))
    P.need(campaign == B and not output.exists() and output.parent.is_dir(), 'Fresh exact-campaign extra-point owner required')
    pp = B / 'rc-uniform-incore-full-command-proposal-02.json'
    closed = UR.readback(B / 'rc-uniform-incore-full-preparation-02', FULL_PLAN, B / 'rc-native-outputs' / U.OUTPUT,
        runtime, ROOT / 'build/streaming-tt-resources/8x4-rc-uniform-incore-full-01/report.json', pp)
    P.need(closed == json.loads((B / 'rc-uniform-incore-full-independent-readback-01.json').read_text()), 'Original55 full HOST reopening differs')
    output.mkdir(); shutil.copytree(B / 'rc-uniform-incore-full-preparation-02', output / 'full55-preparation')
    for src, name in [(B / 'rc-uniform-incore-full-independent-readback-01.json', 'full55-readback.json'),
        (ROOT / 'build/streaming-tt-resources/8x4-rc-uniform-incore-full-01/report.json', 'full55-resource.json'),
        (B / 'rc-ooc-command-proposal-03.json', 'base-command.json')]: shutil.copyfile(src, output / name)
    (output / 'previous').mkdir()
    for i in (48, 49): shutil.copytree(B / 'rc-native-outputs' / U.OUTPUT / ('job-' + str(i).zfill(3)), output / 'previous' / ('job-' + str(i).zfill(3)))
    shutil.copytree(B / 'rc-ooc-source-intake-01', output / 'ooc-source')
    original_plan, case, _ = original(output); shutil.copytree(U.geometry(output / 'full55-preparation', case), output / 'geometry')
    scratch = B / ('rc-uniform-extra-scratch-' + output.name.rsplit('-', 1)[-1]); P.need(not scratch.exists(), 'Fresh extra scratch required')
    row = dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-plan.v1', qualified=False, model_qualified=False,
        qualified_timing=False, full55_limited_pilot_passed=False, native_executed=False, policy=policy(), case=case,
        original_solver_policy=original_plan['original_uniform_plan']['policy'], runtime=original_plan['runtime'],
        original55_plan_sha256=FULL_PLAN, original55_failed_readback_sha256=FULL_READBACK,
        scratch_host_path=str(scratch), count_source_evidence=C.evidence(output), producer_sha256=sources(),
        memory_terms_example=memory_admission(dict(panels=61073, links=69117022), 0), files=U.W.input_files(output))
    P.need(E.tree(runtime) == row['runtime'], 'Exact extra-point runtime differs')
    write(output / 'plan.json', row); digest = E.sha(output / 'plan.json'); verify(output, digest)
    scratch.mkdir(); write(scratch / 'owner.json', ownership(row, digest)); return row


def verify(inputs, digest):
    P.need(E.sha(inputs / 'plan.json') == digest, 'Uniform extra plan hash differs')
    row = json.loads((inputs / 'plan.json').read_text()); old, case, _ = original(inputs); scratch = Path(row['scratch_host_path'])
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-uniform-extra-plan.v1'
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'full55_limited_pilot_passed', 'native_executed'))
        and row['policy'] == policy() and row['case'] == case and row['runtime'] == old['runtime']
        and row['original_solver_policy'] == old['original_uniform_plan']['policy']
        and row['original55_plan_sha256'] == FULL_PLAN and row['original55_failed_readback_sha256'] == FULL_READBACK
        and row['count_source_evidence'] == C.evidence(inputs) and row['producer_sha256'] == sources()
        and row['memory_terms_example'] == memory_admission(dict(panels=61073, links=69117022), 0)
        and row['files'] == U.W.input_files(inputs) and E.tree(inputs / 'geometry') == case['files']
        and scratch.parent == B and re.fullmatch(r'rc-uniform-extra-scratch-\d{2}', scratch.name),
        'Uniform extra exact source/geometry/units/parent/memory/policy authority differs')
    return row


def solver_argv(plan, stage):
    P.need(stage in STAGES, 'Undeclared extra-point stage')
    old_mesh = plan['original_solver_policy']['mesh_ladder'][-1]
    P.need(old_mesh == '0.0000431745', 'Exact original finest mesh differs')
    command = U.W.solver_argv(plan['original_solver_policy'], old_mesh)
    P.need(command.count('-m' + old_mesh) == 1, 'Original mesh command token differs')
    command[command.index('-m' + old_mesh)] = '-m' + MESH
    return command + ['-f' + ('1000000000000' if stage == 'count97' else '0')]


def environment(stage):
    return dict(U.C.ENVIRONMENT, TMPDIR='/uniform-extra-scratch/' + stage, TMP='/uniform-extra-scratch/' + stage, TEMP='/uniform-extra-scratch/' + stage)


def header(raw, ratio):
    P.need(type(raw) is str and len(raw) <= 8 * 1024 ** 2, 'Extra-point raw log unsupported')
    for pattern, expected in [(r'^Out-of-core free memory to link memory condition \(-f\):\s*(' + P.NUM + r')\s*$', ratio),
        (r'^Mesh refinement \(-m\):\s*(' + P.NUM + r')\s*$', MESH),
        (r'^Solution scheme \(-g\): Galerkin, GMRES tolerance \(-t\):\s*(' + P.NUM + r')\s*$', '0.0005'),
        (r'^Potential interaction coefficient to mesh refinement ratio \(-d\):\s*(' + P.NUM + r')\s*$', '0.25')]:
        values = re.findall(pattern, raw, re.M); P.need(len(values) == 1 and P.number(values[0]) == P.number(expected), 'Extra-point actual fixed header differs')
    P.need(re.findall(r'^Precond Type\(s\) \(-p\):\s*([^\r\n]*?)\s*$', raw, re.M)
        == ['Two-levels, two-levels preconditioner dimension (-ps): 128'], 'Extra-point actual preconditioner differs')


def parse_count(raw):
    header(raw, '1000000000000'); count = C.counts(raw)
    errors = [line.strip() for line in raw.splitlines() if re.search(r'(?i)warning|\b(?:warn|error|fatal)\b|segmentation fault|killed|timeout', line)]
    P.need(errors == C.EXPECTED_ERRORS and raw.count('Cannot go out-of-core, terminating process') == 1
        and len(re.findall(r'^Number of panels after refinement: \d+$', raw, re.M)) == 1
        and len(re.findall(r'^Number of links to be computed: \d+$', raw, re.M)) == 1
        and re.findall(r"^Out-of-core temporary files folder: '([^']+)'$", raw, re.M) == ['/uniform-extra-scratch/count97']
        and 'Dimension' not in raw and 'GMRES Iteration:' not in raw
        and len(re.findall(r'^Total time: ' + P.NUM + r's \(\d+ days, \d+ hours, \d+ mins, \d+ s\)$', raw, re.M)) == 1,
        'Extra count probe is not the exact intentional zero-chunk97 branch')
    return count


def resource_pass(row):
    delta = U.G.counters(row['cgroup_before'], row['cgroup_after']); before, after = row['cgroup_before'], row['cgroup_after']
    P.need(before['memory_max'] == after['memory_max'] and after['memory_peak'] >= before['memory_peak']
        and row['counter_deltas'] == delta and before['memory_current'] <= row['maximum_polled_memory_current'] <= after['memory_peak'],
        'Extra-point cgroup counter/peak identity differs')
    return (type(row['exit_code']) is int and row['exit_code'] == (97 if row['stage'] == 'count97' else 0)
        and row['process_tree_reaped'] is True and row['timed_out'] is False and row['guard_reason'] is None
        and after['memory_peak'] < after['memory_max'] * 95 // 100
        and all(v == 0 for d in delta.values() for k, v in d.items() if k == 'max' or k.startswith('oom'))
        and max(row['maximum_scratch_logical_bytes'], row['maximum_scratch_allocated_bytes']) < 17179869184
        and row['minimum_bind_disk_free_bytes'] >= 12884901888
        and row['scratch_cleanup']['before'] == row['scratch_cleanup']['after'] == []
        and (row['stage'] != 'solve' or row['maximum_scratch_files'] == row['maximum_scratch_logical_bytes'] == row['maximum_scratch_allocated_bytes'] == 0)
        and row['scratch_cleanup']['only_exact_owned_regular_scratch_removed'] is True and row['inputs_runtime_unchanged'] is True)


def leaf(inputs, digest, plan, runtime, stage, output, admission=None):
    P.need(stage in STAGES and not output.exists() and str(runtime) == '/solver/runtime', 'Fresh exact extra-point leaf required')
    output.mkdir(); work = output / 'work'; shutil.copytree(inputs / 'geometry', work)
    scratch = Path('/uniform-extra-scratch') / stage; P.need(not scratch.exists(), 'Fresh extra-point scratch stage required'); scratch.mkdir()
    before = U.G.cgroup_snapshot(); started = time.monotonic(); child = None
    meminfo = Path('/proc/meminfo').read_text(); (output / 'meminfo.txt').write_text(meminfo); C.memtotal(meminfo)
    if stage == 'solve': P.need(admission and admission['admitted'] and memory_admission(admission['actual_counts'], before['memory_peak'])['admitted'], 'Extra-point pre-exec count-based admission failed')
    row = dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-leaf.v1', plan_sha256=digest, stage=stage,
        argv=solver_argv(plan, stage), environment=environment(stage), timeout_seconds=120, cgroups=UX.native_limits(),
        cgroup_before=before, maximum_polled_memory_current=before['memory_current'], minimum_bind_disk_free_bytes=shutil.disk_usage(scratch).free,
        maximum_scratch_logical_bytes=0, maximum_scratch_allocated_bytes=0, maximum_scratch_files=0,
        timed_out=False, guard_reason=None, process_tree_reaped=False, exit_code=None, expected_count97_observed=False,
        counts=None, numeric=None, numerical_passed=False, resource_feasible=False, qualified=False,
        model_qualified=False, full55_limited_pilot_passed=False, qualified_timing=False)
    try:
        P.need(row['minimum_bind_disk_free_bytes'] >= 17179869184 + 12884901888, 'Extra-point disk admission lacks fixed reserve')
        with (output / 'native.log').open('xb') as stream:
            child = subprocess.Popen(row['argv'], cwd=work, env=row['environment'], stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            while child.poll() is None:
                current = U.G.cgroup_snapshot()['memory_current']; row['maximum_polled_memory_current'] = max(current, row['maximum_polled_memory_current'])
                sample = C.census(scratch); measure = C.scratch_measure(sample); free = shutil.disk_usage(scratch).free
                row['minimum_bind_disk_free_bytes'] = min(free, row['minimum_bind_disk_free_bytes'])
                for key, source in [('maximum_scratch_logical_bytes', 'logical_bytes'), ('maximum_scratch_allocated_bytes', 'allocated_bytes'), ('maximum_scratch_files', 'files')]: row[key] = max(row[key], measure[source])
                elapsed = time.monotonic() - started
                reason = ('memory95' if current >= before['memory_max'] * 95 // 100 else 'scratch16GiB' if max(measure['logical_bytes'], measure['allocated_bytes']) >= 17179869184 else 'disk12GiB' if free < 12884901888 else 'timeout120' if elapsed >= 120 else None)
                if reason: row['guard_reason'] = reason; row['timed_out'] = reason == 'timeout120'; break
                time.sleep(.25)
            if child.poll() is None: os.killpg(child.pid, signal.SIGKILL)
            row['exit_code'] = child.wait(timeout=2)
        try: os.killpg(child.pid, 0)
        except ProcessLookupError: row['process_tree_reaped'] = True
        else: os.killpg(child.pid, signal.SIGKILL); raise ValueError('Extra-point process group remained live')
        raw = (output / 'native.log').read_text()
        if stage == 'count97':
            P.need(row['exit_code'] == 97, 'Extra count probe expected97 exit missing'); row['counts'] = parse_count(raw); row['expected_count97_observed'] = True
        else:
            P.need(row['exit_code'] == 0, 'Extra-fine solve exit failure'); header(raw, '0')
            P.need(U.G.mode_observed(raw), 'Extra-fine actual f0 mode differs')
            row['counts'] = C.counts(raw); row['numeric'] = U.X.parse(raw, dict(policy=plan['original_solver_policy']), plan['case'], MESH); row['numerical_passed'] = True
    except BaseException as error: row['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None: os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        terminal = C.census(scratch); measure = C.scratch_measure(terminal)
        for key, source in [('maximum_scratch_logical_bytes', 'logical_bytes'), ('maximum_scratch_allocated_bytes', 'allocated_bytes'), ('maximum_scratch_files', 'files')]: row[key] = max(row[key], measure[source])
        row['scratch_cleanup'] = C.scratch_cleanup(scratch) if row['process_tree_reaped'] else dict(before=terminal, after=terminal, only_exact_owned_regular_scratch_removed=False)
        row['cgroup_after'] = U.G.cgroup_snapshot(); row['counter_deltas'] = U.G.counters(before, row['cgroup_after'])
        row['inputs_runtime_unchanged'] = verify(inputs, digest) == plan and E.tree(runtime) == plan['runtime'] and E.tree(work) == plan['case']['files']
        row['resource_feasible'] = resource_pass(row); row['log_sha256'] = E.sha(output / 'native.log') if (output / 'native.log').exists() else None
        row['meminfo_sha256'] = E.sha(output / 'meminfo.txt'); row['wall_seconds'] = time.monotonic() - started; write(output / 'report.json', row)
    return row


def run(inputs, digest, runtime, output):
    plan = verify(inputs, digest); UX.native_limits(); root = Path('/uniform-extra-scratch'); verify_owner(root, plan, digest, fresh=True)
    P.need(not output.exists() and output.parent.is_dir() and E.tree(runtime) == plan['runtime'], 'Extra-point fresh owner/runtime differs')
    output.mkdir(); started = time.monotonic(); row = dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-execution.v1',
        plan_sha256=digest, policy=policy(), qualified=False, model_qualified=False, full55_limited_pilot_passed=False,
        qualified_timing=False, passed=False, measurement_packet_completed=False, resource_feasible=False,
        numerical_passed=False, memory_admission=None, jobs=[])
    try:
        first = leaf(inputs, digest, plan, runtime, 'count97', output / 'count97')
        row['jobs'].append(dict(stage='count97', report_sha256=E.sha(output / 'count97/report.json')))
        P.need(first['resource_feasible'] and first['expected_count97_observed'], 'Extra-point count97 resource/typed branch failed')
        row['memory_admission'] = memory_admission(first['counts'], first['cgroup_after']['memory_peak'])
        P.need(row['memory_admission']['admitted'], 'Extra-fine exact count-based6GiB admission rejected')
        P.need(time.monotonic() - started < 140, 'Extra-point lacks full next-leaf allowance')
        second = leaf(inputs, digest, plan, runtime, 'solve', output / 'solve', row['memory_admission'])
        row['jobs'].append(dict(stage='solve', report_sha256=E.sha(output / 'solve/report.json')))
        row['solve_counts_match_probe'] = first['counts'] == second['counts']
        row['measurement_packet_completed'] = first['process_tree_reaped'] and second['process_tree_reaped']
        row['resource_feasible'] = first['resource_feasible'] and second['resource_feasible']
        row['numerical_passed'] = second['numerical_passed'] and row['solve_counts_match_probe']; row['passed'] = row['resource_feasible'] and row['numerical_passed']
    except BaseException as error: row['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        row['inputs_runtime_unchanged'] = verify(inputs, digest) == plan and E.tree(runtime) == plan['runtime']
        verify_owner(root, plan, digest); row['scratch_terminal_entries'] = sorted(p.name for p in root.iterdir())
        row['scratch_stage_directories_empty'] = all(not list(p.iterdir()) for p in root.iterdir() if p.is_dir())
        row['work_wall_seconds'] = time.monotonic() - started; row['work_budget_satisfied'] = row['work_wall_seconds'] <= 270
        row['resource_feasible'] &= row['work_budget_satisfied']; row['passed'] &= row['work_budget_satisfied'] and row['inputs_runtime_unchanged'] and row['scratch_stage_directories_empty']
        row['wall_seconds'] = row['work_wall_seconds']; write(output / 'report.json', row)
    return row


def proposal(inputs, digest, runtime, parent, require_fresh=True):
    inputs, runtime, parent = (p.resolve() for p in (inputs, runtime, parent)); plan = verify(inputs, digest)
    scratch = Path(plan['scratch_host_path']); verify_owner(scratch, plan, digest, fresh=require_fresh)
    old = json.loads((inputs / 'base-command.json').read_text()); command = list(old['argv'])
    replacements = {old['container_name']: CONTAINER,
        'type=bind,src=' + str(Path(old['plan_path']).parent) + ',dst=/rc-inputs,readonly': 'type=bind,src=' + str(inputs) + ',dst=/rc-inputs,readonly',
        'type=bind,src=' + old['scratch_host_path'] + ',dst=/ooc-scratch': 'type=bind,src=' + str(scratch) + ',dst=/uniform-extra-scratch',
        '/rc-source/streaming_8x4_rc_ooc.py': '/rc-source/' + NEW[0], old['plan_sha256']: digest,
        '/rc-output-parent/' + C.OUTPUT: '/rc-output-parent/' + OUTPUT}
    for before, after in replacements.items(): P.need(command.count(before) == 1, 'Extra-point exact identity token differs'); command[command.index(before)] = after
    P.need(E.tree(runtime) == plan['runtime'] and str(runtime) == old['runtime_path'] and parent.is_dir()
        and ('type=bind,src=' + str(parent) + ',dst=/rc-output-parent') in command
        and (not require_fresh or not (parent / OUTPUT).exists()), 'Extra-point runtime/fresh output differs')
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-command-proposal.v1', root_go_required=True, admitted=False,
        native_executed=False, model_qualified=False, full55_limited_pilot_passed=False, qualified_timing=False,
        plan_path=str(inputs / 'plan.json'), plan_sha256=digest, runtime_path=str(runtime), scratch_host_path=str(scratch),
        scratch_owner_sha256=E.sha(scratch / 'owner.json'), timeout_seconds=330, container_name=CONTAINER,
        output_name=OUTPUT, policy=policy(), producer_sha256=sources(), argv=command)


def launch_reopen(path, command):
    py = '/opt/homebrew/opt/python@3.13/bin/python3.13'; resource = ROOT / 'build/streaming-tt-resources' / ('8x4-' + OUTPUT) / 'report.json'
    argv = [py, '-B', str(ROOT / 'scripts/streaming_8x4_acceptance_resources.py'), '--campaign-root', str(ROOT), '--kind', 'solver',
        '--tag', '8x4-' + OUTPUT, '--timeout-seconds', '330', '--rss-mib', '4096', '--container-name', CONTAINER,
        '--input', str(path.resolve()), '--input', command['plan_path'], '--input', str(Path(command['scratch_host_path']) / 'owner.json')]
    for name in sorted(command['producer_sha256']): argv += ['--input', str(ROOT / 'scripts' / name)]
    argv += ['--', *command['argv']]
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-launch-reopen.v1', root_go_required=True, native_executed=False,
        resource_supervisor_argv=argv, HOST_readback_argv=[py, '-B', str(ROOT / 'scripts' / NEW[1]), '--inputs', str(Path(command['plan_path']).parent),
            '--plan-sha256', command['plan_sha256'], '--directory', str(B / 'rc-native-outputs' / OUTPUT), '--runtime', command['runtime_path'],
            '--resource-report', str(resource), '--command-proposal', str(path.resolve()), '--output', str(B / 'rc-uniform-extra-independent-readback-01.json')])


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare')
    for n in ('campaign', 'runtime', 'output'): q.add_argument('--' + n, type=Path, required=True)
    for action in ('verify', 'proposal', 'run'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action != 'verify': q.add_argument('--runtime', type=Path, required=True); q.add_argument('--output', type=Path, required=True)
        if action == 'proposal': q.add_argument('--launch-reopen', type=Path, required=True)
    a = p.parse_args()
    if a.action == 'prepare': prepare(a.campaign, a.runtime, a.output); print(E.sha(a.output / 'plan.json')); return 0
    if a.action == 'verify': verify(a.inputs, a.plan_sha256); print('verified'); return 0
    if a.action == 'proposal':
        command = proposal(a.inputs, a.plan_sha256, a.runtime, B / 'rc-native-outputs'); write(a.output, command); write(a.launch_reopen, launch_reopen(a.output, command)); return 0
    return 0 if run(a.inputs, a.plan_sha256, a.runtime, a.output)['passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
