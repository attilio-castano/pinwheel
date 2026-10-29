"""Fixed extra-fine HOST controls; no solver or Native execution."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value
X = module('streaming_8x4_rc_uniform_extra'); R = module('streaming_8x4_rc_uniform_extra_readback')
B = X.B
RAW = (B / 'rc-native-outputs/rc-uniform-incore-full-01/job-049/native.log').read_text()
FULL = json.loads((B / 'rc-uniform-incore-full-preparation-02/plan.json').read_text())
CASE = next(c for c in FULL['cases'] if c['name'] == X.CASE)
PLAN = dict(original_solver_policy=FULL['original_uniform_plan']['policy'], case=CASE)


def count_raw():
    raw = RAW[:RAW.index('Done computing links')]
    raw = raw.replace('(-f): 0', '(-f): 1e+12').replace('(-m): 4.31745e-05', '(-m): 2.158725e-05')
    return raw + "Out-of-core temporary files folder: '/uniform-extra-scratch/count97'\n" + '\n'.join(X.C.EXPECTED_ERRORS[:1]) + '\n       Cannot go out-of-core, terminating process\nDone computing links\nTotal time: 1.000000s (0 days, 0 hours, 0 mins, 1 s)\n' + X.C.EXPECTED_ERRORS[1] + '\n'


def snapshot():
    return dict(memory_current=1000, memory_peak=2000, memory_max=6442450944, memory_swap_max=0,
        memory_events=dict(max=0, oom=0, oom_kill=0), memory_events_local=dict(max=0, oom=0, oom_kill=0))


class ExtraControls(unittest.TestCase):
    def test_exact_point_flags_units_resources_and_no_old55_promotion(self):
        self.assertEqual(X.CASE, 'wire_w0p32_L20_M30'); self.assertEqual(X.MESH, '0.00002158725')
        self.assertEqual(CASE['coordinate_unit_m'], '0.000001')
        for stage, flag in [('count97', '-f1000000000000'), ('solve', '-f0')]:
            old = X.U.W.solver_argv(PLAN['original_solver_policy'], '0.0000431745')
            command = X.solver_argv(PLAN, stage)
            self.assertEqual(command[-1], flag); self.assertEqual(len(command), len(old) + 1)
            self.assertEqual([(a, b) for a, b in zip(old, command[:-1]) if a != b], [('-m0.0000431745', '-m' + X.MESH)])
            self.assertEqual(X.solver_argv(PLAN, stage)[-3:-1], ['-pn', '-ps128'])
        p = X.policy()
        for k, v in dict(memory_bytes=6442450944, cpus=1, pids=128, work_seconds=270, outer_seconds=330, seconds_per_leaf=120).items(): self.assertEqual(p[k], v)
        self.assertFalse(p['full55_limited_pilot_passed']); self.assertFalse(p['model_qualified']); self.assertTrue(p['no_retry_or_fallback'])
        with self.assertRaises(ValueError): X.solver_argv(PLAN, 'retry')

    def test_new_mesh_adapter_rejects_wrong_or_duplicate_token_and_foreign_geometry(self):
        bad = copy.deepcopy(PLAN); bad['original_solver_policy']['mesh_ladder'][-1] = '0.000086349'
        with self.assertRaisesRegex(ValueError, 'original finest mesh'): X.solver_argv(bad, 'solve')
        old = X.U.W.solver_argv(PLAN['original_solver_policy'], '0.0000431745')
        for command in ([t for t in old if t != '-m0.0000431745'], old + ['-m0.0000431745']):
            with patch.object(X.U.W, 'solver_argv', return_value=command):
                with self.assertRaisesRegex(ValueError, 'mesh command token'): X.solver_argv(PLAN, 'solve')
        with patch.object(X, 'CASE', 'wire_w0p16_L20_M30'):
            with self.assertRaisesRegex(ValueError, 'Original55 must remain'):
                X.original(B / 'rc-uniform-extra-preparation-01')

    def test_actual_count97_branch_preconditioner_and_extra_errors(self):
        raw = count_raw(); self.assertEqual(X.parse_count(raw), dict(panels=61073, links=69117022))
        for bad in (raw + '\nRuntimeWarning: bad\n', raw.replace('(-f): 1e+12', '(-f): 5'),
            raw.replace('(-m): 2.158725e-05', '(-m): 4.31745e-05'), raw.replace('/uniform-extra-scratch/count97', '/tmp'),
            raw.replace('Two-levels, two-levels preconditioner dimension (-ps): 128', 'Jacobi'),
            raw + '\nDimension 2 x 2\n', raw + '\nNumber of panels after refinement: 61073\n'):
            with self.assertRaises(ValueError): X.parse_count(bad)

    def test_f0_numerical_parser_is_original_with_new_explicit_mesh(self):
        raw = RAW.replace('(-m): 4.31745e-05', '(-m): 2.158725e-05'); X.header(raw, '0')
        self.assertTrue(X.U.G.mode_observed(raw))
        numeric = X.U.X.parse(raw, dict(policy=PLAN['original_solver_policy']), CASE, X.MESH)
        self.assertFalse(numeric['model_qualified'])
        for bad in (raw + '\nWarning: bad\n', raw.replace('(-d): 0.25', '(-d): 1'), raw.replace('(-m): 2.158725e-05', '(-m): 4.31745e-05')):
            with self.assertRaises(ValueError): X.U.X.parse(bad, dict(policy=PLAN['original_solver_policy']), CASE, X.MESH)

    def test_complete_source_memory_terms_and_actual_count_rejection(self):
        count = dict(panels=61073, links=69117022); r = X.memory_admission(count, 100000000)
        t = r['terms']; self.assertTrue(r['admitted']); self.assertTrue(r['no_assumed_mesh_growth_factor'])
        self.assertEqual(t['two_maximum_SUPER_matrices_bytes'], 268435456)
        self.assertEqual(t['two_worst_1001_vector_arrays_bytes'], 2 * 1001 * 61073 * 8)
        self.assertEqual(t['complete_rounded_link_buffers_bytes'], 66 * 1048576 * 16)
        self.assertEqual(t['additional_untracked_reserve_bytes'], 536870912)
        self.assertEqual(r['planning_total_bytes'], sum(t.values()))
        self.assertFalse(X.memory_admission(dict(panels=200000, links=300000000), 100000000)['admitted'])
        self.assertFalse(X.memory_admission(count, 6442450944)['admitted'])
        with self.assertRaises(ValueError): X.memory_admission(dict(panels=True, links=1), 0)

    def resource(self, stage='solve'):
        before = snapshot(); after = snapshot()
        return dict(stage=stage, exit_code=97 if stage == 'count97' else 0, cgroup_before=before, cgroup_after=after,
            counter_deltas=X.U.G.counters(before, after), maximum_polled_memory_current=1500,
            process_tree_reaped=True, timed_out=False, guard_reason=None, maximum_scratch_logical_bytes=0,
            maximum_scratch_allocated_bytes=0, maximum_scratch_files=0, minimum_bind_disk_free_bytes=30 * 1024 ** 3,
            scratch_cleanup=dict(before=[], after=[], only_exact_owned_regular_scratch_removed=True), inputs_runtime_unchanged=True)

    def test_stage_exits_counters_peak_guard_and_no_solve_scratch_fallback(self):
        for stage in X.STAGES:
            row = self.resource(stage); self.assertTrue(X.resource_pass(row))
            for change in (dict(exit_code=-9), dict(exit_code=74), dict(timed_out=True), dict(process_tree_reaped=False),
                dict(guard_reason='memory95'), dict(minimum_bind_disk_free_bytes=12 * 1024 ** 3 - 1)):
                self.assertFalse(X.resource_pass(dict(row, **change)))
        row = self.resource(); row['cgroup_after']['memory_events']['oom_kill'] = 1
        row['counter_deltas'] = X.U.G.counters(row['cgroup_before'], row['cgroup_after']); self.assertFalse(X.resource_pass(row))
        self.assertFalse(X.resource_pass(dict(self.resource(), maximum_scratch_files=1)))
        row = self.resource(); row['cgroup_before']['memory_peak'] = 3000
        with self.assertRaises(ValueError): X.resource_pass(row)
        row = self.resource(); del row['cgroup_after']['memory_events']['max']
        with self.assertRaises(ValueError): X.resource_pass(row)

    def test_owned_scratch_rejects_foreign_or_aliased_stage(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); plan = dict(scratch_host_path=str(root)); X.write(root / 'owner.json', X.ownership(plan, 'pin'))
            X.verify_owner(root, plan, 'pin', fresh=True)
            (root / 'foreign').mkdir()
            with self.assertRaises(ValueError): X.verify_owner(root, plan, 'pin')
            (root / 'foreign').rmdir(); (root / 'solve').symlink_to(root / 'absent')
            with self.assertRaises(ValueError): X.verify_owner(root, plan, 'pin')

    def simulated_run(self, work=269, count_ok=True, huge=False):
        temp = tempfile.TemporaryDirectory(); self.addCleanup(temp.cleanup); base = Path(temp.name); scratch = base / 'scratch'; scratch.mkdir()
        plan = dict(runtime={}); calls = []
        def leaf(inputs, digest, p, runtime, stage, owner, admission=None):
            calls.append(stage); owner.mkdir(); row = dict(process_tree_reaped=True, resource_feasible=count_ok,
                expected_count97_observed=stage == 'count97', numerical_passed=stage == 'solve',
                counts=dict(panels=200000 if huge else 61073, links=300000000 if huge else 69117022),
                cgroup_after=dict(memory_peak=2000))
            X.write(owner / 'report.json', row); return row
        clock = iter([0, 1, work])
        paths = lambda p: scratch if str(p) == '/uniform-extra-scratch' else Path(p)
        with patch.object(X, 'verify', return_value=plan), patch.object(X.UX, 'native_limits', return_value={}), \
             patch.object(X, 'verify_owner'), patch.object(X.E, 'tree', return_value={}), patch.object(X, 'leaf', side_effect=leaf), \
             patch.object(X, 'Path', side_effect=paths), patch.object(X.time, 'monotonic', side_effect=lambda: next(clock)):
            result = X.run(base, 'pin', Path('/solver/runtime'), base / X.OUTPUT)
        return result, calls

    def test_no_solve_after_count_or_memory_failure_and_actual_work_limit(self):
        for options in (dict(count_ok=False), dict(huge=True)):
            result, calls = self.simulated_run(**options)
            self.assertEqual(calls, ['count97']); self.assertFalse(result['passed']); self.assertFalse(result['measurement_packet_completed'])
        for work in (269, 271):
            result, calls = self.simulated_run(work)
            self.assertEqual(calls, X.STAGES); self.assertTrue(result['measurement_packet_completed']); self.assertTrue(result['numerical_passed'])
            self.assertIs(result['resource_feasible'], work <= 270); self.assertIs(result['passed'], work <= 270)

    def test_point_continuity_cannot_change_old55_or_create_extended_authority(self):
        r = json.loads((B / 'rc-uniform-incore-full-independent-readback-01.json').read_text())
        prior = r['raw_readback']['leaves'][48:50]; new = copy.deepcopy(prior[1])
        result = R.continuity(prior, new); self.assertTrue(result['both_consecutive_pairs_at_most_two_percent'])
        self.assertFalse(result['old55_limited_pilot_passed']); self.assertFalse(result['new_extended_universe_authority'])
        new['numeric']['matrix'][1][1] = str(X.P.number(new['numeric']['matrix'][1][1]) * X.P.number('1.03'))
        self.assertFalse(R.continuity(prior, new)['both_consecutive_pairs_at_most_two_percent'])

    def test_exact_six_command_identity_changes_and_json_roundtrip(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner = Path(temporary); scratch = owner / 'scratch'; scratch.mkdir(); (scratch / 'owner.json').write_text('{}')
            old = json.loads((B / 'rc-ooc-command-proposal-03.json').read_text()); (owner / 'base-command.json').write_text(json.dumps(old))
            plan = dict(runtime={}, scratch_host_path=str(scratch))
            with patch.object(X, 'verify', return_value=plan), patch.object(X, 'verify_owner'), patch.object(X.E, 'tree', return_value={}):
                new = X.proposal(owner, 'newpin', Path(old['runtime_path']), B / 'rc-native-outputs', require_fresh=False)
            self.assertEqual(len(new['argv']), len(old['argv'])); self.assertEqual(sum(a != b for a, b in zip(old['argv'], new['argv'])), 6)
            self.assertEqual(new['argv'][new['argv'].index('--memory') + 1], '6g')
            path = owner / 'proposal.json'
            self.assertEqual(X.launch_reopen(path, new), X.launch_reopen(path, json.loads(json.dumps(new, sort_keys=True))))

    def test_actual_old55_failed_authority_and_transitive_source_seals(self):
        owner = B / 'rc-uniform-extra-preparation-01'
        plan, case, prior = X.original(owner)
        self.assertEqual(case['name'], X.CASE); self.assertEqual(len(prior), 2)
        with patch.object(X, 'FULL_READBACK', '0' * 64):
            with self.assertRaisesRegex(ValueError, 'failed readback differs'): X.original(owner)
        sources = X.sources()
        for name in X.NEW + ('streaming_8x4_rc_uniform_incore_readback.py', 'streaming_8x4_rc_ooc_readback.py', 'streaming_tt_resources.py'):
            self.assertEqual(sources[name], X.E.sha(ROOT / 'scripts' / name))


if __name__ == '__main__': unittest.main()
