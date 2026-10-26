"""Fresh full55 HOST controls; no solver, subprocess or Native launch."""
import copy
import importlib.util
import inspect
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
    row = importlib.util.module_from_spec(spec); spec.loader.exec_module(row); return row
W = module('streaming_8x4_rc_uniform_incore')
X = module('streaming_8x4_rc_uniform_incore_execute')
R = module('streaming_8x4_rc_uniform_incore_readback')
GOOD = (ROOT / 'test/fixtures/streaming-8x4-rc-wire-coarse-20261022.log').read_text()


class UniformIncoreControls(unittest.TestCase):
    def plan(self):
        owner = W.CAMPAIGN / 'rc-incore-preparation-02/original-1/preparation'
        return json.loads((owner / 'plan.json').read_text())

    def wrapped(self):
        old = self.plan()
        return dict(original_uniform_plan=old, cases=old['cases'], runtime={})

    def test_exact_fresh55_schedule_units_resources_and_delta(self):
        old = self.plan(); plan = self.wrapped(); expected = W.W.jobs(old)
        self.assertEqual(W.jobs(plan), expected); self.assertEqual(len(expected), 55)
        self.assertEqual(len({(j['case'], j['mesh']) for j in expected}), 55)
        self.assertEqual([c['coordinate_unit_m'] for c in old['cases']], ['0.00000095367431640625'] + ['0.000001'] * 10)
        for mesh in old['policy']['mesh_ladder']:
            self.assertEqual(W.solver_argv(plan, mesh), W.W.solver_argv(old['policy'], mesh) + ['-f0'])
        policy = W.policy()
        for name, value in dict(maximum_calls=55, work_seconds=1800, outer_seconds=1860, seconds_per_leaf=120,
            next_leaf_reserve_seconds=130, cpus=1, memory_bytes=6442450944, pids=128, scratch_bytes=536870912).items():
            self.assertEqual(policy[name], value)
        self.assertTrue(policy['all_55_fresh_required']); self.assertTrue(policy['stop_on_first_numeric_failure'])
        self.assertTrue(policy['no_cache_reuse']); self.assertFalse(policy['model_qualified'])

    def test_actual_mode_mesh_preconditioner_unit_and_warning_gates(self):
        plan = self.wrapped(); old = plan['original_uniform_plan']; mesh = old['policy']['mesh_ladder'][0]
        raw = GOOD.replace('condition (-f): 5', 'condition (-f): 0').replace('(-d): 1', '(-d): 0.25')
        raw = raw.replace('Precond Type(s) (-p): Jacobi ', 'Precond Type(s) (-p): Two-levels, two-levels preconditioner dimension (-ps): 128 ')
        case = dict(matrix_names=['g1_GND_SUB', 'g2_SIGNAL'], coordinate_unit_m='0.000001')
        actual = X.parse(raw, plan, case, mesh)
        self.assertEqual(actual, W.X.parse(raw, old, case, mesh))
        s20 = X.parse(raw, plan, dict(case, coordinate_unit_m='0.00000095367431640625'), mesh)
        self.assertNotEqual(actual['matrix_F'], s20['matrix_F'])
        for wrong in (raw.replace('condition (-f): 0', 'condition (-f): 5'), raw + '\nGoing out-of-core\n',
                      raw + '\nWarning: failure\n', raw.replace('(-d): 0.25', '(-d): 1'),
                      raw.replace('Mesh refinement (-m): ' + mesh, 'Mesh refinement (-m): 0.1')):
            with self.assertRaises(ValueError): X.parse(wrong, plan, case, mesh)

    def test_reviewed_guard_leaf_body_preserved_except_typed_selected_case(self):
        expected = inspect.getsource(W.G.leaf)
        substitutions = [
            ('def leaf(inputs, digest, plan, index, runtime, output):', 'def leaf(inputs, digest, plan, job, runtime, output):'),
            ("case = plan['cases'][index]", "case = next(c for c in plan['cases'] if c['name'] == job['case'])"),
            ("inputs / ('original-' + str(index)) / 'failed/work' / n", 'W.geometry(inputs, case) / n'),
            ('pinwheel.streaming-8x4-rc-incore-native-leaf.v1', 'pinwheel.streaming-8x4-rc-uniform-incore-full-native-leaf.v1'),
            ("'leaf_index': index", "'case': job['case'], 'mesh': job['mesh']"),
            ("argv(inputs, index)", "W.solver_argv(plan, job['mesh'])"),
            ('W.C.ENVIRONMENT', 'W.C.ENVIRONMENT'),
            ('E.verify_cgroups()', 'native_limits()'),
            ('parse(raw, inputs, index)', "parse(raw, plan, case, job['mesh'])"),
            ('W.write(output', 'W.write(output')]
        for before, after in substitutions: expected = expected.replace(before, after)
        self.assertEqual(inspect.getsource(X.leaf), expected)

    def mock_run(self, failure=55, resource=True, reaped=True, elapsed=0):
        plan = self.wrapped(); calls = []
        temporary = tempfile.TemporaryDirectory(); self.addCleanup(temporary.cleanup)
        output = Path(temporary.name) / W.OUTPUT
        def fake_leaf(inputs, digest, prepared, job, runtime, owner):
            calls.append(job); owner.mkdir(); failed = len(calls) == failure
            row = dict(exit_code=0, solver_executed=True, process_tree_reaped=(reaped if failed else True),
                copied_inputs_unchanged=True, source_runtime_unchanged=True, producer_plan_unchanged=True,
                resource_feasible=(resource if failed else True), numeric_passed=not failed)
            W.write(owner / 'report.json', row); return row
        clock = iter([0] + [elapsed] * 500)
        with patch.object(X, 'verify', return_value=plan), patch.object(X.E, 'tree', return_value={}), \
             patch.object(X, 'native_limits', return_value={}), patch.object(X, 'leaf', side_effect=fake_leaf), \
             patch.object(X.time, 'monotonic', side_effect=lambda: next(clock)):
            result = X.run(Path(temporary.name), 'seal', Path('/solver/runtime'), output)
        return result, calls

    def test_first_numeric_failure_stops_suffix_and_last_failure_is_complete_not_pass(self):
        for failure in (1, 55):
            result, calls = self.mock_run(failure)
            self.assertEqual(len(calls), failure)
            self.assertIs(result['measurement_packet_completed'], failure == 55)
            self.assertIs(result['resource_feasible'], failure == 55)
            self.assertFalse(result['numeric_passed']); self.assertFalse(result['passed'])

    def test_resource_custody_and_next_leaf_allowance_stop_without_promotion(self):
        result, calls = self.mock_run(1, resource=False)
        self.assertEqual(len(calls), 1); self.assertFalse(result['resource_feasible'])
        result, calls = self.mock_run(55, reaped=False)
        self.assertEqual(len(calls), 55); self.assertFalse(result['measurement_packet_completed'])
        result, calls = self.mock_run(elapsed=1671)
        self.assertEqual(calls, []); self.assertFalse(result['measurement_packet_completed'])

    def raw_packet(self, count=55, failed=None):
        temporary = tempfile.TemporaryDirectory(); self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name); plan = self.wrapped(); jobs = W.jobs(plan)[:count]; rows = []
        for index, job in enumerate(jobs):
            owner = directory / ('job-' + str(index).zfill(3)); owner.mkdir(); (owner / 'work').mkdir()
            (owner / 'native.log').write_text('retained raw'); (owner / 'report.json').write_text('{}')
            good = index != failed
            rows.append(dict(job, resource_feasible=True, numeric_passed=good, numeric={}))
            jobs[index] = dict(job, report_sha256=W.E.sha(owner / 'report.json'), resource_feasible=True, numeric_passed=good)
        complete = count == 55; numeric = complete and all(r['numeric_passed'] for r in rows)
        report = dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-execution.v1', plan_sha256='seal', policy=W.policy(),
            qualified=False, model_qualified=False, qualified_timing=False, limited_pilot_passed=False,
            inputs_runtime_unchanged=True, jobs=jobs, work_wall_seconds=1, wall_seconds=2, work_budget_satisfied=True,
            measurement_packet_completed=complete, resource_feasible=complete, numeric_passed=numeric, passed=complete and numeric)
        W.write(directory / 'report.json', report)
        return directory, plan, rows, report

    def test_raw_complete_required_and_failure_prefix_cannot_continue(self):
        for count, failed in ((54, None), (55, 54), (55, 0)):
            directory, plan, rows, report = self.raw_packet(count, failed)
            with patch.object(R, 'leaf', side_effect=rows), patch.object(R.W.F, 'mathematical_analysis', return_value={'passed': True}) as math:
                if failed == 0:
                    with self.assertRaisesRegex(ValueError, 'continued after'): R.raw_readback(directory, 'seal', directory, plan)
                else:
                    result = R.raw_readback(directory, 'seal', directory, plan)
                    self.assertFalse(result['analysis']['passed']); self.assertFalse(result['numeric_passed']); math.assert_not_called()
        directory, plan, rows, report = self.raw_packet()
        with patch.object(R, 'leaf', side_effect=rows), patch.object(R.W.F, 'mathematical_analysis', return_value={'passed': True}) as math:
            self.assertTrue(R.raw_readback(directory, 'seal', directory, plan)['analysis']['passed'])
            math.assert_called_once_with(plan['original_uniform_plan'], [dict(case=r['case'], mesh=r['mesh'], passed=True, numeric={}) for r in rows])

    def test_raw_reorder_foreign_artifact_or_work_budget_cannot_pass(self):
        for mutation in ('reorder', 'foreign', 'budget'):
            directory, plan, rows, report = self.raw_packet()
            if mutation == 'reorder': report['jobs'][0], report['jobs'][1] = report['jobs'][1], report['jobs'][0]
            elif mutation == 'foreign': (directory / 'foreign.json').write_text('{}')
            else: report['work_wall_seconds'] = 1801; report['wall_seconds'] = 1802
            (directory / 'report.json').write_text(json.dumps(report))
            with patch.object(R, 'leaf', side_effect=rows):
                with self.assertRaises(ValueError): R.raw_readback(directory, 'seal', directory, plan)

    def test_producer_closure_and_failed_authority_rejection(self):
        source = W.sources(); self.assertEqual(len(source), 28)
        for name in W.NEW + ('streaming_8x4_rc_full_policy.py', 'streaming_8x4_rc_incore_readback.py', 'streaming_8x4_acceptance_resources.py'):
            self.assertEqual(source[name], W.E.sha(ROOT / 'scripts' / name))
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'input.json'; path.write_text('{}'); pin = R.bound(path)
            row = dict(new_policy_plan=pin, native_report=pin, command_proposal=pin, runtime_path=temporary,
                resource_cleanup_join={'resource_report': pin}, limited_uniform_finite_wire_pilot_passed=False)
            output = Path(temporary) / 'authority.json'; W.write(output, row)
            with patch.object(R, 'readback', return_value=row):
                with self.assertRaisesRegex(ValueError, 'cannot be promoted'): R.closed_authority(output)

    def test_actual_probe_relocation_keeps_original_path_claims(self):
        owner = W.CAMPAIGN / 'rc-uniform-incore-full-preparation-01'
        intake = W.probe_join(owner)
        self.assertTrue(intake['all_original_bytes_and_path_claims_unchanged'])
        self.assertTrue(intake['probe_is_not_full55_mathematical_authority'])
        self.assertTrue(intake['no_probe_result_reused_as_fresh_measurement'])
        with patch.object(W, 'CAMPAIGN', Path('/foreign-campaign')):
            with self.assertRaisesRegex(ValueError, 'literal command/input/source/cleanup'):
                W.probe_join(owner)

    def test_launch_order_survives_json_roundtrip(self):
        command = dict(container_name='exact', plan_path='/exact/plan.json', plan_sha256='exact', runtime_path='/exact/runtime',
            producer_sha256={'z.py': 'z', 'a.py': 'a'}, argv=['exact'])
        path = Path('/exact/proposal.json')
        self.assertEqual(W.launch_reopen(path, command), W.launch_reopen(path, json.loads(json.dumps(command, sort_keys=True))))


if __name__ == '__main__': unittest.main()
