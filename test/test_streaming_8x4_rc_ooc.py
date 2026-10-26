"""Focused HOST count/projection/ownership/failure controls; no Native."""
import copy
import importlib.util
import json
import math
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
def module(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'scripts'/(name+'.py'));value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
X=module('streaming_8x4_rc_ooc');R=module('streaming_8x4_rc_ooc_readback')
B=ROOT/'build/campaigns/8x4-20261022-01'


def raw_count():
    raw=(B/'rc-native-outputs/rc-full-layered-m1-jacobi-d025-01/job-003/native.log').read_text()
    raw=raw[:raw.index('Error: free space')].replace('(-f): 5','(-f): 1e+12').replace('(-m): 8.6349e-05','(-m): 4.31745e-05').replace("folder: '/tmp'","folder: '/ooc-scratch/count97'")
    return raw+'Error: available free memory is not enough to allocate any chunk\n       Cannot go out-of-core, terminating process\nDone computing links\nTotal time: 1.000000s (0 days, 0 hours, 0 mins, 1 s)\nError: Cannot go Out-of-Core (possibly disk full)!\n'


def snap():return dict(memory_current=1000,memory_peak=2000,memory_max=6442450944,memory_swap_max=0,
    memory_events=dict(max=0,oom=0,oom_kill=0),memory_events_local=dict(max=0,oom=0,oom_kill=0))


class OOCControls(unittest.TestCase):
    def test_exact_count97_expected_branch_rejects_extra_error_mode_or_matrix(self):
        raw=raw_count();self.assertEqual(X.parse_count(raw),dict(panels=47709,links=149944592))
        for bad in (raw+'RuntimeWarning: unexpected\n',raw.replace('(-f): 1e+12','(-f): 5'),raw.replace('/ooc-scratch/count97','/tmp'),
            raw+'Dimension 2 x 2\n',raw.replace('allocate any chunk','allocate chunk'),raw+'Number of links to be computed: 1\n',raw+'Number of panels after refinement: 47709\n'):
            with self.assertRaises(ValueError):X.parse_count(bad)

    def test_count_ratio_and_source_zero_chunk_boundary(self):
        maximum_signed64=2**63-1
        self.assertEqual(int(maximum_signed64/1e12)//X.CHUNK_BYTES,0)
        self.assertEqual(X.I.FIXED[0]['case'],X.CASE);self.assertEqual(X.MESH,'0.0000431745')
        self.assertEqual(X.policy()['maximum_calls'],2);self.assertFalse(X.policy()['count_probe_expected97_is_numerical_success'])
        self.assertFalse(X.policy()['scratch_threshold_is_hard_quota'])
        source=(B/'rc-fastercap-scale-source-intake-03/Autorefine.cpp').read_text()
        self.assertLess(source.index('if(m_ulLinkChunkNum[m_ucInteractionLevel] == 0)'),source.index('// allocate temporary file names'))
        self.assertIn('return FC_CANNOT_GO_OOC',source)

    def test_whole_VM_projection_bounds_all_free_memory_values_and_padding(self):
        count=dict(panels=95418,links=599778368);total=8*1024**3
        row=X.projection(count,total,128*1024**2);self.assertTrue(row['admitted'])
        self.assertEqual(row['possible_nonzero_chunks'],[1,102])
        for c in range(1,103):
            padded=((count['links']+c*X.CHUNK-1)//(c*X.CHUNK))*c*X.CHUNK_BYTES
            self.assertLessEqual(padded,row['maximum_padded_file_bytes'])
        self.assertGreater(row['maximum_padded_file_bytes'],8*1024**3)
        self.assertLess(row['maximum_padded_file_bytes'],16*1024**3)
        self.assertFalse(X.projection(dict(panels=95418,links=2_000_000_000),total,128*1024**2)['admitted'])
        self.assertFalse(X.projection(dict(panels=1_000_000,links=599778368),total,128*1024**2)['admitted'])
        self.assertFalse(X.projection(dict(panels=100,links=1),total,128*1024**2)['admitted'])

    def test_memtotal_actual_bound_rejects_duplicate_or_unbounded(self):
        self.assertEqual(X.memtotal('MemTotal: 8388608 kB\nMemFree: 1 kB\n'),8*1024**3)
        for raw in ('MemTotal: 1 kB\nMemTotal: 1 kB\n','MemFree: 1 kB\n','MemTotal: 16000000000 kB\n'):
            with self.assertRaises(ValueError):X.memtotal(raw)

    def test_exact_scratch_census_cleanup_and_alias_rejection(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);a=root/'frcl1.tmp';a.write_bytes(b'abc');(root/'frcp2.tmp').write_bytes(b'def')
            rows=X.census(root);self.assertEqual(X.scratch_measure(rows)['logical_bytes'],6)
            self.assertFalse(rows[0]['content_hashed']);self.assertEqual(X.scratch_cleanup(root)['after'],[])
            self.assertEqual(list(root.iterdir()),[])
            bad=root/'foreign';bad.write_text('x')
            with self.assertRaises(ValueError):X.census(root)
            bad.unlink();a.symlink_to(root/'absent')
            with self.assertRaises(ValueError):X.census(root)

    def test_environment_and_single_geometry_flags_have_no_hidden_retry(self):
        plan=dict(original_solver_policy=X.W.policy(X.W.PROFILES[0]))
        for stage,flag in [('count97','-f1000000000000'),('solve','-f5')]:
            argv=X.solver_argv(plan,stage)
            self.assertEqual(argv[:-1],X.W.solver_argv(plan['original_solver_policy'],X.MESH));self.assertEqual(argv[-1],flag)
            env=X.environment(stage)
            for name in ('TMPDIR','TMP','TEMP'):self.assertEqual(env[name],'/ooc-scratch/'+stage)
            for name,value in X.W.C.ENVIRONMENT.items():self.assertEqual(env[name],value)
        with self.assertRaises(ValueError):X.solver_argv(plan,'retry')

    def test_cgroup_max_oom_memory_and_scratch_failures_stay_resource_only(self):
        before=snap();after=snap();row=dict(stage='count97',exit_code=97,cgroup_before=before,cgroup_after=after,counter_deltas=X.I.counters(before,after),
            maximum_polled_memory_current=1500,process_tree_reaped=True,timed_out=False,guard_reason=None,
            maximum_scratch_logical_bytes=1000,maximum_scratch_allocated_bytes=4096,minimum_bind_disk_free_bytes=30*1024**3,
            scratch_cleanup=dict(after=[]),inputs_runtime_unchanged=True)
        self.assertTrue(X.resource_pass(row))
        for changed in (dict(timed_out=True),dict(exit_code=-9),dict(exit_code=74),dict(stage='solve'),dict(guard_reason='memory95'),dict(process_tree_reaped=False),
            dict(maximum_scratch_logical_bytes=16*1024**3),dict(minimum_bind_disk_free_bytes=12*1024**3-1)):
            self.assertFalse(X.resource_pass(dict(row,**changed)))
        missing=snap();del missing['memory_events']['max']
        with self.assertRaises(ValueError):R.validate_snapshot(missing)
        wrong=copy.deepcopy(row);wrong['cgroup_after']['memory_events']['oom_kill']=1
        wrong['counter_deltas']=X.I.counters(wrong['cgroup_before'],wrong['cgroup_after']);self.assertFalse(X.resource_pass(wrong))
        with self.assertRaises(ValueError):X.resource_pass(dict(row,maximum_polled_memory_current=2001))
        wrong=copy.deepcopy(row);wrong['cgroup_after']['memory_peak']=1500
        with self.assertRaises(ValueError):X.resource_pass(wrong)
        wrong=copy.deepcopy(row);wrong['cgroup_after']['memory_max']-=1
        with self.assertRaises(ValueError):X.resource_pass(wrong)

    def test_full_two_call_work_budget_is_measured_and_enforced_at_closeout(self):
        for seconds in (269.,271.):
            with tempfile.TemporaryDirectory() as temporary:
                owner=Path(temporary);scratch=owner/'scratch';scratch.mkdir();info=owner/'meminfo'
                info.write_text('MemTotal: 8388608 kB\n');output=owner/'out'
                def path(value):
                    return scratch if value=='/ooc-scratch' else info if value=='/proc/meminfo' else Path(value)
                def leaf(inputs,digest,plan,runtime,stage,target,admission=None):
                    target.mkdir();(target/'report.json').write_text('{}');(target/'meminfo.txt').write_text(info.read_text());(scratch/stage).mkdir()
                    return dict(resource_feasible=True,expected_count97_observed=stage=='count97',scratch_cleanup=dict(before=[]),
                        counts=dict(panels=1,links=100000000),cgroup_after=dict(memory_peak=1000),process_tree_reaped=True,numerical_passed=stage=='solve')
                with patch.object(X,'verify',return_value=dict(runtime={})),patch.object(X.E,'verify_cgroups',return_value={}),\
                    patch.object(X.E,'tree',return_value={}),patch.object(X,'verify_owner'),patch.object(X,'Path',side_effect=path),\
                    patch.object(X,'leaf',side_effect=leaf),patch.object(X,'projection',return_value=dict(admitted=True)),\
                    patch.object(X.time,'monotonic',side_effect=[0.,10.,seconds]):
                    row=X.run(owner,'pin',Path('/solver/runtime'),output)
                self.assertTrue(row['measurement_packet_completed']);self.assertTrue(row['numerical_passed'])
                self.assertIs(row['work_budget_satisfied'],seconds<=270);self.assertIs(row['passed'],seconds<=270)
                self.assertIs(row['resource_feasible'],seconds<=270);self.assertEqual(row['work_wall_seconds'],seconds)

    def test_source_intake_actual_git_blobs_and_nonflushing_log_policy(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner=Path(temporary);X.shutil.copytree(B/'rc-ooc-source-intake-01',owner/'ooc-source')
            self.assertTrue(X.evidence(owner))
            raw=(owner/'ooc-source/FasterCapGlobal.cpp').read_text();section=raw[raw.index('int LogMsg('):]
            self.assertNotIn('std::cout.flush()',section)
            (owner/'ooc-source/wx-filename.cpp').write_text('changed')
            with self.assertRaises(ValueError):X.evidence(owner)

    def test_original_closed_incore_authority_reparses_both_exact_leaves(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner=Path(temporary);prior=owner/'prior';prior.mkdir()
            X.shutil.copytree(B/'rc-incore-preparation-02',prior/'preparation')
            X.shutil.copytree(B/'rc-native-outputs/rc-incore-two-leaf-01',prior/'results')
            X.shutil.copyfile(B/'rc-incore-command-proposal-02.json',prior/'proposal.json')
            X.shutil.copyfile(ROOT/'build/streaming-tt-resources/8x4-rc-incore-two-leaf-01/report.json',prior/'resource.json')
            _,case,_=X.previous(owner);self.assertEqual(case['name'],X.CASE)
            p=prior/'results/job-000/native.log';p.write_text(p.read_text()+'\nWARNING unexpected\n')
            with self.assertRaises(ValueError):X.previous(owner)


if __name__=='__main__':unittest.main()
