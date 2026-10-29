"""Fixed -f0/memory/OOM/custody HOST controls; no Native executable runs."""
import copy
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
def module(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'scripts'/(name+'.py'))
    row=importlib.util.module_from_spec(spec);spec.loader.exec_module(row);return row
W=module('streaming_8x4_rc_incore');R=module('streaming_8x4_rc_incore_readback')
GOOD=(ROOT/'test/fixtures/streaming-8x4-rc-wire-coarse-20261022.log').read_text()


class IncoreControls(unittest.TestCase):
    def snapshot(self):
        return {'memory_current':1024,'memory_peak':2048,'memory_max':6442450944,'memory_swap_max':0,
            'memory_events':{'low':0,'high':0,'max':0,'oom':0,'oom_kill':0},
            'memory_events_local':{'low':0,'high':0,'max':0,'oom':0,'oom_kill':0}}

    def test_only_two_exact_failed_points_and_source_memory_admission(self):
        self.assertEqual([(r['case'],r['mesh']) for r in W.FIXED],
            [('TYP-w.16-self-L10-E20','0.000086349'),('historical_U_new_manual','0.0000431745')])
        self.assertEqual([W.estimate(f)['planning_total_bytes'] for f in W.FIXED],[5179799696,5152309056])
        self.assertTrue(all(W.estimate(f)['admission'] for f in W.FIXED))
        self.assertEqual(W.policy()['outer_seconds'],330);self.assertEqual(W.policy()['seconds_per_leaf'],120)
        self.assertEqual(W.policy()['only_solver_delta'],['-f0']);self.assertFalse(W.policy()['model_qualified'])

    def test_actual_mode_header_required_once_and_five_is_not_zero(self):
        zero=GOOD.replace('condition (-f): 5','condition (-f): 0')
        self.assertTrue(W.mode_observed(zero))
        for raw in (GOOD,zero+'\nOut-of-core free memory to link memory condition (-f): 0\n',
                    zero.replace('condition (-f): 0','condition (-f): nan'),zero+'\nGoing out-of-core\n'):
            self.assertFalse(W.mode_observed(raw))
        old={'policy':W.W.policy(W.W.PROFILES[0])};case={'matrix_names':['g1_GND_SUB','g2_SIGNAL'],'coordinate_unit_m':'0.00000095367431640625'}
        raw=zero.replace('(-d): 1','(-d): 0.25').replace('Mesh refinement (-m): 0.000383703','Mesh refinement (-m): 0.000086349')
        with patch.object(W,'original',return_value=(old,case)):
            self.assertFalse(W.parse(raw,Path('/unused'),0)['model_qualified'])
            with self.assertRaises(ValueError):W.parse(raw+'\nWarning: physics failure\n',Path('/unused'),0)

    def test_events_distinguish_oom_from_unknown_sigkill_and_guard(self):
        before=self.snapshot();after=copy.deepcopy(before)
        row={'cgroup_before':before,'cgroup_after':after,'exit_code':0,'timed_out':False,
             'memory_guard_triggered':False,'actual_f0_observed':True}
        self.assertTrue(W.resource_feasible(row))
        for changed in ({'exit_code':-9},{'timed_out':True},{'memory_guard_triggered':True},{'actual_f0_observed':False}):
            self.assertFalse(W.resource_feasible(dict(row,**changed)))
        after['memory_events']['oom_kill']=1
        self.assertEqual(W.counters(before,after)['memory_events']['oom_kill'],1);self.assertFalse(W.resource_feasible(row))
        after['memory_events']['oom_kill']=0;after['memory_peak']=6442450944*95//100
        self.assertFalse(W.resource_feasible(row))
        after['memory_peak']=2048;after['memory_events_local']['max']=1
        self.assertFalse(W.resource_feasible(row))
        after['memory_events_local']['max']=-1
        with self.assertRaises(ValueError):W.counters(before,after)
        missing=copy.deepcopy(before);del missing['memory_events']['max']
        with self.assertRaises(ValueError):W.counters(missing,missing)

    def test_polled_current_cannot_exceed_kernel_peak_or_claim_guard_fit(self):
        row={'cgroup_before':self.snapshot(),'cgroup_after':self.snapshot(),'maximum_polled_memory_current':1500,'resource_feasible':True}
        R.validate_poll_peak(row)
        for value in (1023,2049):
            with self.assertRaises(ValueError):R.validate_poll_peak(dict(row,maximum_polled_memory_current=value))
        row['cgroup_after']['memory_peak']=6442450944;row['maximum_polled_memory_current']=6442450944
        with self.assertRaises(ValueError):R.validate_poll_peak(row)

    def test_guard_preserves_exact_95percent_and_120second_limits(self):
        limit=6442450944;threshold=limit*95//100
        self.assertIsNone(W.guard_reason(threshold-1,limit,119.9))
        self.assertEqual(W.guard_reason(threshold,limit,0),'memory')
        self.assertEqual(W.guard_reason(0,limit,120),'timeout')

    def test_cgroup_snapshot_keeps_actual_peak_and_all_event_counters(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            for n in W.policy()['capture']:
                value='oom 0\noom_kill 0\nmax 0\n' if n in ('memory.events','memory.events.local') else str({'memory.max':6442450944,'memory.swap.max':0,'memory.current':1024,'memory.peak':4096}[n])
                (root/n).write_text(value)
            row=W.cgroup_snapshot(root);self.assertEqual(row['memory_peak'],4096);self.assertEqual(row['memory_events']['oom_kill'],0)
            (root/'memory.events.local').write_text('oom 0\noom_kill 0\n')
            with self.assertRaises(ValueError):W.cgroup_snapshot(root)
            (root/'memory.events.local').write_text('oom 0\noom_kill 0\nmax 0\n')
            (root/'memory.swap.max').write_text('1')
            with self.assertRaises(ValueError):W.cgroup_snapshot(root)

    def test_closed_numeric_failure_can_continue_but_resource_failure_stops_suffix(self):
        for resource_ok in (True,False):
            with tempfile.TemporaryDirectory() as temporary:
                output=Path(temporary)/W.OUTPUT;plan={'runtime':{}};calls=[]
                def leaf(inputs,digest,prepared,index,runtime,owner):
                    calls.append(index);owner.mkdir();row={'exit_code':0,'solver_executed':True,'process_tree_reaped':True,
                        'copied_inputs_unchanged':True,'source_runtime_unchanged':True,'producer_plan_unchanged':True,
                        'resource_feasible':resource_ok,'numeric_passed':False}
                    W.W.write(owner/'report.json',row);return row
                with patch.object(W,'verify',return_value=plan),patch.object(W.E,'tree',return_value={}),patch.object(W,'leaf',side_effect=leaf):
                    row=W.run(Path(temporary),'seal',Path('/solver/runtime'),output)
                self.assertEqual(calls,[0,1] if resource_ok else [0]);self.assertIs(row['measurement_packet_completed'],resource_ok)
                self.assertIs(row['resource_feasible'],resource_ok);self.assertFalse(row['numeric_passed']);self.assertFalse(row['passed'])


if __name__=='__main__':unittest.main()
