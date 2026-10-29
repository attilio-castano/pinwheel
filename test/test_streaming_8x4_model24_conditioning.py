"""Portable fixed-factorial HOST controls, no CAD/solver/retained-file reads."""
import copy
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'));sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_conditioning as W
import streaming_8x4_model24_conditioning_readback as R
from test_streaming_8x4_model24 import solver_log,roles

class ConditioningControls(unittest.TestCase):
    def raw(self,b):return solver_log().replace('(-t): 0.0005','(-t): '+b['gmres_tolerance']).replace('(-d): 0.25','(-d): '+b['interaction_ratio'])
    def jobs(self):return [dict(index=c*4+b,case=c,branch=r,numeric_passed=b in (1,3),resource_feasible=True) for c in range(2) for b,r in enumerate(W.Q.branches())]
    def test_exact_fixed_factorial_argv_and_same_physics(self):
        self.assertEqual(len(W.Q.branches()),4)
        for b in W.Q.branches():
            row=W.Q.parse(self.raw(b),roles(),b,0,False,False);self.assertTrue(row['complete_full_matrix_checked']);self.assertFalse(row['model_qualified'])
            self.assertEqual(W.Q.argv(b)[4],'-m'+W.K.MESH);self.assertEqual(W.Q.argv(b)[-1],'-f0')
        with self.assertRaises(ValueError):W.Q.argv(dict(W.Q.branches()[0],gmres_tolerance='.1'))
    def test_warning_exit_bad_residual_interaction_wrong_name_and_f0_fatal(self):
        b=W.Q.branches()[1];raw=self.raw(b)
        for bad in (raw+'Error: not converging after1000\n',raw.replace('0.000001','0.0005'),raw.replace('(-d): 0.25','(-d): 0.125'),raw.replace('g2_SIGNAL_A','g2_OTHER'),raw.replace('(-f): 0','(-f): 5'),raw+raw):
            with self.assertRaises(ValueError):W.Q.parse(bad,roles(),b,0,False,False)
        for exit,timeout,memory in [(1,False,False),(0,True,False),(0,False,True)]:
            with self.assertRaises(ValueError):W.Q.parse(raw,roles(),b,exit,timeout,memory)
    def test_unweakened_reciprocity_and_unordered_excitation_reject(self):
        b=W.Q.branches()[0];raw=self.raw(b)
        with self.assertRaises(ValueError):W.Q.parse(raw.replace('-5e-11','-8e-11',1),roles(),b,0,False,False)
        with self.assertRaises(ValueError):W.Q.parse(raw+'GMRES Iteration: 0 2\n',roles(),b,0,False,False)
    def test_complete_both_geometry_membership_no_successful_subset(self):
        jobs=self.jobs();a=W.Q.aggregate(jobs);self.assertEqual([p['both_geometries_passed'] for p in a],[False,True,False,True])
        for bad in (jobs[:-1],jobs+[jobs[0]],list(reversed(jobs)),jobs[:4]*2):
            with self.assertRaises(ValueError):W.Q.aggregate(bad)
        jobs[5]['numeric_passed']=False;self.assertFalse(W.Q.aggregate(jobs)[1]['both_geometries_passed'])
    def test_observed_work_overrun_cannot_pass_both_profiles(self):
        leaves=self.jobs();profiles=W.Q.aggregate(leaves)
        for duration in (539.9,540.001):
            row=dict(actual_work_seconds=duration,work_budget_passed=duration<=540,measurement_packet_completed=True,all_numeric_passed=False,resource_feasible=duration<=540,profile_results=profiles,passed=duration<=540)
            self.assertIs(R.work_state(row,leaves)[3],duration<=540)
            if duration>540:
                with self.assertRaises(ValueError):R.work_state(dict(row,passed=True),leaves)
        with self.assertRaises(ValueError):R.work_state(dict(row,measurement_packet_completed=True),leaves[:-1])
    def test_aggregate_diagnostic_preserves_baseline_failures(self):
        p=W.policy();self.assertEqual(p['leaf_seconds'],60);self.assertEqual(p['maximum_calls'],8);self.assertFalse(p['model_qualified'])
        self.assertEqual(self.jobs()[0]['numeric_passed'],False);self.assertEqual(self.jobs()[4]['numeric_passed'],False)
        jobs=self.jobs()
        for j in jobs:j['numeric_passed']=False
        self.assertTrue(all(not p['both_geometries_passed'] for p in W.Q.aggregate(jobs)))
    def test_missing_parent_failed_smoke_does_not_admit(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'launcher.json';p.write_text('{}')
            with self.assertRaises(ValueError):W.parent_smoke(p)

if __name__=='__main__':unittest.main()
