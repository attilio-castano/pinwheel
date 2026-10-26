"""Portable six-set grammar controls. No ignored recovery, Native or solver."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_model24_process_patterns as W
import streaming_8x4_model24_process_patterns_readback as R


def raw():
    return ('MODEL24_ITF_VERSION_BEGIN\nOpenROAD '+W.S.N.OPENROAD_COMMIT+'\nMODEL24_ITF_VERSION_END\nMODEL24_ITF_API_BEGIN\nMODEL24_ITF_API_END\n'+
        ''.join('MODEL24_ITF_SET '+c+' '+s+' DONE\n' for c in W.U.CORNERS for s in ('1v2','3v2'))+'MODEL24_ITF_TERMINAL\n')

class ProcessPatternControls(unittest.TestCase):
    def test_fixed_six_sets_and_exact_corner_policy_paths(self):
        row=W.parse_terminal(raw(),0,False);self.assertEqual(len(row['sets']),6);self.assertFalse(row['model_qualified'])
        command=W.tcl();self.assertEqual(command.count('gen_solver_patterns -process_file'),6)
        for c in W.U.CORNERS:self.assertIn('/owned-itf/'+c+'.process -process_name '+c,command)
        self.assertNotIn('FasterCap',command);self.assertNotIn('width_delta',command)
    def test_missing_reordered_foreign_correct40_plus41_and_exitzero_warning_reject(self):
        first='MODEL24_ITF_SET ITF_MIN 1v2 DONE';second='MODEL24_ITF_SET ITF_MIN 3v2 DONE'
        for bad in (raw().replace(first,''),raw().replace(first,'x').replace(second,first).replace('x',second),raw().replace('ITF_MAX','MAX'),raw().replace('MODEL24_ITF_VERSION_END','f'*41+'\nMODEL24_ITF_VERSION_END'),raw()+'WARNING wrong process\n'):
            with self.assertRaises(ValueError):W.parse_terminal(bad,0,False)
        for code,timeout in [(1,False),(0,True)]:
            with self.assertRaises(ValueError):W.parse_terminal(raw(),code,timeout)
    def test_observation_scope_and_whole_work_clock(self):
        p=W.policy();self.assertEqual((p['generator_calls'],p['leaf_seconds'],p['outer_seconds']),(6,60,120));self.assertTrue(p['no_calibration']);self.assertFalse(p['model_qualified'])
        self.assertTrue(R.work(dict(actual_work_seconds=90,work_budget_passed=True)))
        self.assertFalse(R.work(dict(actual_work_seconds=90.1,work_budget_passed=False)))
        for s,flag in [(90.1,True),(-1,True),(float('nan'),False)]:
            with self.assertRaises(ValueError):R.work(dict(actual_work_seconds=s,work_budget_passed=flag))
    def test_exact_six_set_case_transform_does_not_rewrite_material_coordinates(self):
        import tempfile,json
        rows=[dict(path='1v2/MODEL24_TYP/Over1/M1oM0/W.16_W.16/S.18_S.18_L10/wires') for _ in range(310)]
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'pattern-authority.json').write_text(json.dumps(dict(pattern_intake_completed=True,model_qualified=False,inventory=dict(observed_cases=rows))))
            with self.assertRaises(ValueError):W.expected_cases(root)
        self.assertEqual(W.PROCESS_MANIFEST,'bde97789d062746d40372f146b535ac6f14b88238ff30754c6f6f1eedf3b70f4')

if __name__=='__main__':unittest.main()
