"""Focused HOST controls for the fixed synthetic far-row study; no Native."""
import copy
from decimal import Decimal as D
import hashlib
import inspect
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_rc_cap_far as W
import streaming_8x4_rc_cap_far_geometry as G
import streaming_8x4_rc_cap_far_readback as R


def training():
    return dict(case_id='TYP-w.16-self', names=['W1'], mesh_step_um=.02, extent_um=32,
        plan_sha256=W.C.REFERENCE_HASH, matrix_F_per_m=[[8.505504630513887e-11]])


def table():
    return ('unchanged prefix\nMetal 1 OVER 0\nDIST count 5 width 0.16\n'
        '.18 .000121501 .0000127722 0\n.27 .0000735131 .000015695 0\n'
        '.36 .0000595316 .0000168634 0\n.54 .0000432019 .0000178891 0\n'
        '.9 .0000328544 .0000225122 0\nEND DIST\nunchanged suffix\n')


def synthetic_rows():
    rows=[];targets={}
    for job in G.JOBS:
        groups=[]
        for prefix,case,_,spacing,_ in G.CASES:
            per_m=[[D('8e-11')]] if spacing is None else [[D('18e-11'),D('-12e-11')],[D('-12e-11'),D('18e-11')]]
            targets[case]=dict(matrix_F_per_m=[[str(x) for x in r] for r in per_m],
                ground_F_per_m=[str(sum(r)) for r in per_m])
            for length in (50,100,150):
                names=[r['net'] for r in G.definition(job)['rows'] if r['case']==case and r['length_um']==length]
                matrix=[[str(x*D(length)*D('1e-6')) for x in r] for r in per_m]
                groups.append(dict(names=names,matrix_F=matrix))
        rows.append(dict(job=job,values=dict(groups=groups)))
    return dict(targets=targets),rows


class FarControls(unittest.TestCase):
    def test_only_append_exact_fitted_row_preserving_all_old_bytes(self):
        old=table();expected=old.replace('DIST count 5 width 0.16','DIST count 6 width 0.16').replace(
            'END DIST\n','9 0 0.000042527523152569435 0\nEND DIST\n')
        with patch.object(W.C,'TABLE_HASH',hashlib.sha256(old.encode()).hexdigest()), patch.object(
                W,'CANDIDATE_HASH',hashlib.sha256(expected.encode()).hexdigest()):
            result,witness=W.table_transform(old,training())
            self.assertEqual(result,expected)
            self.assertTrue(witness['all_original_rows_and_other_bytes_unchanged'])
            self.assertTrue(witness['synthetic_zero_coupling_is_not_measured_physics'])
            for key,bad in [('case_id','TYP-w.16-s.18'),('matrix_F_per_m',[[8e-11]]),('mesh_step_um',.04)]:
                row=training();row[key]=bad
                with self.assertRaises(ValueError):W.table_transform(old,row)

    def test_exact_four_eighteen_net_geometry_and_ndr_widths(self):
        for job in G.JOBS:
            row=G.definition(job);got=G.validate(G.fixture(row),row)
            self.assertEqual(len(got['routes']),18);self.assertEqual(len(got['ports']),36)
            self.assertEqual(got['NDR']['Metal1'],dict(width_dbu=320,spacing_dbu=210))
            for wire in row['rows']:
                self.assertEqual(wire['end_DBU'][0]-wire['start_DBU'][0],wire['length_um']*1000)
            self.assertTrue(all(w['NDR']=='WIDE_Metal1' for w in row['rows'] if w['width_DBU']==320))

    def test_ndr_binding_width_net_and_outline_mutations_reject(self):
        row=G.definition(G.JOBS[0]);text=G.fixture(row)
        for bad in (text.replace('WIDTH 320','WIDTH 160'),text.replace('NONDEFAULTRULE WIDE_Metal1','NONDEFAULTRULE foreign',1),
                    text.replace('NETS 18','NETS 17'),text.replace('MICRONS 1000','MICRONS 2000'),
                    text.replace('214000 5696000','214001 5696000'),
                    text.replace('+ ROUTED Metal1','+ ROUTED Metal2',1),
                    text.replace('+ ROUTED Metal1','+ USE CLOCK + ROUTED Metal1',1)):
            with self.assertRaises(ValueError):G.validate(bad,row)

    def test_exact_port_and_wildcard_geometry(self):
        row=G.definition(G.JOBS[0]);text=G.fixture(row)
        # The actual writer's repeated-coordinate wildcard is admitted, without tolerance.
        old='+ ROUTED Metal1 ( 32000 32000 ) ( 82000 32000 )';self.assertIn(old,text)
        self.assertTrue(G.validate(text.replace(old,'+ ROUTED Metal1 ( 32000 32000 ) ( 82000 * )',1),row))
        # The pinned writer emits an explicit SIGNAL use in each net header.
        self.assertTrue(G.validate(text.replace('+ ROUTED Metal1','+ USE SIGNAL + ROUTED Metal1'),row))
        for bad in (text.replace('( -160 -160 )','( -80 -80 )',1),
                    text.replace('+ FIXED ( 32000 32000 ) N','+ FIXED ( 32001 32000 ) N',1),
                    text.replace('self16_L50_W1_A + NET self16_L50_W1','foreign_A + NET self16_L50_W1',1)):
            with self.assertRaises(ValueError):G.validate(bad,row)

    def test_exact_reference_rectangles_and_full_stack_join(self):
        cases=[]
        for _,name,width,spacing,_ in G.CASES:
            w=D(width);centers=[D(0)] if spacing is None else [-(D(spacing)+w)/2,(D(spacing)+w)/2]
            cases.append(dict(name=name,epsilon_layers=[[0,1000,4.1]],rectangles=[
                dict(name='W'+str(i+1),bounds_um=list(map(str,[x-w/2,x+w/2,D('1.04'),D('1.46')]))) for i,x in enumerate(centers)]))
        self.assertTrue(G.physical_join(cases))
        cases[2]['rectangles'][0]['bounds_um'][0]='-.35'
        with self.assertRaises(ValueError):G.physical_join(cases)

    def test_complete_matrix_lengths_and_missing_call_reject(self):
        plan,rows=synthetic_rows();got=W.measurements(plan,rows)
        self.assertTrue(got['measurement_controls_passed']);self.assertTrue(got['candidate_development_gates_passed'])
        self.assertEqual(got['full_accuracy_status'],'unmeasured');self.assertFalse(got['original_BEM_prerequisite_passed'])
        self.assertFalse(got['trained_fit_is_independent_validation'])
        self.assertFalse(any(c['independent_validation'] for c in got['development_reference_comparisons'] if c['role']=='training'))
        with self.assertRaises(ValueError):W.measurements(plan,rows[:-1])
        rows[0]['values']['groups']=rows[0]['values']['groups'][1:]
        with self.assertRaises(ValueError):W.measurements(plan,rows)

    def test_untuned_held_out_offdiagonal_failure_stays_failed(self):
        plan,rows=synthetic_rows()
        for row in rows[2:]:
            for group in row['values']['groups']:
                if group['names'][0].startswith('pair36_'):
                    # Keep diagonals, alter coupling and hence ground by >10%; no waivers.
                    group['matrix_F'][0][1]=str(D(group['matrix_F'][0][1])*D('.8'))
                    group['matrix_F'][1][0]=group['matrix_F'][0][1]
        got=W.measurements(plan,rows)
        self.assertTrue(got['measurement_controls_passed']);self.assertFalse(got['candidate_development_gates_passed'])
        failed=[r for r in got['development_reference_comparisons'] if not r['within_10percent_numerically']]
        self.assertEqual([(r['job'],r['role']) for r in failed],[(j,'held_out_consumer') for j in G.JOBS[2:]])

    def test_spacing_and_length_controls_still_fail(self):
        plan,rows=synthetic_rows()
        for group in rows[3]['values']['groups']:
            group['matrix_F']=[[str(D(v)*D('1.03')) for v in r] for r in group['matrix_F']]
        self.assertFalse(W.measurements(plan,rows)['measurement_controls_passed'])
        plan,rows=synthetic_rows();group=rows[0]['values']['groups'][2]
        group['matrix_F']=[[str(D(v)*D('1.2')) for v in r] for r in group['matrix_F']]
        self.assertFalse(W.measurements(plan,rows)['measurement_controls_passed'])

    def test_worker_control_flow_is_exact_baseline_with_declared_adaptations(self):
        source=inspect.getsource(W.C.run)
        source=source.replace('pinwheel.streaming-8x4-rc-consumer-cap-execution.v1','pinwheel.streaming-8x4-rc-cap-far-execution.v1')
        source=source.replace("for name in ('tech.lef', 'rules.txt', 'run.tcl'):","for name in ('tech.lef', 'run.tcl'):")
        source=source.replace("            shutil.copyfile(base / (job['job'] + '.def'), owner / 'fixture.def')",
            "            shutil.copyfile(base / (job['policy'] + '_rules.txt'), owner / 'rules.txt')\n            shutil.copyfile(base / (job['job'] + '.def'), owner / 'fixture.def')")
        source=source.replace('measurements(leaves)','measurements(plan, leaves)').replace(
            "report['analysis']['measurement_controls_passed']","report['analysis']['candidate_development_gates_passed']")
        self.assertEqual(inspect.getsource(W.run),source)
        self.assertIn("analysis['candidate_development_gates_passed']",inspect.getsource(R.raw_readback))

    def test_exact_campaign_shared_lock_wrapper_and_guard_required(self):
        row=dict(supervisor_sha256=W.P.sha(R.ROOT/'scripts/streaming_tt_resources.py'),campaign_boundary=dict(
            schema='pinwheel.streaming-8x4-resource-boundary.v1',campaign_root=str(R.ROOT),campaign_kind='rc_experiment',
            shared_lease=dict(heavy_lock=str(R.ROOT/'build/streaming-tt-resources/heavy.lock'),
                cleanup_sentinel=str(R.ROOT/'build/streaming-tt-resources/cleanup-unconfirmed.json')),
            wrapper_sha256=W.P.sha(R.ROOT/'scripts/streaming_8x4_acceptance_resources.py'),
            inherited_supervisor_sha256=W.P.sha(R.ROOT/'scripts/streaming_tt_resources.py')))
        self.assertEqual(R.campaign_boundary(row),row['campaign_boundary'])
        for key in ('schema','campaign_root','campaign_kind','wrapper_sha256','inherited_supervisor_sha256'):
            bad=copy.deepcopy(row);bad['campaign_boundary'][key]='wrong'
            with self.assertRaises(ValueError):R.campaign_boundary(bad)
        for key in ('heavy_lock','cleanup_sentinel'):
            bad=copy.deepcopy(row);bad['campaign_boundary']['shared_lease'][key]='wrong'
            with self.assertRaises(ValueError):R.campaign_boundary(bad)
        bad=copy.deepcopy(row);bad['supervisor_sha256']='wrong'
        with self.assertRaises(ValueError):R.campaign_boundary(bad)


if __name__=='__main__':unittest.main()
