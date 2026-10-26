"""Portable HOST controls for observed native grammar and six-conductor probes."""
import copy
from decimal import Decimal as D
import inspect
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path[:0]=[str(ROOT/'scripts'),str(ROOT/'test')]
import streaming_8x4_model24_native_geometry as G
import streaming_8x4_model24_smoke as W
import streaming_8x4_model24_smoke_readback as R
from test_streaming_8x4_model24 import ITF_FIXTURE


def native_diagonal(far=False):
    path=G.REPRESENTATIVES[1 if far else 0];spacing=D('.42' if far else '.21');offset=D('6.56' if far else '0')
    distance=D('.2')+spacing;left=-distance;right=distance;span=D('.2')+2*distance
    text='PATTERN '+'/'.join(Path(path).parts[1:-1])+'\nGROUND_PLANE 0 M0_w0 HEIGHT -0.1 0 THICKNESS 0.1\n'
    text+='DIELECTRIC p1_1 HEIGHT 0 .4 EPSILON 3.95\nDIELECTRIC nitTop HEIGHT 8.9 9.3 EPSILON 6.6\n'
    for index,x,voltage in [(1,left,0),(2,D(0),1),(3,right,0)]:
        text+=f'WIRE {index} M4_w{index} LL {x} 4.06 LR {x+D(".2")} 4.06 UR {x+D(".2")} 4.55 UL {x} 4.55 LENGTH 2 VOLTAGE {voltage}\n'
    for index,x in [(4,offset),(5,offset+D('3.28'))]:
        text+=f'WIRE {index} M5_w{index} LL {x} 5.4 LR {x+D("1.64")} 5.4 UR {x+D("1.64")} 7.4 UL {x} 7.4 LENGTH 2 VOLTAGE 0\n'
    text+=f'WINDOW_BBOX LL {left} 0 UR {right+D(".2")} 14.3 LENGTH 2\nSIM_WIN_EXT LL {-span} 0 UR {span} 0 LENGTH 0 2\n'
    return path,text


def native_overunder():
    path='1v2/MODEL24_TYP/OverUnder1/M4oM2uM5/W0.2_W0.2/S0.21_S0.21_L10/wires'
    return path,('PATTERN '+'/'.join(Path(path).parts[1:-1])+'\n'
        'GROUND_PLANE 2 M2_w2 HEIGHT -.49 0 THICKNESS .49\nGROUND_PLANE 5 M5_w5 HEIGHT 2.91 4.91 THICKNESS 2\n'
        'DIELECTRIC m3_1 HEIGHT 0 .54 EPSILON 4.1\nDIELECTRIC m4_2 HEIGHT 1.57 2.06 EPSILON 4.1\n'
        'WIRE 1 M4_w1 LL 0 1.57 LR .2 1.57 UR .2 2.06 UL 0 2.06 LENGTH 2 VOLTAGE 1\n'
        'WINDOW_BBOX LL -.41 0 UR .61 5.4 LENGTH 2\nSIM_WIN_EXT LL -1.02 0 UR 1.02 0 LENGTH 0 2\n')


class Model24SmokeControls(unittest.TestCase):
    def test_explicit_six_conductor_names_targets_and_global_full_stack(self):
        for far in (False,True):
            path,text=native_diagonal(far);row=G.normalize(text,path,ITF_FIXTURE)
            self.assertEqual(len(row['physical_records']),6);self.assertEqual(row['local_to_global_y_offset_um'],'0')
            actual=G.build(text,path,ITF_FIXTURE);self.assertEqual(len(actual['ordered_conductor_roles']),6)
            self.assertEqual(actual['certificate']['all_faces'],65);self.assertEqual(actual['certificate']['dielectric_faces'],29)
            self.assertTrue(actual['no_native_conductor_omitted_or_added']);self.assertFalse(actual['model_qualified'])

    def test_local_ground_translation_is_bound_to_every_wire_plane_and_dielectric(self):
        path,text=native_overunder();row=G.normalize(text,path,ITF_FIXTURE)
        self.assertEqual(D(row['local_to_global_y_offset_um']),D('2.49'))
        self.assertEqual(list(map(D,[row['physical_records'][2]['global_bottom_um'],row['physical_records'][2]['global_top_um']])),[D('4.06'),D('4.55')])
        built=G.build(text,path,ITF_FIXTURE);self.assertEqual(len(built['ordered_conductor_roles']),3)
        self.assertTrue(built['certificate']['internal_anchor_rename_is_bijective_and_not_a_new_substrate'])
        self.assertNotIn('GND_SUB',built['certificate']['conductors'])
        with self.assertRaises(ValueError):G.normalize(text.replace('LR .2 1.57','LR .2 1.58'),path,ITF_FIXTURE)

    def test_native_material_thickness_target_and_path_mutations_reject(self):
        path,text=native_diagonal()
        bad_values=[text.replace('EPSILON 6.6','EPSILON 4.1'),text.replace('5.4','5.5'),
            text.replace('VOLTAGE 1','VOLTAGE 0'),text.replace('M4_w1','M4_w2'),
            text.replace('SIM_WIN_EXT LL -1.02','SIM_WIN_EXT LL -1.03'),text+'UNKNOWN 0\n']
        for bad in bad_values:
            with self.assertRaises(ValueError):G.normalize(bad,path,ITF_FIXTURE)
        for bad_path in (path.replace('M4duM5','M3duM5'),path.replace('W0.2_W1.64','W0.3_W1.64'),
                         path.replace('S0.21_S0','S0.42_S0'),path.replace('3v2','1v2')):
            with self.assertRaises(ValueError):G.parse(text.replace('PATTERN '+'/'.join(Path(path).parts[1:-1]),'PATTERN '+'/'.join(Path(bad_path).parts[1:-1])),bad_path)

    def test_zero_voltage_neighbor_wire_remains_independent_matrix_signal(self):
        path,text=native_diagonal();row=G.build(text,path,ITF_FIXTURE);roles=row['ordered_conductor_roles']
        self.assertEqual(sum(r['role']=='ground' for r in roles),1);self.assertEqual(sum(r['role']=='signal' for r in roles),5)
        self.assertEqual(sum('voltage1' in r['origin'] for r in roles),1)
        self.assertTrue(all('native' in r['origin'] for r in roles))

    def test_two_fixed_cost_calls_do_not_claim_a_numerical_universe(self):
        p=W.policy();self.assertEqual(p['maximum_calls'],2);self.assertEqual(p['work_seconds'],270);self.assertEqual(p['outer_seconds'],330)
        self.assertEqual(p['native_case_paths'],G.REPRESENTATIVES);self.assertEqual(p['manual_mesh'],W.K.MESH)
        self.assertFalse(p['model_qualified']);self.assertTrue(p['smoke_is_not_mesh_length_boundary_or_independent_accuracy_qualification'])
        self.assertEqual(W.K.solver_argv()[-3:],['-t0.0005','-d0.25','-f0'])

    def test_packet_no_prefix_promotion_and_actual_work_overrun(self):
        plan=dict(cases=[dict(native_path=n) for n in G.REPRESENTATIVES],runtime={})
        for elapsed in (269.9,270.001):
            with tempfile.TemporaryDirectory() as temp:
                base=Path(temp)
                def leaf(inputs,digest,plan,index,runtime,owner):
                    owner.mkdir();(owner/'report.json').write_text('{}')
                    return dict(numeric_passed=True,resource_feasible=True,process_tree_reaped=True,
                        copied_inputs_unchanged=True,inputs_sources_unchanged=True,runtime_unchanged=True)
                with patch.object(W,'verify',return_value=plan),patch.object(W.E,'tree',return_value={}),patch.object(W,'leaf',side_effect=leaf),patch.object(W.time,'monotonic',side_effect=[0.,1.,1.,elapsed]):
                    row=W.run(base,'pin',Path('/solver/runtime'),base/W.OUTPUT)
                self.assertTrue(row['measurement_packet_completed']);self.assertTrue(row['all_numeric_passed']);self.assertIs(row['passed'],elapsed<=270)
                leaves=[dict(numeric_passed=True,resource_feasible=True)]*2
                self.assertEqual(R.work_state(row,leaves),(True,True,elapsed<=270))
                bad=dict(row,work_budget_passed=True)
                if elapsed>270:
                    with self.assertRaises(ValueError):R.work_state(bad,leaves)

    def test_missing_closed_pattern_intake_never_admits_smoke(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'launcher';p.write_text('{}')
            with self.assertRaises(ValueError):W.parent_pattern(p)
        self.assertIn('resource_cleanup_join',inspect.getsource(R.readback));self.assertIn('parent_pattern',inspect.getsource(R.readback))


if __name__=='__main__':unittest.main()
