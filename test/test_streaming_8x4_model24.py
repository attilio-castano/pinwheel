"""Focused model24 HOST controls. No OpenROAD, solver, Docker or generator runs."""
import ast
import copy
from decimal import Decimal as D
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_model24_contract as K
import streaming_8x4_model24_geometry as G
import streaming_8x4_model24_patterns as W
import streaming_8x4_model24_patterns_readback as R
ITF_FIXTURE='''TECHNOLOGY = sg13cmos5l
DIELECTRIC air { THICKNESS=5.0 ER=1.0 }
DIELECTRIC nitTop { THICKNESS=0.4 ER=6.6 }
DIELECTRIC oxTopMetal1 { THICKNESS=3.5 ER=4.1 }
CONDUCTOR TopMetal1 { THICKNESS=2.0 WMIN=1.64 SMIN=1.64 RPSQ=0.018 }
DIELECTRIC ox4 { THICKNESS=1.34 ER=4.1 }
CONDUCTOR Metal4 { THICKNESS=0.490 WMIN=0.2 SMIN=0.21 RPSQ=0.088 }
DIELECTRIC ox3 { THICKNESS=1.03 ER=4.1 }
CONDUCTOR Metal3 { THICKNESS=0.490 WMIN=0.2 SMIN=0.21 RPSQ=0.088 }
DIELECTRIC ox2 { THICKNESS=1.03 ER=4.1 }
CONDUCTOR Metal2 { THICKNESS=0.490 WMIN=0.2 SMIN=0.21 RPSQ=0.088 }
DIELECTRIC ox1 { THICKNESS=0.960 ER=4.1 }
CONDUCTOR Metal1 { THICKNESS=0.420 WMIN=0.16 SMIN=0.18 RPSQ=0.110 }
DIELECTRIC dummyOx { THICKNESS=0.59 ER=4.1 }
DIELECTRIC nitride { THICKNESS=0.05 ER=6.5 }
DIELECTRIC fox { THICKNESS=0.4 ER=3.95 }
'''


def roles():
    return [dict(ordinal=i,name=n,role='ground' if i==1 else 'signal',matrix_name='g'+str(i)+'_'+n,origin='synthetic explicit test role')
        for i,n in enumerate(['GND_SUB','SIGNAL_A','SIGNAL_B'],1)]


def solver_log():
    names=K.role_names(roles());matrix=[['2e-10','-5e-11','-3e-11'],['-5e-11','2e-10','-4e-11'],['-3e-11','-4e-11','2e-10']]
    return ('Mesh refinement (-m): '+K.MESH+'\nSolution scheme (-g): Galerkin, GMRES tolerance (-t): 0.0005\n'
        'Potential interaction coefficient to mesh refinement ratio (-d): 0.25\n'
        'Precond Type(s) (-p): Jacobi\nOut-of-core free memory to link memory condition (-f): 0\n'
        'Dimension 3 x 3\n'+''.join(n+' '+' '.join(row)+'\n' for n,row in zip(names,matrix))+
        'Total time: 1s (0 days, 0 hours, 0 mins, 1 s)\n')


def pattern_log():
    return ('MODEL24_OPENROAD_VERSION_BEGIN\n'+W.OPENROAD_COMMIT+'\nMODEL24_OPENROAD_VERSION_RETURN <>\nMODEL24_OPENROAD_VERSION_END\n'
        'MODEL24_PATTERN_API_BEGIN\ngen_solver_patterns help\nread_rcx_tables help\nwrite_rcx_model help\n'
        'MODEL24_PATTERN_API_END\nMODEL24_PATTERN_SET 1v2 DONE\nMODEL24_PATTERN_SET 3v2 DONE\nMODEL24_PATTERN_TERMINAL\n')


def cg():
    return dict(memory_current=1000,memory_peak=2000,memory_max=2147483648,memory_swap_max=0,
        memory_events=dict(max=0,oom=0,oom_kill=0),memory_events_local=dict(max=0,oom=0,oom_kill=0))


class Model24Controls(unittest.TestCase):
    def test_valid_full_matrix_conductor_roles_and_single_unit_conversion(self):
        r=K.parse_terminal(solver_log(),roles(),0,False,False)
        self.assertEqual(r['signal_names'],['SIGNAL_A','SIGNAL_B']);self.assertEqual(len(r['numeric']['matrix_F']),3)
        self.assertEqual(D(r['signal_matrix_F'][0][0]),D('2e-10')*D(K.UNIT))
        self.assertEqual(D(r['ground_F'][0]),D('1.6e-10')*D(K.UNIT));self.assertFalse(r['model_qualified'])

    def test_complete_printed_matrix_cannot_mask_timeout_nonzero_or_memory_stop(self):
        for code,timed,memory in [(124,True,False),(1,False,False),(0,True,False),(0,False,True),(-9,False,False)]:
            with self.assertRaisesRegex(ValueError,'no last-iteration fallback'):K.parse_terminal(solver_log(),roles(),code,timed,memory)

    def test_exit_zero_warnings_nonconvergence_truncation_wrong_flags_are_fatal(self):
        raw=solver_log()
        for bad in (raw+'Error: not converging after 1000 iterations\n',raw+'WARNING matrix issue\n',
            raw.replace('(-f): 0','(-f): 5'),raw.replace('(-m): '+K.MESH,'(-m): 1'),
            raw.replace('Dimension 3 x 3','Dimension 2 x 2'),raw.split('Total time:')[0],raw+raw):
            with self.assertRaises(ValueError):K.parse_terminal(bad,roles(),0,False,False)

    def test_role_identity_does_not_classify_by_wire_prefix_or_matrix_position(self):
        r=roles();r[0]['role']='signal'
        with self.assertRaises(ValueError):K.role_names(r)
        r=roles();r[1]['matrix_name']=r[2]['matrix_name']
        with self.assertRaises(ValueError):K.role_names(r)
        r=roles();r.reverse()
        with self.assertRaises(ValueError):K.role_names(r)
        raw=solver_log().replace('g2_SIGNAL_A','g2_FOREIGN')
        with self.assertRaises(ValueError):K.parse_terminal(raw,roles(),0,False,False)

    def test_length_subtraction_rejects_name_shape_and_order_truncation(self):
        first=K.parse_terminal(solver_log(),roles(),0,False,False);second=copy.deepcopy(first)
        second['signal_matrix_F']=[[str(D(x)*2) for x in row] for row in first['signal_matrix_F']]
        result=K.length_difference(first,second,'10','20');self.assertEqual(len(result['matrix_F_per_m']),2)
        for key,value in [('ordered_conductor_roles',list(reversed(second['ordered_conductor_roles']))),
            ('signal_names',list(reversed(second['signal_names']))),('signal_matrix_F',[['1']])]:
            bad=copy.deepcopy(second);bad[key]=value
            with self.assertRaises(ValueError):K.length_difference(first,bad,'10','20')
        with self.assertRaises(ValueError):K.length_difference(first,second,'20','10')

    def test_generation_requires_complete_source_corner_exact_terminal_manifest(self):
        sources={'solver':'a'*64,'geometry':'b'*64};corners={k:dict(label=k,process_sha256='c'*64,consumer_policy_sha256='d'*64) for k in ('MIN','TYP','MAX')}
        rows=[dict(case_id=k,corner=k,source_bindings=sources,corner_binding=corners[k],terminal_passed=True,
            inputs_unchanged=True,role_identity_passed=True,strict_numeric_passed=True,raw_receipt_sha256='e'*64) for k in corners]
        self.assertTrue(K.completion_manifest(list(corners),rows,sources,corners)['complete_declared_membership'])
        for bad in (rows[:-1],list(reversed(rows)),rows+[rows[0]]):
            with self.assertRaises(ValueError):K.completion_manifest(list(corners),bad,sources,corners)
        for key,value in [('terminal_passed',False),('corner','MAX'),('raw_receipt_sha256',''),('source_bindings',{})]:
            bad=copy.deepcopy(rows);bad[0][key]=value
            with self.assertRaises(ValueError):K.completion_manifest(list(corners),bad,sources,corners)

    def test_full_routing_stack_CSG_and_new_heldouts_unmeasured(self):
        text=ITF_FIXTURE
        for recipe in G.recipes():
            row=G.build(text,recipe);self.assertTrue(row['full_stack_explicit']);self.assertTrue(row['same_frozen_CSG_operator'])
            self.assertFalse(row['model_qualified']);self.assertFalse(row['native_pattern_grammar_assumed'])
            self.assertEqual(K.role_names(row['ordered_conductor_roles']),['g1_GND_SUB']+['g'+str(i+2)+'_'+r['name'] for i,r in enumerate(row['case']['rectangles'])])
            self.assertIn('nitTop',[s['name'] for s in row['full_routing_stack']['slabs']]);self.assertEqual(row['full_routing_stack']['outside_er'],'1.0')
            self.assertGreater(row['certificate']['dielectric_faces'],0)
        held=[r for r in G.recipes() if r['role']=='untouched_heldout'];self.assertEqual(len(held),2)
        self.assertNotEqual(held[0]['widths_um'],['.20','.20'])

    def test_corner_aliases_and_missing_corner_bindings_reject_before_assembly(self):
        sources={'solver':'a'*64};corners={k:dict(label=k,process_sha256='b'*64,consumer_policy_sha256='c'*64) for k in ('MIN','TYP','MAX')}
        rows=[dict(case_id='one',corner='MIN',source_bindings=sources,corner_binding=corners['MIN'],
            terminal_passed=True,inputs_unchanged=True,role_identity_passed=True,strict_numeric_passed=True,raw_receipt_sha256='d'*64)]
        for bad in ({'TYP':corners['TYP']},dict(corners,MIN=dict(corners['MIN'],label='MAX'))):
            with self.assertRaises(ValueError):K.completion_manifest(['one'],rows,sources,bad)

    def test_pattern_Tcl_is_exact_two_observation_sets_not_solver_or_model(self):
        text=W.tcl();self.assertEqual(text.count('gen_solver_patterns -'),2)
        self.assertIn(' -wire_cnt 1 -version 2',text);self.assertIn(' -wire_cnt 3 -version 2',text)
        self.assertNotIn('extract_parasitics',text);self.assertNotIn('FasterCap',text)
        self.assertNotIn('write_rcx_model -file',text)
        self.assertTrue(W.parse_terminal(pattern_log(),0,False)['terminal_passed'])
        for bad in (pattern_log().replace('3v2 DONE','1v2 DONE'),pattern_log().replace('MODEL24_PATTERN_TERMINAL',''),pattern_log()+'Error: invalid command\n'):
            with self.assertRaises(ValueError):W.parse_terminal(bad,0,False)
        with self.assertRaises(ValueError):W.parse_terminal(pattern_log(),124,True)

    def test_version_command_may_print_instead_of_return_but_full_commit_required(self):
        text=pattern_log();self.assertEqual(W.parse_terminal(text,0,False)['observed_openroad_commit'],W.OPENROAD_COMMIT)
        for bad in (text.replace(W.OPENROAD_COMMIT,'a'*40),text.replace(W.OPENROAD_COMMIT,''),
            text.replace('MODEL24_OPENROAD_VERSION_RETURN <>','MODEL24_OPENROAD_VERSION_RETURN <'+'a'*40+'>'),
            text.replace('MODEL24_OPENROAD_VERSION_RETURN <>','MODEL24_OPENROAD_VERSION_RETURN <'+'a'*41+'>'),
            text.replace('MODEL24_PATTERN_API_BEGIN','MODEL24_PATTERN_API_BEGIN\nMODEL24_OPENROAD_VERSION_END',1)):
            with self.assertRaises(ValueError):W.parse_terminal(bad,0,False)
        self.assertNotIn('openroad_git_describe',W.tcl())

    def test_pattern_inventory_is_complete_observation_not_grammar_or_physics(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            for group in ('1v2','3v2'):
                owner=root/group/'case';owner.mkdir(parents=True);(owner/'wires').write_text('opaque native pattern data\n')
            (root/'native.log').write_text(pattern_log());result=W.output_inventory(root)
            self.assertEqual(len(result['observed_cases']),2);self.assertFalse(result['expected_physical_case_universe_proven'])
            self.assertFalse(result['actual_native_pattern_grammar_qualified'])
            (root/'3v2/case/wires').unlink()
            with self.assertRaises(ValueError):W.output_inventory(root)
            (root/'3v2/case/wires').symlink_to(root/'1v2/case/wires')
            with self.assertRaises(ValueError):W.output_inventory(root)

    def test_pattern_memory_events_and_exact_resource_flags(self):
        before,after=cg(),cg();row=dict(cgroup_before=before,cgroup_after=after,cgroup_counter_deltas=W.I.counters(before,after),
            maximum_polled_memory_current=1500,exit_code=0,timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,process_tree_reaped=True)
        self.assertTrue(W.resource_observation(row))
        for key in ('timed_out','memory_guard_triggered','output_guard_triggered'):
            bad=copy.deepcopy(row);bad[key]=True;self.assertFalse(W.resource_observation(bad))
        bad=copy.deepcopy(row);bad['cgroup_after']['memory_events']['oom_kill']=1
        bad['cgroup_counter_deltas']=W.I.counters(bad['cgroup_before'],bad['cgroup_after']);self.assertFalse(W.resource_observation(bad))
        bad=copy.deepcopy(row);bad['maximum_polled_memory_current']=3000
        with self.assertRaises(ValueError):W.resource_observation(bad)

    def test_all_eight_original_qualification_gates_remain_false(self):
        requirements=K.qualification_requirements();self.assertEqual(set(requirements['coverage']),W.R24.MODEL_COVERAGE)
        self.assertTrue(all(r['coverage_complete'] is False for r in requirements['coverage'].values()))
        self.assertFalse(requirements['model_qualified']);self.assertTrue(requirements['postroute_census_join_required'])
        self.assertEqual(requirements['consumer_independent_C_error'],'0.10');self.assertEqual(requirements['existing_absolute_R_and_via_gate'],'0.001')


if __name__=='__main__':unittest.main()
