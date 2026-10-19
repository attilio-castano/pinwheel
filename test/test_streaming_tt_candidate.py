"""Refusal of false optimized admissions and absent nominal wire RC."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_candidate as C


class CandidateTests(unittest.TestCase):
    def test_parent_pending_replay_is_not_a_physical_or_final_proof_flag(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'parent.json'
            value=dict(schema='pinwheel.streaming-tt-optimized-intake.v1',passed=True,purpose='bounded_physical_measurement',
                qualified=False,physical_acceptance_claim=False,checked={key:True for key in C.CHECKED})
            for mode in ['missing_check','proof_source','sv_reimport','parent_failed','wrong_purpose','physical_claim','qualified','wrong_schema']:
                changed=deepcopy(value)
                if mode=='missing_check':changed['checked']['archive_membership']=False
                elif mode=='proof_source':changed['checked']['independent_proof_source_regeneration']=False
                elif mode=='sv_reimport':changed['checked']['physical_sv_reimport']=False
                elif mode=='parent_failed':changed['passed']=False
                elif mode=='wrong_purpose':changed['purpose']='final_signoff'
                elif mode=='physical_claim':changed['physical_acceptance_claim']=True
                elif mode=='qualified':changed['qualified']=True
                else:changed['schema']='other'
                path.write_text(json.dumps(changed))
                with self.subTest(mode=mode),self.assertRaisesRegex(ValueError,'Parent has not admitted'):
                    C.optimized_candidate(path,hashlib.sha256(path.read_bytes()).hexdigest())

    def test_admission_hash_checked_before_any_consumption(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'parent.json';path.write_text('{}')
            with self.assertRaisesRegex(ValueError,'before use'): C.optimized_candidate(path,'0'*64)

    def test_final_component_symlink_is_refused_before_resolution(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);target=root/'actual.json';target.write_text('{}')
            alias=root/'alias.json';alias.symlink_to(target)
            expected=hashlib.sha256(target.read_bytes()).hexdigest()
            with self.assertRaisesRegex(ValueError,'aliased'):C.bound(dict(path=str(alias),sha256=expected))
            with self.assertRaisesRegex(ValueError,'aliased'):C.optimized_candidate(alias,expected)

    def test_candidate_recipe_keeps_tie_repair_and_explicit_positive_wire_rc(self):
        value=json.loads((ROOT/'physical/streaming-tt-candidate.json').read_text())
        self.assertNotIn('DESIGN_REPAIR_TIE_FANOUT',value) # pinned default remains enabled
        self.assertEqual(value['RT_MAX_LAYER'],'Metal4')
        self.assertEqual(set(value['LAYERS_RC']),{'nom_*'})
        self.assertEqual(set(value['LAYERS_RC']['nom_*']),{'Metal1','Metal2','Metal3','Metal4','TopMetal1'})
        for layer in value['LAYERS_RC']['nom_*'].values():
            self.assertGreater(layer['res'],0);self.assertGreater(layer['cap'],0)
        self.assertEqual(value['CLOCK_PERIOD'],20)
        self.assertEqual(value['PL_RESIZER_HOLD_SLACK_MARGIN'],0.02)

    def test_controlled_recipe_changes_only_native_clustering_and_repair_settings(self):
        value=json.loads((ROOT/'physical/streaming-tt-candidate.json').read_text())
        result=C.recipe_experiment(value)
        self.assertEqual(set(result['changes']),set(C.RECIPE_CHANGES))
        self.assertEqual(result['changes']['CTS_SINK_CLUSTERING_SIZE']['after'],8)
        self.assertEqual(result['cts_trial']['changes'],{'CTS_SINK_CLUSTERING_SIZE':{'before':None,'after':8}})
        self.assertEqual(result['cts_trial']['required_resolved_settings'],
            {'CTS_SINK_CLUSTERING_ENABLE':True,'CTS_SINK_CLUSTERING_SIZE':8})
        self.assertFalse(result['cts_trial']['native_measured'])
        self.assertFalse(result['cts_trial']['clock_fanout_closed'])
        self.assertEqual(result['changes']['CTS_APPLY_NDR']['resolved_before'],'half')
        self.assertEqual(result['changes']['CTS_APPLY_NDR']['after'],'none')
        self.assertEqual(result['changes']['RUN_POST_GRT_DESIGN_REPAIR']['resolved_before'],False)
        self.assertEqual(result['changes']['RUN_POST_GRT_RESIZER_TIMING']['resolved_before'],False)
        self.assertFalse(result['changes']['RUN_POST_GRT_RESIZER_TIMING']['after'])
        self.assertEqual(result['changes']['GRT_RESIZER_HOLD_SLACK_MARGIN']['after'],0.02)
        for key,changed in [('CLOCK_PERIOD',25),('RT_MAX_LAYER','TopMetal1'),
                ('PL_RESIZER_HOLD_SLACK_MARGIN',0),('RUN_POST_GRT_RESIZER_TIMING',True),
                ('CTS_SINK_CLUSTERING_SIZE',20),('CTS_SINK_CLUSTERING_SIZE',None),('CTS_SINK_CLUSTERING_SIZE',8.0),
                ('CTS_SINK_CLUSTERING_ENABLE',False),('CTS_APPLY_NDR','half')]:
            altered=deepcopy(value);altered[key]=changed
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'five settings'):
                C.recipe_experiment(altered)

    def test_resolved_size_and_actual_command_both_required_not_search_summary(self):
        resolved=dict(CTS_SINK_CLUSTERING_ENABLE=True,CTS_SINK_CLUSTERING_SIZE=8)
        command='+ clock_tree_synthesis -buf_list buf8 -sink_clustering_enable -sink_clustering_size 8\n'
        result=C.validate_cts_trial(resolved,command)
        self.assertTrue(result['resolved_and_logged_cts_trial'])
        self.assertFalse(result['actual_clock_loads_validated'])
        for changed,log in [(dict(resolved,CTS_SINK_CLUSTERING_SIZE=None),command),
                (dict(resolved,CTS_SINK_CLUSTERING_SIZE=8.0),command),
                (dict(resolved,CTS_SINK_CLUSTERING_ENABLE=False),command),
                (resolved,command.replace(' -sink_clustering_size 8','')+'Best clustering solution size8\n'),
                (resolved,command.replace('size 8','size 20')),
                (resolved,command+command),
                (resolved,command.rstrip()+' -sink_clustering_size 20\n')]:
            with self.subTest(log=log),self.assertRaises(ValueError):C.validate_cts_trial(changed,log)


if __name__ == '__main__':unittest.main()
