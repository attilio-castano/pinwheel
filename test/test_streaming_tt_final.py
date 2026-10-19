"""Exact native ordering, checkpoint view binding and final admission refusals."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock,patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_final as F
from streaming_tt_intake import dependency_closure


class FinalTests(unittest.TestCase):
    def test_exact_replay_count_uses_complete_bound_parent_sources_and_strict_intake(self):
        import streaming_tt_replay_inventory as V
        profile='pinwheel.streaming-tt-exact-parent-replay.v1'
        for mutation in (None,'caller-count','parent-map','parent-dict','parent-plan','duplicate','missing-stage',
                         'regenerated-prefix','missing-intake','intake-count','source','empty-inputs','changed-input','unknown-profile'):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as temporary:
                root=Path(temporary).resolve();worker=root/'worker';worker.mkdir();parent_path=root/'parent.json'
                rows=[]
                for stage,module in zip(('frontend-proof','core-d2-proof','device-proof'),('Frontend','Core','Device')):
                    p=worker/stage/(module+'.lean');p.parent.mkdir();p.write_text('actual closed generated source')
                    rows.append(dict(module=module,path=str(p),sha256=F.P.sha(p)))
                def bound(path):return dict(path=str(path),sha256=F.P.sha(path))
                def write(path,data):F.P.write(path,data);return bound(path)
                worker_ref=write(worker/'report.json',{'passed':True})
                parent=dict(source_commit='a'*40,generated_module_count=3,
                    generated_sources_sha256={r['path']:r['sha256'] for r in rows},worker_report=worker_ref)
                parent_binding=write(parent_path,parent);plan_path=root/'native-replay-plan.json'
                write(plan_path,dict(source_commit='a'*40,modules=rows))
                extra=root/'validator-input';extra.write_text('frozen producer')
                inventory=dict(schema=profile,parent_intake=parent_binding,source_commit='a'*40,
                    native_replay_plan=bound(plan_path),module_count=3,modules=deepcopy(rows),
                    generated_sources_sha256=deepcopy(parent['generated_sources_sha256']),input_sha256={str(extra):F.P.sha(extra)},
                    validator_producer=bound(ROOT/'scripts/streaming_tt_replay_inventory.py'),regeneration_execution=dict(host_fixture=True))
                regeneration=write(root/'regeneration.json',dict(modules=[dict(module=r['module'],sha256=r['sha256']) for r in rows]))
                replay=dict(replay_inventory_profile=profile,exact_parent_inventory=inventory,regenerated_modules=3,
                    module_count=3,positive_native_checks=3,regeneration_manifest=regeneration)
                sealed=dict(replay_inventory_profile=profile,exact_parent_inventory=deepcopy(inventory),generated_modules=3,positive_native_checks=3)
                if mutation=='caller-count':inventory['module_count']=392
                elif mutation=='parent-map':parent['generated_sources_sha256'].pop(rows[-1]['path'])
                elif mutation=='parent-dict':parent['generated_module_count']=2
                elif mutation=='parent-plan':write(plan_path,dict(source_commit='a'*40,modules=list(reversed(rows))))
                elif mutation=='duplicate':write(plan_path,dict(source_commit='a'*40,modules=[rows[0],rows[0],rows[2]]))
                elif mutation=='missing-stage':write(plan_path,dict(source_commit='a'*40,modules=rows[:-1]))
                elif mutation=='regenerated-prefix':
                    replay['regeneration_manifest']=write(root/'regeneration.json',dict(modules=[dict(module=r['module'],sha256=r['sha256']) for r in rows[:-1]]))
                elif mutation=='missing-intake':sealed.pop('exact_parent_inventory')
                elif mutation=='intake-count':sealed['positive_native_checks']=392
                elif mutation=='source':Path(rows[0]['path']).write_text('changed source')
                elif mutation=='empty-inputs':inventory['input_sha256']={}
                elif mutation=='changed-input':extra.write_text('changed producer')
                elif mutation=='unknown-profile':replay['replay_inventory_profile']='unrecognized'
                with patch.object(V,'derive',return_value=deepcopy(inventory)):
                    if mutation is None:self.assertEqual(F.replay_count(parent_path,parent,replay,sealed,parent_binding,'a'*40),3)
                    else:
                        with self.assertRaises(ValueError):F.replay_count(parent_path,parent,replay,sealed,parent_binding,'a'*40)
        self.assertEqual(F.replay_count(None,{}, {},{},None,None),392)
        with self.assertRaises(ValueError):F.replay_count(None,{},dict(exact_parent_inventory={}),{},None,None)

    def test_drt_cts_trial_requires_closed_artifacts_and_actual_explicit_command(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);flow=root/'flow';step=flow/'27-openroad-cts';step.mkdir(parents=True)
            resolved=flow/'resolved.json';F.P.write(resolved,dict(CTS_SINK_CLUSTERING_ENABLE=True,CTS_SINK_CLUSTERING_SIZE=8))
            log=step/'openroad-cts.log';log.write_text('+ clock_tree_synthesis -sink_clustering_enable -sink_clustering_size 8\n')
            prepared=dict(physical_recipe_experiment=dict(cts_trial={}))
            report=dict(artifact_sha256={str(path.relative_to(root)):F.P.sha(path) for path in (resolved,log)})
            self.assertTrue(F.verify_cts_trial(report,prepared,root)['resolved_and_logged_cts_trial'])
            log.write_text('+ clock_tree_synthesis -sink_clustering_enable\nBest clustering solution size8\n')
            with self.assertRaisesRegex(ValueError,'artifact changed'):F.verify_cts_trial(report,prepared,root)
            report['artifact_sha256'][str(log.relative_to(root))]=F.P.sha(log)
            with self.assertRaisesRegex(ValueError,'did not request'):F.verify_cts_trial(report,prepared,root)

    def test_preparation_binds_admission_after_copying_and_protecting_sources(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();design=root/'design';(design/'inputs').mkdir(parents=True)
            pdn=design/'inputs/pdn.tcl';pdn.write_text('actual pdn')
            prepared=design/'inputs.json';F.P.write(prepared,{'input_sha256':{'pdn.tcl':F.P.sha(pdn)}})
            state=root/'state.json';F.P.write(state,{'odb':'actual.odb'})
            admission=root/'admission.json';admission.write_text('actual admission')
            (root/'coarse').mkdir();F.P.write(root/'coarse/report.json',{})
            for name in ('scripts/streaming_tt_final.py','scripts/run-streaming-tt-final.py','test/test_streaming_tt_final.py'):
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('pass\n')
            (root/'scripts/streaming_tt_final.py').write_text('import fixture_extra\n')
            (root/'scripts/fixture_extra.py').write_text('pass\n')
            with patch.object(F.P,'ROOT',root),patch.object(F.P,'BASE',root/'physical'),\
                    patch.object(F,'admission',return_value=({'source_commit':'source'},
                        {'prepared_input':prepared,'state':state,'coarse_report':root/'coarse/report.json'},design)),\
                    patch.object(F.P,'producer_hashes',return_value={}),\
                    patch.object(F.P,'committed',side_effect=lambda path:path.read_bytes()),\
                    patch.object(F,'snapshot_state',return_value=({'odb':'/work/inputs/checkpoint/actual.odb'},{})),\
                    patch.object(F,'verify_view_inventory'),patch.object(F,'verify'),\
                    patch.object(F.subprocess,'check_output',return_value='commit\n'):
                result=F.prepare(admission,F.P.sha(admission),'attempt',60)
            metadata=F.P.read(result)
            self.assertEqual(metadata['external_input_sha256'],{str(admission):F.P.sha(admission)})
            self.assertEqual((result.parent/'inputs/pdn.tcl').read_text(),'actual pdn')
            self.assertIn('scripts/fixture_extra.py',metadata['producer_sha256'])
            self.assertEqual((result.parent/'inputs/producer/scripts/fixture_extra.py').read_text(),'pass\n')

    def test_native_success_with_unconfirmed_owned_cleanup_is_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);(root/'tools').mkdir();(root/'tools/physical-toolchain.json').write_text('{}')
            base=root/'physical';out=base/'attempt';out.mkdir(parents=True);(out/'inputs').mkdir()
            path=out/'inputs.json';path.write_text('{}')
            metadata=dict(tag='attempt',producer_sha256={},producer_commit='p',source_commit='s',
                timeout_seconds=1,pdk=str(root/'pdk'))
            order=SimpleNamespace(returncode=0,stdout=json.dumps(['OpenROAD.STAMidPNR-3',*F.TAIL]),stderr='')
            process=Mock();process.wait.return_value=0;process.poll.return_value=0
            cleanup=SimpleNamespace(cleanup=Mock(return_value=dict(status='unconfirmed',remaining=['owned-container'])))
            with patch.object(F.P,'ROOT',root),patch.object(F.P,'BASE',base),\
                    patch.object(F,'verify',return_value=metadata),\
                    patch.object(F,'common_runner',return_value=cleanup),\
                    patch.object(F.P,'inspect_runtime',return_value={'image_id':'pinned-image'}),\
                    patch.object(F.subprocess,'run',return_value=order),\
                    patch.object(F.subprocess,'Popen',return_value=process),\
                    patch.object(F,'collect_states',return_value=[]):
                result=F.run(path)
            report=json.loads((out/'report.json').read_text())
            self.assertEqual(result,3);self.assertEqual(report['status'],'cleanup_unconfirmed')
            self.assertEqual(report['exit_code'],0) # Native success is retained honestly.
            self.assertEqual(report['container_termination']['remaining'],['owned-container'])
            self.assertTrue((base/'streaming-tt-active.json').is_file())
            cleanup.cleanup.assert_called_once()

    def test_live_checkpoint_view_must_match_closed_artifact_inventory(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);coarse=root/'coarse';coarse.mkdir();design=root/'design'
            (design/'inputs').mkdir(parents=True);(design/'pdk').mkdir()
            odb=coarse/'physical.odb';odb.write_bytes(b'closed-actual-odb')
            source=design/'inputs/source.v';source.write_text('source')
            library=design/'pdk/cells.lib';library.write_text('library')
            digest=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
            values={str(p.resolve()):digest(p) for p in (odb,source,library)}
            report={'artifact_sha256':{'physical.odb':digest(odb)}}
            prepared={'input_sha256':{'source.v':digest(source)},'pdk':{'complete_files_sha256':{'cells.lib':digest(library)}}}
            F.verify_view_inventory(values,report,coarse,prepared,design)
            odb.write_bytes(b'changed-after-closeout');values[str(odb.resolve())]=digest(odb)
            with self.assertRaisesRegex(ValueError,'closed source inventory'):
                F.verify_view_inventory(values,report,coarse,prepared,design)
            report['artifact_sha256']={}
            with self.assertRaisesRegex(ValueError,'closed source inventory'):
                F.verify_view_inventory(values,report,coarse,prepared,design)

    def test_native_order_requires_immediate_continuation_and_every_later_step(self):
        actual=['OpenROAD.STAMidPNR-2','OpenROAD.GlobalRouting','OpenROAD.STAMidPNR-3',*F.TAIL]
        self.assertEqual(F.validate_order(actual),actual)
        for changed in [actual[:-1],actual[:4]+actual[5:],actual[:3]+['unexpected']+actual[3:],
                ['OpenROAD.STAMidPNR-3',*reversed(F.TAIL)],actual+[actual[-1]]]:
            with self.subTest(changed=changed),self.assertRaises(ValueError):F.validate_order(changed)
        for name in ('OpenROAD.RCX','KLayout.StreamOut','Checker.TrDRC','Checker.DisconnectedPins',
                'Checker.SetupViolations','Checker.HoldViolations'):
            with self.subTest(name=name),self.assertRaises(ValueError):F.validate_order([x for x in actual if x!=name])

    def test_snapshot_copies_all_nested_views_and_keeps_carried_nl_separate(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);flow=root/'flow';flow.mkdir();design=root/'design';(design/'inputs').mkdir(parents=True)
            (design/'pdk').mkdir();out=root/'snapshot';out.mkdir()
            (flow/'physical.odb').write_bytes(b'authoritative');(flow/'old.v').write_text('carried')
            (flow/'timing.sdf').write_text('timing');(design/'inputs/header.json').write_text('{}')
            state={'odb':'/work/run/physical.odb','nl':'/work/run/old.v',
                'sdf':{'corner':['/work/run/timing.sdf']},'json_h':'/work/inputs/header.json','def':None,
                'metrics':{'old_slack':-1}}
            value,bindings=F.snapshot_state(state,flow,design,out)
            self.assertEqual(len(bindings),4);self.assertNotEqual(value['odb'],value['nl'])
            self.assertEqual(value['metrics'],state['metrics']);self.assertEqual(value['def'],None)
            for native,expected in bindings.items():
                self.assertEqual(hashlib.sha256(Path(native).read_bytes()).hexdigest(),expected)
            self.assertEqual(sorted(p.read_bytes() for p in out.iterdir()),[b'authoritative',b'carried',b'timing',b'{}'])
            self.assertEqual(state['odb'],'/work/run/physical.odb')

    def test_unresolved_escaping_or_aliased_view_is_never_accepted(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);flow=root/'flow';flow.mkdir();design=root/'design';design.mkdir();out=root/'out';out.mkdir()
            (root/'outside').write_text('outside');(flow/'link').symlink_to(root/'outside')
            for value in ('/etc/passwd','/work/run/../outside','/work/run/link','relative.odb'):
                with self.subTest(value=value),self.assertRaises(ValueError):
                    F.snapshot_state({'odb':value},flow,design,out)
            with self.assertRaisesRegex(ValueError,'authoritative'):
                F.snapshot_state({'odb':None},flow,design,out)

    def test_unadmitted_or_mutated_receipt_refuses_before_native_execution(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'admission.json'
            baseline=dict(schema='pinwheel.streaming-tt-detailed-route-admission.v1',passed=True,qualified=False,
                physical_acceptance_claim=False,checked={name:True for name in F.CHECKS})
            for key,value in [('passed',False),('qualified',True),('physical_acceptance_claim',True),('schema','other')]:
                changed=deepcopy(baseline);changed[key]=value;path.write_text(json.dumps(changed))
                with self.subTest(key=key),self.assertRaisesRegex(ValueError,'has not admitted'):
                    F.admission(path,hashlib.sha256(path.read_bytes()).hexdigest())
            for name in F.CHECKS:
                changed=deepcopy(baseline);changed['checked'][name]=False;path.write_text(json.dumps(changed))
                with self.subTest(name=name),self.assertRaisesRegex(ValueError,'has not admitted'):
                    F.admission(path,hashlib.sha256(path.read_bytes()).hexdigest())
            with self.assertRaisesRegex(ValueError,'changed before use'):F.admission(path,'0'*64)

    def test_new_producer_import_closure_includes_actual_dynamic_coarse_runner(self):
        closure=dependency_closure(ROOT,['scripts/run-streaming-tt-final.py','scripts/streaming_tt_final.py'])
        for name in ('scripts/run-streaming-tt-physical.py','scripts/streaming_tt_candidate.py',
                'scripts/streaming_tt_verilog.py','scripts/streaming_tt_pdk.py','scripts/streaming_tt_rc.py'):
            self.assertIn(name,closure['files'])
        self.assertNotIn('scripts/streaming_tt_sta.py',closure['files'])
        self.assertIn('scripts/streaming_tt_replay_inventory.py',closure['files'])
        self.assertIn('scripts/streaming_tt_fresh_foundation.py',closure['files'])
        self.assertNotIn('scripts/streaming_tt_opt_intake.py',closure['files'])


if __name__=='__main__':unittest.main()
