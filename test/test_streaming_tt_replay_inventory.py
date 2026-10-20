"""Independent-regeneration membership controls; no Native execution."""
from copy import deepcopy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_replay_inventory as V


class ExactReplayInventoryTests(unittest.TestCase):
    def test_isolated_host_child_owns_indirect_imports_and_refuses_escape_or_native_tools(self):
        for mutation in (None,'outside-import','site-packages','native-tool','output-limit','timeout'):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as name:
                root=Path(name).resolve();scripts=root/'selected/scripts';scripts.mkdir(parents=True)
                module=scripts/'streaming_tt_opt_intake.py'
                body='import indirect\ndef regenerated_sources(cfg,worker,out):\n return indirect.modules, indirect.identities\n'
                (scripts/'indirect.py').write_text('modules=[]\nidentities={}\n')
                if mutation=='outside-import':
                    foreign=root/'foreign';foreign.mkdir();(foreign/'rogue.py').write_text('value=True\n')
                    body="import sys\nsys.path.insert(0,"+repr(str(foreign))+")\nimport rogue\n"+body
                elif mutation=='site-packages':
                    body="import types,sys,sysconfig\nrogue=types.ModuleType('rogue')\nrogue.__file__=sysconfig.get_path('stdlib')+'/site-packages/rogue.py'\nsys.modules['rogue']=rogue\n"+body
                elif mutation=='native-tool':body="import subprocess,sys\nsubprocess.run([sys.executable,'-c','pass'])\n"+body
                elif mutation=='output-limit':body="print('x'*20000)\n"+body
                elif mutation=='timeout':body="import time\ntime.sleep(5)\n"+body
                module.write_text(body);cfg=dict(root=str(scripts.parent),tools={'python':str(Path(sys.executable).resolve())})
                cfgpath=root/'config.json';cfgpath.write_text(json.dumps(cfg));worker=root/'worker.json';worker.write_text('{}')
                with patch.object(V,'ROOT',root),patch.object(V,'HOST_TIMEOUT',.2 if mutation=='timeout' else 5),\
                        patch.object(V,'HOST_OUTPUT_LIMIT',10000):
                    if mutation is None:
                        modules,identities,imports,execution=V.regenerate(cfgpath,worker,cfg,{})
                        self.assertEqual(modules,[]);self.assertEqual(identities,{})
                        self.assertIn(str(scripts/'indirect.py'),imports)
                        self.assertEqual(execution['argv'][1:4],['-I','-S','-B'])
                        self.assertTrue(execution['process_group_closed'])
                    else:
                        with self.assertRaises(ValueError):V.regenerate(cfgpath,worker,cfg,{})
                reports=list((root/'build/streaming-tt-replay-inventory').glob('*/report.json'))
                self.assertEqual(len(reports),1);receipt=json.loads(reports[0].read_text())
                self.assertTrue(receipt['process_group_closed'])
                if mutation=='native-tool':self.assertIn('Native/tool execution forbidden',reports[0].with_name('stdout.log').read_text())
                elif mutation in ('output-limit','timeout'):self.assertEqual(receipt['stop_reason'],mutation.replace('-','_'))

    def fixture(self,base):
        repo=base/'repo';snapshot=base/'snapshot';worker=base/'worker';parent=base/'parent'
        for p in (repo/'scripts',snapshot/'scripts',worker,parent):p.mkdir(parents=True)
        producers={}
        for name in ('streaming_tt_opt_intake.py','streaming_tt_opt_proof.py','streaming_ready_readback.py','streaming_tt_fresh_foundation.py'):
            for root in (repo,snapshot):(root/'scripts'/name).write_text('# same frozen interpreter\n')
            if name=='streaming_tt_fresh_foundation.py':
                for root in (repo,snapshot):(root/'scripts'/name).write_bytes(Path(V.F.__file__).read_bytes())
            producers['scripts/'+name]=V.F.sha(repo/'scripts'/name)
        for name in ('streaming_tt_fresh_replay.py','streaming_tt_replay_intake.py'):
            (repo/'scripts'/name).write_text('# current validator\n')
        (repo/'scripts/streaming_tt_replay_inventory.py').write_bytes(Path(V.__file__).read_bytes())
        (snapshot/'test').mkdir();(snapshot/'test/ProofAudit.lean').write_text('-- bound nonscript source input\n')
        producers['test/ProofAudit.lean']=V.F.sha(snapshot/'test/ProofAudit.lean')
        commit='a'*40;modules=[]
        for stage,name in zip(V.STAGES,('FrontendProof','CoreProof','DeviceProof')):
            directory=worker/stage;directory.mkdir();p=directory/(name+'.lean');p.write_text('theorem exact : True := by trivial\n')
            modules.append(dict(module=name,path=str(p),sha256=V.F.sha(p)))
        identities={r['path']:r['sha256'] for r in modules}
        def write(path,data):path.write_text(json.dumps(data));return V.F.bound(path)
        python=str(Path(sys.executable).resolve());library=base/'cells.lib';library.write_text('bound function model')
        positive=snapshot/'.lake/build/lib/lean/Pinwheel/Fixture.olean';positive.parent.mkdir(parents=True);positive.write_text('bound fixture object')
        marker=write(base/'binding.json',dict(candidate_commit=commit,candidate_root=str(snapshot),python=python,
            positive_library_artifact_sha256={'Pinwheel/Fixture.olean':V.F.sha(positive)}))
        cfg=write(base/'config.json',dict(source_commit=commit,producer_commit=commit,root=str(snapshot),fresh_foundation=marker,tools={'python':python},library=str(library),components={}))
        restored=worker/'restored.json';restored.write_text('{}')
        artifact_map={str(worker/name):value for name,value in V.F.manifest(worker).items()}
        report=write(worker/'report.json',dict(fresh_foundation=marker,artifact_sha256=artifact_map,outer={'restored_json':str(restored)}))
        raw=write(base/'raw.json',dict(passed=True,stage='components',source_commit=commit,producer_commit=commit,source_sha256=producers))
        write(parent/'native-replay-plan.json',dict(source_commit=commit,modules=modules))
        target=parent/'report.json';write(target,dict(schema='pinwheel.streaming-tt-optimized-intake.v1',passed=True,qualified=False,
            source_commit=commit,producer_commit=commit,checked={key:True for key in V.CHECKS},worker_config=cfg,
            worker_report=report,raw_gate_report=raw,generated_module_count=len(modules),generated_sources_sha256=identities))
        return repo,target,modules,identities

    def generated(self,parent,modules,identities):
        config=V.F.read(V.F.verify_bound(V.F.read(parent)['worker_config']))
        return modules,identities,{str(Path(config['root'])/'scripts/streaming_tt_opt_intake.py'):'streaming_tt_opt_intake'},dict(host_fixture=True)

    def test_cardinality_comes_from_all_regenerated_sources_not_a_caller_count(self):
        with tempfile.TemporaryDirectory() as name:
            repo,parent,modules,identities=self.fixture(Path(name).resolve())
            with patch.object(V,'ROOT',repo),patch.object(V.F,'verify_binding'),patch.object(V.F,'verify_staged'),\
                    patch.object(V,'regenerate',return_value=self.generated(parent,modules,identities)):
                value=V.derive(parent)
                (repo/'scripts/unrelated_postpnr.py').write_text('# independently advancing controller\n')
                self.assertEqual(V.derive(parent),value)
            self.assertEqual(value['module_count'],3);self.assertEqual(value['modules'],modules)
            self.assertEqual(value['schema'],V.PROFILE)

    def test_private_boundary_is_cold_outside_and_reuses_only_one_child_inside(self):
        with tempfile.TemporaryDirectory() as name:
            repo,parent,modules,identities=self.fixture(Path(name).resolve())
            payload=self.generated(parent,modules,identities)
            with patch.object(V,'ROOT',repo),patch.object(V.F,'verify_binding') as binding_check,\
                    patch.object(V.F,'verify_staged') as library_check,\
                    patch.object(V,'regenerate',return_value=payload) as child:
                V.derive(parent);V.derive(parent);self.assertEqual(child.call_count,2)
                before=binding_check.call_count
                with V._host_boundary(parent) as authority:
                    self.assertEqual(authority,V.derive(parent));self.assertEqual(child.call_count,3)
                    # A caller must not mutate the retained deterministic payload.
                    authority['modules'].pop()
                    self.assertEqual(V.derive(parent)['module_count'],3)
                    self.assertEqual(len(V.derive(parent)['modules']),3)
                    with self.assertRaises(ValueError):
                        with V._host_boundary(parent):pass
                self.assertEqual(child.call_count,3)
                self.assertEqual(binding_check.call_count-before,10) # Entry, three derives, exit; pre/post each.
                self.assertEqual(binding_check.call_count,library_check.call_count)
                with V._host_boundary(parent):V.derive(parent)
                self.assertEqual(child.call_count,4)
                V.derive(parent);self.assertEqual(child.call_count,5)
                self.assertIsNone(V._HOST_BOUNDARY.get())

    def test_boundary_exception_discards_and_failed_derive_poison_cannot_be_caught_away(self):
        with tempfile.TemporaryDirectory() as name:
            repo,parent,modules,identities=self.fixture(Path(name).resolve())
            with patch.object(V,'ROOT',repo),patch.object(V.F,'verify_binding'),\
                    patch.object(V.F,'verify_staged'),\
                    patch.object(V,'regenerate',return_value=self.generated(parent,modules,identities)) as child:
                with self.assertRaisesRegex(RuntimeError,'caller failure'):
                    with V._host_boundary(parent):raise RuntimeError('caller failure')
                self.assertIsNone(V._HOST_BOUNDARY.get());V.derive(parent)
                self.assertEqual(child.call_count,2)
                with self.assertRaises(ValueError):
                    with V._host_boundary(parent):
                        with self.assertRaises(ValueError):V.derive(parent.with_name('missing.json'))
                        # Catching a failed sub-validation does not restore authority.
                        with self.assertRaises(ValueError):V.derive(parent)
                self.assertIsNone(V._HOST_BOUNDARY.get())
                V.derive(parent);self.assertEqual(child.call_count,4)

    def test_boundary_rechecks_mutations_and_exit_membership_without_another_child(self):
        for mutation in ('source','import','helper','runtime','parent','worker','selected-membership',
                         'worker-membership','coherent-worker','plan'):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as name:
                base=Path(name).resolve();repo,parent,modules,identities=self.fixture(base)
                runtime=base/'runtime';runtime.write_text('exact runtime fixture');runtime_sha=V.F.sha(runtime)
                def binding_check(_):V.F.require(V.F.sha(runtime)==runtime_sha,'Runtime fixture changed')
                def mutate():
                    if mutation=='source':Path(modules[0]['path']).write_text('changed proof')
                    elif mutation=='import':(base/'snapshot/scripts/streaming_tt_opt_intake.py').write_text('changed generator')
                    elif mutation=='helper':(repo/'scripts/streaming_tt_fresh_replay.py').write_text('changed validator')
                    elif mutation=='runtime':runtime.write_text('changed runtime')
                    elif mutation=='parent':parent.write_text(parent.read_text()+' ')
                    elif mutation=='worker':(base/'worker/report.json').write_text('{}')
                    elif mutation=='selected-membership':(base/'snapshot/scripts/extra.py').write_text('unowned')
                    elif mutation=='worker-membership':(base/'worker/extra.olean').write_text('unowned')
                    elif mutation=='plan':parent.with_name('native-replay-plan.json').write_text('{}')
                    else:
                        # Even a coherently reclosed upstream change cannot hit a prior payload.
                        path=base/'worker/extra.json';path.write_text('{}')
                        worker_path=base/'worker/report.json';worker=V.F.read(worker_path)
                        worker['artifact_sha256'][str(path)]=V.F.sha(path);worker_path.write_text(json.dumps(worker))
                        report=V.F.read(parent);report['worker_report']=V.F.bound(worker_path);parent.write_text(json.dumps(report))
                with patch.object(V,'ROOT',repo),patch.object(V.F,'verify_binding',side_effect=binding_check),\
                        patch.object(V.F,'verify_staged'),\
                        patch.object(V,'regenerate',return_value=self.generated(parent,modules,identities)) as child:
                    with self.assertRaises(ValueError):
                        with V._host_boundary(parent):mutate() # Exit itself must detect the mutation.
                    self.assertEqual(child.call_count,1)
                    self.assertIsNone(V._HOST_BOUNDARY.get())

    def test_child_time_mutation_and_loaded_producer_identity_refused(self):
        for mutation in ('selected-membership','worker-membership','loaded-producer'):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as name:
                base=Path(name).resolve();repo,parent,modules,identities=self.fixture(base)
                payload=self.generated(parent,modules,identities)
                def child(**_):
                    target=base/('snapshot/scripts/extra.py' if mutation=='selected-membership' else 'worker/extra.json')
                    target.write_text('new unowned input');return payload
                with patch.object(V,'ROOT',repo),patch.object(V.F,'verify_binding'),\
                        patch.object(V.F,'verify_staged'),patch.object(V,'regenerate',side_effect=child),\
                        patch.object(V,'_LOADED_SOURCE_SHA256','0'*64 if mutation=='loaded-producer' else V._LOADED_SOURCE_SHA256):
                    with self.assertRaises(ValueError):
                        with V._host_boundary(parent):pass
                self.assertIsNone(V._HOST_BOUNDARY.get())

    def test_boundary_rechecks_child_environment_and_loader_overrides_on_every_hit(self):
        for key,value in (('LANG','changed-locale'),('PYTHONPATH','/foreign/imports')):
            with self.subTest(key=key),tempfile.TemporaryDirectory() as name:
                repo,parent,modules,identities=self.fixture(Path(name).resolve())
                with patch.object(V,'ROOT',repo),patch.object(V.F,'verify_binding'),\
                        patch.object(V.F,'verify_staged'),\
                        patch.object(V,'regenerate',return_value=self.generated(parent,modules,identities)) as child,\
                        patch.dict(os.environ,{}):
                    os.environ.pop('PYTHONPATH',None)
                    with self.assertRaises(ValueError):
                        with V._host_boundary(parent):
                            os.environ[key]=value
                            V.derive(parent)
                    self.assertEqual(child.call_count,1)
                    self.assertIsNone(V._HOST_BOUNDARY.get())

    def test_coherent_report_count_plan_and_source_mutants_refused(self):
        for mutation in ('caller_count','bool_count','omit_plan','reorder_plan','duplicate_owner','partial_regeneration',
                         'extra_map','changed_source','wrong_stage','changed_interpreter','missing_interpreter',
                         'added_python','changed_data','changed_positive','extra_worker'):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as name:
                repo,parent,modules,identities=self.fixture(Path(name).resolve());root=Path(name)
                report=json.loads(parent.read_text());plan_path=parent.parent/'native-replay-plan.json';plan=json.loads(plan_path.read_text())
                if mutation=='caller_count':report['generated_module_count']=392
                elif mutation=='bool_count':report['generated_module_count']=True
                elif mutation=='omit_plan':plan['modules'].pop()
                elif mutation=='reorder_plan':plan['modules'].reverse()
                elif mutation=='duplicate_owner':modules[-1]=deepcopy(modules[0])
                elif mutation=='partial_regeneration':modules=modules[:-1];identities={r['path']:r['sha256'] for r in modules}
                elif mutation=='extra_map':report['generated_sources_sha256']['/unknown/extra.lean']='0'*64
                elif mutation=='changed_source':Path(modules[0]['path']).write_text('axiom changed : False\n')
                elif mutation=='wrong_stage':
                    p=root/'worker'/'other';p.mkdir();q=p/'FrontendProof.lean';q.write_text('changed stage')
                    modules[0]=dict(module='FrontendProof',path=str(q),sha256=V.F.sha(q))
                elif mutation=='changed_interpreter':(root/'snapshot/scripts/streaming_tt_opt_proof.py').write_text('# changed producer\n')
                elif mutation=='missing_interpreter':(root/'snapshot/scripts/streaming_ready_readback.py').unlink()
                elif mutation=='added_python':(root/'snapshot/scripts/hidden_private.py').write_text('# unowned helper\n')
                elif mutation=='changed_data':(root/'snapshot/test/ProofAudit.lean').write_text('-- changed nonscript source\n')
                elif mutation=='changed_positive':(root/'snapshot/.lake/build/lib/lean/Pinwheel/Fixture.olean').write_text('changed cache')
                else:(root/'worker/unowned.olean').write_text('unowned proof output')
                parent.write_text(json.dumps(report));plan_path.write_text(json.dumps(plan))
                with patch.object(V,'ROOT',repo),patch.object(V.F,'verify_binding'),patch.object(V.F,'verify_staged'),\
                        patch.object(V,'regenerate',return_value=self.generated(parent,modules,identities)):
                    with self.assertRaises(ValueError):V.derive(parent)

    def test_new_profile_compares_whole_regenerated_inventory_and_legacy_stays392(self):
        with tempfile.TemporaryDirectory() as name:
            repo,parent,modules,identities=self.fixture(Path(name).resolve())
            with patch.object(V,'ROOT',repo),patch.object(V.F,'verify_binding'),patch.object(V.F,'verify_staged'),\
                    patch.object(V,'regenerate',return_value=self.generated(parent,modules,identities)):
                expected=V.derive(parent)
                replay=dict(replay_inventory_profile=V.PROFILE,exact_parent_inventory=expected,
                    module_count=3,regenerated_modules=3,positive_native_checks=3)
                staged=[dict(module=r['module'],source='/fresh/'+r['module']+'.lean',sha256=r['sha256']) for r in modules]
                self.assertEqual(V.validate(replay,parent,staged),3)
                for mutation in ('caller_count','bool_count','prefix_inventory','prefix_rows','reorder','unknown_profile','missing_profile','missing_parent'):
                    changed=deepcopy(replay);rows=deepcopy(staged);target=parent
                    if mutation=='caller_count':changed.update(module_count=392,regenerated_modules=392,positive_native_checks=392)
                    elif mutation=='bool_count':changed['module_count']=True
                    elif mutation=='prefix_inventory':changed['exact_parent_inventory']['modules'].pop()
                    elif mutation=='prefix_rows':rows.pop()
                    elif mutation=='reorder':rows.reverse()
                    elif mutation=='unknown_profile':changed['replay_inventory_profile']='unknown'
                    elif mutation=='missing_profile':changed.pop('replay_inventory_profile')
                    else:target=None
                    with self.subTest(mutation=mutation),self.assertRaises(ValueError):V.validate(changed,target,rows)
            self.assertEqual(V.validate(dict(positive_native_checks=392)),392)
            for count in (391,393,True):
                with self.subTest(legacy=count),self.assertRaises(ValueError):V.validate(dict(positive_native_checks=count))

    def test_actual_staged_final_revalidates_canonical_inventory_without_writing_frozen_inputs(self):
        """Real copied V/F/Final and child codegen; foundation receipt is structural."""
        from streaming_tt_intake import dependency_closure
        with tempfile.TemporaryDirectory() as name:
            base=Path(name).resolve();repo,parent,modules,identities=self.fixture(base)
            closure=dependency_closure(ROOT,['scripts/run-streaming-tt-final.py','scripts/streaming_tt_final.py'])
            staged=base/'physical/attempt/inputs/producer'
            for relative in closure['files']:
                for target in (repo,staged):
                    path=target/relative;path.parent.mkdir(parents=True,exist_ok=True)
                    shutil.copyfile(ROOT/relative,path)
            receipt=V.F.read(parent);cfgpath=Path(receipt['worker_config']['path']);cfg=V.F.read(cfgpath)
            # This immutable selected generator exercises the actual isolated child.
            selected=Path(cfg['root']);intake=selected/'scripts/streaming_tt_opt_intake.py'
            intake.write_text('def regenerated_sources(cfg,worker,out):\n'
                ' rows=cfg["fixture_modules"]\n return rows,{row["path"]:row["sha256"] for row in rows}\n')
            cfg['fixture_modules']=modules;cfgpath.write_text(json.dumps(cfg));receipt['worker_config']=V.F.bound(cfgpath)
            rawpath=Path(receipt['raw_gate_report']['path']);raw=V.F.read(rawpath)
            raw['source_sha256']['scripts/streaming_tt_opt_intake.py']=V.F.sha(intake)
            rawpath.write_text(json.dumps(raw));receipt['raw_gate_report']=V.F.bound(rawpath)
            parent.write_text(json.dumps(receipt))
            with patch.object(V.F,'verify_binding'),patch.object(V.F,'verify_staged'):
                inventory=V.derive(parent,validator_workspace=repo)
            regeneration=base/'regeneration.json';regeneration.write_text(json.dumps(dict(modules=modules)))
            replay=dict(replay_inventory_profile=V.PROFILE,exact_parent_inventory=inventory,
                module_count=3,regenerated_modules=3,positive_native_checks=3,regeneration_manifest=V.F.bound(regeneration))
            sealed=dict(replay_inventory_profile=V.PROFILE,exact_parent_inventory=inventory,
                generated_modules=3,positive_native_checks=3)
            case=base/'case.json';case.write_text(json.dumps(dict(workspace=str(repo),parent=str(parent),replay=replay,sealed=sealed)))
            child=r'''
import json,sys
from pathlib import Path
sys.path.insert(0,sys.argv[1])
import streaming_tt_final as final
import streaming_tt_replay_inventory as inventory
case=json.loads(Path(sys.argv[2]).read_text())
final.P.ROOT=Path(case['workspace'])
# Only the foundation receipt fixture is synthetic; staged codegen/identity run.
inventory.F.verify_binding=lambda value:None
inventory.F.verify_staged=lambda value:None
parent=Path(case['parent']);report=final.P.read(parent)
value=final.replay_count(parent,report,case['replay'],case['sealed'],
    dict(path=str(parent),sha256=final.P.sha(parent)),report['source_commit'])
assert value==3
assert Path(inventory.__file__).resolve().is_relative_to(Path(sys.argv[1]).resolve())
assert Path(inventory.F.__file__).resolve().is_relative_to(Path(sys.argv[1]).resolve())
print(value)
'''
            before=V.F.manifest(staged.parent)
            def run():
                return subprocess.run([sys.executable,'-I','-S','-B','-c',child,str(staged/'scripts'),str(case)],
                    stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=15)
            result=run();self.assertEqual(result.returncode,0,result.stdout);self.assertEqual(result.stdout.strip(),'3')
            self.assertEqual(V.F.manifest(staged.parent),before)
            observations=list((repo/'build/streaming-tt-replay-inventory').glob('*/report.json'))
            self.assertEqual(len(observations),2)
            executed=[V.F.read(path)['executed_producer_sha256'] for path in observations]
            self.assertTrue(any(str(staged/'scripts/streaming_tt_replay_inventory.py') in value for value in executed))
            self.assertFalse((staged/'build').exists())
            for mutation in ('staged-inventory','staged-foundation','wrong-workspace'):
                target=staged/'scripts'/('streaming_tt_fresh_foundation.py' if mutation=='staged-foundation'
                    else 'streaming_tt_replay_inventory.py')
                original=target.read_bytes();original_case=case.read_bytes()
                if mutation=='wrong-workspace':
                    changed=V.F.read(case);changed['workspace']=str(staged);case.write_text(json.dumps(changed))
                else:target.write_bytes(original+b'\n# wrong frozen producer\n')
                frozen=V.F.manifest(staged.parent)
                with self.subTest(mutation=mutation):
                    self.assertNotEqual(run().returncode,0)
                    self.assertEqual(V.F.manifest(staged.parent),frozen)
                target.write_bytes(original);case.write_bytes(original_case)
            self.assertEqual(len(list((repo/'build/streaming-tt-replay-inventory').glob('*/report.json'))),2)


if __name__=='__main__':unittest.main()
