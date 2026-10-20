"""Structural392-stage and private-control boundary mutations, with no Lean."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_fresh_foundation as F
import streaming_tt_fresh_replay as R


def fixture(root,counts=(130,130,132)):
    root=root.resolve();source=root/'selected';source.mkdir();tool=root/'tool/bin/lean';tool.parent.mkdir(parents=True);tool.write_text('pinned fixture compiler')
    library=source/'.lake/build/lib/lean';library.mkdir(parents=True)
    before=root/'runtime-before.json';R.dump(before,{str(tool):dict(sha256=F.sha(tool),resolved=str(tool),bytes=tool.stat().st_size)})
    runtime=root/'runtime.json';R.dump(runtime,dict(runtime_before=F.bound(before)))
    binding=dict(candidate_root=str(source),candidate_commit='a'*40,lean=str(tool),runtime_report=F.bound(runtime))
    bp=root/'binding.json';R.dump(bp,binding);marker=F.bound(bp)
    cfg=dict(root=str(source),source_commit='a'*40,producer_commit='a'*40,fresh_foundation=marker,tools={'lean':str(tool)})
    base=root/'replay';base.mkdir();runner=root/'runner.py';runner.write_text('frozen fixture runner')
    commands=[];stages=[];modules=[]
    total=sum(counts)
    for stage,count in zip(('frontend','core-d2','device'),counts):
        out=base/stage;out.mkdir();rows=[];source_hashes={};native_events=[]
        lean_path=':'.join(map(str,[library,tool.parent.parent/'lib/lean',out]))
        for i in range(count):
            name=stage.replace('-','')+str(i);path=out/(name+'.lean');path.write_text('import Std\n');obj=path.with_suffix('.olean');obj.write_text('closed fixture object')
            log=out/(name+'.phase.log');log.write_text('');digest=F.sha(path);source_hashes[name]=digest
            modules.append(dict(module=name,source=str(path),sha256=digest))
            intent=dict(index=i,module=name,source=str(path),source_sha256=digest,source_sha256_before=digest,compiler_sha256_before=F.sha(tool),negative_control=False,started_at='2026-10-18T16:00:00+00:00',
                argv=[str(tool),'-M4096','-j1','-DElab.async=false','--root='+str(out),'-DwarningAsError=true','-DmaxErrors=1','-o',str(obj),str(path)],lean_path=lean_path)
            row=dict(intent,exit_code=0,timed_out=False,native_process_group_closed=True,source_unchanged=True,olean_exists_nonempty=True,
                source_sha256_after=digest,compiler_sha256_after=F.sha(tool),object_sha256=F.sha(obj),olean_sha256=F.sha(obj),log=str(log),log_sha256=F.sha(log))
            rows.append(row);native_events += [dict(event='intent',**intent),dict(event='result',**row)]
        journal=out/'native-phase-journal.jsonl';journal.write_text(''.join(json.dumps(row)+'\n' for row in native_events))
        imports=out/'imports.json';post=out/'post-imports.json'
        for path in (imports,post):R.dump(path,dict(foundation_binding_sha256=marker['sha256'],rows=[dict(status='resolved_exactly_once',foundation_binding_sha256=marker['sha256'])]))
        schedule=out/'modules.json';R.dump(schedule,list(source_hashes))
        seal=out/'source-seal.json';R.dump(seal,dict(import_resolution_sha256=F.sha(imports),runner_sha256=F.sha(runner),schedule_sha256=F.sha(schedule),foundation_binding_sha256=marker['sha256'],
            positive_foundation_artifacts=1298,foundation_library_verified_before_native=True,sources=source_hashes,lean_binary_sha256=F.sha(tool),lean_path=lean_path,native_journal_path=str(journal)))
        report=out/'native-report.json';R.dump(report,dict(status='completed',qualified=False,phase=stage,required_modules=list(source_hashes),required_count=count,completed_count=count,attempted_count=count,
            exact_membership_and_order=True,all_final_checks_passed=True,final_checks={k:True for k in R.STAGE_CHECKS},source_seal_sha256=F.sha(seal),post_import_resolution_sha256=F.sha(post),native_journal=F.bound(journal),commands=rows))
        stages.append({k:F.bound(v) for k,v in dict(report=report,source_seal=seal,import_resolution=imports,post_import_resolution=post,native_journal=journal,runner=runner,schedule=schedule).items()});commands+=rows
    positive=dict(schema='pinwheel.streaming-tt-fresh-replay-positive.v1',passed=True,qualified=False,source_commit='a'*40,producer_commit='a'*40,
        fresh_foundation=marker,positive_native_checks=total,positive_native_stages=stages,commands=commands)
    # A structural checker fixture tests frozen delegation, never kernel evidence.
    checker=base/'verify.py';checker.write_text('''import json\nfrom pathlib import Path
def complete_group(report_path,plan_rows,binding,binding_sha,repository,runner,stages):
 report=json.loads(report_path.read_text());position=next(i for i,s in enumerate(stages) if Path(s['out'])==report_path.parent)
 prior=[n for s in stages[:position] for n in s['modules']]
 for file,complete in [('imports.json',[]),('post-imports.json',report['required_modules'])]:
  receipt=json.loads((report_path.parent/file).read_text());selected=set(prior+complete)
  if [r['module'] for r in receipt['rows']]!=list(plan_rows):raise ValueError('Incomplete ordered import rows')
  if receipt['ordered_roots']!=report['commands'][0]['lean_path'].split(':'):raise ValueError('Wrong actual import roots')
  if receipt['resolved_count']!=len(selected) or receipt['pending_count']!=len(plan_rows)-len(selected):raise ValueError('Wrong import counts')
  for row in receipt['rows']:
   if row['status']!=('resolved_exactly_once' if row['module'] in selected else 'pending_no_olean_anywhere'):raise ValueError('Wrong import status')
 return report
''')
    origin=base/'plan.json';planrows=[dict(module=r['module'],source=r['source'],source_sha256=r['sha256'],target_olean=str(Path(r['source']).with_suffix('.olean'))) for r in modules]
    planstages=[dict(out=str(base/s),modules=[r['module'] for r in modules if Path(r['source']).parent==base/s]) for s in ('frontend','core-d2','device')]
    R.dump(origin,dict(foundation_binding=marker,foundation_binding_sha256=marker['sha256'],proof_root=str(base),required_count=total,rows=planrows,stages=planstages))
    prior=[]
    for stage,selected in zip(stages,planstages):
        report_path=Path(stage['report']['path']);native=F.read(report_path)
        for key,completed in [('import_resolution',[]),('post_import_resolution',selected['modules'])]:
            rp=Path(stage[key]['path']);resolved=set(prior+completed)
            receipt=dict(foundation_binding_sha256=marker['sha256'],plan_path=str(origin),plan_sha256=F.sha(origin),checker_sha256=F.sha(checker),
                ordered_roots=native['commands'][0]['lean_path'].split(':'),resolved_count=len(resolved),pending_count=total-len(resolved),
                rows=[dict(module=r['module'],status='resolved_exactly_once' if r['module'] in resolved else 'pending_no_olean_anywhere',foundation_binding_sha256=marker['sha256']) for r in modules])
            R.dump(rp,receipt);stage[key]=F.bound(rp)
        sealpath=Path(stage['source_seal']['path']);seal=F.read(sealpath);seal['import_resolution_sha256']=stage['import_resolution']['sha256'];R.dump(sealpath,seal)
        stage['source_seal']=F.bound(sealpath);native['source_seal_sha256']=F.sha(sealpath);native['post_import_resolution_sha256']=stage['post_import_resolution']['sha256'];R.dump(report_path,native);stage['report']=F.bound(report_path)
        prior+=selected['modules']
    regeneration=base/'source-regeneration.json';R.dump(regeneration,{'modules':modules,'input_sha256':{str(checker):F.sha(checker)}});positive['regeneration_manifest']=F.bound(regeneration)
    for key in ('all_regenerated_sources_identical','generated_sources_unchanged','library_objects_unchanged','original_artifacts_unchanged','sources_unchanged'):positive[key]=True
    positive_path=base/'positive.json';R.dump(positive_path,positive)
    cp=root/'config.json';R.dump(cp,cfg);wp=root/'worker.json';R.dump(wp,dict(audit_owner_modules=[r['module'] for r in modules]))
    raw=root/'raw.json';R.dump(raw,dict(source_sha256={}))
    parent=root/'parent.json';R.dump(parent,dict(schema='pinwheel.streaming-tt-optimized-intake.v1',passed=True,worker_config=F.bound(cp),worker_report=F.bound(wp),raw_gate_report=F.bound(raw)))
    return cfg,binding,modules,positive,positive_path,parent


class FreshReplayTests(unittest.TestCase):
    def validate(self,positive,cfg,modules,path):
        with patch.object(F,'verify_binding',return_value=True),patch.object(F,'verify_staged',return_value=True):
            return R.validate_positive_stages(positive,cfg,modules,path)

    def test_new_exact_inventory_profile_validates_all9_actual_fixture_events(self):
        import streaming_tt_replay_inventory as V
        with tempfile.TemporaryDirectory() as name:
            cfg,binding,modules,positive,path,parent=fixture(Path(name),counts=(3,4,2))
            expected=dict(schema=V.PROFILE,module_count=9,modules=[dict(module=r['module'],sha256=r['sha256']) for r in modules],
                validator_producer=F.bound(ROOT/'scripts/streaming_tt_replay_inventory.py'))
            positive.update(replay_inventory_profile=V.PROFILE,exact_parent_inventory=expected,module_count=9,regenerated_modules=9)
            with patch.object(F,'verify_binding',return_value=True),patch.object(F,'verify_staged',return_value=True),\
                    patch.object(V,'derive',return_value=expected) as derive:
                _,events=R.validate_positive_stages(positive,cfg,modules,path,parent_path=parent)
                self.assertEqual(len(events),18);derive.assert_called_once_with(parent,validator_workspace=V.ROOT)
                for mutation in ('prefix','invented_count','unknown_profile','missing_profile'):
                    changed=deepcopy(positive);rows=deepcopy(modules)
                    if mutation=='prefix':rows.pop()
                    elif mutation=='invented_count':changed.update(module_count=392,regenerated_modules=392,positive_native_checks=392)
                    elif mutation=='unknown_profile':changed['replay_inventory_profile']='unrecognized'
                    else:changed.pop('replay_inventory_profile')
                    with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                        R.validate_positive_stages(changed,cfg,rows,path,parent_path=parent)

    def test_all392_original_events_and_exact_stage_membership(self):
        with tempfile.TemporaryDirectory() as name:
            cfg,binding,modules,positive,path,parent=fixture(Path(name))
            _,events=self.validate(positive,cfg,modules,path);self.assertEqual(len(events),784)
            for mutation in ('missing-stage','duplicate-command','binding','source','missing-check','unqualified-state','object','extra-output','journal','vacuous-intent','partial-intent','bool-index'):
                changed=deepcopy(positive)
                if mutation=='missing-stage':changed['positive_native_stages'].pop()
                elif mutation=='duplicate-command':changed['commands'][-1]=changed['commands'][0]
                elif mutation=='binding':changed['fresh_foundation']={'path':'wrong','sha256':'a'*64}
                elif mutation=='source':changed_modules=deepcopy(modules);changed_modules[0]['sha256']='b'*64
                elif mutation in ('missing-check','unqualified-state'):
                    p=Path(changed['positive_native_stages'][0]['report']['path']);old=p.read_text();r=json.loads(old)
                    if mutation=='missing-check':r['final_checks'].pop('command_intents_durable_and_exact')
                    else:r['status']='running'
                    R.dump(p,r);changed['positive_native_stages'][0]['report']=F.bound(p)
                elif mutation=='object':p=Path(modules[0]['source']).with_suffix('.olean');old=p.read_text();p.write_text('changed object')
                elif mutation=='extra-output':p=path.parent/'frontend/Old.olean';p.write_text('old')
                elif mutation in ('journal','vacuous-intent','partial-intent','bool-index'):
                    p=Path(changed['positive_native_stages'][0]['native_journal']['path']);old=p.read_text()
                    altered=R.events(p)
                    if mutation=='journal':altered=[]
                    elif mutation=='vacuous-intent':altered[0]={'event':'intent'}
                    elif mutation=='partial-intent':altered[0].pop('source_sha256_before')
                    else:altered[0]['index']=False
                    p.write_text(''.join(json.dumps(r)+'\n' for r in altered))
                    changed['positive_native_stages'][0]['native_journal']=F.bound(p)
                    # A coherent updated result/receipt must still not allow an empty intent.
                    if mutation in ('vacuous-intent','partial-intent','bool-index'):
                        rp=Path(changed['positive_native_stages'][0]['report']['path']);ro=rp.read_text();rr=json.loads(ro)
                        rr['native_journal']=F.bound(p);R.dump(rp,rr);changed['positive_native_stages'][0]['report']=F.bound(rp)
                with self.subTest(mutation=mutation),self.assertRaises((ValueError,FileNotFoundError)):
                    self.validate(changed,cfg,changed_modules if mutation=='source' else modules,path)
                if mutation in ('missing-check','unqualified-state','object','journal','vacuous-intent','partial-intent','bool-index'):p.write_text(old)
                if mutation in ('vacuous-intent','partial-intent','bool-index'):rp.write_text(ro)
                elif mutation=='extra-output':p.unlink()

    def test_exact_private_native_intents_and_aggregate_use_same_two_commands(self):
        with tempfile.TemporaryDirectory() as name:
            cfg,binding,modules,positive,path,parent=fixture(Path(name));out=Path(name).resolve()/'private'
            class FakeNative:
                pid=999999
                def __init__(self,argv,*,cwd,env,stdout,stderr,start_new_session):
                    events=R.events(out/'journal.jsonl');self.argv=argv
                    if events[-1]['event']!='intent' or events[-1]['argv']!=argv:raise AssertionError('Missing real pre-use intent')
                    if not start_new_session:raise AssertionError('Unowned process')
                    self.code=1 if 'PrivateAudit.lean' in argv[-1] else 0
                    if self.code:stdout.write(b'Unapproved axioms in _private.StreamingOptimizedReplayExactPrivateAxiom.x.forbiddenUnused\n')
                    else:Path(argv[argv.index('-o')+1]).write_text('fresh fixture private object')
                def wait(self,timeout):return self.code
            with patch.object(F,'verify_binding',return_value=True),patch.object(F,'verify_staged',return_value=True), \
                 patch.object(R.subprocess,'Popen',side_effect=FakeNative),patch.object(F,'closed_group',return_value=True):
                private=R.run_private_control(parent,path,out)
                self.assertTrue(private['passed']);self.assertEqual([r['exit_code'] for r in private['commands']],[0,1])
                result=R.assemble(parent,path,out/'report.json');self.assertEqual(len(result['commands']),394)
                self.assertEqual(result['commands'][-2:],private['commands'])
                self.assertEqual(R.events(path.parent/'native-journal.jsonl')[-4:],R.events(out/'journal.jsonl'))
            manifest=F.read(out/'input-manifest.json')
            for mutation in ('argv','environment','timeout','ownership','object','runtime','intent','vacuous-intent','partial-intent','wrong-name','unrelated-error'):
                bad=deepcopy(private);changed=deepcopy(manifest)
                if mutation=='argv':bad['commands'][0]['argv'][1]='-M0'
                elif mutation=='environment':changed['environment']['LEAN_PATH']='/old/cache'
                elif mutation=='timeout':bad['commands'][0]['timed_out']=True
                elif mutation=='ownership':bad['commands'][0]['native_process_group_closed']=False
                elif mutation=='object':bad['commands'][0]['object_sha256']='a'*64
                elif mutation=='runtime':changed['runtime_files']={}
                elif mutation=='wrong-name':bad['commands'][0]['module']='UnrelatedControl'
                elif mutation=='unrelated-error':
                    lp=Path(bad['commands'][1]['log']);lo=lp.read_text();lp.write_text('error: unknown constant\n')
                    bad['commands'][1]['log_sha256']=F.sha(lp)
                    jp=out/'journal.jsonl';jo=jp.read_text();ev=R.events(jp)
                    ev[-1]['log_sha256']=F.sha(lp);jp.write_text(''.join(json.dumps(r)+'\n' for r in ev));bad['native_journal']=F.bound(jp)
                elif mutation=='intent':bad['native_journal']=F.bound(path.parent/'native-journal.jsonl')
                else:
                    jp=out/'journal.jsonl';jo=jp.read_text();ev=R.events(jp)
                    if mutation=='vacuous-intent':ev[0]={'event':'intent'}
                    else:ev[0].pop('environment')
                    jp.write_text(''.join(json.dumps(r)+'\n' for r in ev));bad['native_journal']=F.bound(jp)
                with self.subTest(mutation=mutation),self.assertRaises(ValueError):R.validate_private_commands(bad,changed,cfg,path,binding,
                    F.read(F.verify_bound(F.read(parent)['worker_report'])))
                if mutation in ('vacuous-intent','partial-intent'):jp.write_text(jo)
                elif mutation=='unrelated-error':jp.write_text(jo);lp.write_text(lo)

    def test_frozen_checker_delegation_rejects_coherently_changed_import_receipts(self):
        for mutation in ('empty-before','empty-after','partial-rows','downgraded-row','wrong-roots','changed-checker'):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as name:
                cfg,binding,modules,positive,path,parent=fixture(Path(name))
                stage=positive['positive_native_stages'][0]
                key='post_import_resolution' if mutation in ('empty-after','downgraded-row') else 'import_resolution'
                receipt_path=Path(stage[key]['path']);receipt=F.read(receipt_path)
                if mutation.startswith('empty-'):receipt['rows']=[]
                elif mutation=='partial-rows':receipt['rows'].pop()
                elif mutation=='downgraded-row':receipt['rows'][0]['status']='pending_no_olean_anywhere'
                elif mutation=='wrong-roots':receipt['ordered_roots']=['/old/cache']
                else:
                    checker=path.parent/'verify.py';checker.write_text(checker.read_text()+'\n# changed checker\n')
                    receipt['checker_sha256']=F.sha(checker)
                R.dump(receipt_path,receipt);stage[key]=F.bound(receipt_path)
                report_path=Path(stage['report']['path']);report=F.read(report_path)
                if key=='import_resolution':
                    seal_path=Path(stage['source_seal']['path']);seal=F.read(seal_path)
                    seal['import_resolution_sha256']=F.sha(receipt_path);R.dump(seal_path,seal);stage['source_seal']=F.bound(seal_path)
                    report['source_seal_sha256']=F.sha(seal_path)
                else:report['post_import_resolution_sha256']=F.sha(receipt_path)
                R.dump(report_path,report);stage['report']=F.bound(report_path)
                with self.assertRaises(ValueError):self.validate(positive,cfg,modules,path)


if __name__=='__main__':unittest.main()
