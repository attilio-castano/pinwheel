"""Portable explicit6g/full9 controls; no KLayout/Docker/ignored input reads."""
import ast
from copy import deepcopy
import inspect
import json
from pathlib import Path
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_official_budget as B
import streaming_8x4_closure24_official_readback as R


def journal(root,memory='6g'):
    root=root.resolve()
    out=root/'out';pdk=root/'pdk';out.mkdir(exist_ok=True);records=[]
    config=dict(schema='pinwheel.closure24-official-budget-native-config.v1',resource_policy=B.policy(),out=str(out),pdk=str(pdk),owner='test-owner',image_id='image',container_name=B.ORIGINAL.container_name(out))
    config_path=root/'config.json';config_path.write_text(json.dumps(config))
    checks=('pin_label_purposes_overlapping_drawing','sg13cmos5l','zero_area')
    scripts=('tech-files/pin_label_purposes_overlapping_drawing.rb.drc',str(pdk/'ihp-sg13cmos5l/libs.tech/klayout/tech/drc/ihp-sg13cmos5l.drc'),'tech-files/zeroarea.rb.drc')
    for check,script in zip(checks,scripts):
        report=out/'tt/precheck/reports'/('drc_'+check+'.xml');report.parent.mkdir(parents=True,exist_ok=True);report.write_text('actual-report')
        args=['-b','-r',script,'-rd',check+'=true','-rd','input='+str(root/'actual.gds'),'-rd','thr=1','-rd','report='+str(report),'-rd','report_file='+str(report)]
        with patch.object(B.ORIGINAL.Path,'cwd',return_value=out/'tt/precheck'),patch.object(B.ORIGINAL.subprocess,'run',return_value=SimpleNamespace(returncode=0)) as run:
            B.native_klayout(config_path,args);command=run.call_args.args[0]
        for flag in ('--memory','--memory-swap'):command[command.index(flag)+1]=memory
        records.extend([dict(event='intent',identity=check,argv=command),dict(event='result',identity=check,exit_code=0,seconds=1.0)])
    path=out/'native-klayout.jsonl';path.write_text('\n'.join(json.dumps(r) for r in records)+'\n')
    return path,dict(out=out,pdk=pdk,owner='test-owner',image_id='image',gds=root/'actual.gds'),records


class OfficialBudgetControls(unittest.TestCase):
    def test_native_launcher_and_reader_bodies_change_only_memory_and_swap_ceiling(self):
        for name in ('native_klayout','native_journal'):
            text,diff=B.native_source(name);old=inspect.getsource(getattr(B.ORIGINAL,name))
            self.assertEqual(text.replace("'--memory', '6g', '--memory-swap', '6g'","'--memory', '2g', '--memory-swap', '2g'"),old)
            self.assertIn('6g',diff);self.assertIn("'--cpus', '1'",text);self.assertNotIn('threads=',text)
        self.assertIn("'--memory', '2g'",inspect.getsource(B.ORIGINAL.native_journal))

    def test_explicit6g_journal_closes_all_three_and_old2g_reader_remains_strict(self):
        with tempfile.TemporaryDirectory() as d:
            path,args,rows=journal(Path(d));self.assertTrue(B.native_journal(path,**args)['passed'])
            with self.assertRaisesRegex(ValueError,'arguments'):B.ORIGINAL.native_journal(path,**args)
            for bad in (rows[:-1],rows[:2]+rows[4:],rows+rows[:2],list(reversed(rows))):
                path.write_text('\n'.join(json.dumps(r) for r in bad)+'\n')
                with self.assertRaises(ValueError):B.native_journal(path,**args)

    def test_wrong_memory_cpu_extra_swap_mode_or_flag_is_not_a_resource_alias(self):
        with tempfile.TemporaryDirectory() as d:
            path,args,rows=journal(Path(d));original=json.loads(json.dumps(rows))
            for flag,value in (('--memory','2g'),('--memory-swap','7g'),('--cpus','2')):
                bad=json.loads(json.dumps(original));a=bad[0]['argv'];a[a.index(flag)+1]=value;path.write_text('\n'.join(json.dumps(r) for r in bad)+'\n')
                with self.assertRaises(ValueError):B.native_journal(path,**args)
            bad=json.loads(json.dumps(original));bad[0]['argv']+=['-rd','run_mode=flat'];path.write_text('\n'.join(json.dumps(r) for r in bad)+'\n')
            with self.assertRaises(ValueError):B.native_journal(path,**args)

    def test_untyped_or_wrong_resource_native_config_rejects_before_subprocess(self):
        with tempfile.TemporaryDirectory() as d,patch.object(B.ORIGINAL.subprocess,'run') as run:
            p=Path(d)/'config.json'
            for row in ({},dict(schema='old',resource_policy=B.policy()),dict(schema='pinwheel.closure24-official-budget-native-config.v1',resource_policy=dict(B.policy(),cpus=2))):
                p.write_text(json.dumps(row))
                with self.assertRaises(ValueError):B.native_klayout(p,[])
            run.assert_not_called()

    def test_whole_controller_has_only_declared_resource_custody_deltas(self):
        text,diff=B.controller_source();old=B.pinned(B.CONTROLLER)
        normalized=text.replace('import streaming_8x4_closure24_official_budget as S','import streaming_tt_signoff as S')
        normalized=normalized.replace('\nSOURCE_ENTRIES = SOURCE_ENTRIES + (S.OWN, S.ENTRY, S.READER)\n','')
        normalized=normalized.replace("require(timeout==3600,'The one explicit resource replay requires its fixed3600second whole-precheck budget')","require(1<=timeout<=1800,'Official precheck exceeds bounded30minute allowance')")
        normalized=normalized.replace("source=inputs/'producer'/S.OWN","source=inputs/'producer/scripts/streaming_tt_signoff.py'")
        normalized=normalized.replace("image_id=runtime['image_id'],container_name=S.container_name(output),\n        schema='pinwheel.closure24-official-budget-native-config.v1',resource_policy=S.policy()))","image_id=runtime['image_id'],container_name=S.container_name(output)))")
        normalized=normalized.replace('pinwheel.closure24-official-budget-precheck-run.v1','pinwheel.closure24-official-precheck-run.v1').replace("official_support_commit=lock['support_commit'],resource_policy=S.policy(),","official_support_commit=lock['support_commit'],")
        self.assertEqual(normalized,old);self.assertTrue(diff)
        current=B.controller();self.assertIs(current.S.precheck_result,B.ORIGINAL.precheck_result);self.assertIs(current.S.cleanup,B.ORIGINAL.cleanup)
        for n in (B.OWN,B.ENTRY,B.READER):self.assertIn(n,current.SOURCE_ENTRIES)

    def test_full_nine_order_no_skip_and_whole_result_exit_gate_remain_unchanged(self):
        names=list(B.BASE.Q.OFFICIAL_CHECKS)
        def xml(order):return '<testsuites><testsuite name="Tiny Tapeout Prechecks">'+''.join('<testcase name="'+n+'" time="1" />' for n in order)+'</testsuite></testsuites>'
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'results.xml';path.write_text(xml(names));self.assertTrue(B.ORIGINAL.precheck_result(path,names,0)['passed'])
            for order in (names[:-1],names[::-1],names+[names[0]]):
                path.write_text(xml(order))
                with self.assertRaises(ValueError):B.ORIGINAL.precheck_result(path,names,0)
            path.write_text(xml(names).replace('name="'+names[0]+'" time="1" />','name="'+names[0]+'" time="1"><skipped /></testcase>'))
            with self.assertRaisesRegex(ValueError,'Unsupported/skipped'):B.ORIGINAL.precheck_result(path,names,0)

    def test_fixed_whole_budget_resources_and_one_fresh_attempt_are_explicit(self):
        p=B.policy();self.assertEqual((p['whole_precheck_seconds'],p['supervisor_seconds'],p['cpus'],p['memory_bytes'],p['memory_plus_swap_bytes']),(3600,3660,1,6*1024**3,6*1024**3))
        self.assertEqual((p['extra_swap_bytes'],p['maximum_attempts'],p['complete_selected_checks'],p['complete_Native_KLayout_calls']),(0,1,9,3))
        self.assertFalse(p['thread_mode_deck_support_flags_changed']);self.assertFalse(p['skipped_checks_or_partial_native_journal_allowed'])
        with tempfile.TemporaryDirectory() as d,patch.object(B,'verify',return_value=dict(output=d)),patch.object(B,'controller') as run:
            with self.assertRaises(ValueError):B.run(Path(d)/'plan.json')
            run.assert_not_called()

    def test_prior_memory_stop_identity_and_old_controller_namespaces_are_immutable(self):
        self.assertEqual(B.OLD_REPORT,'d62014b6dfe17ab47a1662a5f7c92a744048a285bbe6fea99e62553b238bbd02')
        self.assertEqual(B.OLD_GUARD,'abeecc53edb77728efa327a3f880c2dfec246e63b363a7e21de0bbb6f6bb4f02')
        original=B.BASE.S;new=B.controller();self.assertIs(B.BASE.S,original);self.assertIs(new.S,B)
        self.assertNotEqual(new.run_official.__globals__,B.BASE.run_official.__globals__)
        self.assertEqual(Path(new.run_official.__globals__['__file__']).resolve(),(B.ROOT/B.ENTRY).resolve())
        with patch.dict(B.PINS,{B.SIGNOFF:'0'*64}):
            with self.assertRaises(ValueError):B.native_source('native_klayout')

    def resource_fixture(self,root):
        paths={name:root/(name+'.json') for name in ('proposal','plan','view','old-report','old-resource','GO','resource')}
        for path in paths.values():path.write_text('{}')
        plan=dict(views_report=B.bound(paths['view']),prior_report=B.bound(paths['old-report']),prior_guard=B.bound(paths['old-resource']),producer_sha256={})
        proposal=dict(argv=['exact-worker'],plan=B.bound(paths['plan']));paths['proposal'].write_text(json.dumps(proposal))
        paths['GO'].write_text(json.dumps(dict(proposal_sha256=B.sha(paths['proposal']),physical_acceptance=False)))
        wrapper=B.ROOT/'scripts/streaming_8x4_closure24_resources.py';policy=B.ROOT/'scripts/streaming_8x4_closure24_policy.py';guard=B.ROOT/'scripts/streaming_tt_resources.py'
        boundary=dict(schema='pinwheel.streaming-8x4-closure24-resource-boundary.v1',campaign_id=R.P.CAMPAIGN,schedule=R.P.SCHEDULE,
            campaign_root=str(B.ROOT),campaign_kind='fixed_cad',shared_lease=R.P.shared_lease_paths(B.ROOT),campaign_directory=str(B.ROOT/'build/campaigns'/R.P.CAMPAIGN),
            frozen_parent=plan['views_report'],wrapper_path=str(wrapper),wrapper_sha256=B.sha(wrapper),policy_path=str(policy),policy_sha256=B.sha(policy),
            inherited_supervisor_path=str(guard),inherited_supervisor_sha256=B.sha(guard),historical_producer_sha256=R.P.historical_sources(B.ROOT),acceptance_claim=False,engineering_evidence_verified=False)
        seals={str(paths[n].resolve()):B.sha(paths[n]) for n in ('proposal','plan','GO','view','old-report','old-resource')}
        seals.update({str(wrapper):B.sha(wrapper),str(policy):B.sha(policy),**R.P.historical_sources(B.ROOT)})
        row=dict(schema='pinwheel.streaming-tt-resource-job.v1',argv=proposal['argv'],kind='cad-validation',timeout_seconds=3660,rss_mib=2048,
            cleanup_confirmed=True,inputs_unchanged=True,containers_remaining=[],owned_processes_remaining=[],cleanup_errors=[],validation_parent=plan['views_report'],
            campaign_boundary=boundary,supervisor_sha256=B.sha(guard),input_sha256=seals,status='completed',exit_code=0)
        return paths,plan,proposal,row

    def test_actual_resource_context_requires_shared_lease_parent_source_seals_and_clock(self):
        with tempfile.TemporaryDirectory() as d:
            paths,plan,proposal,row=self.resource_fixture(Path(d));paths['resource'].write_text(json.dumps(row))
            self.assertTrue(R.resource_join(paths['resource'],paths['proposal'],proposal,plan,paths['GO'],dict(passed=True))['cleanup_confirmed'])
            mutations=[lambda x:x.update(timeout_seconds=1860),lambda x:x.update(validation_parent={}),
                lambda x:x['campaign_boundary'].update(shared_lease={}),lambda x:x['campaign_boundary'].update(wrapper_path='/other/wrapper.py'),
                lambda x:x['input_sha256'].pop(str(paths['old-report'].resolve())),lambda x:x.update(cleanup_confirmed=False)]
            for mutate in mutations:
                bad=deepcopy(row);mutate(bad);paths['resource'].write_text(json.dumps(bad))
                with self.assertRaises(ValueError):R.resource_join(paths['resource'],paths['proposal'],proposal,plan,paths['GO'],dict(passed=True))

    def test_closed_resource_failure_cannot_promote_partial_official_checks(self):
        with tempfile.TemporaryDirectory() as d:
            paths,plan,proposal,row=self.resource_fixture(Path(d));row.update(status='stopped',exit_code=124,stop_reason='memory guard');paths['resource'].write_text(json.dumps(row))
            failed=R.resource_join(paths['resource'],paths['proposal'],proposal,plan,paths['GO'],dict(passed=False));self.assertEqual(failed['exit_code'],124)
            with self.assertRaises(ValueError):R.resource_join(paths['resource'],paths['proposal'],proposal,plan,paths['GO'],dict(passed=True))

if __name__=='__main__':unittest.main()
