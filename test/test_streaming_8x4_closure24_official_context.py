"""Portable authority/producer separation and staged-wrapper HOST controls."""
import ast
from copy import deepcopy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_official_context as C
import streaming_8x4_closure24_official_context_readback as R


def function(text,name):return next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name==name)


class OfficialContextControls(unittest.TestCase):
    def test_actual_membership_predicate_reproduces_old_failure_and_keeps_two_contexts(self):
        f=function(C.OLD.pinned(C.OLD.CONTROLLER),'verify_views_preparation')
        claim=next(n for n in f.body if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call)
            and any(isinstance(a,ast.Constant) and a.value=='Final view producer dependency membership differs' for a in n.value.args))
        args=ast.arguments(posonlyargs=[],args=[ast.arg(arg=n) for n in ('SOURCE_ENTRIES','packet','dependency_closure','require','P')],kwonlyargs=[],kw_defaults=[],defaults=[])
        tree=ast.fix_missing_locations(ast.Module(body=[ast.FunctionDef(name='check',args=args,body=[deepcopy(claim)],decorator_list=[])],type_ignores=[]))
        env={};exec(compile(tree,'<actual-view-membership-predicate>','exec'),env)
        authority=tuple('authority'+str(i) for i in range(65));old=authority+('old-helper','old-entry','old-reader');fresh=old+('context-helper','context-entry','context-reader')
        packet=dict(producer_dependency_closure=dict(files=list(authority)),producer_sha256={n:'a'*64 for n in authority})
        closure=lambda root,entries:dict(files=list(entries));p=SimpleNamespace(ROOT='same-root')
        for entries in (old,fresh):
            with self.assertRaisesRegex(ValueError,'dependency membership'):env['check'](entries,packet,closure,C.need,p)
        env['check'](authority,packet,closure,C.need,p)
        module=C.controller();self.assertIs(module.closed_views,C.OLD.BASE.closed_views)
        self.assertIs(module.closed_views.__globals__,C.OLD.BASE.__dict__)
        self.assertEqual(len(C.OLD.dependency_closure(C.ROOT,C.OLD.BASE.SOURCE_ENTRIES)['files']),65)
        self.assertEqual(len(C.OLD.dependency_closure(C.ROOT,module.SOURCE_ENTRIES)['files']),71)

    def test_whole_controller_changes_only_owner_schema_and_authority_callback(self):
        text,diff=C.controller_source();old,_=C.OLD.controller_source()
        normalized=text.replace('import streaming_8x4_closure24_official_context as S','import streaming_8x4_closure24_official_budget as S')
        normalized=normalized.replace('SOURCE_ENTRIES = SOURCE_ENTRIES + (S.OLD.OWN, S.OLD.ENTRY, S.OLD.READER, S.OWN, S.ENTRY, S.READER)','SOURCE_ENTRIES = SOURCE_ENTRIES + (S.OWN, S.ENTRY, S.READER)')
        normalized=normalized.replace('# Prior views retain their exact immutable65-source authority namespace.\nclosed_views = S.OLD.BASE.closed_views\n\n','')
        normalized=normalized.replace('pinwheel.closure24-official-context-precheck-run.v1','pinwheel.closure24-official-budget-precheck-run.v1')
        self.assertEqual(normalized,old);self.assertTrue(diff)
        for name in ('run_official','stage_producer','unchanged_producer'):
            if name=='unchanged_producer':continue
            self.assertEqual(ast.dump(function(normalized,name)),ast.dump(function(old,name)))

    def test_runpy_dictionary_explicitly_exports_unchanged6g_functions(self):
        import runpy
        row=runpy.run_path(str(C.ROOT/C.OWN));self.assertIs(row['native_klayout'],C.OLD.native_klayout);self.assertIs(row['native_journal'],C.OLD.native_journal)
        self.assertEqual(C.policy(),C.OLD.policy());self.assertEqual(C.policy()['memory_bytes'],6*1024**3)

    def test_exact_staged_wrapper_import_path_under_clean_HOST_process(self):
        # This temporary unittest fixture is not stage_producer and never
        # launches its returned function. Actual execution retains Git-first.
        with tempfile.TemporaryDirectory() as d:
            root=Path(d).resolve();_,files=C.sources()
            for name in files:
                dest=root/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(C.ROOT/name,dest)
            code='''import runpy,sys,json
from pathlib import Path
source=Path(sys.argv[1]);sys.path.insert(0,str(source.parent));m=runpy.run_path(str(source))
f=m["native_klayout"];r=m["native_journal"]
assert Path(f.__globals__["ROOT"]).resolve()==source.parents[1].resolve()
assert f is sys.modules["streaming_8x4_closure24_official_budget"].native_klayout
print(json.dumps(dict(explicit_function_keys=True,staged_import_root=True,Native_started=False)))
'''
            result=subprocess.run([sys.executable,'-I','-B','-c',code,str(root/C.OWN)],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr);self.assertEqual(json.loads(result.stdout),dict(explicit_function_keys=True,staged_import_root=True,Native_started=False))

    def test_reader_has_only_new_context_binding_without_any_resource_or_fullcheck_weakening(self):
        text,diff=C.reader_source();old=(C.ROOT/C.OLD.READER).read_text()
        normalized=text.replace('import streaming_8x4_closure24_official_context as B','import streaming_8x4_closure24_official_budget as B')
        normalized=normalized.replace("    required.update({entry['path']:entry['sha256'] for entry in plan['pre_native_failure']['evidence'].values()})\n",'')
        normalized=normalized.replace(" and report['prior_context_failure']==plan['pre_native_failure']",'')
        normalized=normalized.replace('pinwheel.closure24-official-context-precheck-run.v1','pinwheel.closure24-official-budget-precheck-run.v1').replace('pinwheel.closure24-official-context-independent-readback.v1','pinwheel.closure24-official-budget-independent-readback.v1')
        normalized=normalized.replace("prior_context_failure=plan['pre_native_failure'],",'')
        self.assertEqual(normalized,old);self.assertTrue(diff);self.assertIs(R.B,C)
        self.assertIs(C.OLD.ORIGINAL.precheck_result,C.ORIGINAL.precheck_result)

    def test_frozen_old68_source_policy_and_old_namespace_are_preserved(self):
        before=C.OLD.BASE.SOURCE_ENTRIES;old=C.OLD.controller();new=C.controller()
        self.assertIsNot(old.closed_views,C.OLD.BASE.closed_views);self.assertIs(new.closed_views,C.OLD.BASE.closed_views)
        self.assertEqual(C.OLD.BASE.SOURCE_ENTRIES,before);self.assertEqual(len(C.sources()[1]),71)
        self.assertEqual(Path(new.run_official.__globals__['__file__']).resolve(),(C.ROOT/C.ENTRY).resolve())
        with patch.dict(C.PINS,{C.OLD.OWN:'0'*64}):
            with self.assertRaises(ValueError):C.controller_source()

    def test_prior_failure_has_no_output_and_exact_source_seals(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d).resolve();prep=root/'prep';prep.mkdir();planpath=prep/'plan.json';planpath.write_text('{}')
            proposal=root/'final24-official-budget-command-proposal-03.json';proposal.write_text(json.dumps(dict(argv=['exact-old-worker'])))
            launcher=root/'final24-official-budget-launch-reopen-03.json';launcher.write_text('{}')
            failed=root/'failed';failed.mkdir();resource=failed/'report.json';log=failed/'native.log';log.write_text('preserved HOST membership failure')
            plan=dict(producer_sha256={},output=str(root/'absent-Native-output'))
            row=dict(status='failed',exit_code=1,cleanup_confirmed=True,inputs_unchanged=True,containers_remaining=[],owned_processes_remaining=[],cleanup_errors=[],argv=['exact-old-worker'],input_sha256={str(planpath):C.sha(planpath)})
            resource.write_text(json.dumps(row))
            with patch.object(C.OLD,'verify',return_value=plan),patch.multiple(C,PRIOR_PLAN=C.sha(planpath),PRIOR_FAILURE=C.sha(resource),PRIOR_LOG=C.sha(log),PRIOR_PROPOSAL=C.sha(proposal),PRIOR_LAUNCHER=C.sha(launcher)):
                _,binding=C.previous_context(planpath,resource);self.assertFalse(binding['prior_Native_KLayout_started']);self.assertFalse(binding['prior_output_created'])
                Path(plan['output']).mkdir()
                with self.assertRaisesRegex(ValueError,'created an output'):C.previous_context(planpath,resource)
            Path(plan['output']).rmdir();row['input_sha256'].clear();resource.write_text(json.dumps(row))
            with patch.object(C.OLD,'verify',return_value=plan),patch.multiple(C,PRIOR_PLAN=C.sha(planpath),PRIOR_FAILURE=C.sha(resource),PRIOR_LOG=C.sha(log),PRIOR_PROPOSAL=C.sha(proposal),PRIOR_LAUNCHER=C.sha(launcher)):
                with self.assertRaisesRegex(ValueError,'source actual resource seals'):C.previous_context(planpath,resource)

    def test_one_fresh_attempt_and_commit_first_stage_body_stay_unchanged(self):
        with tempfile.TemporaryDirectory() as d,patch.object(C,'verify',return_value=dict(output=d)),patch.object(C,'controller') as native:
            with self.assertRaises(ValueError):C.run(Path(d)/'plan.json')
            native.assert_not_called()
        old,_=C.OLD.controller_source();new,_=C.controller_source()
        self.assertEqual(ast.dump(function(old,'stage_producer')),ast.dump(function(new,'stage_producer')))
        self.assertIn("subprocess.check_output(['git','show',head+':'+name]",new)

if __name__=='__main__':unittest.main()
