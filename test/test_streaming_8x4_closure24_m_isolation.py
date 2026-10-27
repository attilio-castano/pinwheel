"""Portable process barrier/body/ownership controls; no Lean or regeneration."""
import ast
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_m_isolation as I
import streaming_8x4_closure24_isolated_m_execute as X
import streaming_8x4_closure24_m_assignment_diagnostic as D
import streaming_8x4_closure24_m_process as P


def function(text,name):return next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef)and n.name==name)


def native_original():
    text=Path(I.PRIOR.ORIGINAL.__file__).read_text();node=function(text,'compile_one')
    return ''.join(text.splitlines(True)[node.lineno-1:node.end_lineno])


def process_rows(*,child=True):
    rows={10:dict(pid=10,ppid=1,pgid=10,rss_kib=100,birth='Sat Oct 24 19:00:00 2026',command='/actual/Python.app/Contents/MacOS/Python -B driver.py')}
    if child:rows[20]=dict(pid=20,ppid=10,pgid=20,rss_kib=200,birth='Sat Oct 24 19:01:00 2026',command='/exact/lean -M4096 -j1 source.lean')
    for row in rows.values():row['observed_executable']=exe_fixture(row['command'])
    return rows


def exe_fixture(command):
    token=command.split()[0];return dict(path=token,resolved=token,sha256='a'*64)


def memory_fixture(path,*,child=True):
    argv=['/exact/lean','-M4096','-j1','source.lean'];rows=process_rows(child=child)
    records=[dict(event='start',label='Exact',parent_pid=10,child_pid=20,argv=argv),
        dict(event='sample',label='Exact',seconds=.1,processes={str(k):v for k,v in rows.items()},
            parent_and_child_rss_kib=300 if child else None,missing_pids=[]if child else[20]),
        dict(event='finish',label='Exact',samples=1,child_samples=int(child),child_birth_observed=child,
            maximum_observed_parent_and_child_rss_kib=300 if child else None,error=None)]
    path.write_text('\n'.join(json.dumps(row)for row in records)+'\n');return records,[('Exact',argv)]


class IsolationControls(unittest.TestCase):
    def setUp(self):
        self.executable=patch.object(P,'executable_identity',side_effect=exe_fixture);self.executable.start();self.addCleanup(self.executable.stop)

    def test_canonical_compiler_body_and_native_journal_are_identical_except_observer(self):
        text=I.compile_source()
        text=text.replace(';memory_watch=None','').replace("            memory_watch=PROCESS.start(child.pid,argv,journal.parent/'process-memory.jsonl',label=module)\n",'').replace('        PROCESS.finish(memory_watch)\n','')
        self.assertEqual(text,native_original())
        self.assertEqual(ast.dump(function(text,'compile_one')),ast.dump(function(native_original(),'compile_one')))
        for name in ('native_argv','imports','verify_imports','observe_foundation_runtime','runtime_identity',
                'private_texts','verify_private_import_inventory','command_timeout','budget_policy'):
            self.assertIs(getattr(X,name),getattr(I.PRIOR,name),name)
        self.assertEqual(X.budget_policy(),I.PRIOR.budget_policy())

    def test_exact_full_child_derivation_precedes_parent_verify_and_native_loop(self):
        text,_=I.controller_source();positive=function(text,'positive');body=ast.unparse(positive)
        self.assertNotIn('rederive=True',body)
        self.assertLess(body.index('ISOLATION.run_rederive'),body.index('M.verify(prepared, rederive=False)'))
        self.assertLess(body.index('M.verify(prepared, rederive=False)'),body.index('for index, row in enumerate(rows)'))
        child=function(Path(I.__file__).read_text(),'rederive');calls=[n for n in ast.walk(child)if isinstance(n,ast.Call)and isinstance(n.func,ast.Attribute)and n.func.attr=='verify'and isinstance(n.func.value,ast.Name)and n.func.value.id=='M']
        self.assertEqual([next(k.value.value for k in n.keywords if k.arg=='rederive')for n in calls],[False,True])
        self.assertIn('checked == record and expected == manifest',ast.unparse(child))
        self.assertIn('stage_membership(manifest, completed=False)',ast.unparse(function(Path(I.__file__).read_text(),'run_rederive')))

    def test_positive_private_complete_algorithms_normalize_to_exact_frozen_bodies(self):
        old,_=I.SCOPE.controller_source('execution');new,_=I.controller_source()
        normalized=new.replace('pinwheel.closure24-isolated-actual-M-positive.v1','pinwheel.closure24-scope-actual-M-positive.v1').replace('pinwheel.closure24-isolated-actual-M-private.v1','pinwheel.closure24-scope-actual-M-private.v1')
        normalized=normalized.replace("        admission=ISOLATION.run_rederive(prepared,output/'rederivation')\n        report['rederivation_admission']=admission;save(path,report)\n        record,manifest=M.verify(prepared,rederive=False);dep=D.verify(record['source_N']['path'])",
            "        record,manifest=M.verify(prepared,rederive=True);dep=D.verify(record['source_N']['path'])")
        removed=["        ISOLATION.verify_rederive(admission['report']['path'],prepared)\n",
            "        report['driver_process']=ISOLATION.PROCESS.snapshot((os.getpid(),))[os.getpid()];save(path,report)\n",
            "    report['driver_process']=ISOLATION.PROCESS.snapshot((os.getpid(),))[os.getpid()]\n",
            "        report['process_memory']=bound(output/'process-memory.jsonl');ISOLATION.verify_memory(report)\n",
            "    F.require(ISOLATION.verify_rederive(record['rederivation_admission']['report']['path'],record['prepared']['path'])==record['rederivation_admission'],'Complete isolated rederivation admission changed')\n",
            "    ISOLATION.verify_memory(record)\n"]
        for text in removed:normalized=normalized.replace(text,'')
        for name in ('positive','private','verify_positive','verify_private','generated_roots_owned'):
            self.assertEqual(ast.dump(function(normalized,name)),ast.dump(function(old,name)),name)
        self.assertEqual(I.REDERIVE_SECONDS,600)

    def test_new_body_globals_and_sources_are_separate_without_loading_generator(self):
        # This hash/body control supplies an identity; committed admission is separate.
        self.assertIs(X.M,I.M);self.assertIsNot(X.positive,I.PRIOR.positive)
        self.assertIs(X.positive.__globals__['ISOLATION'],I)
        self.assertNotIn('ISOLATION',I.PRIOR.positive.__globals__)
        self.assertEqual(Path(X.source_seal.__globals__['__file__']).resolve(),Path(X.__file__).resolve())
        seal=I.sources(commit='a'*40);self.assertEqual(len(seal['sha256']),len(set(seal['sha256'])))
        for name in (I.OWN,I.ENTRY,I.OBSERVER,I.DIAGNOSTIC):self.assertIn(name,seal['sha256'])
        self.assertNotIn('_streaming8_actual_M_generator',sys.modules)
        with self.assertRaises(ValueError):I.sources(commit='not-an-immutable-commit')

    def test_ps_parser_preserves_actual_birth_command_and_kernel_RSS(self):
        output='10 1 10 100 Sat Oct 24 19:00:00 2026 /actual/Python.app/Contents/MacOS/Python -B driver.py\n20 10 20 200 Sat Oct 24 19:01:00 2026 /exact/lean -M4096 -j1 source.lean\n'
        with patch.object(P.subprocess,'run',return_value=SimpleNamespace(returncode=0,stdout=output,stderr='')) as call:
            self.assertEqual(P.snapshot((10,20)),process_rows());self.assertIn('-ww',call.call_args.args[0])
        with patch.object(P.subprocess,'run',return_value=SimpleNamespace(returncode=1,stdout='',stderr='Operation not permitted')):
            with self.assertRaises(ValueError):P.snapshot((10,20))

    def test_process_lifetime_and_command_changes_reject_not_reconstructed(self):
        rows=process_rows();births={};argv=['/exact/lean','-M4096','-j1','source.lean']
        self.assertEqual(P.validate_sample(rows,10,20,argv,births),300)
        for change in (lambda x:x[20].update(birth='different lifetime'),lambda x:x[20].update(command='/other/lean wrong.lean'),
                lambda x:x[20].update(ppid=99),lambda x:x[20].update(pgid=99),lambda x:x.pop(10)):
            bad=deepcopy(rows);change(bad)
            with self.assertRaises(ValueError):P.validate_sample(bad,10,20,argv,dict(births))

    def test_memory_reopener_requires_complete_order_and_rederives_aggregates(self):
        with tempfile.TemporaryDirectory()as d:
            path=Path(d)/'memory.jsonl';rows,commands=memory_fixture(path)
            self.assertEqual(P.verify(path,commands,require_child_observed=True)['observations'][0]['maximum_observed_parent_and_child_rss_kib'],300)
            for change in (lambda x:x[1].update(parent_and_child_rss_kib=0),lambda x:x[2].update(samples=0),
                    lambda x:x[2].update(error='observer failed'),lambda x:x.pop(2),lambda x:x.reverse()):
                bad=deepcopy(rows);change(bad);path.write_text('\n'.join(json.dumps(x)for x in bad)+'\n')
                with self.assertRaises((ValueError,KeyError)):P.verify(path,commands)

    def test_short_lived_child_absence_is_unknown_never_zero_or_fabricated_birth(self):
        with tempfile.TemporaryDirectory()as d:
            path=Path(d)/'memory.jsonl';_,commands=memory_fixture(path,child=False);row=P.verify(path,commands)
            self.assertIsNone(row['observations'][0]['maximum_observed_parent_and_child_rss_kib'])
            self.assertEqual(row['observations'][0]['child_samples'],0)
            with self.assertRaises(ValueError):P.verify(path,commands,require_child_observed=True)

    def test_child_reopen_rejects_partial_wrong_target_context_or_owned_process(self):
        with tempfile.TemporaryDirectory()as d:
            out=Path(d);childdir=out/'rederivation';childdir.mkdir();path=childdir/'report.json'
            (out/'rederivation.log').write_text('complete derivation only\n');(out/'rederivation-memory.jsonl').write_text('bound observations\n')
            prepared=out/'prepared.json';prepared.write_text('{}');producer=dict(commit='a'*40,sha256={})
            record=dict(actual_odb=dict(path='ODB',sha256='b'*64),physical_candidate={'candidate':'B'},generation_manifest={'path':'manifest','sha256':'c'*64},source_worker_context={'exact':'original/restored-config'})
            manifest=dict(m_rows=[{},{}]);runtime=dict(foundation=dict(files=14923),tools={'actual':'pinned'})
            child=dict(schema='pinwheel.closure24-M-rederivation-child.v1',passed=True,complete_independent_rederivation=True,
                prepared=I.bound(prepared),producer=producer,all_actual_modules=2,actual_odb=record['actual_odb'],physical_candidate=record['physical_candidate'],
                generation_manifest=record['generation_manifest'],source_worker_context=record['source_worker_context'],input_sha256={'exact':'seals'},
                runtime_before=runtime,runtime_after=runtime,Native_Lean_executed=False,full_positive_proved=False,physical_acceptance=False,
                python=dict(I.python_identity(),optimize=0),
                argv=I.rederive_argv(prepared,childdir),pid=42,pgid=42)
            own=dict(pid=42,ppid=41,pgid=42,rss_kib=500,birth='Sat Oct 24 19:01:00 2026',command=' '.join(child['argv']))
            own['observed_executable']=exe_fixture(own['command']);child['self_process']=own
            process=dict(schema='pinwheel.closure24-M-rederivation-process.v1',argv=child['argv'],cwd=str(I.ROOT),pid=42,exit_code=0,
                timed_out=False,process_group_closed=True,observer_error=None,timeout_seconds=600,log=I.bound(out/'rederivation.log'),memory_journal=I.bound(out/'rederivation-memory.jsonl'))
            with patch.object(I.M,'verify',return_value=(record,manifest)),patch.object(I,'sources',return_value=producer),patch.object(I,'input_seal',return_value={'exact':'seals'}),\
                    patch.object(I,'current_runtime_binding',return_value=runtime),patch.object(I.PROCESS,'verify',return_value=dict(parent_pid=41,observations=[dict(child_lifetime=P.lifetime(own))])),\
                    patch.object(I,'python_identity',return_value=dict(I.python_identity(),optimize=0)):
                path.write_text(json.dumps(child));(out/'rederivation-process.json').write_text(json.dumps(process))
                self.assertTrue(I.verify_rederive(path,prepared)['child_closed_before_Lean'])
                for change in (lambda c,p:c.update(all_actual_modules=1),lambda c,p:c.update(source_worker_context={}),lambda c,p:c.update(actual_odb={}),
                        lambda c,p:c.update(input_sha256={}),lambda c,p:p.update(process_group_closed=False),lambda c,p:p.update(pid=43),
                        lambda c,p:p.update(exit_code=124),lambda c,p:p.update(observer_error='unknown'),
                        lambda c,p:c.update(runtime_after={}),lambda c,p:c.update(full_positive_proved=True),
                        lambda c,p:c['self_process'].update(birth='reconstructed wrong lifetime')):
                    a,b=deepcopy(child),deepcopy(process);change(a,b);path.write_text(json.dumps(a));(out/'rederivation-process.json').write_text(json.dumps(b))
                    with self.assertRaises(ValueError):I.verify_rederive(path,prepared)

    def test_barrier_waits_for_child_and_group_close_before_admission(self):
        with tempfile.TemporaryDirectory()as d:
            root=Path(d);prepared=root/'prepared.json';prepared.write_text('{}');events=[]
            class Child:
                pid=20
                def wait(self,timeout):events.append(('wait',timeout));return 0
                def poll(self):return 0
            with patch.object(I.M,'verify',return_value=({},{})),patch.object(I.PRIOR,'stage_membership'),\
                    patch.object(I.subprocess,'Popen',return_value=Child()),patch.object(I.PROCESS,'start',side_effect=lambda *a,**k:events.append(('observe',))or object()),\
                    patch.object(I.PROCESS,'finish',side_effect=lambda w:events.append(('observer-close',))),\
                    patch.object(I.PRIOR.F,'closed_group',side_effect=lambda pid:events.append(('group-close',pid))or True),\
                    patch.object(I,'verify_rederive',side_effect=lambda *a:events.append(('admit',))or {'passed':True}):
                self.assertTrue(I.run_rederive(prepared,root/'rederivation')['passed'])
            self.assertLess(events.index(('wait',600)),events.index(('group-close',20)))
            self.assertLess(events.index(('group-close',20)),events.index(('admit',)))
            self.assertLess(events.index(('observer-close',)),events.index(('admit',)))

    def test_prefix_stage_rejection_prevents_rederivation_or_any_child_launch(self):
        with tempfile.TemporaryDirectory()as d:
            root=Path(d)
            with patch.object(I.M,'verify',return_value=({},{})),patch.object(I.PRIOR,'stage_membership',side_effect=ValueError('cached prefix')),\
                    patch.object(I.subprocess,'Popen')as launch:
                with self.assertRaisesRegex(ValueError,'cached prefix'):I.run_rederive(root/'prepared.json',root/'rederivation')
                launch.assert_not_called()

    def test_unclosed_child_or_timeout_cannot_admit_even_if_other_steps_finish(self):
        with tempfile.TemporaryDirectory()as d:
            root=Path(d)
            class Child:
                pid=20
                def __init__(self):self.calls=0
                def wait(self,timeout):
                    self.calls+=1
                    if self.calls==1:raise subprocess.TimeoutExpired('exact-rederivation',timeout)
                    return 0
                def poll(self):return 0
            with patch.object(I.M,'verify',return_value=({},{})),patch.object(I.PRIOR,'stage_membership'),\
                    patch.object(I.subprocess,'Popen',return_value=Child()),patch.object(I.PROCESS,'start',return_value=object()),\
                    patch.object(I.PROCESS,'finish'),patch.object(I.PRIOR.F,'terminate_group',return_value=True),\
                    patch.object(I.PRIOR.F,'closed_group',return_value=True),patch.object(I,'verify_rederive')as admit:
                with self.assertRaises(ValueError):I.run_rederive(root/'prepared.json',root/'rederivation')
                admit.assert_not_called()
            receipt=json.loads((root/'rederivation-process.json').read_text())
            self.assertEqual(receipt['exit_code'],124);self.assertTrue(receipt['timed_out']);self.assertTrue(receipt['process_group_closed'])

    def test_declared_python_payload_and_observed_Python_app_are_separate_witnesses(self):
        declared=I.python_identity();self.assertEqual(declared['path'],sys.executable)
        self.assertEqual(declared['resolved'],str(Path(sys.executable).resolve()));self.assertEqual(len(declared['sha256']),64)
        actual='/different/Framework/Python.app/Contents/MacOS/Python -B exact-child.py'
        self.assertTrue(P.argv_matches(actual,['/declared/bin/python','-B','exact-child.py']))
        self.assertFalse(P.argv_matches(actual,['/declared/bin/python','-O','exact-child.py']))
        self.assertNotEqual(exe_fixture(actual)['path'],'/declared/bin/python')

    def test_exact_diagnostic_changes_only_new_object_destination_and_never_import_roots(self):
        argv=['/exact/lean','-M4096','-j1','-DElab.async=false','--root=/old/M/all','-DwarningAsError=true','-DmaxErrors=1','-o','/old/M/all/PhysicalCoreAssignment.olean','/old/M/all/PhysicalCoreAssignment.lean']
        plan=dict(context=dict(original_argv=argv,roots=['/old/M/all']),output='/new/sibling/diagnostic')
        changed=D.command(plan);self.assertEqual([i for i,(a,b)in enumerate(zip(argv,changed))if a!=b],[8])
        self.assertEqual(changed[8],'/new/sibling/diagnostic/PhysicalCoreAssignment.olean')
        self.assertEqual(D.policy()['aggregate_rss_mib'],4096);self.assertEqual(D.policy()['leaf_seconds'],180)
        self.assertFalse(D.policy()['object_may_enter_any_acceptance_import_root'])
        for bad in (dict(plan,output='/old/M/all/diagnostic'),dict(plan,context=dict(plan['context'],original_argv=[x.replace('-M4096','-M8192')for x in argv]))):
            with self.assertRaises(ValueError):D.command(bad)


if __name__=='__main__':unittest.main()
