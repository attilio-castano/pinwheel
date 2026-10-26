"""Portable actual Rs/(lean) regression and complete-M context controls."""
import ast
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_m_process_state as OLD
import streaming_8x4_closure24_m_process_comm as P
import streaming_8x4_closure24_m_state_isolation as OLDI
import streaming_8x4_closure24_m_comm_isolation as I
import streaming_8x4_closure24_comm_m_execute as X

ARGV=['/exact/lean','-M4096','-j1','source.lean']
BIRTH='Sat Oct 24 17:22:45 2026'
PARENT='/exact/Python.app/Contents/MacOS/Python -B driver.py'


def exe(command):
    path=command.split()[0]
    if not Path(path).is_absolute():raise ValueError('Observed LIVE executable path is not absolute')
    return dict(path=path,resolved=path,sha256='a'*64)


def raw(command=None,state='Rs',*,child=True,parent_command=PARENT,birth=BIRTH,rss=485264):
    # Exact field values/state/comm from lifecycle-positive01 raw journal
    # SHA4813b218..., final ps-raw at2.035658s. Literals avoid ignored-build
    # dependencies in a clean checkout. Paths/PIDs are compact test fixtures.
    lines=[f'10 1 10 514368 {BIRTH} Ss {parent_command}']
    if child:lines.append(f'20 10 20 {rss} {birth} {state} '+(command or' '.join(ARGV)))
    return dict(argv=P.ps_argv((10,20)),returncode=0,stdout='\n'.join(lines)+'\n',stderr='',error=None)


def write_memory(path,raws,argv=ARGV):
    records=[dict(event='start',label='Exact',parent_pid=10,child_pid=20,argv=argv)]
    tracked={};children=0;zombies=0;fallbacks=0;maximum=None
    for i,capture in enumerate(raws):
        records.append(dict(event='ps-raw',label='Exact',seconds=i*.1,**capture))
        rows=P.parse(capture,(10,20));total=P.validate_sample(rows,10,20,argv,tracked)
        dead=20 in rows and rows[20]['state'].startswith('Z')
        fallback=20 in rows and rows[20]['command_metadata']=='kernel-comm-fallback'
        children+=int(20 in rows and rows[20]['argv_identity_known']);zombies+=int(dead);fallbacks+=int(fallback)
        if total is not None:maximum=total if maximum is None else max(maximum,total)
        records.append(dict(event='sample',label='Exact',seconds=i*.1,processes={str(k):v for k,v in rows.items()},
            parent_and_child_rss_kib=total,missing_pids=[pid for pid in(10,20)if pid not in rows],
            defunct_child_observed=dead,kernel_comm_fallback_child_observed=fallback))
    records.append(dict(event='finish',label='Exact',samples=len(raws),child_samples=children,zombie_child_samples=zombies,
        kernel_comm_fallback_child_samples=fallbacks,child_birth_observed=20 in tracked,
        maximum_observed_parent_and_child_rss_kib=maximum,error=None))
    path.write_text('\n'.join(json.dumps(row)for row in records)+'\n');return records


def function(text,name):return next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef)and n.name==name)


class CommControls(unittest.TestCase):
    def setUp(self):
        self.stub=patch.object(P,'executable_identity',side_effect=exe);self.stub.start();self.addCleanup(self.stub.stop)

    def test_actual_live_comm_reproduces_old_error_and_retains_unknown_metadata(self):
        with patch.object(OLD,'executable_identity',side_effect=exe):
            with self.assertRaisesRegex(ValueError,'not absolute'):OLD.parse(raw('(lean)'),(10,20))
        row=P.parse(raw('(lean)'),(10,20))[20]
        self.assertEqual(row['state'],'Rs');self.assertEqual(row['command'],'(lean)');self.assertEqual(row['rss_kib'],485264)
        self.assertEqual(row['kernel_comm'],'lean');self.assertFalse(row['argv_identity_known'])
        self.assertIsNone(row['observed_executable']);self.assertIsNone(row['active_rss_kib'])

    def test_full_to_fallback_to_full_allows_R_S_and_keeps_known_identity_separate(self):
        tracked={}
        for value in [raw(),raw('(lean)',state='S'),raw(state='R+')]:
            rows=P.parse(value,(10,20));P.validate_sample(rows,10,20,ARGV,tracked)
        self.assertEqual(tracked[20]['active_identity']['command'],' '.join(ARGV))
        self.assertFalse(tracked[20]['zombie_seen'])

    def test_fallback_only_is_unknown_and_not_long_child_identity_coverage(self):
        with tempfile.TemporaryDirectory()as d:
            p=Path(d)/'memory.jsonl';write_memory(p,[raw('(lean)'),raw(child=False)])
            result=P.verify(p,[('Exact',ARGV)])['observations'][0]
            self.assertEqual(result['child_samples'],0);self.assertEqual(result['kernel_comm_fallback_child_samples'],1)
            self.assertIsNone(result['child_active_identity']);self.assertIsNone(result['maximum_observed_parent_and_child_rss_kib'])
            with self.assertRaises(ValueError):P.verify(p,[('Exact',ARGV)],require_child_observed=True)

    def test_full_fallback_full_independent_raw_reopen_counts_only_full_samples(self):
        with tempfile.TemporaryDirectory()as d:
            p=Path(d)/'memory.jsonl';write_memory(p,[raw(),raw('(lean)'),raw()])
            row=P.verify(p,[('Exact',ARGV)],require_child_observed=True)['observations'][0]
            self.assertEqual(row['child_samples'],2);self.assertEqual(row['kernel_comm_fallback_child_samples'],1)
            self.assertEqual(row['zombie_child_samples'],0);self.assertEqual(row['maximum_observed_parent_and_child_rss_kib'],999632)

    def test_wrong_comm_relative_live_parent_fallback_and_lifetime_drift_reject(self):
        for capture in [raw('(other)'),raw('lean source.lean'),raw('(lean)',parent_command='(Python)'),
                raw('(lean)',birth='Sat Oct 24 17:22:46 2026')]:
            tracked={};P.validate_sample(P.parse(raw(),(10,20)),10,20,ARGV,tracked)
            with self.assertRaises(ValueError):P.validate_sample(P.parse(capture,(10,20)),10,20,ARGV,tracked)
        for field in ('ppid','pgid'):
            rows=P.parse(raw('(lean)'),(10,20));rows[20][field]+=1
            with self.assertRaises(ValueError):P.validate_sample(rows,10,20,ARGV,{})

    def test_full_identity_cannot_change_across_unknown_fallback(self):
        tracked={}
        for capture in [raw(),raw('(lean)')]:P.validate_sample(P.parse(capture,(10,20)),10,20,ARGV,tracked)
        for capture in [raw('/different/lean -M4096 -j1 source.lean'),raw('/exact/lean -M4096 -j1 changed.lean')]:
            with self.assertRaises(ValueError):P.validate_sample(P.parse(capture,(10,20)),10,20,ARGV,deepcopy(tracked))

    def test_Z_remains_terminal_and_retains_distinct_unknown_memory(self):
        tracked={};rows=P.parse(raw('<defunct>',state='Z',rss=0),(10,20))
        P.validate_sample(rows,10,20,ARGV,tracked);self.assertEqual(rows[20]['command_metadata'],'zombie')
        for capture in [raw('(lean)'),raw()]:
            with self.assertRaises(ValueError):P.validate_sample(P.parse(capture,(10,20)),10,20,ARGV,deepcopy(tracked))

    def test_Python_redirect_fallback_is_role_only_and_needs_actual_parent_app_witness(self):
        argv=['/exact/bin/python3.13','-B','child.py']
        rows=P.parse(raw('(Python)'),(10,20));P.validate_sample(rows,10,20,argv,{})
        self.assertIsNone(rows[20]['observed_executable'])
        with self.assertRaises(ValueError):
            P.validate_sample(P.parse(raw('(Python)',parent_command='/exact/bin/python3.13 -B driver.py'),(10,20)),10,20,argv,{})
        with self.assertRaises(ValueError):P.validate_sample(rows,10,20,['/exact/bash','child.py'],{})

    def test_reader_rejects_forged_expected_identity_zero_RSS_and_wrong_counters(self):
        with tempfile.TemporaryDirectory()as d:
            p=Path(d)/'memory.jsonl';records=write_memory(p,[raw('(lean)')])
            for change in [lambda r:r[2]['processes']['20'].update(observed_executable=exe('/exact/lean')),
                    lambda r:r[2]['processes']['20'].update(active_rss_kib=0),
                    lambda r:r[-1].update(child_samples=1),lambda r:r[2].update(parent_and_child_rss_kib=999632),
                    lambda r:r[1].update(stdout=r[1]['stdout'].replace('(lean)','(other)'))]:
                value=deepcopy(records);change(value);p.write_text('\n'.join(json.dumps(r)for r in value)+'\n')
                with self.assertRaises(ValueError):P.verify(p,[('Exact',ARGV)])

    def test_bad_live_observation_raw_is_durable_before_failure(self):
        with tempfile.TemporaryDirectory()as d:
            p=Path(d)/'memory.jsonl';capture=raw('relative-live-command')
            with patch.object(P.os,'getpid',return_value=10),patch.object(P,'capture',return_value=capture):
                watch=P.start(20,ARGV,p,label='Exact');watch.thread.join(timeout=1)
                with self.assertRaises(ValueError):P.finish(watch)
            records=[json.loads(s)for s in p.read_text().splitlines()]
            self.assertEqual(records[1]['stdout'],capture['stdout']);self.assertEqual(records[2]['event'],'observer-error')

    def test_operational_globals_and_sources_are_fresh_without_old_mutation(self):
        for name in ('rederive','run_rederive','verify_rederive','verify_memory'):
            self.assertIs(getattr(I,name).__globals__['PROCESS'],P)
            self.assertIs(getattr(OLDI,name).__globals__['PROCESS'],OLD)
        self.assertIs(X.compile_one.__globals__['PROCESS'],P);self.assertIs(X.ISOLATION,I)
        for name in (*I.FROZEN_PROCESS_SOURCES,I.OWN,I.ENTRY,I.OBSERVER):self.assertIn(name,I.sources()['sha256'])
        with patch.dict(I.FROZEN_PROCESS_SOURCES,{OLDI.OBSERVER:'0'*64}):
            with self.assertRaises(ValueError):I.body_source()

    def test_no_recursive_historical_verifier_or_M_graph_in_failure_context(self):
        node=function(Path(I.__file__).read_text(),'failure_binding')
        calls=[ast.unparse(n.func)for n in ast.walk(node)if isinstance(n,ast.Call)]
        self.assertFalse(any('verify_rederive'in c or 'M.verify'in c or 'failure_binding'in c for c in calls))
        self.assertIn('r.digest',calls);self.assertIn('r.read',calls)

    def test_canonical_native_result_survives_an_observer_error_but_proof_still_fails(self):
        with tempfile.TemporaryDirectory()as d:
            root=Path(d);source=root/'Small.lean';source.write_text('def x : Bool := true\n');compiler=root/'lean';compiler.write_bytes(b'fake-test-only')
            obj=root/'Small.olean';log=root/'Small.log';journal=root/'native.jsonl'
            class Child:
                pid=20
                def wait(self,timeout):obj.write_bytes(b'fake-test-object');return 0
                def poll(self):return 0
            namespace=dict(vars(OLDI.PREVIOUS.PRIOR.ORIGINAL),PROCESS=P)
            exec(compile(I.compile_source(),'<test-only-observed-compile>','exec'),namespace)
            with patch.object(OLDI.PREVIOUS.PRIOR.ORIGINAL.subprocess,'Popen',return_value=Child()),patch.object(P,'start',return_value=object()),\
                    patch.object(P,'finish',side_effect=ValueError('observer failed')),patch.object(OLDI.PREVIOUS.PRIOR.F,'closed_group',return_value=True):
                with self.assertRaisesRegex(ValueError,'observer failed'):
                    namespace['compile_one'](compiler,source,obj,log,journal,0,'Small',{'LEAN_PATH':str(root)},[root])
            records=[json.loads(line)for line in journal.read_text().splitlines()]
            self.assertEqual([r['event']for r in records],['intent','result']);self.assertEqual(records[1]['exit_code'],0)

    def test_all_math_compile_private_and_budgets_are_unchanged(self):
        self.assertEqual(I.compile_source(),OLDI.compile_source())
        text,_=I.controller_source();old,_=OLDI.controller_source()
        normalized=text.replace('streaming_8x4_closure24_m_comm_isolation','streaming_8x4_closure24_m_state_isolation')
        normalized=normalized.replace('pinwheel.closure24-comm-isolated','pinwheel.closure24-state-isolated')
        self.assertEqual(normalized,old)
        self.assertEqual(X.budget_policy(),OLDI.PREVIOUS.PRIOR.budget_policy());self.assertEqual(I.REDERIVE_SECONDS,600)
        for name in ('native_argv','imports','verify_imports','observe_foundation_runtime','private_texts','command_timeout'):
            self.assertIs(getattr(X,name),getattr(OLDI.PREVIOUS.PRIOR,name))

    def test_exact_helper_delta_is_only_new_identity_schema_and_context(self):
        text,_=I.body_source();old,_=OLDI.body_source()
        text=text.replace('streaming_8x4_closure24_m_process_comm','streaming_8x4_closure24_m_process_state')
        text=text.replace('streaming_8x4_closure24_m_comm_isolation','streaming_8x4_closure24_m_state_isolation')
        text=text.replace('streaming_8x4_closure24_comm_m_execute','streaming_8x4_closure24_state_m_execute')
        text=text.replace('as COMM','as STATE').replace('COMM.','STATE.')
        text=text.replace('pinwheel.closure24-comm-M-','pinwheel.closure24-state-M-')
        text=text.replace('pinwheel.closure24-comm-isolated','pinwheel.closure24-state-isolated')
        self.assertEqual(text,old)


if __name__=='__main__':unittest.main()
