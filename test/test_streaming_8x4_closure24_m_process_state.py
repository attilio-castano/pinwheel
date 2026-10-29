"""Portable captured-state/lifetime and complete-M ownership regressions."""
import ast
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_m_process as OLD
import streaming_8x4_closure24_m_process_state as P
import streaming_8x4_closure24_m_state_isolation as S
import streaming_8x4_closure24_state_m_execute as X

REAL_EXECUTABLE_IDENTITY=P.executable_identity
ARGV=['/exact/lean','-M4096','-j1','source.lean']
BIRTH='Sat Oct 24 16:49:05 2026'


def exe(command):
    path=command.split()[0]
    if not Path(path).is_absolute():raise ValueError('Observed LIVE executable path is not absolute')
    return dict(path=path,resolved=path,sha256='a'*64)


def raw(*,state='R',child=True,birth=BIRTH,command=None,parent_state='Ss',parent_command='/exact/Python.app -B driver.py',rss=200):
    # Z <defunct> is from the real 2026-10-24 owned /usr/bin/true lifecycle
    # capture at B2/m-observer-state-reproduction-02/raw-ps.jsonl, SHA6efb8a6e...
    # Tests use literals and never depend on ignored campaign artifacts.
    lines=[f'10 1 10 100 {BIRTH} {parent_state} {parent_command}']
    if child:lines.append(f'20 10 20 {rss} {birth} {state} '+(command or('<defunct>'if state.startswith('Z')else' '.join(ARGV))))
    return dict(argv=P.ps_argv((10,20)),returncode=0,stdout='\n'.join(lines)+'\n',stderr='',error=None)


def write_memory(path,raws):
    records=[dict(event='start',label='Exact',parent_pid=10,child_pid=20,argv=ARGV)]
    tracked={};children=0;zombies=0;maximum=None
    for i,capture in enumerate(raws):
        records.append(dict(event='ps-raw',label='Exact',seconds=i*.1,**capture))
        rows=P.parse(capture,(10,20));total=P.validate_sample(rows,10,20,ARGV,tracked)
        dead=20 in rows and rows[20]['state'].startswith('Z');children+=int(20 in rows and not dead);zombies+=int(dead)
        if total is not None:maximum=total if maximum is None else max(maximum,total)
        records.append(dict(event='sample',label='Exact',seconds=i*.1,processes={str(k):v for k,v in rows.items()},
            parent_and_child_rss_kib=total,missing_pids=[pid for pid in(10,20)if pid not in rows],defunct_child_observed=dead))
    records.append(dict(event='finish',label='Exact',samples=len(raws),child_samples=children,zombie_child_samples=zombies,
        child_birth_observed=20 in tracked,maximum_observed_parent_and_child_rss_kib=maximum,error=None))
    path.write_text('\n'.join(json.dumps(row)for row in records)+'\n');return records


def function(text,name):return next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef)and n.name==name)


class ProcessStateControls(unittest.TestCase):
    def setUp(self):
        self.stub=patch.object(P,'executable_identity',side_effect=exe);self.stub.start();self.addCleanup(self.stub.stop)

    def test_captured_Z_defunct_reproduces_old_failure_and_new_parse_keeps_unknown_identity(self):
        parent=str(Path(sys.executable).resolve())+' -B driver.py'
        legacy=f'10 1 10 100 {BIRTH} {parent}\n20 10 20 0 {BIRTH} <defunct>\n'
        with patch.object(OLD.subprocess,'run',return_value=SimpleNamespace(returncode=0,stdout=legacy,stderr='')):
            with self.assertRaisesRegex(ValueError,'not absolute'):OLD.snapshot((10,20))
        rows=P.parse(raw(state='Z',rss=0),(10,20));z=rows[20]
        self.assertEqual(z['rss_kib'],0);self.assertIsNone(z['active_rss_kib']);self.assertIsNone(z['observed_executable'])
        self.assertFalse(z['argv_identity_known']);self.assertEqual(z['command'],'<defunct>');self.assertEqual(z['state'],'Z')
        self.assertEqual(P.lifetime(z),dict(pid=20,ppid=10,pgid=20,birth=BIRTH))

    def test_R_S_transitions_preserve_lifetime_and_live_identity(self):
        tracked={}
        for state,parent_state in [('R','Ss'),('S+','R+'),('R','Ss')]:
            self.assertEqual(P.validate_sample(P.parse(raw(state=state,parent_state=parent_state),(10,20)),10,20,ARGV,tracked),300)
        self.assertEqual(tracked[20]['active_identity']['command'],' '.join(ARGV))

    def test_active_to_Z_to_absent_keeps_raw_terminal_identity_and_no_active_zero(self):
        with tempfile.TemporaryDirectory()as d:
            path=Path(d)/'memory.jsonl';write_memory(path,[raw(),raw(state='Z',rss=0),raw(child=False)])
            result=P.verify(path,[('Exact',ARGV)],require_child_observed=True);child=result['observations'][0]
            self.assertEqual(child['child_samples'],1);self.assertEqual(child['zombie_child_samples'],1)
            self.assertEqual(child['maximum_observed_parent_and_child_rss_kib'],300)
            self.assertEqual(child['child_active_identity']['command'],' '.join(ARGV))

    def test_fast_Z_only_is_unknown_and_does_not_satisfy_long_child_coverage(self):
        with tempfile.TemporaryDirectory()as d:
            path=Path(d)/'memory.jsonl';write_memory(path,[raw(state='Z',rss=0),raw(child=False)])
            child=P.verify(path,[('Exact',ARGV)])['observations'][0]
            self.assertEqual(child['child_samples'],0);self.assertEqual(child['zombie_child_samples'],1)
            self.assertIsNone(child['child_active_identity']);self.assertIsNone(child['maximum_observed_parent_and_child_rss_kib'])
            with self.assertRaises(ValueError):P.verify(path,[('Exact',ARGV)],require_child_observed=True)

    def test_live_nonabsolute_command_still_rejects_with_actual_identity_function(self):
        with patch.object(P,'executable_identity',side_effect=REAL_EXECUTABLE_IDENTITY):
            capture=raw(command='<defunct>',state='R',parent_command=str(Path(sys.executable).resolve())+' -B driver.py')
            with self.assertRaisesRegex(ValueError,'LIVE executable path is not absolute'):P.parse(capture,(10,20))

    def test_parent_must_live_and_child_PID_birth_and_argv_must_not_drift(self):
        tracked={};P.validate_sample(P.parse(raw(),(10,20)),10,20,ARGV,tracked)
        bad=[raw(parent_state='Z',parent_command='<defunct>'),raw(birth='Sat Oct 24 16:50:00 2026'),
            raw(command='/exact/lean changed.lean'),raw(parent_command='/different/Python.app -B driver.py')]
        for value in bad:
            with self.assertRaises(ValueError):P.validate_sample(P.parse(value,(10,20)),10,20,ARGV,deepcopy(tracked))
        rows=P.parse(raw(),(10,20));rows.pop(10)
        with self.assertRaises(ValueError):P.validate_sample(rows,10,20,ARGV,{})

    def test_no_live_return_after_Z_or_terminal_PID_lifetime_replacement(self):
        tracked={};P.validate_sample(P.parse(raw(state='Z'),(10,20)),10,20,ARGV,tracked)
        with self.assertRaises(ValueError):P.validate_sample(P.parse(raw(),(10,20)),10,20,ARGV,tracked)
        rows=P.parse(raw(state='Z'),(10,20));rows[20]['pgid']=21
        with self.assertRaises(ValueError):P.validate_sample(rows,10,20,ARGV,{})

    def test_raw_ps_failure_is_durable_before_parse_error(self):
        with tempfile.TemporaryDirectory()as d:
            path=Path(d)/'memory.jsonl';capture=raw(command='<defunct>',state='R')
            with patch.object(P.os,'getpid',return_value=10),patch.object(P,'capture',return_value=capture):
                watch=P.start(20,ARGV,path,label='Exact');watch.thread.join(timeout=1)
                with self.assertRaisesRegex(ValueError,'State memory observer failed'):P.finish(watch)
            records=[json.loads(line)for line in path.read_text().splitlines()]
            self.assertEqual(records[1]['event'],'ps-raw');self.assertEqual(records[1]['stdout'],capture['stdout'])
            self.assertEqual(records[2]['event'],'observer-error');self.assertEqual(records[-1]['event'],'finish')

    def test_reader_rederives_parsed_state_from_raw_and_rejects_omissions_or_invented_memory(self):
        with tempfile.TemporaryDirectory()as d:
            path=Path(d)/'memory.jsonl';records=write_memory(path,[raw(state='Z',rss=0)])
            mutations=[lambda r:r[2].update(parent_and_child_rss_kib=100),lambda r:r[2]['processes']['20'].update(observed_executable=exe('/expected/lean')),
                lambda r:r.pop(1),lambda r:r[1].update(stdout=r[1]['stdout'].replace(' Z ',' R ')),
                lambda r:r[1].update(argv=['foreign-ps']),lambda r:r[-1].update(child_samples=1)]
            for mutate in mutations:
                value=deepcopy(records);mutate(value);path.write_text('\n'.join(json.dumps(r)for r in value)+'\n')
                with self.assertRaises((ValueError,KeyError)):P.verify(path,[('Exact',ARGV)])

    def test_startup_has_exact_raw_identity_and_live_executable(self):
        with tempfile.TemporaryDirectory()as d:
            path=Path(d)/'startup.jsonl';capture=raw(child=False);capture['argv']=P.ps_argv((10,))
            path.write_text(json.dumps(dict(event='ps-raw',label='driver-startup',**capture))+'\n');row=P.parse(capture,(10,))[10]
            self.assertTrue(P.verify_startup(path,row,label='driver-startup'))
            changed=deepcopy(row);changed['command']='/other/Python.app -B driver.py'
            with self.assertRaises(ValueError):P.verify_startup(path,changed,label='driver-startup')

    def test_all_operational_helpers_use_new_state_globals_without_old_mutation(self):
        # This hash/body control supplies an identity; committed admission is separate.
        for name in ('rederive','run_rederive','verify_rederive','verify_memory'):
            self.assertIs(getattr(S,name).__globals__['PROCESS'],P,name)
            self.assertIs(getattr(S.PREVIOUS,name).__globals__['PROCESS'],OLD,name)
        self.assertIs(X.ISOLATION,S);self.assertIs(X.compile_one.__globals__['PROCESS'],P)
        self.assertIsNot(X.positive,S.PREVIOUS.PRIOR.positive)
        self.assertEqual(X.budget_policy(),S.PREVIOUS.PRIOR.budget_policy())
        files=S.sources(commit='a'*40)['sha256']
        for name in (*S.FROZEN_PROCESS_SOURCES,S.OWN,S.ENTRY,S.OBSERVER):self.assertIn(name,files)
        with patch.dict(S.FROZEN_PROCESS_SOURCES,{S.PREVIOUS.OBSERVER:'0'*64}):
            with self.assertRaises(ValueError):S.body_source()

    def test_canonical_native_result_survives_an_observer_error_but_proof_still_fails(self):
        with tempfile.TemporaryDirectory()as d:
            root=Path(d);source=root/'Small.lean';source.write_text('def x : Bool := true\n');compiler=root/'lean';compiler.write_bytes(b'fake-test-only')
            obj=root/'Small.olean';log=root/'Small.log';journal=root/'native.jsonl'
            class Child:
                pid=20
                def wait(self,timeout):obj.write_bytes(b'fake-test-object');return 0
                def poll(self):return 0
            namespace=dict(vars(S.PREVIOUS.PRIOR.ORIGINAL),PROCESS=P)
            exec(compile(S.compile_source(),'<test-only-observed-compile>','exec'),namespace)
            with patch.object(S.PREVIOUS.PRIOR.ORIGINAL.subprocess,'Popen',return_value=Child()),patch.object(P,'start',return_value=object()),\
                    patch.object(P,'finish',side_effect=ValueError('observer failed')),patch.object(S.PREVIOUS.PRIOR.F,'closed_group',return_value=True):
                with self.assertRaisesRegex(ValueError,'observer failed'):
                    namespace['compile_one'](compiler,source,obj,log,journal,0,'Small',{'LEAN_PATH':str(root)},[root])
            records=[json.loads(line)for line in journal.read_text().splitlines()]
            self.assertEqual([r['event']for r in records],['intent','result']);self.assertEqual(records[1]['exit_code'],0)

    def test_full_positive_private_bodies_and_budgets_unchanged_after_observation_normalization(self):
        text,_=S.controller_source();old,_=S.PREVIOUS.controller_source()
        normalized=text.replace('import streaming_8x4_closure24_m_state_isolation as ISOLATION','import streaming_8x4_closure24_m_isolation as ISOLATION')
        normalized=normalized.replace('pinwheel.closure24-state-isolated-actual-M-positive.v1','pinwheel.closure24-isolated-actual-M-positive.v1').replace('pinwheel.closure24-state-isolated-actual-M-private.v1','pinwheel.closure24-isolated-actual-M-private.v1')
        normalized=normalized.replace("ISOLATION.PROCESS.snapshot((os.getpid(),),raw_path=output/'driver-process-raw.jsonl',label='driver-startup')[os.getpid()];report['driver_process_raw']=bound(output/'driver-process-raw.jsonl')","ISOLATION.PROCESS.snapshot((os.getpid(),))[os.getpid()]")
        for name in ('positive','private','verify_positive','verify_private','input_seal','generated_roots_owned'):
            self.assertEqual(ast.dump(function(normalized,name)),ast.dump(function(old,name)),name)
        for name in ('native_argv','imports','verify_imports','observe_foundation_runtime','private_texts','command_timeout'):
            self.assertIs(getattr(X,name),getattr(S.PREVIOUS.PRIOR,name),name)
        self.assertEqual(S.REDERIVE_SECONDS,600)

    def test_canonical_compile_body_is_byte_identical_after_removing_observation_only(self):
        text=S.compile_source().replace(';memory_watch=None','')
        text=text.replace("            memory_watch=PROCESS.start(child.pid,argv,journal.parent/'process-memory.jsonl',label=module)\n",'')
        text=text.replace('        observer_error=None\n        try:PROCESS.finish(memory_watch)\n        except BaseException as error:observer_error=error\n','')
        text=text.replace('    if observer_error is not None:raise observer_error\n','')
        original=Path(S.PREVIOUS.PRIOR.ORIGINAL.__file__).read_text();node=function(original,'compile_one')
        expected=''.join(original.splitlines(True)[node.lineno-1:node.end_lineno])
        self.assertEqual(text,expected)


if __name__=='__main__':unittest.main()
