"""Host mutation controls for the fresh optimized compiler boundary; no Native."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_tt_fresh_foundation as F


def fixture(root):
    root = root.resolve(); source = root / 'snapshot'; source.mkdir()
    tools = {}
    for name in ('lean', 'lake', 'yosys', 'abc'):
        path = root / 'tool/bin' / name; path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('pinned:' + name); tools[name] = str(path)
    core = source / 'Pinwheel/Core.lean'; core.parent.mkdir(); core.write_text('import Std\n')
    obj = source / '.lake/build/lib/lean/Pinwheel/Core.olean'
    obj.parent.mkdir(parents=True); obj.write_text('fresh positive object')
    b = dict(candidate_root=str(source), candidate_commit='a'*40, modules=['Pinwheel.Core'],
        lean=tools['lean'], lake=tools['lake'], python=sys.executable,
        positive_library_artifact_sha256={'Pinwheel/Core.olean': F.sha(obj)},
        foundation_source_projection={'Pinwheel/Core.lean': F.sha(core)})
    entry = source / 'scripts/check-streaming-ready-fresh.py'; entry.parent.mkdir(); entry.write_text('frozen entry')
    marker = root / 'binding.json'; marker.write_text(json.dumps(b))
    out = root / 'worker'; out.mkdir()
    config = dict(root=str(source), source_commit='a'*40, producer_commit='a'*40,
                  tools=tools, fresh_foundation=F.bound(marker))
    return b, config, out


class FakeNative:
    pid = 999999
    returncode = 0

    def __init__(self, argv, *, cwd, stdout, stderr, text, start_new_session):
        self.argv = argv
        if not start_new_session: raise AssertionError('Owned process group required')
        self.cwd = Path(cwd)

    def communicate(self, timeout):
        if '-o' in self.argv:
            Path(self.argv[self.argv.index('-o')+1]).write_text('native fixture object:' + self.argv[-1])
        return 'native fixture log\n', None


class FreshOptimizedTests(unittest.TestCase):
    def test_inherited_compiler_import_and_tool_overrides_refused(self):
        for key in ('LEAN_PATH','PYTHONPATH','DYLD_INSERT_LIBRARIES','YOSYS_DATDIR','ABC_PATH'):
            with self.subTest(key=key),patch.dict(F.os.environ,{key:'/foreign/override'}):
                with self.assertRaises(ValueError): F.check_native_environment()

    def executor(self, config, out):
        with patch.object(F, 'verify_binding', return_value=True), patch.object(F, 'verify_staged', return_value=True):
            return F.FreshNativeExecutor(config, out)

    def native(self):
        return patch.object(F.subprocess, 'Popen', side_effect=FakeNative)

    def compile(self, executor, out, name, imports='import Pinwheel.Core\n'):
        proof = out / 'proof'; proof.mkdir(exist_ok=True)
        source = proof / (name + '.lean'); source.write_text(imports + 'theorem fixture : True := True.intro\n')
        argv = ['env', 'LEAN_PATH=' + str(proof), executor.binding['lean'], '-o', str(source.with_suffix('.olean')), str(source)]
        return executor.run(argv, proof / (name + '.log'), timeout=7)

    def test_durable_intent_precedes_native_and_generated_import_requires_prior_producer(self):
        with tempfile.TemporaryDirectory() as name:
            b, cfg, out = fixture(Path(name)); executor = self.executor(cfg, out)
            def launch(argv, **options):
                events = [json.loads(line) for line in executor.path.read_text().splitlines()]
                self.assertEqual(events[-1]['event'], 'intent')
                self.assertEqual(events[-1]['actual_argv'], argv)
                self.assertEqual(argv[3:7], [b['lean'], '-M4096', '-j1', '-DElab.async=false'])
                return FakeNative(argv, **options)
            with patch.object(F.subprocess, 'Popen', side_effect=launch), patch.object(F, 'closed_group', return_value=True):
                self.compile(executor, out, 'First')
                self.compile(executor, out, 'Second', 'import First\n')
                forged = out / 'proof/Forged.lean'; forged.write_text('import Std\n')
                forged.with_suffix('.olean').write_text('unproved old object')
                with self.assertRaisesRegex(ValueError, 'earlier closed native'):
                    self.compile(executor, out, 'Third', 'import Forged\n')
            with patch.object(F, 'verify_binding', return_value=True), patch.object(F, 'verify_staged', return_value=True):
                self.assertEqual(executor.closeout()['commands'], 2)

    def test_consumed_project_source_object_and_ambiguous_generated_import_refused(self):
        with tempfile.TemporaryDirectory() as name:
            b, cfg, out = fixture(Path(name)); a=out/'a'; c=out/'c'; a.mkdir(); c.mkdir()
            src=a/'Test.lean'; src.write_text('import Pinwheel.Core\n')
            paths=F.consumed_imports(src,[a,c],b)
            self.assertIn(str(Path(b['candidate_root'])/'Pinwheel/Core.lean'),paths)
            core=Path(b['candidate_root'])/'Pinwheel/Core.lean'; old=core.read_text(); core.write_text('changed')
            with self.assertRaisesRegex(ValueError,'source differs'): F.consumed_imports(src,[a,c],b)
            core.write_text(old)
            obj=Path(b['candidate_root'])/'.lake/build/lib/lean/Pinwheel/Core.olean'; obj.write_text('changed')
            with self.assertRaisesRegex(ValueError,'object changed'): F.consumed_imports(src,[a,c],b)
            src.write_text('import Duplicate\n')
            for directory in (a,c): (directory/'Duplicate.lean').write_text('import Std\n')
            with self.assertRaisesRegex(ValueError,'ambiguous'): F.consumed_imports(src,[a,c],b)

    def test_source_mutation_missing_output_and_timeout_never_close(self):
        for kind in ('source', 'missing-output', 'timeout', 'lingering-group'):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as name:
                b,cfg,out=fixture(Path(name)); executor=self.executor(cfg,out)
                class BrokenNative(FakeNative):
                    def communicate(self, timeout):
                        if kind=='source': Path(self.argv[-1]).write_text('mutated during compile')
                        if kind=='timeout' and not hasattr(self,'waited'):
                            self.waited=True; raise subprocess.TimeoutExpired(self.argv,timeout)
                        return ('failure fixture\n',None) if kind=='missing-output' else super().communicate(timeout)
                with patch.object(F.subprocess,'Popen',side_effect=BrokenNative), \
                     patch.object(F,'closed_group',return_value=kind!='lingering-group'), \
                     patch.object(F,'terminate_group',return_value=False), patch.object(F.os,'killpg'):
                    with self.assertRaises(ValueError): self.compile(executor,out,'Failed')
                with patch.object(F,'verify_binding',return_value=True),patch.object(F,'verify_staged',return_value=True):
                    # Missing output also leaves an explicitly unsuccessful batch.
                    with self.assertRaises(ValueError): executor.closeout()

    def batch(self, root):
        b,cfg,out=fixture(root); executor=self.executor(cfg,out)
        worker=dict(commands=[],components={},fresh_foundation=cfg['fresh_foundation'])
        with self.native(),patch.object(F,'closed_group',return_value=True):
            native=self.compile(executor,out,'First')
            row=executor.rows[-1]
            worker['commands'].append(dict(argv=native.args,exit_code=0,log=row['log'],log_sha256=row['log_sha256'],native_journal_index=0))
            for label in ('frontend','core-d2'):
                directory=out/label;directory.mkdir(); script=directory/'map.ys';script.write_text('mapping fixture')
                mapped=executor.run([cfg['tools']['yosys'],'-s',str(script)],directory/'yosys.log',timeout=7)
                component=dict(mapping=dict(argv=mapped.args,exit_code=0,native_journal_index=mapped.native_journal_index),proof=dict(modules=[]))
                proof=out/(label+'-proof');proof.mkdir();source=proof/'Module.lean';source.write_text('import Pinwheel.Core\n')
                cmd=executor.run(['env','LEAN_PATH='+str(proof),b['lean'],'-o',str(source.with_suffix('.olean')),str(source)],proof/'Module.log',timeout=7)
                component['proof']['modules'].append(dict(module='Module',argv=cmd.args,exit_code=0,
                    log_sha256=F.sha(proof/'Module.log'),native_journal_index=cmd.native_journal_index))
                worker['components'][label]=component
        with patch.object(F,'verify_binding',return_value=True),patch.object(F,'verify_staged',return_value=True):
            worker['fresh_optimized_native']=executor.closeout()
        return cfg,out,worker

    def validate(self,cfg,out,worker):
        with patch.object(F,'verify_binding',return_value=True),patch.object(F,'verify_staged',return_value=True):
            return F.validate_optimized_native({'fresh_foundation':cfg['fresh_foundation']},cfg,worker,out)

    def test_independent_parent_closes_every_native_operation_exactly_once(self):
        with tempfile.TemporaryDirectory() as name:
            cfg,out,worker=self.batch(Path(name))
            self.assertEqual(self.validate(cfg,out,worker)['candidate_commit'],'a'*40)
            for mutation in ('duplicate','missing','wrong-argv','wrong-log','bool-index','marker'):
                changed=deepcopy(worker)
                if mutation=='duplicate': changed['commands'].append(deepcopy(changed['commands'][0]))
                elif mutation=='missing': changed['commands']=[]
                elif mutation=='wrong-argv': changed['commands'][0]['argv']=['/old/lean']
                elif mutation=='wrong-log': changed['commands'][0]['log_sha256']='b'*64
                elif mutation=='bool-index': changed['commands'][0]['native_journal_index']=False
                else: changed['fresh_foundation']['sha256']='b'*64
                with self.subTest(mutation=mutation),self.assertRaises(ValueError): self.validate(cfg,out,changed)

    def test_independent_parent_rejects_semantic_journal_and_object_mutations(self):
        for mutation in ('requested','actual','source','log','object','timeout','truncated','nonzero','bool-exit'):
            with self.subTest(mutation=mutation),tempfile.TemporaryDirectory() as name:
                cfg,out,worker=self.batch(Path(name)); journal=out/'fresh-foundation-optimized-native.jsonl'
                events=[json.loads(line) for line in journal.read_text().splitlines()]
                if mutation=='requested': events[0]['requested_argv']=['/old/lean'];events[1]['requested_argv']=['/old/lean']
                elif mutation=='actual': events[0]['actual_argv']=['/old/lean'];events[1]['actual_argv']=['/old/lean']
                elif mutation=='source': (out/'proof/First.lean').write_text('changed source')
                elif mutation=='log': Path(events[1]['log']).write_text('changed log')
                elif mutation=='object': (out/'proof/First.olean').write_text('changed object')
                elif mutation=='timeout': events[1]['timed_out']=True
                elif mutation=='truncated': events.pop()
                elif mutation=='bool-exit': events[1]['exit_code']=False
                else: events[1]['exit_code']=1
                journal.write_text(''.join(json.dumps(row)+'\n' for row in events))
                worker['fresh_optimized_native']['journal']=F.bound(journal)
                with self.assertRaises(ValueError): self.validate(cfg,out,worker)


if __name__=='__main__': unittest.main()
