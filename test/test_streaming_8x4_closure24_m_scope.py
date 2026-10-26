"""Portable scope-only regression; executes no generation, Lean or CAD."""
import ast
import copy
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_m_scope as S
import streaming_8x4_closure24_scope_m as M
import streaming_8x4_closure24_scope_m_execute as X
import streaming_8x4_closure24_context_m as PRIOR_M
import streaming_8x4_closure24_context_m_execute as PRIOR_X

ROOT=Path(__file__).resolve().parents[1]
PAYLOAD=(ROOT/'test/fixtures/streaming_8x4/GEN04-generate.py.txt').read_bytes()


def function(text,name):return next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name==name)


def probe(text,context_name):
    """Run the actual capture/import-loop/final-equality AST, not the generator."""
    f=function(text,'_generate')
    capture=next(n for n in f.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==context_name for t in n.targets))
    imports=next(n for n in f.body if isinstance(n,ast.For) and isinstance(n.iter,ast.Call) and isinstance(n.iter.func,ast.Attribute)
        and isinstance(n.iter.func.value,ast.Name) and n.iter.func.value.id=='sources')
    final=next(n for n in f.body if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and any(isinstance(a,ast.Constant)
        and a.value=='Explicit relocated source N closure changed during actual M derivation' for a in n.value.args))
    args=ast.arguments(posonlyargs=[],args=[ast.arg(arg=n) for n in ('D','F','config','sources','available')],kwonlyargs=[],kw_defaults=[],defaults=[])
    body=[copy.deepcopy(capture),copy.deepcopy(imports),copy.deepcopy(final),ast.Return(value=ast.Tuple(elts=[ast.Name(id=context_name,ctx=ast.Load()),ast.Name(id='dependency',ctx=ast.Load())],ctx=ast.Load()))]
    module=ast.fix_missing_locations(ast.Module(body=[ast.FunctionDef(name='scope_probe',args=args,body=body,decorator_list=[])],type_ignores=[]))
    namespace={};exec(compile(module,'<exact-import-loop-scope-probe>','exec'),namespace);return namespace['scope_probe']


def require(value,message):
    if not value:raise ValueError(message)


class ScopeControls(unittest.TestCase):
    def test_actual_original_import_loop_overwrites_old_adapter_and_new_scope_preserves_context(self):
        old,_=PRIOR_M.adapted_generator(PAYLOAD);new,_=M.adapted_generator(PAYLOAD)
        context=dict(source_worker_config=dict(path='authenticated-original-config',sha256='a'*64),state_bits=6039)
        def run(fn,second=context,sources=None):
            results=iter([copy.deepcopy(context),copy.deepcopy(second)])
            return fn(SimpleNamespace(dependency_context=lambda _:next(results)),SimpleNamespace(require=require),{},
                sources or {'First':'import Lean\n','Second':'import First Std\n'},set())
        with self.assertRaisesRegex(ValueError,'closure changed'):run(probe(old,'dependency'))
        kept,last=run(probe(new,S.NAME));self.assertEqual(kept,context);self.assertEqual(last,'Std')
        with self.assertRaisesRegex(ValueError,'closure changed'):run(probe(new,S.NAME),dict(context,state_bits=1))
        with self.assertRaisesRegex(ValueError,'missing/later import'):run(probe(new,S.NAME),sources={'First':'import Missing\n'})

    def test_whole_generated_body_is_identical_after_introduced_name_and_typed_scope_normalization(self):
        old,_=PRIOR_M.adapted_generator(PAYLOAD);new,diff=M.adapted_generator(PAYLOAD)
        normalized=new.replace(S.NAME,'dependency').replace('import streaming_8x4_closure24_scope_m as D','import streaming_8x4_closure24_context_m as D')
        normalized=normalized.replace('pinwheel.closure24-scope-actual-target-M.v1','pinwheel.closure24-context-actual-target-M.v1').replace('pinwheel.closure24-scope-actual-M-generation.v1','pinwheel.closure24-context-actual-M-generation.v1')
        self.assertEqual(normalized,old);self.assertTrue(diff)
        self.assertEqual(S.CONTEXT.unresolved_names(new),[])
        self.assertEqual(ast.dump(function(normalized,'_generate')),ast.dump(function(old,'_generate')))
        for name in ('codec_from_backends','source_layout'):
            self.assertEqual(ast.dump(function(new,name)),ast.dump(function(old,name)))

    def test_original_import_loop_and_all_its_dependency_uses_are_unchanged(self):
        old,_=PRIOR_M.adapted_generator(PAYLOAD);new,_=M.adapted_generator(PAYLOAD)
        def loops(text):return [n for n in ast.walk(function(text,'_generate')) if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='dependency']
        self.assertEqual(len(loops(old)),1);self.assertEqual(len(loops(new)),1)
        self.assertEqual(ast.dump(loops(old)[0]),ast.dump(loops(new)[0]))
        self.assertIn("bound_path(source_dependency_context['source_worker_config'])",new)
        self.assertIn('F.require(D.dependency_context(config)==source_dependency_context,',new)

    def test_descriptive_name_has_exactly_one_store_and_missing_or_preexisting_anchors_reject(self):
        old,_=PRIOR_M.adapted_generator(PAYLOAD);new=S.rename_context(old)
        stores=[n for n in ast.walk(function(new,'_generate')) if isinstance(n,ast.Name) and n.id==S.NAME and isinstance(n.ctx,ast.Store)]
        self.assertEqual(len(stores),1)
        for bad in (old+'\n'+S.NAME+'=None\n',old.replace('    dependency=D.dependency_context(config)','    dependency=None',1),old.replace("bound_path(dependency['source_worker_config'])","None",1)):
            with self.assertRaises(ValueError):S.rename_context(bad)

    def test_positive_private_native_algorithms_are_exact_and_all_budgets_reused(self):
        new,_=S.controller_source('execution');old,_=S.CONTEXT.controller_source('execution')
        normal=new.replace('pinwheel.closure24-scope-actual-M-positive.v1','pinwheel.closure24-context-actual-M-positive.v1').replace('pinwheel.closure24-scope-actual-M-private.v1','pinwheel.closure24-context-actual-M-private.v1')
        for name in ('positive','private','verify_positive','verify_private','input_seal','generated_roots_owned'):
            self.assertEqual(ast.dump(function(normal,name)),ast.dump(function(old,name)),name)
        for name in ('compile_one','native_argv','environment','observe_foundation_runtime','verify_imports','private_texts','budget_policy','command_timeout','verify_command_timeout'):
            self.assertIs(getattr(X,name),getattr(PRIOR_X,name),name)
        self.assertEqual(X.budget_policy(),PRIOR_X.budget_policy())

    def test_new_owner_namespace_and_explicit_prior_source_seals(self):
        self.assertEqual(X.M.__name__,'streaming_8x4_closure24_scope_m');self.assertEqual(PRIOR_X.M.__name__,'streaming_8x4_closure24_context_m')
        self.assertEqual(Path(M.generate.__globals__['__file__']).resolve(),Path(M.__file__).resolve())
        self.assertEqual(Path(X.source_seal.__globals__['__file__']).resolve(),Path(X.__file__).resolve())
        self.assertEqual(len(M.SOURCES),len(set(M.SOURCES)))
        for name in (*S.PRIOR,S.OWN,S.NEW_GENERATION,S.NEW_EXECUTION,S.CONTEXT.GENERATION,S.CONTEXT.EXECUTION):self.assertIn(name,M.SOURCES)
        gen,_=S.controller_source('generation');self.assertIn('pinwheel.closure24-scope-actual-M-preparation.v1',gen)
        self.assertIn("record.get('source_worker_context')==source_context",gen)
        self.assertIn("manifest['fresh_adaptation'].get('source_worker_context')==source_context",gen)

    def test_frozen_prior_context_and_controller_sources_reject_drift(self):
        with patch.dict(S.PRIOR,{S.CONTEXT.OWN:'0'*64}):
            with self.assertRaises(ValueError):S.controller_source('generation')
        with patch.dict(S.CONTEXT.PINS,{S.CONTEXT.EXECUTION:'0'*64}):
            with self.assertRaises(ValueError):S.controller_source('execution')

if __name__=='__main__':unittest.main()
