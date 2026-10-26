"""Portable context/unchanged-body controls; no generation, Lean or build data."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_m_context as C
import streaming_8x4_closure24_context_m as M
import streaming_8x4_closure24_context_m_execute as X
import streaming_8x4_closure24_final_m as BASE_M
import streaming_8x4_closure24_final_m_execute as BASE_X

ROOT=Path(__file__).resolve().parents[1]


def write(path,row):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(row,sort_keys=True)+'\n')


def fixture(root):
    root=root.resolve()
    config=root/'recovery/final-N-config'/C.N.CONFIG
    write(config,dict(source_commit=C.N.SOURCE,source_config='original payload'))
    cfgpin=C.R.digest(config);owner=root/'recovery/final-N-config';metadata=owner/'RESTORED-FILES-METADATA.jsonl'
    row=dict(root='wt1373',kind='file',path=C.N.CONFIG,sha=cfgpin,restored_relative_path=str(config.relative_to(owner)))
    write(metadata,row)
    prepared=root/'original/prepared.json';write(prepared,dict(worker_config=dict(path=str(C.N.OLD/C.N.CONFIG),sha256=cfgpin)))
    dep_path=root/'N/report.json';write(dep_path,dict(portable_fixture=True))
    dep=dict(original_records={'prepared.json':dict(original_path=str(C.N.OLD/C.N.N/'prepared.json'),**C.bound(prepared))},
        original_worker_config=C.bound(config),source_commit=C.N.SOURCE,
        input_sha256={str(config):cfgpin,str(metadata):C.R.digest(metadata)},
        recovered_owner_sha256={str(owner):{str(config.relative_to(owner)):cfgpin,'RESTORED-FILES-METADATA.jsonl':C.R.digest(metadata)}})
    return dep_path,dep,config,metadata,prepared


def function(source,name):
    return next(n for n in ast.parse(source).body if isinstance(n,ast.FunctionDef) and n.name==name)


class ContextControls(unittest.TestCase):
    def check(self,root,mutate=None):
        path,dep,cfg,metadata,prepared=fixture(root)
        if mutate:mutate(path,dep,cfg,metadata,prepared)
        with patch.object(C.N,'verify',return_value=dep),patch.object(C,'ORIGINAL_CONFIG_PIN',C.R.digest(cfg)),\
                patch.object(C,'ORIGINAL_PREPARED_PIN',C.R.digest(prepared)):
            return C.binding(path),dep

    def test_original_restored_configuration_is_exact_historical_payload_not_derived_cfg(self):
        with tempfile.TemporaryDirectory() as d:
            row,dep=self.check(Path(d))
            self.assertEqual(row['relocated_worker_configuration'],dep['original_worker_config'])
            self.assertEqual(row['original_worker_configuration']['sha256'],row['relocated_worker_configuration']['sha256'])
            self.assertEqual(row['original_worker_configuration']['path'],str(C.N.OLD/C.N.CONFIG))
            self.assertEqual(row['archive_row']['path'],C.N.CONFIG)
            self.assertFalse(row['historical_receipts_rewritten']);self.assertFalse(row['derived_generation_config_substituted'])

    def test_relocated_configuration_requires_consumed_content_and_original_receipt(self):
        mutations=[lambda p,d,c,m,o:d['input_sha256'].pop(str(c)),
            lambda p,d,c,m,o:d['original_worker_config'].update(sha256='0'*64),
            lambda p,d,c,m,o:write(o,dict(worker_config=dict(path='/new/public-wire/worker-config.json',sha256=C.R.digest(c)))),
            lambda p,d,c,m,o:d['original_records']['prepared.json'].update(original_path='/other/prepared.json')]
        for mutate in mutations:
            with tempfile.TemporaryDirectory() as d,self.assertRaises(ValueError):self.check(Path(d),mutate)

    def test_original_archive_path_and_metadata_cannot_be_a_dummy_equal_byte_alias(self):
        def change_metadata(p,d,c,m,o):
            row=json.loads(m.read_text());row['path']='build/other/worker-config.json';write(m,row)
            d['input_sha256'][str(m)]=C.R.digest(m);d['recovered_owner_sha256'][str(m.parent)]['RESTORED-FILES-METADATA.jsonl']=C.R.digest(m)
        def ambiguous(p,d,c,m,o):d['recovered_owner_sha256'][str(c.parent)]={}
        def wrong_source(p,d,c,m,o):
            write(c,dict(source_commit='a'*40));pin=C.R.digest(c);d['original_worker_config']['sha256']=pin;d['input_sha256'][str(c)]=pin
            row=json.loads(m.read_text());row['sha']=pin;write(m,row);d['input_sha256'][str(m)]=C.R.digest(m)
            d['recovered_owner_sha256'][str(m.parent)].update({'RESTORED-FILES-METADATA.jsonl':C.R.digest(m),str(c.relative_to(m.parent)):pin})
            write(o,dict(worker_config=dict(path=str(C.N.OLD/C.N.CONFIG),sha256=pin)))
        for mutate in (change_metadata,ambiguous,wrong_source):
            with tempfile.TemporaryDirectory() as d,self.assertRaises(ValueError):self.check(Path(d),mutate)

    def test_context_extends_verified_original_input_without_mutating_old_context(self):
        with tempfile.TemporaryDirectory() as d:
            path,dep,cfg,meta,prepared=fixture(Path(d));old=dict(exact=dict(input_sha256={str(cfg):C.R.digest(cfg)}),cfg=dict(derived='kept'),worker=dict(original='kept'))
            original=copy.deepcopy(old)
            with patch.object(C.N,'verify',return_value=dep),patch.object(C,'ORIGINAL_CONFIG_PIN',C.R.digest(cfg)),\
                    patch.object(C,'ORIGINAL_PREPARED_PIN',C.R.digest(prepared)),patch.object(C.HISTORICAL,'dependency_context',return_value=old):
                actual=C.dependency_context(dict(source_dependency_prepared=C.bound(path)))
                self.assertEqual(actual['source_worker_config'],C.bound(cfg));self.assertEqual(old,original)
                old['exact']['input_sha256'].clear()
                with self.assertRaises(ValueError):C.dependency_context(dict(source_dependency_prepared=C.bound(path)))
                with self.assertRaises(ValueError):C.dependency_context(dict(source_dependency_prepared=dict(path=str(path),sha256='0'*64)))

    def test_complete_GEN04_only_changes_one_custody_expression_and_typed_namespace(self):
        payload=(ROOT/'test/fixtures/streaming_8x4/GEN04-generate.py.txt').read_bytes()
        original,_=BASE_M.adapted_generator(payload);actual,diff=M.adapted_generator(payload)
        expected=original.replace('import streaming_8x4_closure24_final_m as D','import streaming_8x4_closure24_context_m as D')
        for a,b in (('pinwheel.closure24-actual-target-M.v1','pinwheel.closure24-context-actual-target-M.v1'),('pinwheel.closure24-actual-M-generation.v1','pinwheel.closure24-context-actual-M-generation.v1')):expected=expected.replace(a,b)
        expected=expected.replace("bound_path(prepared['worker_config'])","bound_path(dependency['source_worker_config'])")
        self.assertEqual(actual,expected);self.assertIn("bound_path(dependency['source_worker_config'])",diff)
        self.assertEqual(C.unresolved_names(original),['prepared']);self.assertEqual(C.unresolved_names(actual),[])
        self.assertEqual(C.unresolved_names(actual.replace("bound_path(dependency['source_worker_config'])","missing_context")),['missing_context'])
        self.assertIn('len(ag.flipflops)==6039',actual);self.assertIn('==24',actual)
        for n in ('source_layout','codec_from_backends'):
            self.assertEqual(ast.dump(function(actual,n)),ast.dump(function(original,n)))

    def test_all_top_level_generator_function_scopes_remain_bound(self):
        payload=(ROOT/'test/fixtures/streaming_8x4/GEN04-generate.py.txt').read_bytes();actual,_=M.adapted_generator(payload)
        for node in ast.parse(actual).body:
            if isinstance(node,ast.FunctionDef):self.assertEqual(C.unresolved_names(actual,node.name),[],node.name)

    def test_exact_controller_bodies_reuse_all_native_algorithms_and_budget(self):
        source,_=C.controller_source('execution');baseline=(ROOT/C.EXECUTION).read_text()
        normalized=source.replace('pinwheel.closure24-context-actual-M-positive.v1','pinwheel.closure24-actual-M-positive.v1').replace('pinwheel.closure24-context-actual-M-private.v1','pinwheel.closure24-actual-M-private.v1')
        for name in ('positive','verify_positive','private','verify_private','input_seal','generated_roots_owned'):
            self.assertEqual(ast.dump(function(normalized,name)),ast.dump(function(baseline,name)),name)
        for name in ('compile_one','native_argv','environment','observe_foundation_runtime','runtime_identity','stage_membership','verify_imports','private_texts','verify_private_import_inventory','budget_policy','command_timeout','verify_command_timeout'):
            self.assertIs(getattr(X,name),getattr(BASE_X,name),name)
        self.assertEqual(X.command_timeout('PhysicalGRTExactPrivateAudit'),600);self.assertEqual(X.command_timeout('PhysicalGRTFinalRequired'),180)

    def test_new_typed_controllers_and_full_context_reopening_are_explicit(self):
        gen,diff=C.controller_source('generation');exe,ediff=C.controller_source('execution')
        for token in ('pinwheel.closure24-context-actual-M-preparation.v1','source_worker_context=source_context',"record.get('source_worker_context')==source_context","manifest['fresh_adaptation'].get('source_worker_context')==source_context"):
            self.assertIn(token,gen)
        self.assertIn('pinwheel.closure24-context-actual-M-positive.v1',exe);self.assertIn('pinwheel.closure24-context-actual-M-private.v1',exe)
        self.assertTrue(diff and ediff);self.assertEqual(len(M.SOURCES),len(set(M.SOURCES)))
        for n in (C.OWN,C.NEW_GENERATION,C.NEW_EXECUTION,C.GENERATION,C.EXECUTION):self.assertIn(n,M.SOURCES)

    def test_existing_sealed_module_globals_are_never_redirected(self):
        self.assertEqual(BASE_X.M.__name__,'streaming_8x4_closure24_final_m')
        self.assertEqual(X.M.__name__,'streaming_8x4_closure24_context_m')
        self.assertIs(BASE_M.dependency_context,BASE_M.ORIGINAL.dependency_context)
        self.assertIs(M.dependency_context,C.dependency_context)
        self.assertEqual(C.R.digest(ROOT/C.GENERATION),C.PINS[C.GENERATION]);self.assertEqual(C.R.digest(ROOT/C.EXECUTION),C.PINS[C.EXECUTION])

    def test_frozen_controller_hash_and_single_expression_anchor_fail_closed(self):
        with patch.dict(C.PINS,{C.GENERATION:'0'*64}):
            with self.assertRaises(ValueError):C.controller_source('generation')
        for text in ('no matching custody expression',"bound_path(prepared['worker_config'])\nbound_path(prepared['worker_config'])"):
            with self.assertRaises(ValueError):C.repair_generator(text)

    def test_isolated_functions_bind_new_owner_and_original_context_cannot_change(self):
        self.assertEqual(Path(M.generate.__globals__['__file__']).resolve(),Path(M.__file__).resolve())
        self.assertEqual(Path(X.source_seal.__globals__['__file__']).resolve(),Path(X.__file__).resolve())
        self.assertNotEqual(M.generate.__globals__,BASE_M.generate.__globals__)
        self.assertIs(X.M,M)
        with tempfile.TemporaryDirectory() as d:
            path,dep,cfg,meta,prepared=fixture(Path(d))
            with patch.object(C.N,'verify',return_value=dep):
                with self.assertRaises(ValueError):C.binding(path,dict(dep,source_commit='0'*40))

if __name__=='__main__':unittest.main()
