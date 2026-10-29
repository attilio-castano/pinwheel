"""Portable exact-span/owner/private/global-context controls; no Lean/build data."""
import ast
from copy import deepcopy
import inspect
from pathlib import Path
import re
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_composition as COMPOSITION
import streaming_8x4_closure24_m_typed_join as T
import streaming_8x4_closure24_join_m as M
import streaming_8x4_closure24_m_join_isolation as I
import streaming_8x4_closure24_join_m_execute as X
import streaming_8x4_closure24_m_codec_isolation as OLD
import streaming_8x4_closure24_codec_m as OLDM


def fixture():
    sources={name:'finite-'+name for name in T.CODEC.FT.INVENTORY}
    sources[T.CODEC.CODEC]='codec-output'
    sources.update(COMPOSITION.generate());sources.update(COMPOSITION.generate_actual())
    sources.update({f'Untouched{i}':'unchanged-'+str(i)for i in range(3965-len(sources))})
    owners=[f'SourceN{i}'for i in range(395)]+list(sources)
    sources[T.AUDIT]=T.ORIGINAL_AUDIT(owners)
    finite=dict(schema='pinwheel.closure24-finite-transport.v1',total_transport_lines=547,unchanged_module_count=3959,
        modules={name:dict(after_sha256=T.digest(sources[name]))for name in T.CODEC.FT.INVENTORY})
    codec=dict(schema='pinwheel.closure24-codec-index-proof.v1',new_private_chunk_lemmas=48,
        transformed_codec_sha256=T.digest(sources[T.CODEC.CODEC]),composed_changed_modules=[*finite['modules'],T.CODEC.CODEC],
        composed_changed_module_count=8,composed_unchanged_module_count=3958)
    return sources,finite,codec


class TypedJoinControls(unittest.TestCase):
    def test_actual_typed_and_actual_join_outputs_equal_validated_diagnostic_bytes(self):
        typed=COMPOSITION.generate()[T.TYPED];actual=COMPOSITION.generate_actual()[T.ACTUAL]
        self.assertEqual(T.digest(typed),T.INPUT_PINS[T.TYPED]);self.assertEqual(T.digest(actual),T.INPUT_PINS[T.ACTUAL])
        fixed=T.exact_replacements(typed,T.join_replacements())
        self.assertEqual(T.digest(fixed),T.OUTPUT_PINS[T.TYPED])
        self.assertEqual(T.digest(T.exact_replacements(actual,[T.ACTUAL_REPLACEMENT])),T.OUTPUT_PINS[T.ACTUAL])
        self.assertEqual(len(T.join_replacements()),7)
        self.assertIn('(frontendEq : @left.frontend = @right.frontend)',fixed)
        self.assertIn('(coreEq : @left.core = @right.core)',fixed)
        self.assertEqual(fixed.count('    exact (congr\n'),5)
        self.assertNotIn('sorry',fixed);self.assertNotIn('set_option maxRecDepth 100001',fixed)

    def test_foreign_duplicate_missing_or_changed_proof_span_refuses(self):
        typed=COMPOSITION.generate()[T.TYPED];old,new=T.join_replacements()[0]
        for bad in (typed.replace(old,old+'\n'+old,1),typed.replace(old,'changed',1)):
            with self.assertRaises(ValueError):T.exact_replacements(bad,T.join_replacements())
        sources,finite,codec=fixture()
        with patch.dict(T.INPUT_PINS,{T.AUDIT:T.digest(sources[T.AUDIT])}),patch.dict(T.OUTPUT_PINS,{T.AUDIT:T.digest(T.audit_source(
                re.findall(r'^import ([A-Za-z0-9_.]+)$',sources[T.AUDIT],re.M)[1:]))}):
            for name in (T.TYPED,T.ACTUAL):
                wrong=dict(sources);wrong[name]+='\n'
                with self.assertRaises(ValueError):T.transport_sources(wrong,finite,codec)

    def test_complete_owner_data_is_ordered_bounded_and_private_count_is_separate(self):
        for count in (4360,4362):
            owners=[f'Owner{i}'for i in range(count)];data=T.owner_data(owners)
            rows=re.findall(r'@\[noinline\] private def auditOwnersChunk(\d+) : Array String := #\[(.*?)\]$',data,re.M)
            chunks=[T.json.loads('['+body+']')for _,body in rows]
            self.assertEqual([name for chunk in chunks for name in chunk],owners)
            self.assertEqual([len(chunk)for chunk in chunks],[64]*68+[count-4352]);self.assertEqual(len(rows),69)
            self.assertEqual(data.count('@[noinline] private def auditOwners :'),1)
            self.assertNotIn('set_option',data)
        for owners in ([f'O{i}'for i in range(4359)],['same']*4360,[f'O{i}'for i in range(4361)]):
            with self.assertRaises(ValueError):T.owner_data(owners)

    def test_auditor_imports_body_none_case_whitelist_and_order_reverse_exact(self):
        owners=[f'Owner{i}'for i in range(4360)];old=T.ORIGINAL_AUDIT(owners);new=T.transform_audit(old,owners)
        literal='(#['+','.join(T.json.dumps(n)for n in owners)+'] : Array String)'
        reverse=new.replace(T.owner_data(owners),'',1).replace('auditOwners.contains owner',literal+'.contains owner',1)
        self.assertEqual(reverse,old)
        self.assertIn('| none => info.isAxiom || info.isTheorem',new)
        for token in ('for (name, info) in env.constants.toList','collectAxioms name','``propext','``Classical.choice','``Quot.sound','Empty mapped audit'):
            self.assertIn(token,new)
        for bad in (old+'\n',old.replace('info.isAxiom || info.isTheorem','info.isTheorem'),old.replace('``Quot.sound','``False')):
            with self.assertRaises(ValueError):T.transform_audit(bad,owners)

    def test_three_module_post_Codec_transform_and_honest11_total_changes(self):
        sources,finite,codec=fixture();audit_pin=T.digest(sources[T.AUDIT])
        owners=re.findall(r'^import ([A-Za-z0-9_.]+)$',sources[T.AUDIT],re.M)[1:]
        expected=T.digest(T.audit_source(owners))
        with patch.dict(T.INPUT_PINS,{T.AUDIT:audit_pin}),patch.dict(T.OUTPUT_PINS,{T.AUDIT:expected}):
            new,cert=T.transport_sources(sources,finite,codec)
            self.assertEqual([name for name in sources if sources[name]!=new[name]],list(T.INPUT_PINS))
            self.assertEqual(len(new),3966);self.assertEqual(cert['composed_changed_module_count'],11)
            self.assertEqual(cert['composed_unchanged_module_count'],3955)
            self.assertFalse(cert['original_TypedJoin_public_header_text_unchanged']);self.assertTrue(cert['full_function_width_polymorphism'])
            for wrong in (dict(codec,new_private_chunk_lemmas=47),dict(codec,transformed_codec_sha256='0'*64)):
                with self.assertRaises(ValueError):T.transport_sources(sources,finite,wrong)
            wrong=deepcopy(finite);wrong['modules'].pop(next(iter(wrong['modules'])))
            with self.assertRaises(ValueError):T.transport_sources(sources,wrong,codec)

    def test_private_original_code_BAD_and_inventory_unchanged_new_globals_only(self):
        old=T.ORIGINAL_EXECUTION.private_texts;old_global=old.__globals__['audit_source'];owners=[f'Owner{i}'for i in range(4360)]+[X.REQUIRED]
        texts=X.private_texts(owners);original=old(owners)
        self.assertIs(X.private_texts.__code__,old.__code__);self.assertIsNot(X.private_texts.__globals__,old.__globals__)
        self.assertIs(X.private_texts.__globals__['audit_source'],T.audit_source)
        self.assertIs(old.__globals__['audit_source'],old_global)
        self.assertEqual(texts[X.BAD],original[X.BAD]);self.assertEqual(texts[X.AUDIT],T.transform_audit(original[X.AUDIT],[*owners,X.BAD]))
        X.verify_private_import_inventory(texts,owners)
        with self.assertRaises(ValueError):T.private_factory(lambda owners:{},T.audit_source)
        with self.assertRaises(ValueError):T.private_factory(old,T.ORIGINAL_AUDIT)
        with self.assertRaises(ValueError):X.private_texts(owners[:-1])

    def test_both_execution_and_private_verifier_share_exact_new_factory(self):
        for name in ('private','verify_private'):
            self.assertIs(getattr(X,name).__globals__['private_texts'],X.private_texts)
            self.assertIs(getattr(X,name).__globals__['audit_source'],T.audit_source)
        self.assertIs(X.verify_private_import_inventory,T.ORIGINAL_EXECUTION.verify_private_import_inventory)

    def test_independent_derive_and_generation_hook_before_new_source_hash_layout(self):
        source=('import streaming_8x4_closure24_m_codec_index as CI\n'+
            '    sources,codec_index_transport=CI.transport_sources(sources,finite_transport)\n    rows,stages,families=source_layout(groups,sources,out_root)\n'+
            'codec_index_transport=codec_index_transport)')
        new=T.adapt_generator(source)
        self.assertLess(new.index('CI.transport_sources'),new.index('TJ.transport_sources'));self.assertLess(new.index('TJ.transport_sources'),new.index('source_layout'))
        self.assertIn('typed_join_transport=typed_join_transport',new)
        with self.assertRaises(ValueError):T.adapt_generator(source+source)
        text,_=T.controller_source();self.assertIn('    text = TYPED_JOIN.adapt_generator(text)',text)
        for name in (T.OWN,T.GENERATION,T.ISOLATION,T.EXECUTION,*T.BUILDERS):self.assertIn(name,M.SOURCES)

    def test_all_operational_M_globals_are_new_and_old_globals_stay_old(self):
        for name in ('sources','input_seal','rederive','run_rederive','verify_rederive'):
            self.assertIs(getattr(I,name).__globals__['M'],M,name);self.assertIs(getattr(OLD,name).__globals__['M'],OLDM,name)
        for name in ('positive','private','verify_positive','verify_private'):
            self.assertIs(getattr(X,name).__globals__['M'],M,name);self.assertIs(getattr(X,name).__globals__['ISOLATION'],I,name)
        self.assertEqual(I.compile_source(),OLD.compile_source());self.assertIs(X.compile_one.__globals__['PROCESS'],OLD.PROCESS)

    def test_exact_timeouts_compiler_and_budget_flags_honest(self):
        policy=X.budget_policy();old=OLD.budget_policy()
        for key in ('default_module_seconds','exact_long_module_seconds','exact_long_modules','outer_four_hour_limit_unchanged','outer_positive_cutoff_and_private_wire_reserve_required'):
            self.assertEqual(policy[key],old[key])
        self.assertFalse(policy['original_TypedJoin_public_header_text_unchanged']);self.assertFalse(policy['mathematical_statements_domains_unchanged'])
        for key in ('full_state_and_input_domains_unchanged','full_function_width_polymorphism','all_other_public_statements_unchanged','positive_and_private_audit_data_representation_changed','audit_predicate_owners_axioms_unchanged'):
            self.assertTrue(policy[key])
        for name in ('native_argv','command_timeout','verify_command_timeout','imports','verify_imports','observe_foundation_runtime'):
            self.assertIs(getattr(X,name),getattr(OLD.PRIOR,name))
        self.assertEqual(I.REDERIVE_SECONDS,600)

    def test_execution_body_only_new_context_private_binding_and_schemas(self):
        text,_=I.controller_source();old,_=OLD.controller_source()
        text=text.replace('streaming_8x4_closure24_join_m as M','streaming_8x4_closure24_codec_m as M')
        text=text.replace('streaming_8x4_closure24_m_join_isolation as ISOLATION','streaming_8x4_closure24_m_codec_isolation as ISOLATION')
        text=text.replace('import streaming_8x4_closure24_m_typed_join as TYPED_JOIN\naudit_source = TYPED_JOIN.audit_source','from streaming_mapped_campaign import audit_source')
        text=text.replace('private_texts = TYPED_JOIN.private_factory(ORIGINAL.private_texts, audit_source)','private_texts = ORIGINAL.private_texts')
        text=text.replace('pinwheel.closure24-typed-join-isolated-actual-M-','pinwheel.closure24-codec-index-isolated-actual-M-')
        self.assertEqual(text,old)

    def test_diagnostic_provenance_is_hash_only_without_ignored_controller_imports(self):
        source=inspect.getsource(I.failure_binding);tree=ast.parse(source)
        attributes={node.attr for node in ast.walk(tree)if isinstance(node,ast.Attribute)}
        self.assertFalse({'read','verify_rederive','admit','exec_module','load'}&attributes)
        self.assertIn('digest',attributes);self.assertIn('failure_binding',attributes)
        production=(T.ROOT/T.OWN).read_text()+(T.ROOT/I.OWN).read_text()
        self.assertNotIn('root_typed_join_tail_diagnostic_',production)
        self.assertNotIn('root_audit_owner_chunk_control_',production)


if __name__=='__main__':unittest.main()
