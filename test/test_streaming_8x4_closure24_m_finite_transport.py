"""Portable complete finite-transport/source-owner/budget controls; no Lean."""
import ast
from copy import deepcopy
from pathlib import Path
import re
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_m_finite_transport as T
import streaming_8x4_closure24_finite_m as M
import streaming_8x4_closure24_m_finite_isolation as I
import streaming_8x4_closure24_finite_m_execute as X
import streaming_8x4_closure24_m_ps_isolation as OLD
import streaming_8x4_closure24_scope_m as OLDM


def fixture():
    result={}
    for module,rows in T.INVENTORY.items():
        blocks=[]
        for name,count,width in rows:
            # Both use patterns occur in actual graph/clock/composition output:
            # an explicit Fin argument and an already projected Nat argument.
            proposition=(lambda index:f'FinPredicate {index}')if 'image'in name or name=='ctsImage'else(lambda index:f'NatPredicate ({index}).val')
            blocks.append(T.FINITE.finite_forall(name,count,proposition,chunk_width=width))
        result[module]='\n\n'.join(blocks)
    result['UntouchedOwner']='theorem untouched : True := by trivial\n'
    return result


class FiniteTransportControls(unittest.TestCase):
    def test_exact_function_copy_has_one_template_line_change(self):
        old=(T.ROOT/T.FINITE_NAME).read_text();new=T.finite_source()
        pairs=[(a,b)for a,b in zip(old.splitlines(),new.splitlines())if a!=b]
        self.assertEqual(len(pairs),1);self.assertEqual(len(old.splitlines()),len(new.splitlines()))
        self.assertIn('congrArg Fin.val same',pairs[0][1]);self.assertIn('[same, show {start}',pairs[0][1])

    def test_Nat_and_Fin257_preserve_all_three_chunks_and_public_statement(self):
        for proposition in (lambda index:f'NatPredicate ({index}).val',lambda index:f'FinPredicate {index}'):
            old=T.FINITE.finite_forall('test',257,proposition);new=T.corrected_finite_forall('test',257,proposition)
            self.assertEqual(old.count('private theorem'),3);self.assertEqual(new.count('private theorem'),3)
            self.assertEqual([s for s in old.splitlines()if not s.strip().startswith('simpa only')],
                [s for s in new.splitlines()if not s.strip().startswith('simpa only')])
            for start in (0,128,256):self.assertIn(f'show {start} + (index.val - {start}) = index.val from congrArg Fin.val same',new)

    def test_complete_seven_module547_line_transform_keeps_all_other_bytes(self):
        old=fixture();new,receipt=T.transport_sources(old)
        self.assertEqual(list(new),list(old));self.assertEqual(receipt['total_transport_lines'],547)
        self.assertEqual(len(receipt['modules']),7);self.assertEqual(receipt['unchanged_module_count'],1)
        self.assertEqual(new['UntouchedOwner'],old['UntouchedOwner'])
        for module in T.INVENTORY:
            a=old[module].splitlines();b=new[module].splitlines();diff=[(x,y)for x,y in zip(a,b)if x!=y]
            self.assertEqual(len(a),len(b));self.assertEqual(len(diff),receipt['modules'][module]['transport_lines'])
            self.assertTrue(all(x.strip()=='simpa only [same] using witness'and'congrArg Fin.val same'in y for x,y in diff))
        self.assertFalse(receipt['mathematical_sources_unchanged']);self.assertTrue(receipt['mathematical_statements_domains_chunks_unchanged'])

    def test_independent_exact_domain_census_includes_all6039_and_tail(self):
        new,_=T.transport_sources(fixture())
        for module,rows in T.INVENTORY.items():
            for name,count,width in rows:
                chunks=re.findall(r'^private theorem '+name+r'_bounded_chunk_\d+ : ∀ offset : Fin (\d+), (.+) := by decide \+kernel$',new[module],re.M)
                points=[]
                for n,proposition in chunks:
                    match=re.search(r'⟨(\d+) \+ offset.val, .*?⟩ : Fin (\d+)',proposition)
                    self.assertIsNotNone(match);self.assertEqual(int(match[2]),count)
                    points.extend(range(int(match[1]),int(match[1])+int(n)))
                self.assertEqual(points,list(range(count)))

    def test_omission_duplicate_shift_typo_and_foreign_transport_reject(self):
        old=fixture();module='PhysicalGRTCanonicalDevice'
        mutations=[]
        missing=deepcopy(old);missing.pop(module);mutations.append(missing)
        shifted=deepcopy(old);shifted[module]=shifted[module].replace('⟨128 + offset.val','⟨129 + offset.val',1);mutations.append(shifted)
        typo=deepcopy(old);typo[module]=typo[module].replace('simpa only [same] using witness','simpa only [same] using nonexistent',1);mutations.append(typo)
        duplicate=deepcopy(old);duplicate[module]+='\n'+duplicate[module];mutations.append(duplicate)
        foreign=deepcopy(old);foreign['UntouchedOwner']+='\n  simpa only [same] using witness\n';mutations.append(foreign)
        for value in mutations:
            with self.assertRaises(ValueError):T.transport_sources(value)
        with patch.object(T,'FINITE_PIN','0'*64):
            with self.assertRaises(ValueError):T.finite_source()

    def test_generator_hook_is_before_source_hash_layout_and_derive_uses_generate(self):
        # Compact exact anchor literals; no test depends on ignored campaign data.
        source=('import streaming_tt_finite\n'+'    rows,stages,families=source_layout(groups,sources,out_root)\n'+
            '        layout_profile=LAYOUT_PROFILE,diagnostic_families=families,input_sha256=inputs,producer_sha256=producer)')
        new=T.adapt_generator(source)
        self.assertLess(new.index('FT.transport_sources'),new.index('source_layout'))
        self.assertIn('finite_transport=finite_transport',new)
        with self.assertRaises(ValueError):T.adapt_generator(source+source)
        self.assertIs(M.verify.__globals__['TRANSPORT'],T)
        for name in (T.OWN,T.GENERATION,T.ISOLATION,T.EXECUTION,T.FINITE_NAME):self.assertIn(name,M.SOURCES)

    def test_full_independent_generation_and_opaque_execution_own_new_M_globals(self):
        for name in ('rederive','run_rederive','verify_rederive','sources'):
            self.assertIs(getattr(I,name).__globals__['M'],M,name)
            self.assertIs(getattr(OLD,name).__globals__['M'],OLDM,name)
        for name in ('positive','private','verify_positive','verify_private'):
            self.assertIs(getattr(X,name).__globals__['M'],M,name)
            self.assertIs(getattr(X,name).__globals__['ISOLATION'],I,name)
        self.assertIs(X.compile_one.__globals__['PROCESS'],OLD.PROCESS)
        self.assertEqual(I.compile_source(),OLD.compile_source());self.assertEqual(I.REDERIVE_SECONDS,600)

    def test_native_budgets_identical_and_proof_text_change_is_honest(self):
        new=X.budget_policy();old=OLD.PRIOR.budget_policy()
        self.assertFalse(new['mathematical_sources_unchanged']);self.assertTrue(new['proof_transport_tactics_changed'])
        self.assertTrue(new['mathematical_statements_domains_chunks_unchanged'])
        for name in ('default_module_seconds','exact_long_module_seconds','exact_long_modules','outer_four_hour_limit_unchanged','outer_positive_cutoff_and_private_wire_reserve_required'):
            self.assertEqual(new[name],old[name])
        for name in ('command_timeout','verify_command_timeout','native_argv','imports','verify_imports','private_texts','observe_foundation_runtime'):
            self.assertIs(getattr(X,name),getattr(OLD.PRIOR,name),name)

    def test_full_execution_body_only_new_context_schema_and_budget_metadata(self):
        text,_=I.controller_source();old,_=OLD.controller_source()
        text=text.replace('streaming_8x4_closure24_finite_m as M','streaming_8x4_closure24_scope_m as M')
        text=text.replace('streaming_8x4_closure24_m_finite_isolation as ISOLATION','streaming_8x4_closure24_m_ps_isolation as ISOLATION')
        text=text.replace('budget_policy = ISOLATION.budget_policy','budget_policy = ORIGINAL.budget_policy')
        text=text.replace('pinwheel.closure24-finite-isolated-actual-M-','pinwheel.closure24-opaque-isolated-actual-M-')
        self.assertEqual(text,old)

    def test_large_failed_report_is_hash_only_and_no_accepted_prefix(self):
        node=next(n for n in ast.parse(Path(I.__file__).read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='failure_binding')
        calls=[ast.unparse(n.func)for n in ast.walk(node)if isinstance(n,ast.Call)]
        self.assertFalse(any('verify_rederive'in c or 'M.verify'in c for c in calls))
        self.assertIn('PREVIOUS.R.digest',calls)
        reads=[ast.unparse(n)for n in ast.walk(node)if isinstance(n,ast.Call)and ast.unparse(n.func)=='PREVIOUS.R.read']
        self.assertEqual(reads,['PREVIOUS.R.read(guard)'])


if __name__=='__main__':unittest.main()
