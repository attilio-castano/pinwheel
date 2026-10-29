"""Portable index-only source/chunk/namespace/budget controls; no Lean."""
from copy import deepcopy
from pathlib import Path
import re
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_m_codec_index as C
import streaming_8x4_closure24_codec_m as M
import streaming_8x4_closure24_m_codec_isolation as I
import streaming_8x4_closure24_codec_m_execute as X
import streaming_8x4_closure24_m_finite_isolation as OLD
import streaming_8x4_closure24_finite_m as OLDM


def codec_fixture():
    # Compact structural fixture with the real829-public-declaration census.
    # It tests source transformation, not kernel validity or actual geometry.
    defs=[f'def fixture{i} : Nat := {i}'for i in range(759)]
    groups=['theorem core_word : True := by trivial']+[f'theorem group{i} : True := by trivial'for i in range(65)]
    return '\n\n'.join([*defs,C.ORIGINAL,*groups,'theorem field_index : True := by trivial',
        'theorem arbitrary_state : True := by trivial','theorem arbitrary_package : True := by trivial'])


class CodecIndexControls(unittest.TestCase):
    def setUp(self):
        self.text=codec_fixture();self.pin=patch.object(C,'CODEC_PIN',C.digest(self.text));self.pin.start();self.addCleanup(self.pin.stop)

    def test_public_statement_all_other_bytes_and_core_word_are_exact(self):
        result=C.codec_source(self.text);block=C.corrected_block()
        self.assertEqual(result.replace(block,C.ORIGINAL),self.text)
        self.assertIn(C.STATEMENT+' := by\n',result)
        self.assertNotIn(C.STATEMENT.replace('∀ index,','∀ index : Fin 6039,')+' := by',result)
        self.assertIn('theorem core_word : True := by trivial',result)
        self.assertNotIn('#eval',result);self.assertNotIn('stderrAsMessages',result)

    def test_independent6039_index_coverage47full_plus23tail(self):
        result=C.codec_source(self.text);chunks=re.findall(r'^private theorem index_field_bounded_chunk_(\d+) : ∀ offset : Fin (\d+), .*?⟨(\d+) \+ offset.val,.*? : Fin (\d+)\).* := by decide \+kernel$',result,re.M)
        self.assertEqual(len(chunks),48);points=[]
        for i,(number,width,start,domain)in enumerate(chunks):
            self.assertEqual((int(number),int(start),int(domain)),(i,i*128,6039));points.extend(range(int(start),int(start)+int(width)))
        self.assertEqual(points,list(range(6039)));self.assertEqual([int(r[1])for r in chunks],[128]*47+[23])
        self.assertEqual(len(re.findall(r'(?m)^(?:def|theorem)\s+',result)),829)
        self.assertEqual(result.count('private theorem index_field_bounded_chunk_'),48)

    def test_changed_statement_duplicate_or_foreign_source_and_chunk_refuse(self):
        for value in [self.text+'\n',self.text.replace(C.ORIGINAL,C.ORIGINAL+'\n'+C.ORIGINAL),
            self.text.replace('layoutField index','layoutField changed',1)]:
            with self.assertRaises(ValueError):C.codec_source(value)
        block=C.corrected_block()
        for value in [block.replace('Fin 23,','Fin 22,',1),block.replace('⟨128 + offset.val','⟨129 + offset.val',1)]:
            with patch.object(C,'corrected_block',return_value=value):
                with self.assertRaises(ValueError):C.codec_source(self.text)

    def test_exact_stage_composition_only_Codec_changes_after_finite(self):
        sources={name:'finite-output-'+name for name in C.FT.INVENTORY};sources[C.CODEC]=self.text
        sources.update({f'Untouched{i}':'unchanged-'+str(i)for i in range(3966-len(sources))})
        finite=dict(schema='pinwheel.closure24-finite-transport.v1',total_transport_lines=547,unchanged_module_count=3959,
            modules={name:dict(after_sha256=C.digest(sources[name]))for name in C.FT.INVENTORY})
        new,certificate=C.transport_sources(sources,finite)
        self.assertEqual([n for n in sources if new[n]!=sources[n]],[C.CODEC])
        self.assertEqual(len(new),3966);self.assertEqual(certificate['new_private_chunk_lemmas'],48)
        self.assertEqual(certificate['composed_changed_module_count'],8);self.assertEqual(certificate['composed_unchanged_module_count'],3958)
        self.assertTrue(certificate['finite_stage_claim_is_pre_Codec_only'])
        for change in [lambda v:v.update(total_transport_lines=546),lambda v:v['modules'].pop(next(iter(v['modules']))),
            lambda v:v['modules'][next(iter(v['modules']))].update(after_sha256='0'*64)]:
            wrong=deepcopy(finite);change(wrong)
            with self.assertRaises(ValueError):C.transport_sources(sources,wrong)

    def test_hook_orders_finite_then_Codec_then_new_hash_layout(self):
        source=('import streaming_8x4_closure24_m_finite_transport as FT\n'+
            '    sources,finite_transport=FT.transport_sources(sources)\n    rows,stages,families=source_layout(groups,sources,out_root)\n'+
            'producer_sha256=producer,finite_transport=finite_transport)')
        new=C.adapt_generator(source)
        self.assertLess(new.index('FT.transport_sources'),new.index('CI.transport_sources'))
        self.assertLess(new.index('CI.transport_sources'),new.index('source_layout'))
        self.assertIn('codec_index_transport=codec_index_transport',new)
        with self.assertRaises(ValueError):C.adapt_generator(source+source)
        for name in (C.OWN,C.GENERATION,C.ISOLATION,C.EXECUTION,C.BUILDER):self.assertIn(name,M.SOURCES)

    def test_fresh_generation_rederive_positive_private_readers_all_use_new_M(self):
        for name in ('sources','input_seal','rederive','run_rederive','verify_rederive'):
            self.assertIs(getattr(I,name).__globals__['M'],M,name)
            self.assertIs(getattr(OLD,name).__globals__['M'],OLDM,name)
        for name in ('positive','private','verify_positive','verify_private'):
            self.assertIs(getattr(X,name).__globals__['M'],M,name)
            self.assertIs(getattr(X,name).__globals__['ISOLATION'],I,name)
        self.assertEqual(I.compile_source(),OLD.compile_source())
        self.assertIs(X.compile_one.__globals__['PROCESS'],OLD.PROCESS)

    def test_budget_metadata_honest_and_limits_and_private_controls_unchanged(self):
        policy=X.budget_policy();old=OLD.budget_policy()
        self.assertFalse(policy['mathematical_sources_unchanged']);self.assertFalse(policy['mathematical_statements_domains_chunks_unchanged'])
        for name in ('mathematical_statements_domains_unchanged','original_seven_finite_chunk_domains_unchanged','codec_index_proof_chunked'):
            self.assertTrue(policy[name])
        for name in ('default_module_seconds','exact_long_module_seconds','exact_long_modules','outer_four_hour_limit_unchanged','outer_positive_cutoff_and_private_wire_reserve_required'):
            self.assertEqual(policy[name],old[name])
        for name in ('native_argv','command_timeout','verify_command_timeout','imports','verify_imports','private_texts','observe_foundation_runtime'):
            self.assertIs(getattr(X,name),getattr(OLD.PRIOR,name),name)
        self.assertEqual(I.REDERIVE_SECONDS,600)

    def test_full_execution_body_only_new_M_context_and_typed_schema(self):
        text,_=I.controller_source();old,_=OLD.controller_source()
        text=text.replace('streaming_8x4_closure24_codec_m as M','streaming_8x4_closure24_finite_m as M')
        text=text.replace('streaming_8x4_closure24_m_codec_isolation as ISOLATION','streaming_8x4_closure24_m_finite_isolation as ISOLATION')
        text=text.replace('pinwheel.closure24-codec-index-isolated-actual-M-','pinwheel.closure24-finite-isolated-actual-M-')
        self.assertEqual(text,old)


if __name__=='__main__':unittest.main()
