"""Replace only the full6039 index_field kernel proof by48 bounded chunks."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import sys
import types

import streaming_8x4_closure24_m_finite_transport as FT
import streaming_8x4_closure24_finite_m as PREVIOUS

ROOT=FT.ROOT
OWN='scripts/streaming_8x4_closure24_m_codec_index.py'
GENERATION='scripts/streaming_8x4_closure24_codec_m.py'
ISOLATION='scripts/streaming_8x4_closure24_m_codec_isolation.py'
EXECUTION='scripts/streaming_8x4_closure24_codec_m_execute.py'
BUILDER='scripts/streaming_tt_state.py'
CODEC='PhysicalStateCodec'
CODEC_PIN='4abea79fcd2b6b98e5219dee13de93c2de5530aaa7ef7cdf4a6dfd5d1c6d0f21'
FT_PIN='a7e381069cba6b701d4b99b86a36300d65e6ebd1d559b6278d8b564994d2eb28'
PREVIOUS_PIN='d663a1ee6d17465113713fc29241b91e4248d50362641a15b7da3d43a84ede3d'
STATEMENT='theorem index_field : ∀ index, layoutIndex (layoutField index) = index'
ORIGINAL=STATEMENT+' := by decide +kernel'
need=FT.need
replace_once=FT.replace_once


def digest(text):return hashlib.sha256(text.encode()).hexdigest()


def corrected_block():
    text=FT.corrected_finite_forall('index_field',6039,lambda index:f'layoutIndex (layoutField {index}) = {index}',chunk_width=128)
    typed='theorem index_field : ∀ index : Fin 6039, layoutIndex (layoutField index) = index := by'
    return replace_once(text,typed,STATEMENT+' := by')


def codec_source(text):
    need(digest(text)==CODEC_PIN and text.count(ORIGINAL)==1,'Exact original full Codec source required')
    block=corrected_block();result=replace_once(text,ORIGINAL,block)
    need(result.replace(block,ORIGINAL,1)==text,'Codec change escaped its one original proof')
    public=lambda s:re.findall(r'(?m)^(?:def|theorem)\s+([A-Za-z0-9_]+)',s)
    need(public(text)==public(result)and len(public(text))==829,'Original829public declarations changed')
    chunks=re.findall(r'^private theorem index_field_bounded_chunk_(\d+) : ∀ offset : Fin (\d+), .*?⟨(\d+) \+ offset.val,.*? : Fin (\d+)\).* := by decide \+kernel$',result,re.M)
    need([(int(a),int(b),int(c),int(d))for a,b,c,d in chunks]==
        [(i,min(128,6039-i*128),i*128,6039)for i in range(48)],'Complete47x128+23tail Codec domain differs')
    return result


def transport_sources(sources,finite):
    need(FT.PREVIOUS.R.digest(ROOT/FT.OWN)==FT_PIN and FT.PREVIOUS.R.digest(ROOT/FT.GENERATION)==PREVIOUS_PIN,
        'Original finite producer/entry changed')
    need(type(sources)is dict and len(sources)==3966 and CODEC in sources and
        finite['schema']=='pinwheel.closure24-finite-transport.v1'and finite['total_transport_lines']==547 and
        set(finite['modules'])==set(FT.INVENTORY)and finite['unchanged_module_count']==3959 and CODEC not in finite['modules'],
        'Exact pre-Codec finite stage inventory required')
    for name,row in finite['modules'].items():need(digest(sources[name])==row['after_sha256'],'Finite-stage output changed before Codec transformation')
    before=sources[CODEC];after=codec_source(before);result=dict(sources);result[CODEC]=after
    need([name for name in sources if sources[name]!=result[name]]==[CODEC],'Codec adapter changed another module')
    return result,dict(schema='pinwheel.closure24-codec-index-proof.v1',
        producer=dict(path=str(ROOT/OWN),sha256=FT.PREVIOUS.R.digest(ROOT/OWN)),
        original_codec_sha256=CODEC_PIN,transformed_codec_sha256=digest(after),
        original_public_statement=STATEMENT,original_public_declarations=829,new_private_chunk_lemmas=48,
        chunks=[dict(number=i,start=i*128,width=min(128,6039-i*128))for i in range(48)],full_domain=6039,
        original_public_statements_domains_unchanged=True,other_Codec_bytes_unchanged=True,core_word_unchanged=True,
        proof_body_changed_only='index_field',module_count=3966,external_N=395,complete_positive_modules=4361,
        stage_order=['original-math-generation','seven-module-finite-transport','Codec-index-only','source_layout'],
        pre_Codec_finite_certificate_sha256=digest(json.dumps(finite,sort_keys=True,separators=(',',':'))),
        composed_changed_modules=[*finite['modules'],CODEC],composed_changed_module_count=8,composed_unchanged_module_count=3958,
        finite_stage_claim_is_pre_Codec_only=True,mathematical_sources_unchanged=False,
        mathematical_statements_domains_unchanged=True,codec_index_proof_chunked=True)


def adapt_generator(text):
    text=replace_once(text,'import streaming_8x4_closure24_m_finite_transport as FT\n',
        'import streaming_8x4_closure24_m_finite_transport as FT\nimport streaming_8x4_closure24_m_codec_index as CI\n')
    text=replace_once(text,'    sources,finite_transport=FT.transport_sources(sources)\n    rows,stages,families=source_layout(groups,sources,out_root)',
        '    sources,finite_transport=FT.transport_sources(sources)\n    sources,codec_index_transport=CI.transport_sources(sources,finite_transport)\n    rows,stages,families=source_layout(groups,sources,out_root)')
    text=replace_once(text,'producer_sha256=producer,finite_transport=finite_transport)',
        'producer_sha256=producer,finite_transport=finite_transport,codec_index_transport=codec_index_transport)')
    return text


def controller_source():
    need(FT.PREVIOUS.R.digest(ROOT/FT.OWN)==FT_PIN and FT.PREVIOUS.R.digest(ROOT/FT.GENERATION)==PREVIOUS_PIN,
        'Frozen finite generation family changed')
    original,_=FT.controller_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_m_finite_transport as TRANSPORT',
        'import streaming_8x4_closure24_m_finite_transport as TRANSPORT\nimport streaming_8x4_closure24_m_codec_index as CODEC_INDEX')
    text=replace_once(text,"'import streaming_8x4_closure24_finite_m as D'","'import streaming_8x4_closure24_codec_m as D'")
    text=replace_once(text,'    text = TRANSPORT.adapt_generator(text)','    text = TRANSPORT.adapt_generator(text)\n    text = CODEC_INDEX.adapt_generator(text)')
    text=replace_once(text,'def bound(path):',
        'SOURCES = tuple(dict.fromkeys((*SOURCES, CODEC_INDEX.OWN, CODEC_INDEX.GENERATION, CODEC_INDEX.ISOLATION, CODEC_INDEX.EXECUTION, CODEC_INDEX.BUILDER)))\n\n\ndef bound(path):')
    for old,new in (('pinwheel.closure24-finite-actual-target-M.v1','pinwheel.closure24-codec-index-actual-target-M.v1'),
        ('pinwheel.closure24-finite-actual-M-generation.v1','pinwheel.closure24-codec-index-actual-M-generation.v1'),
        ('pinwheel.closure24-finite-actual-M-preparation.v1','pinwheel.closure24-codec-index-actual-M-preparation.v1')):
        need(old in text,'Missing finite-generation schema');text=text.replace(old,new)
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-finite/generation',tofile='codec-index/generation'))


def load_controller(name,path):
    text,diff=controller_source();module=types.ModuleType(name+'.codec_index_generation');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::codec-index','exec'),module.__dict__)
    module.CODEC_GENERATION_DIFF=diff;return module
