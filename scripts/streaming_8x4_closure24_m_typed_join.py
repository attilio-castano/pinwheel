"""Exact typed-join elaboration fixes and bounded whole-owner audit data.

Old generators, diagnostics and receipts stay immutable. Both complete source
generation and independent derivation apply these transforms before layout.
The private factory reuses the original function code with isolated globals.
"""
import builtins
import difflib
import hashlib
import json
from pathlib import Path
import re
import sys
import types

import streaming_8x4_closure24_m_codec_index as CODEC
import streaming_8x4_closure24_codec_m as PREVIOUS
import streaming_8x4_final_m_execute as ORIGINAL_EXECUTION
from streaming_mapped_campaign import audit_source as ORIGINAL_AUDIT

ROOT=CODEC.ROOT
OWN='scripts/streaming_8x4_closure24_m_typed_join.py'
GENERATION='scripts/streaming_8x4_closure24_join_m.py'
ISOLATION='scripts/streaming_8x4_closure24_m_join_isolation.py'
EXECUTION='scripts/streaming_8x4_closure24_join_m_execute.py'
BUILDERS=('scripts/streaming_tt_composition.py','scripts/streaming_mapped_campaign.py')
FROZEN={CODEC.OWN:'428a396c8350a8b28a0f98c30c4824c76a39a546f953110dcad8fc0445292fba',
    CODEC.GENERATION:'26b974e52bf3852c1962eb1eeec6e438a27623ca524abceb2686e2fce6b80e1b',
    BUILDERS[0]:'0d3ab95639a9dd455e2f08fdb32497c578645d72e574834e4263eaa8a2daf752',
    BUILDERS[1]:'2bf7c994e609db99d437276a80eec589a78b33d6cedf1fdbae2a8106a4498b20',
    'scripts/streaming_8x4_final_m_execute.py':'53738a4ea2e26f63d25d4500ee3049ae105d5f6e5b39ab4676a76fd5c1541bd6'}
TYPED='PhysicalGRTTypedJoin'
ACTUAL='PhysicalGRTActualTypedJoin'
AUDIT='PhysicalGRTFinalAudit'
INPUT_PINS={TYPED:'32e3e8c8f12b398c4609b7a2e0d68c4568a5fad924bd96bc3d3e7049d2c03e78',
    ACTUAL:'9bab1032b3038b2d4c21a2ade150ba4d59ccc2fc7bcc7202db8260d11caa7aed',
    AUDIT:'9db3c82d26fb7ad9601021a8fd982596d7d839694563b2537448f29756fe367e'}
OUTPUT_PINS={TYPED:'13a7715906db268143b413a81a01117372d849b7c7312edb5989b7684b92e85b',
    ACTUAL:'8d19ec8acba9a89cea8f2d2661c2b3eb60b28c8ffa5e9217d318d58e04fa553b',
    AUDIT:'6d7b8522757245ad1881de79317fef9dc01477fb2dfe99f4360f012d87ea7ce7'}
need=CODEC.need
replace_once=CODEC.replace_once


def digest(text):return hashlib.sha256(text.encode()).hexdigest()


def prior_sources():
    for name,pin in FROZEN.items():need(PREVIOUS.R.digest(ROOT/name)==pin,'Frozen typed-join/audit producer changed')


def join_replacements():
    rows=[('(frontendEq : left.frontend = right.frontend)','(frontendEq : @left.frontend = @right.frontend)'),
        ('(coreEq : left.core = right.core)','(coreEq : @left.core = @right.core)')]
    for port in ('miso','ready','busy','levels','enabled'):
        frontend=port in('miso','ready');kind='Frontend'if frontend else'Core';family='frontend'if frontend else'core'
        state='Values Streaming.Frontend.Register'if frontend else'Values (Streaming.Core.Register 1)'
        before=f'    rw [{family}_inputs_typed input bits, {family}_state_typed input bits]\n    exact {family}_observe_typed _ _ .{port}'
        after=('    exact (congr\n      (congrArg\n'+
            f'        (fun (i : Values Streaming.{kind}.Input) (s : {state}) =>\n'+
            f'          Pinwheel.Artifact.StreamingPhysical{kind}.Component.observe i s .{port})\n'+
            f'        ({family}_inputs_typed input bits))\n      ({family}_state_typed input bits)).trans\n'+
            f'        ({family}_observe_typed _ _ .{port})')
        rows.append((before,after))
    return rows


ACTUAL_REPLACEMENT=('  all_goals exact (Pinwheel.Artifact.StreamingPhysicalGRT.ActualProof.observe_correct input bits _).trans\n'
    '    (OriginalProof.observe_correct input bits _).symm',
    '  all_goals exact ((Pinwheel.Artifact.StreamingPhysicalGRT.ActualProof.observe_correct input bits _).trans\n'
    '    (OriginalProof.observe_correct input bits _).symm)')


def exact_replacements(text,rows):
    result=text
    for old,new in rows:result=replace_once(result,old,new)
    reverse=result
    for old,new in reversed(rows):reverse=replace_once(reverse,new,old)
    need(reverse==text,'Typed proof transform escaped declared exact spans')
    return result


def balanced(names):
    need(bool(names),'Empty owner-data tree forbidden')
    if len(names)==1:return names[0]
    middle=len(names)//2
    return '('+balanced(names[:middle])+' ++ '+balanced(names[middle:])+')'


def owner_data(owners):
    need(type(owners)is list and len(owners)in(4360,4362)and len(set(owners))==len(owners)and
        all(type(name)is str and re.fullmatch('[A-Za-z_][A-Za-z0-9_.]*',name)for name in owners),
        'Exact complete positive/private ordered owner list required')
    chunks=[owners[at:at+64]for at in range(0,len(owners),64)]
    names=['auditOwnersChunk'+str(i).zfill(3)for i in range(len(chunks))]
    text='\n'.join(['@[noinline] private def '+name+' : Array String := #['+
        ','.join(json.dumps(owner)for owner in chunk)+']'for name,chunk in zip(names,chunks)]+
        ['@[noinline] private def auditOwners : Array String := '+balanced(names)])+'\n'
    need(len(chunks)==69 and [len(chunk)for chunk in chunks]==[64]*68+[len(owners)-4352],
        'Bounded owner table partition differs')
    return text


def transform_audit(text,owners):
    prior_sources();need(text==ORIGINAL_AUDIT(owners),'Exact original complete auditor source required')
    literal='(#['+','.join(json.dumps(name)for name in owners)+'] : Array String)'
    data=owner_data(owners);result=replace_once(text,literal,'auditOwners')
    result=replace_once(result,'open Lean Elab Command\n',data+'open Lean Elab Command\n')
    reverse=replace_once(result,data,'');reverse=replace_once(reverse,'auditOwners.contains owner',literal+'.contains owner')
    need(reverse==text and re.findall(r'^import .+$',result,re.M)==['import Lean',*['import '+name for name in owners]],
        'Audit owner representation changed body, predicate or ordered imports')
    return result


def audit_source(owners):return transform_audit(ORIGINAL_AUDIT(owners),owners)


def private_factory(original,wrapped_audit):
    """Reuse exact original code; only its NEW local audit_source differs."""
    prior_sources()
    need(original is ORIGINAL_EXECUTION.private_texts and wrapped_audit is audit_source,'Exact isolated private factory inputs required')
    keys=('F','BAD','AUDIT','REQUIRED','verify_private_import_inventory')
    namespace={name:original.__globals__[name]for name in keys}
    namespace.update(__name__=__name__,__builtins__=vars(builtins),audit_source=wrapped_audit)
    result=types.FunctionType(original.__code__,namespace,original.__name__,original.__defaults__,original.__closure__)
    result.__kwdefaults__=original.__kwdefaults__
    need(result.__code__ is original.__code__ and result.__globals__ is not original.__globals__ and
        result.__globals__['audit_source']is wrapped_audit,'Private source factory failed to isolate globals')
    return result


def transport_sources(sources,finite,codec):
    prior_sources()
    need(type(sources)is dict and len(sources)==3966 and set(INPUT_PINS)<=set(sources)and
        finite['schema']=='pinwheel.closure24-finite-transport.v1'and finite['total_transport_lines']==547 and
        set(finite['modules'])==set(CODEC.FT.INVENTORY)and finite['unchanged_module_count']==3959 and
        codec['schema']=='pinwheel.closure24-codec-index-proof.v1'and codec['new_private_chunk_lemmas']==48 and
        codec['composed_changed_module_count']==8 and codec['composed_unchanged_module_count']==3958,
        'Exact finite+Codec pre-stage required before typed-join/audit adaptation')
    for name,row in finite['modules'].items():need(digest(sources[name])==row['after_sha256'],'Earlier finite output changed')
    need(digest(sources[CODEC.CODEC])==codec['transformed_codec_sha256'],'Earlier Codec output changed')
    for name,pin in INPUT_PINS.items():need(digest(sources[name])==pin,'Exact original join/audit source required: '+name)
    result=dict(sources);result[TYPED]=exact_replacements(sources[TYPED],join_replacements())
    result[ACTUAL]=exact_replacements(sources[ACTUAL],[ACTUAL_REPLACEMENT])
    imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',sources[AUDIT],re.M);owners=imports[1:]
    need(imports[0]=='Lean'and len(owners)==4360 and owners[-3965:]==[name for name in sources if name!=AUDIT],
        'Positive audit lost exact ordered N+precedingM ownership')
    result[AUDIT]=transform_audit(sources[AUDIT],owners)
    need([name for name in sources if sources[name]!=result[name]]==list(INPUT_PINS),'Typed-join/audit transform changed another module/order')
    for name,pin in OUTPUT_PINS.items():need(digest(result[name])==pin,'Validated complete diagnostic output differs: '+name)
    return result,dict(schema='pinwheel.closure24-typed-join-audit-transport.v1',
        producer=dict(path=str(ROOT/OWN),sha256=PREVIOUS.R.digest(ROOT/OWN)),
        modules={name:dict(before_sha256=INPUT_PINS[name],after_sha256=digest(result[name]))for name in INPUT_PINS},
        typed_header_annotations=2,typed_observe_proof_spans=5,actual_pad_outer_parentheses_spans=1,
        original_TypedJoin_public_header_text_unchanged=False,full_state_bits=6039,full_input_bits=18,
        full_state_and_input_domains_unchanged=True,full_function_width_polymorphism=True,all_other_public_statements_unchanged=True,
        positive_audit_owners=owners,positive_owner_chunks=[64]*68+[8],private_owner_count=4362,
        audit_predicate_body_imports_allowed_axioms_unchanged=True,positive_and_private_audit_data_representation_changed=True,
        module_count=3966,external_N=395,complete_positive_modules=4361,
        pre_join_Codec_certificate_sha256=digest(json.dumps(codec,sort_keys=True,separators=(',',':'))),
        composed_changed_modules=[*codec['composed_changed_modules'],*INPUT_PINS],
        composed_changed_module_count=11,composed_unchanged_module_count=3955,
        stage_order=['original-math-generation','seven-module-finite-transport','Codec-index-only','typed-joins-and-audit-data','source_layout'])


def adapt_generator(text):
    text=replace_once(text,'import streaming_8x4_closure24_m_codec_index as CI\n',
        'import streaming_8x4_closure24_m_codec_index as CI\nimport streaming_8x4_closure24_m_typed_join as TJ\n')
    text=replace_once(text,'    sources,codec_index_transport=CI.transport_sources(sources,finite_transport)\n    rows,stages,families=source_layout(groups,sources,out_root)',
        '    sources,codec_index_transport=CI.transport_sources(sources,finite_transport)\n    sources,typed_join_transport=TJ.transport_sources(sources,finite_transport,codec_index_transport)\n    rows,stages,families=source_layout(groups,sources,out_root)')
    return replace_once(text,'codec_index_transport=codec_index_transport)',
        'codec_index_transport=codec_index_transport,typed_join_transport=typed_join_transport)')


def controller_source():
    prior_sources();original,_=CODEC.controller_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_m_codec_index as CODEC_INDEX',
        'import streaming_8x4_closure24_m_codec_index as CODEC_INDEX\nimport streaming_8x4_closure24_m_typed_join as TYPED_JOIN')
    text=replace_once(text,"'import streaming_8x4_closure24_codec_m as D'","'import streaming_8x4_closure24_join_m as D'")
    text=replace_once(text,'    text = CODEC_INDEX.adapt_generator(text)',
        '    text = CODEC_INDEX.adapt_generator(text)\n    text = TYPED_JOIN.adapt_generator(text)')
    text=replace_once(text,'def bound(path):',
        'SOURCES = tuple(dict.fromkeys((*SOURCES, TYPED_JOIN.OWN, TYPED_JOIN.GENERATION, TYPED_JOIN.ISOLATION, TYPED_JOIN.EXECUTION, *TYPED_JOIN.BUILDERS)))\n\n\ndef bound(path):')
    for old,new in (('pinwheel.closure24-codec-index-actual-target-M.v1','pinwheel.closure24-typed-join-actual-target-M.v1'),
        ('pinwheel.closure24-codec-index-actual-M-generation.v1','pinwheel.closure24-typed-join-actual-M-generation.v1'),
        ('pinwheel.closure24-codec-index-actual-M-preparation.v1','pinwheel.closure24-typed-join-actual-M-preparation.v1')):
        need(old in text,'Missing original Codec generation schema');text=text.replace(old,new)
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-Codec/generation',tofile='typed-join/generation'))


def load_controller(name,path):
    text,diff=controller_source();module=types.ModuleType(name+'.typed_join_generation');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::typed-join','exec'),module.__dict__)
    module.TYPED_JOIN_GENERATION_DIFF=diff;return module
