"""Exact finite-proof transport correction; statements/domains/chunks unchanged."""
import difflib
import hashlib
from pathlib import Path
import re
import sys
import types

import streaming_tt_finite as FINITE
import streaming_8x4_closure24_m_scope as SCOPE
import streaming_8x4_closure24_scope_m as PREVIOUS

ROOT=SCOPE.ROOT
OWN='scripts/streaming_8x4_closure24_m_finite_transport.py'
GENERATION='scripts/streaming_8x4_closure24_finite_m.py'
ISOLATION='scripts/streaming_8x4_closure24_m_finite_isolation.py'
EXECUTION='scripts/streaming_8x4_closure24_finite_m_execute.py'
FINITE_NAME='scripts/streaming_tt_finite.py'
FINITE_PIN='97e0f1f9b1f5d00331201ad9e439da9fd74a6735023bbc2086699eaba2499032'
PRIOR={SCOPE.OWN:'5779710a191020264bea4ba2d87e2303c24b97b572f40b3722d3f96a8b216030',
    'scripts/streaming_8x4_closure24_scope_m.py':'9d61699fb801350bbcd7cc0e75c97d728a4218852ab21b903f53c4e58e458faa'}
need=SCOPE.need
replace_once=SCOPE.replace_once
INVENTORY={
    'PhysicalGRTCanonicalDevice':(('nextBound',6039,128),('outputBound',24,128)),
    'PhysicalGRTOriginalDevice':(('nextBound',6039,128),('outputBound',24,128)),
    'PhysicalGRTActualDevice':(('nextBound',6039,128),('outputBound',24,128)),
    'ActualGRTClockDAGProof':tuple((name,6039,128)for name in ('clockBound','resetBound','clock_image','reset_image')),
    'ActualGRTClockInventory':(('ctsBound',1016,128),('ctsImage',1016,128)),
    'PhysicalGRTOriginalProof':(('next',6039,64),('output',24,64)),
    'PhysicalGRTActualProof':(('next',6039,64),('output',24,64))}


def digest(text):return hashlib.sha256(text.encode()).hexdigest()


def finite_source():
    text=(ROOT/FINITE_NAME).read_text();need(digest(text)==FINITE_PIN,'Frozen finite producer changed')
    old="            indent + 'simpa only [same] using witness',"
    new="            indent + f'simpa only [same, show {start} + (index.val - {start}) = index.val from congrArg Fin.val same] using witness',"
    return replace_once(text,old,new)


def corrected_finite_forall(*args,**kwargs):
    namespace={'__name__':__name__+'.finite_copy','__file__':str(ROOT/OWN)}
    exec(compile(finite_source(),'<exact-finite-transport-function-copy>','exec'),namespace)
    return namespace['finite_forall'](*args,**kwargs)


def transport_sources(sources):
    """Re-emit exact complete finite blocks BEFORE source_layout hashes them.

    Both _generate and derive call this same pure transformation. Every old
    block must equal the pinned canonical function's complete output, not a
    regex approximation or an edited old source file.
    """
    need(type(sources)is dict and set(INVENTORY)<=set(sources),'Complete seven-module finite transport inventory required')
    result=dict(sources);records={};total=0
    for module,text in sources.items():
        old=text;count=0
        for name,domain,width in INVENTORY.get(module,()):
            matches=re.findall(r'^theorem '+re.escape(name)+r' : ∀ index : Fin '+str(domain)+r', (.+) := by$',text,re.M)
            need(len(matches)==1,'Exact finite public statement missing/duplicated: '+module+'/'+name)
            statement=matches[0]
            def proposition(index):return re.sub(r'\bindex\b',lambda _:index,statement)
            expected=FINITE.finite_forall(name,domain,proposition,chunk_width=width)
            corrected=corrected_finite_forall(name,domain,proposition,chunk_width=width)
            need(text.count(expected)==1,'Finite original statement/chunk/transport body is not canonical: '+module+'/'+name)
            expected_count=(domain+width-1)//width
            need(len(re.findall(r'^\s+simpa only \[same\] using witness$',expected,re.M))==expected_count,
                'Finite canonical transport count differs')
            text=text.replace(expected,corrected,1);count+=expected_count
        # Reject a foreign/omitted transport in ANY module, including the 3959
        # modules expected to remain byte-identical.
        need(not re.search(r'^\s+simpa only \[same\] using witness$',text,re.M),'Unaccounted finite transport line: '+module)
        if module in INVENTORY:
            before=old.splitlines();after=text.splitlines();need(len(before)==len(after),'Finite source line count changed')
            changed=[(a,b)for a,b in zip(before,after)if a!=b]
            need(len(changed)==count and all(a.strip()=='simpa only [same] using witness'and
                re.fullmatch(r'\s+simpa only \[same, show [0-9]+ \+ \(index.val - [0-9]+\) = index.val from congrArg Fin.val same\] using witness',b)
                for a,b in changed),'Finite correction changed more than exact transport tactics')
            records[module]=dict(before_sha256=digest(old),after_sha256=digest(text),transport_lines=count,
                statements_domains_chunks_unchanged=True)
        else:need(text==old,'Foreign generated source changed')
        result[module]=text;total+=count
    need(len(records)==7 and total==547,'Complete fixed-target finite transport count differs')
    return result,dict(schema='pinwheel.closure24-finite-transport.v1',producer=dict(path=str(ROOT/OWN),sha256=PREVIOUS.R.digest(ROOT/OWN)),
        original_finite=dict(path=str(ROOT/FINITE_NAME),sha256=FINITE_PIN),modules=records,total_transport_lines=547,
        unchanged_module_count=len(sources)-7,mathematical_sources_unchanged=False,
        mathematical_statements_domains_chunks_unchanged=True,proof_transport_tactics_changed=True)


def controller_source():
    for name,pin in PRIOR.items():need(PREVIOUS.R.digest(ROOT/name)==pin,'Frozen source-generation context changed')
    original,_=SCOPE.controller_source('generation');text=original
    text=replace_once(text,'import streaming_8x4_closure24_m_scope as SCOPE',
        'import streaming_8x4_closure24_m_scope as SCOPE\nimport streaming_8x4_closure24_m_finite_transport as TRANSPORT')
    text=replace_once(text,"'import streaming_8x4_closure24_scope_m as D'","'import streaming_8x4_closure24_finite_m as D'")
    text=replace_once(text,'    text = SCOPE.rename_context(text)','    text = SCOPE.rename_context(text)\n    text = TRANSPORT.adapt_generator(text)')
    text=replace_once(text,'def bound(path):',
        'SOURCES = tuple(dict.fromkeys((*SOURCES, TRANSPORT.OWN, TRANSPORT.GENERATION, TRANSPORT.ISOLATION, TRANSPORT.EXECUTION, TRANSPORT.FINITE_NAME)))\n\n\ndef bound(path):')
    for old,new in (('pinwheel.closure24-scope-actual-target-M.v1','pinwheel.closure24-finite-actual-target-M.v1'),
        ('pinwheel.closure24-scope-actual-M-generation.v1','pinwheel.closure24-finite-actual-M-generation.v1'),
        ('pinwheel.closure24-scope-actual-M-preparation.v1','pinwheel.closure24-finite-actual-M-preparation.v1')):
        need(old in text,'Missing old full-generation schema');text=text.replace(old,new)
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-scope/generation',tofile='finite-transport/generation'))


def adapt_generator(text):
    text=replace_once(text,'import streaming_tt_finite\n','import streaming_tt_finite\nimport streaming_8x4_closure24_m_finite_transport as FT\n')
    text=replace_once(text,'    rows,stages,families=source_layout(groups,sources,out_root)',
        '    sources,finite_transport=FT.transport_sources(sources)\n    rows,stages,families=source_layout(groups,sources,out_root)')
    text=replace_once(text,'        layout_profile=LAYOUT_PROFILE,diagnostic_families=families,input_sha256=inputs,producer_sha256=producer)',
        '        layout_profile=LAYOUT_PROFILE,diagnostic_families=families,input_sha256=inputs,producer_sha256=producer,finite_transport=finite_transport)')
    return text


def load_controller(name,path):
    text,diff=controller_source();module=types.ModuleType(name+'.finite_generation_body');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::finite-transport','exec'),module.__dict__)
    module.FINITE_GENERATION_DIFF=diff;return module
