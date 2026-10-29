"""New source-N worker-config custody binding and exact controller adaptations.

Original GEN04, historical N/F03 receipts, the failed M01 and every earlier
controller remain immutable. Only a removed-local custody expression is repaired;
no proof source, partition, import, resource or private-audit gate is weakened.
"""
import builtins
import difflib
import hashlib
import json
from pathlib import Path
import symtable
import sys
import types

import streaming_8x4_final_dependency as N
import streaming_8x4_final_runtime as R
import streaming_8x4_final_m as HISTORICAL

ROOT=Path(__file__).resolve().parents[1]
GENERATION='scripts/streaming_8x4_closure24_final_m.py'
EXECUTION='scripts/streaming_8x4_closure24_final_m_execute.py'
PINS={GENERATION:'37743b7d1ee01d49df3816e225b19534f28384a83714ce0d6586031af8186bad',
      EXECUTION:'a37202d67f3f0b99ad94de501c51bea7b1263d02c05371696f4315a4a36f6346'}
OWN='scripts/streaming_8x4_closure24_m_context.py'
NEW_GENERATION='scripts/streaming_8x4_closure24_context_m.py'
NEW_EXECUTION='scripts/streaming_8x4_closure24_context_m_execute.py'
ORIGINAL_PREPARED_PIN='9205b15a9efec38ee72c8f4e21e4971883faac9a63fdf5881caa4d276d9d1113'
ORIGINAL_CONFIG_PIN='d43a1ead636a48c3a42a60010b4f5f93e7969b24f20966c4b18a677bebf73adb'


def need(value,message):N.F.require(value,message)
def bound(path):return dict(path=str(R.regular(path).resolve()),sha256=R.digest(path))


def binding(dependency_path,dependency=None):
    """Derive original→restored correspondence, never synthesize old receipts."""
    dependency_path=R.regular(dependency_path).resolve()
    observed=N.verify(dependency_path)
    need(dependency is None or dependency==observed,'Source-N dependency changed during context admission')
    dep=observed;record=dep['original_records']['prepared.json']
    need(record['original_path']==str(N.OLD/N.N/'prepared.json') and
        bound(record['path'])==dict(path=record['path'],sha256=record['sha256']) and
        record['sha256']==ORIGINAL_PREPARED_PIN,'Exact original N preparation authority differs')
    prepared=R.read(record['path']);original=prepared['worker_config']
    need(original==dict(path=str(N.OLD/N.CONFIG),sha256=ORIGINAL_CONFIG_PIN),
        'Original N worker-config receipt/path/hash differs')
    relocated=dep['original_worker_config'];actual=R.regular(relocated['path']).resolve()
    need(bound(actual)==relocated and relocated['sha256']==original['sha256'] and
        dep['input_sha256'].get(str(actual))==original['sha256'],
        'Relocated original worker configuration is missing its exact consumed seal')
    owners=[Path(base) for base in dep['recovered_owner_sha256'] if actual.is_relative_to(Path(base))]
    need(len(owners)==1 and owners[0].name=='final-N-config','Ambiguous/wrong worker-config archive owner')
    owner=owners[0];metadata=R.regular(owner/'RESTORED-FILES-METADATA.jsonl');relative=str(actual.relative_to(owner))
    need(dep['input_sha256'].get(str(metadata))==R.digest(metadata) and
        dep['recovered_owner_sha256'][str(owner)].get(str(metadata.relative_to(owner)))==R.digest(metadata) and
        dep['recovered_owner_sha256'][str(owner)].get(relative)==original['sha256'],
        'Worker-config archive metadata/content seals differ')
    rows=[json.loads(line,object_pairs_hook=N.F.pairs) for line in metadata.read_text().splitlines()]
    matches=[row for row in rows if row.get('path')==N.CONFIG and row.get('kind')=='file']
    need(len(matches)==1 and matches[0]['root']=='wt1373' and matches[0]['sha']==original['sha256'] and
        matches[0]['restored_relative_path']==relative,'Original→restored worker-config archive mapping differs')
    cfg=R.read(actual)
    need(cfg['source_commit']==dep['source_commit']==N.SOURCE,'Original N worker-config source identity differs')
    return dict(schema='pinwheel.closure24-source-N-worker-config-context.v1',source_N=bound(dependency_path),
        original_prepared=record,original_worker_configuration=original,relocated_worker_configuration=relocated,
        archive_owner=str(owner),archive_metadata=bound(metadata),archive_row=matches[0],
        configuration_source_commit=cfg['source_commit'],historical_receipts_rewritten=False,
        original_config_used_as_custody_input=True,derived_generation_config_substituted=False)


def dependency_context(config):
    path=R.regular(config['source_dependency_prepared']['path']).resolve()
    need(bound(path)==config['source_dependency_prepared'],'New context selected another N dependency')
    authority=binding(path);context=HISTORICAL.dependency_context(config)
    concrete=authority['relocated_worker_configuration']
    need(context['exact']['input_sha256'].get(concrete['path'])==concrete['sha256'],
        'Original configuration dropped from complete source-N custody inputs')
    return dict(context,source_worker_config=concrete,source_worker_context=authority)


def replace_once(text,old,new):
    need(text.count(old)==1,'Pinned context adaptation anchor differs: '+old[:100])
    return text.replace(old,new,1)


def unresolved_names(text,function='_generate'):
    table=symtable.symtable(text,'<context-source>','exec')
    globals_={s.get_name() for s in table.get_symbols()}|{'__file__','__name__','__package__','__builtins__'}
    scope=next(c for c in table.get_children() if c.get_name()==function)
    return sorted(s.get_name() for s in scope.get_symbols() if s.is_global() and s.is_referenced()
        and s.get_name() not in globals_ and not hasattr(builtins,s.get_name()))


def repair_generator(text):
    text=replace_once(text,"bound_path(prepared['worker_config'])","bound_path(dependency['source_worker_config'])")
    need(unresolved_names(text)==[],'Context-adapted GEN04 still references an unbound local/global')
    return text


def controller_source(kind):
    """Compile an isolated new controller from the exact immutable body.

    This avoids a drifting copy of the full generation/execution framework.
    Every substitution below is source/receipt context; the original Native
    algorithms and proof generation body remain directly inspectable.
    """
    need(kind in ('generation','execution'),'Unknown context controller kind')
    name=GENERATION if kind=='generation' else EXECUTION;path=R.regular(ROOT/name)
    payload=path.read_bytes();need(hashlib.sha256(payload).hexdigest()==PINS[name],'Frozen base controller changed')
    original=payload.decode();text=original
    anchor='import streaming_tt_fresh_foundation as F'
    text=replace_once(text,anchor,anchor+'\nimport streaming_8x4_closure24_m_context as CONTEXT')
    if kind=='generation':
        text=replace_once(text,'dependency_context = ORIGINAL.dependency_context','dependency_context = CONTEXT.dependency_context')
        text=replace_once(text,"'import streaming_8x4_closure24_final_m as D'","'import streaming_8x4_closure24_context_m as D'")
        text=replace_once(text,'    original = payload.decode()','    text = CONTEXT.repair_generator(text)\n    original = payload.decode()')
        text=replace_once(text,'def bound(path):',"SOURCES = tuple(dict.fromkeys((*SOURCES, CONTEXT.OWN, CONTEXT.NEW_GENERATION, CONTEXT.NEW_EXECUTION, CONTEXT.GENERATION, CONTEXT.EXECUTION)))\n\n\ndef bound(path):")
        text=replace_once(text,'authority = A.verify(authority_path); dep = D.verify(dependency_path)',
            'authority = A.verify(authority_path); dep = D.verify(dependency_path)\n    source_context = CONTEXT.binding(dependency_path,dep)')
        text=replace_once(text,'source_N=bound(dependency_path))','source_N=bound(dependency_path),source_worker_context=source_context)')
        text=replace_once(text,"source_N=bound(dependency_path),generation_request=bound(config_path)",
            "source_N=bound(dependency_path),source_worker_context=source_context,generation_request=bound(config_path)")
        text=replace_once(text,"authority=A.verify(record['authority']['path']);D.verify(record['source_N']['path'])",
            "authority=A.verify(record['authority']['path']);dep=D.verify(record['source_N']['path'])\n    source_context=CONTEXT.binding(record['source_N']['path'],dep)\n    F.require(record.get('source_worker_context')==source_context,'Prepared original N worker-config context changed')")
        text=replace_once(text,"    manifest=R.read(record['generation_manifest']['path'])",
            "    manifest=R.read(record['generation_manifest']['path'])\n    F.require(manifest['fresh_adaptation'].get('source_worker_context')==source_context,'Generated original N worker-config context changed')")
        for old,new in (('pinwheel.closure24-actual-target-M.v1','pinwheel.closure24-context-actual-target-M.v1'),
            ('pinwheel.closure24-actual-M-generation.v1','pinwheel.closure24-context-actual-M-generation.v1'),
            ('pinwheel.closure24-actual-M-preparation.v1','pinwheel.closure24-context-actual-M-preparation.v1')):
            need(old in text,'Missing exact typed generation scope');text=text.replace(old,new)
    else:
        text=replace_once(text,'import streaming_8x4_closure24_final_m as M','import streaming_8x4_closure24_context_m as M')
        text=replace_once(text,'def source_seal():','def source_seal():\n    CONTEXT.controller_source("execution")')
        for old,new in (('pinwheel.closure24-actual-M-positive.v1','pinwheel.closure24-context-actual-M-positive.v1'),
            ('pinwheel.closure24-actual-M-private.v1','pinwheel.closure24-context-actual-M-private.v1')):
            need(old in text,'Missing exact typed execution scope');text=text.replace(old,new)
    diff=''.join(difflib.unified_diff(original.splitlines(keepends=True),text.splitlines(keepends=True),
        fromfile='immutable/'+name,tofile='context/'+name))
    return text,diff


def load_controller(kind,name,path):
    text,diff=controller_source(kind);module=types.ModuleType(name+'.isolated_context_body')
    module.__file__=str(Path(path).resolve());sys.modules[module.__name__]=module
    exec(compile(text,str(module.__file__)+'::isolated-body','exec'),module.__dict__)
    module.CONTROLLER_ADAPTATION_DIFF=diff
    return module
