"""New scope-only repair for adapter context shadowed by GEN04's import loop.

The original import-loop variable and every mathematical/source-layout operation
remain unchanged. Earlier context/base sources and failed attempts are immutable.
"""
import ast
from pathlib import Path
import sys
import types
import difflib

import streaming_8x4_closure24_m_context as CONTEXT

ROOT=Path(__file__).resolve().parents[1]
OWN='scripts/streaming_8x4_closure24_m_scope.py'
NEW_GENERATION='scripts/streaming_8x4_closure24_scope_m.py'
NEW_EXECUTION='scripts/streaming_8x4_closure24_scope_m_execute.py'
PRIOR={CONTEXT.OWN:'70f12b1fa4eba37cdc4a52a9444c914b2603eae41c1cedcdff47b7b4ec7e844f',
    CONTEXT.NEW_GENERATION:'b9ebfda4d1d42b2647c1a6c841a6ca55d318115d743a49499022388bad21b4ca',
    CONTEXT.NEW_EXECUTION:'1ab09541ef455ba7761fbbc1aaa07ce6b8dd2978a8ee5b9e01e7cbe0d007a1f7'}
NAME='source_dependency_context'
need=CONTEXT.need
replace_once=CONTEXT.replace_once


def rename_context(text):
    need(NAME not in text,'New descriptive context name already exists')
    anchors=(
        '    dependency=D.dependency_context(config)',
        "    prepared_path=dependency['prepared_path'];source_plan_path=dependency['source_plan_path']",
        "    source_plan=dependency['source_plan'];marker=dependency['marker'];binding=dependency['binding']",
        "    cfg=dependency['cfg'];worker_path=dependency['worker_path'];worker=dependency['worker']",
        "    positive_path=dependency['positive_path'];exact=dependency['exact'];worker_root=worker_path.parent",
        "bound_path(dependency['source_worker_config'])",
        '    F.require(D.dependency_context(config)==dependency,')
    for old in anchors:
        new=old.replace('dependency[',NAME+'[').replace('    dependency=', '    '+NAME+'=').replace('==dependency,','=='+NAME+',')
        text=replace_once(text,old,new)
    function=next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name=='_generate')
    stores=[n for n in ast.walk(function) if isinstance(n,ast.Name) and n.id==NAME and isinstance(n.ctx,ast.Store)]
    need(len(stores)==1,'Introduced context name is reassigned or missing')
    need(CONTEXT.unresolved_names(text)==[],'Scope repair introduced an unresolved generator name')
    return text


def controller_source(kind):
    for name,pin in PRIOR.items():
        need(CONTEXT.R.digest(ROOT/name)==pin,'Prior frozen context producer changed: '+name)
    original,_=CONTEXT.controller_source(kind);text=original
    text=replace_once(text,'import streaming_8x4_closure24_m_context as CONTEXT',
        'import streaming_8x4_closure24_m_context as CONTEXT\nimport streaming_8x4_closure24_m_scope as SCOPE')
    if kind=='generation':
        text=replace_once(text,"'import streaming_8x4_closure24_context_m as D'","'import streaming_8x4_closure24_scope_m as D'")
        text=replace_once(text,'    text = CONTEXT.repair_generator(text)',
            '    text = CONTEXT.repair_generator(text)\n    text = SCOPE.rename_context(text)')
        text=replace_once(text,'def bound(path):',
            'SOURCES = tuple(dict.fromkeys((*SOURCES, SCOPE.OWN, SCOPE.NEW_GENERATION, SCOPE.NEW_EXECUTION)))\n\n\ndef bound(path):')
        changes=(('pinwheel.closure24-context-actual-target-M.v1','pinwheel.closure24-scope-actual-target-M.v1'),
            ('pinwheel.closure24-context-actual-M-generation.v1','pinwheel.closure24-scope-actual-M-generation.v1'),
            ('pinwheel.closure24-context-actual-M-preparation.v1','pinwheel.closure24-scope-actual-M-preparation.v1'))
    else:
        text=replace_once(text,'import streaming_8x4_closure24_context_m as M','import streaming_8x4_closure24_scope_m as M')
        text=replace_once(text,'def source_seal():','def source_seal():\n    SCOPE.controller_source("execution")')
        changes=(('pinwheel.closure24-context-actual-M-positive.v1','pinwheel.closure24-scope-actual-M-positive.v1'),
            ('pinwheel.closure24-context-actual-M-private.v1','pinwheel.closure24-scope-actual-M-private.v1'))
    for old,new in changes:
        need(old in text,'Missing exact prior typed scope');text=text.replace(old,new)
    diff=''.join(difflib.unified_diff(original.splitlines(keepends=True),text.splitlines(keepends=True),
        fromfile='immutable-context/'+kind,tofile='scope/'+kind))
    return text,diff


def load_controller(kind,name,path):
    text,diff=controller_source(kind);module=types.ModuleType(name+'.isolated_scope_body')
    module.__file__=str(Path(path).resolve());sys.modules[module.__name__]=module
    exec(compile(text,str(module.__file__)+'::isolated-scope-body','exec'),module.__dict__)
    module.SCOPE_CONTROLLER_ADAPTATION_DIFF=diff
    return module
