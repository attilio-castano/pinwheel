"""One separately typed full official replay after a measured memory stop.

Only Native memory/swap ceiling and coordinator wall budget change. Official
sources, deck/defaults, one CPU, argv, all checks/readers and cleanup stay exact.
No work launches on import; Root alone admits the fresh attempt.
"""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import sys
import types

import streaming_tt_signoff as ORIGINAL
import streaming_8x4_closure24_signoff_execute as BASE
from streaming_tt_intake import dependency_closure

ROOT=Path(__file__).resolve().parents[1]
OWN='scripts/streaming_8x4_closure24_official_budget.py'
ENTRY='scripts/streaming_8x4_closure24_official_replay.py'
READER='scripts/streaming_8x4_closure24_official_readback.py'
CONTROLLER='scripts/streaming_8x4_closure24_signoff_execute.py'
SIGNOFF='scripts/streaming_tt_signoff.py'
PINS={CONTROLLER:'2ee9bb80e980aeebf8533ac14023f7fd095738650b9e6a3175fb7aa9cff7f1e6',
    SIGNOFF:'abd1ffbf0d915c25245104db33a578a957a6070a97dd80b05631d9f9a7bb4f2d'}
OLD_REPORT='d62014b6dfe17ab47a1662a5f7c92a744048a285bbe6fea99e62553b238bbd02'
OLD_GUARD='abeecc53edb77728efa327a3f880c2dfec246e63b363a7e21de0bbb6f6bb4f02'
DECK='12b03e309986ed7f079ca9283eb29d6635918f53ddd09c3c82ea232cca739567'
OUTPUT='final24-official-budget-01'
need=ORIGINAL.require
sha=ORIGINAL.sha


def __getattr__(name):return getattr(ORIGINAL,name)


def replace_once(text,old,new):
    need(text.count(old)==1,'Exact official resource adaptation anchor differs: '+old[:90]);return text.replace(old,new,1)


def policy():
    return dict(schema='pinwheel.closure24-official-resource-policy.v1',whole_precheck_seconds=3600,
        supervisor_seconds=3660,cpus=1,memory_bytes=6442450944,memory_plus_swap_bytes=6442450944,
        extra_swap_bytes=0,tmpfs_bytes=268435456,maximum_attempts=1,complete_selected_checks=9,
        complete_Native_KLayout_calls=3,thread_mode_deck_support_flags_changed=False,
        skipped_checks_or_partial_native_journal_allowed=False,old_memory_stop_remains_incomplete=True,
        physical_acceptance=False,qualified_timing=False,model_qualified=False)


def pinned(name):
    path=ROOT/name;need(sha(path)==PINS[name],'Frozen official controller/helper changed');return path.read_text()


def native_source(name):
    need(name in ('native_klayout','native_journal'),'Unknown explicit6g Native function')
    original=pinned(SIGNOFF);node=next(n for n in ast.parse(original).body if isinstance(n,ast.FunctionDef) and n.name==name)
    text=''.join(original.splitlines(keepends=True)[node.lineno-1:node.end_lineno])
    result=replace_once(text,"'--memory', '2g', '--memory-swap', '2g'","'--memory', '6g', '--memory-swap', '6g'")
    return result,''.join(difflib.unified_diff(text.splitlines(True),result.splitlines(True),fromfile='immutable/'+name,tofile='explicit6g/'+name))


def native_function(name):
    text,_=native_source(name);namespace=dict(vars(ORIGINAL));exec(compile(text,'<explicit6g-'+name+'>','exec'),namespace)
    return namespace[name]


def native_klayout(config_path,arguments):
    config=ORIGINAL.read(config_path)
    need(config.get('schema')=='pinwheel.closure24-official-budget-native-config.v1' and config.get('resource_policy')==policy(),
        'Explicit6g Native wrapper requires its exact typed resource context')
    return native_function('native_klayout')(config_path,arguments)


def native_journal(path,**kwargs):return native_function('native_journal')(path,**kwargs)


def controller_source():
    original=pinned(CONTROLLER);text=original
    text=replace_once(text,'import streaming_tt_signoff as S','import streaming_8x4_closure24_official_budget as S')
    text=replace_once(text,'\n\nlayout_budget =',
        '\n\nSOURCE_ENTRIES = SOURCE_ENTRIES + (S.OWN, S.ENTRY, S.READER)\n\nlayout_budget =')
    text=replace_once(text,"require(1<=timeout<=1800,'Official precheck exceeds bounded30minute allowance')",
        "require(timeout==3600,'The one explicit resource replay requires its fixed3600second whole-precheck budget')")
    text=replace_once(text,"source=inputs/'producer/scripts/streaming_tt_signoff.py'","source=inputs/'producer'/S.OWN")
    text=replace_once(text,"image_id=runtime['image_id'],container_name=S.container_name(output)))",
        "image_id=runtime['image_id'],container_name=S.container_name(output),\n        schema='pinwheel.closure24-official-budget-native-config.v1',resource_policy=S.policy()))")
    text=replace_once(text,"schema='pinwheel.closure24-official-precheck-run.v1'","schema='pinwheel.closure24-official-budget-precheck-run.v1'")
    text=replace_once(text,'official_support_commit=lock[\'support_commit\'],',
        "official_support_commit=lock['support_commit'],resource_policy=S.policy(),")
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable/'+CONTROLLER,tofile='resource-context/'+CONTROLLER))


def controller():
    text,diff=controller_source();module=types.ModuleType(__name__+'.isolated_resource_controller');module.__file__=str(ROOT/ENTRY)
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::resource-body','exec'),module.__dict__)
    module.RESOURCE_ADAPTATION_DIFF=diff;return module


def sources():
    closure=dependency_closure(ROOT,(*BASE.SOURCE_ENTRIES,OWN,ENTRY,READER));return closure,{n:sha(ROOT/n) for n in closure['files']}


def bound(path):
    path=ORIGINAL.regular(path);return dict(path=str(path),sha256=sha(path))


def previous(report_path,guard_path):
    need(sha(report_path)==OLD_REPORT and sha(guard_path)==OLD_GUARD,'Exact measured official memory-stop receipts differ')
    report=ORIGINAL.read(report_path);guard=ORIGINAL.read(guard_path)
    need(report['schema']=='pinwheel.closure24-official-precheck-run.v1' and report['executed'] is False and report['passed'] is False
        and report['error']=='KeyboardInterrupt: signal 15' and report['inputs_pdk_runtime_unchanged'] is True
        and report['cleanup']['status']=='absent','Original official attempt must remain incomplete')
    need(guard['stop_reason']=='ValueError: Container approaching memory limit' and guard['exit_code']==124 and guard['status']=='stopped'
        and guard['cleanup_confirmed'] is True and guard['inputs_unchanged'] is True
        and guard['containers_remaining']==guard['owned_processes_remaining']==guard['cleanup_errors']==[],
        'Original memory-stop/cleanup evidence differs')
    need(report['selected_checks']==list(BASE.Q.OFFICIAL_CHECKS) and report['drc_scope']['deck']['sha256']==DECK and report['drc_scope']['disabled_rule_switches']==[],
        'Original official full check/deck scope differs')
    view,prepared=BASE.closed_views(report['views_report']['path']);need(bound(report['views_report']['path'])==report['views_report'] and view['target']==report['target']
        and view['physical_candidate']==report['physical_candidate'],'Replay must use exact same closed final views/target')
    return report,guard,view,prepared


def prepare(report_path,guard_path,output):
    report_path=ORIGINAL.regular(report_path);guard_path=ORIGINAL.regular(guard_path);output=output.resolve()
    need(not output.exists() and output.parent.is_dir(),'Preserve earlier official replay preparation');old,guard,views,prepared=previous(report_path,guard_path)
    closure,files=sources();text,diff=controller_source();output.mkdir()
    for name,value in [('controller-adaptation.diff',diff),('native-launcher.diff',native_source('native_klayout')[1]),('native-reader.diff',native_source('native_journal')[1])]:
        (output/name).write_text(value)
    argv=guard['argv'];values={argv[i]:argv[i+1] for i in range(4,len(argv),2)}
    support=Path(values['--support']);python=Path(values['--python']);BASE.Q.official_sources(support,Path(prepared['prepared'])/'inputs/tt_block_8x4_pgvdd.def')
    row=dict(schema='pinwheel.closure24-official-resource-preparation.v1',prior_report=bound(report_path),prior_guard=bound(guard_path),
        views_report=old['views_report'],physical_candidate=old['physical_candidate'],target=old['target'],support=str(support),python=str(python),
        output=str(output.parent/OUTPUT),policy=policy(),producer_dependency_closure=closure,producer_sha256=files,
        diffs={p.name:sha(p) for p in output.iterdir()},executed=False,Root_GO_required=True,physical_acceptance=False)
    ORIGINAL.write(output/'plan.json',row);verify(output/'plan.json');return row


def verify(path):
    path=ORIGINAL.regular(path);row=ORIGINAL.read(path);old,guard,views,prepared=previous(Path(row['prior_report']['path']),Path(row['prior_guard']['path']))
    need(row['schema']=='pinwheel.closure24-official-resource-preparation.v1' and row['policy']==policy() and row['executed'] is False
        and row['physical_acceptance'] is False and row['Root_GO_required'] is True and row['views_report']==old['views_report']
        and row['target']==old['target'] and row['physical_candidate']==old['physical_candidate'],'Resource replay exact plan/context/scope differs')
    need(row['prior_report']==bound(row['prior_report']['path']) and row['prior_guard']==bound(row['prior_guard']['path']),'Prior memory-stop evidence binding changed')
    argv=guard['argv'];values={argv[i]:argv[i+1] for i in range(4,len(argv),2)}
    need(row['support']==values['--support'] and row['python']==values['--python'] and Path(row['output'])==path.parent.parent/OUTPUT,'Replay caller/runtime or fresh output differs')
    closure,files=sources();need(row['producer_dependency_closure']==closure and row['producer_sha256']==files,'Replay producer closure changed')
    expected={'controller-adaptation.diff':controller_source()[1],'native-launcher.diff':native_source('native_klayout')[1],'native-reader.diff':native_source('native_journal')[1]}
    need(set(row['diffs'])==set(expected) and {p.name for p in path.parent.iterdir()}=={'plan.json'}|set(expected),'Replay diff membership differs')
    for name,text in expected.items():need((path.parent/name).read_text()==text and sha(path.parent/name)==row['diffs'][name],'Replay exact resource adaptation differs')
    return row


def proposal(path):
    row=verify(path);return dict(schema='pinwheel.closure24-official-resource-command.v1',plan=bound(path),
        argv=[sys.executable,'-B',str(ROOT/ENTRY),'run','--plan',str(path.resolve())],
        output=row['output'],container_name=ORIGINAL.container_name(Path(row['output'])),policy=policy(),
        views_report=row['views_report'],producer_sha256=row['producer_sha256'],executed=False,Root_GO_required=True,physical_acceptance=False)


def run(path):
    plan=verify(path);need(not Path(plan['output']).exists(),'Never reuse earlier official full attempt')
    report=controller().run_official(Path(plan['views_report']['path']),Path(plan['support']),Path(plan['python']),Path(plan['output']),3600)
    report.update(resource_replay_plan=bound(path),prior_memory_stop=dict(report=plan['prior_report'],resource=plan['prior_guard']))
    ORIGINAL.write(Path(plan['output'])/'report.json',report);return report
