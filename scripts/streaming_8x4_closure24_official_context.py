"""Separate immutable65-view authority from the new71-source replay producer.

The prior68-source attempt failed in HOST context before output/Native creation.
Its sources and failed resource receipt remain unchanged. One full6g attempt
is still subject to Root commit/GO and the unchanged complete official gates.
"""
import difflib
from pathlib import Path
import sys
import types
import streaming_8x4_closure24_official_budget as OLD

ROOT=OLD.ROOT
OWN='scripts/streaming_8x4_closure24_official_context.py'
ENTRY='scripts/streaming_8x4_closure24_official_context_replay.py'
READER='scripts/streaming_8x4_closure24_official_context_readback.py'
PINS={OLD.OWN:'af090469c633b78c705ae1d27bc9c223b0fd8c604854ee94a7349a2bfb307cef',
    OLD.ENTRY:'4ad265d65824863c9f9e7f679b83b5803cbcb7a344ca064af4a5e4e7a79442a7',
    OLD.READER:'d9152040628cf79222e4dcd68c288f8b56eb34c71cb85e53514bf51dc88daedd'}
PRIOR_PLAN='d23284b98af8bdad4865c5ff16d208eedde5ff0e0ef449cfffd54aca2355f4e2'
PRIOR_PROPOSAL='c27f9db6cf144137e2fcce3e46bce545b1fd129a9508ed347219c39579352047'
PRIOR_LAUNCHER='6b1b2c448a520fdc8da507291f7bc822116523a73c3af731a3c6da13ddae6d5a'
PRIOR_FAILURE='7f7b9665ddfde28570bee061641ee1fa15b10e233af24d623a903df05d484b9b'
PRIOR_LOG='049553a9681c2bcfacf4c017f7e4be9c243eda51a0edbd70b923aa8cf9596663'
OUTPUT='final24-official-context-01'
need,sha,bound=OLD.need,OLD.sha,OLD.bound
policy=OLD.policy
# runpy.run_path returns a dictionary, not module getattr delegation. These
# explicit keys are required by the unchanged staged Native wrapper shape.
native_klayout=OLD.native_klayout
native_journal=OLD.native_journal


def __getattr__(name):return getattr(OLD,name)


def old_sources():
    for name,pin in PINS.items():need(sha(ROOT/name)==pin,'Frozen68-source resource adapter changed')


def controller_source():
    old_sources();original,_=OLD.controller_source();text=original
    text=OLD.replace_once(text,'import streaming_8x4_closure24_official_budget as S','import streaming_8x4_closure24_official_context as S')
    text=OLD.replace_once(text,'SOURCE_ENTRIES = SOURCE_ENTRIES + (S.OWN, S.ENTRY, S.READER)',
        'SOURCE_ENTRIES = SOURCE_ENTRIES + (S.OLD.OWN, S.OLD.ENTRY, S.OLD.READER, S.OWN, S.ENTRY, S.READER)')
    text=OLD.replace_once(text,'\ndef run_official(',
        '\n# Prior views retain their exact immutable65-source authority namespace.\nclosed_views = S.OLD.BASE.closed_views\n\ndef run_official(')
    text=OLD.replace_once(text,'pinwheel.closure24-official-budget-precheck-run.v1','pinwheel.closure24-official-context-precheck-run.v1')
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-resource/controller',tofile='authority-context/controller'))


def controller():
    text,diff=controller_source();module=types.ModuleType(__name__+'.isolated_context_controller');module.__file__=str(ROOT/ENTRY)
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::authority-context','exec'),module.__dict__)
    module.AUTHORITY_CONTEXT_DIFF=diff;return module


def sources():
    names=(*OLD.BASE.SOURCE_ENTRIES,OLD.OWN,OLD.ENTRY,OLD.READER,OWN,ENTRY,READER)
    closure=OLD.dependency_closure(ROOT,names);return closure,{n:sha(ROOT/n) for n in closure['files']}


def previous_context(plan_path,failure_path):
    plan_path=OLD.ORIGINAL.regular(plan_path);failure_path=OLD.ORIGINAL.regular(failure_path)
    need(sha(plan_path)==PRIOR_PLAN and sha(failure_path)==PRIOR_FAILURE,'Exact pre-Native context failure identities differ')
    plan=OLD.verify(plan_path);failure=OLD.ORIGINAL.read(failure_path);log=failure_path.parent/'native.log'
    need(sha(log)==PRIOR_LOG and failure['status']=='failed' and failure['exit_code']==1 and failure['cleanup_confirmed'] is True and failure['inputs_unchanged'] is True
        and failure['containers_remaining']==failure['owned_processes_remaining']==failure['cleanup_errors']==[], 'Prior HOST context failure/cleanup differs')
    directory=plan_path.parent.parent;proposal=directory/'final24-official-budget-command-proposal-03.json';launcher=directory/'final24-official-budget-launch-reopen-03.json'
    need(sha(proposal)==PRIOR_PROPOSAL and sha(launcher)==PRIOR_LAUNCHER and failure['argv']==OLD.ORIGINAL.read(proposal)['argv'], 'Prior context caller/proposal/launcher differs')
    required={str(plan_path):PRIOR_PLAN,**{str(ROOT/name):pin for name,pin in plan['producer_sha256'].items()}}
    need(all(failure['input_sha256'].get(name)==pin for name,pin in required.items()),'Prior68-source actual resource seals differ')
    need(not Path(plan['output']).exists(),'Prior pre-Native attempt unexpectedly created an output owner')
    evidence=dict(plan=bound(plan_path),failed_resource=bound(failure_path),failure_log=bound(log),proposal=bound(proposal),launcher=bound(launcher))
    return plan,dict(schema='pinwheel.closure24-official-preNative-context-failure.v1',evidence=evidence,
        failed_context_stays_failed=True,prior_output_created=False,prior_Native_KLayout_started=False)


def authority_preflight(views):
    actual=controller();need(actual.closed_views is OLD.BASE.closed_views and actual.closed_views.__globals__ is OLD.BASE.__dict__,
        'Prior view verifier lost its original authority namespace')
    a=actual.closed_views(views);b=OLD.BASE.closed_views(views);need(a==b,'Actual adapted-controller closed-view preflight differs')
    producer=OLD.dependency_closure(ROOT,actual.SOURCE_ENTRIES);authority=OLD.dependency_closure(ROOT,OLD.BASE.SOURCE_ENTRIES)
    need(a[1]['producer_dependency_closure']==authority and set(authority['files'])<set(producer['files']), 'Original authority/new producer membership contexts were mixed')
    return dict(real_adapted_closed_views_preflight_passed=True,original_authority_source_files=len(authority['files']),
        new_replay_source_files=len(producer['files']),same_exact_closed_views=bound(views),immutable_view_metadata_preserved=True)


def prepare(prior_plan,failure,output):
    output=output.resolve();need(not output.exists() and output.parent.is_dir(),'Preserve earlier context correction preparation')
    prior,failed=previous_context(prior_plan,failure);preflight=authority_preflight(Path(prior['views_report']['path']));closure,files=sources();output.mkdir()
    (output/'controller-context.diff').write_text(controller_source()[1]);(output/'reader-context.diff').write_text(reader_source()[1])
    row=dict(prior,schema='pinwheel.closure24-official-authority-context-preparation.v1',prior_resource_plan=bound(prior_plan),pre_native_failure=failed,
        actual_authority_preflight=preflight,output=str(output.parent/OUTPUT),producer_dependency_closure=closure,producer_sha256=files,
        diffs={p.name:sha(p) for p in output.iterdir()})
    OLD.ORIGINAL.write(output/'plan.json',row);verify(output/'plan.json');return row


def verify(path):
    path=OLD.ORIGINAL.regular(path);row=OLD.ORIGINAL.read(path)
    prior,failed=previous_context(Path(row['prior_resource_plan']['path']),Path(row['pre_native_failure']['evidence']['failed_resource']['path']))
    closure,files=sources();preflight=authority_preflight(Path(prior['views_report']['path']))
    expected=dict(prior,schema='pinwheel.closure24-official-authority-context-preparation.v1',prior_resource_plan=bound(row['prior_resource_plan']['path']),pre_native_failure=failed,
        actual_authority_preflight=preflight,output=str(path.parent.parent/OUTPUT),producer_dependency_closure=closure,producer_sha256=files,
        diffs={name:sha(path.parent/name) for name in ('controller-context.diff','reader-context.diff')})
    need(row==expected and {p.name for p in path.parent.iterdir()}=={'plan.json','controller-context.diff','reader-context.diff'},'Exact corrected context plan/source/custody differs')
    need((path.parent/'controller-context.diff').read_text()==controller_source()[1] and (path.parent/'reader-context.diff').read_text()==reader_source()[1],'Inspectable context adaptation changed')
    return row


def proposal(path):
    row=verify(path);return dict(schema='pinwheel.closure24-official-authority-context-command.v1',plan=bound(path),
        argv=[sys.executable,'-B',str(ROOT/ENTRY),'run','--plan',str(path.resolve())],output=row['output'],container_name=OLD.ORIGINAL.container_name(Path(row['output'])),
        policy=policy(),views_report=row['views_report'],producer_sha256=row['producer_sha256'],executed=False,Root_GO_required=True,physical_acceptance=False)


def run(path):
    plan=verify(path);need(not Path(plan['output']).exists(),'Never reuse an official Native attempt')
    report=controller().run_official(Path(plan['views_report']['path']),Path(plan['support']),Path(plan['python']),Path(plan['output']),3600)
    report.update(resource_replay_plan=bound(path),prior_memory_stop=dict(report=plan['prior_report'],resource=plan['prior_guard']),prior_context_failure=plan['pre_native_failure'])
    OLD.ORIGINAL.write(Path(plan['output'])/'report.json',report);return report


def reader_source():
    old_sources();original=(ROOT/OLD.READER).read_text();text=original
    text=OLD.replace_once(text,'import streaming_8x4_closure24_official_budget as B','import streaming_8x4_closure24_official_context as B')
    text=OLD.replace_once(text,"    B.need(all(resource['input_sha256'].get(name)==pin for name,pin in required.items())",
        "    required.update({entry['path']:entry['sha256'] for entry in plan['pre_native_failure']['evidence'].values()})\n    B.need(all(resource['input_sha256'].get(name)==pin for name,pin in required.items())")
    text=OLD.replace_once(text,"and report['prior_memory_stop']==dict(report=plan['prior_report'],resource=plan['prior_guard'])",
        "and report['prior_memory_stop']==dict(report=plan['prior_report'],resource=plan['prior_guard']) and report['prior_context_failure']==plan['pre_native_failure']")
    text=OLD.replace_once(text,'pinwheel.closure24-official-budget-precheck-run.v1','pinwheel.closure24-official-context-precheck-run.v1')
    text=OLD.replace_once(text,'pinwheel.closure24-official-budget-independent-readback.v1','pinwheel.closure24-official-context-independent-readback.v1')
    text=OLD.replace_once(text,"prior_memory_stop=dict(report=plan['prior_report'],resource=plan['prior_guard']),resource_policy=B.policy()",
        "prior_memory_stop=dict(report=plan['prior_report'],resource=plan['prior_guard']),prior_context_failure=plan['pre_native_failure'],resource_policy=B.policy()")
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-resource/reader',tofile='authority-context/reader'))


def load_reader():
    text,_=reader_source();module=types.ModuleType(__name__+'.isolated_context_reader');module.__file__=str(ROOT/READER)
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::authority-context','exec'),module.__dict__);return module
