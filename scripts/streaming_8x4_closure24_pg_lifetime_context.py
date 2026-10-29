"""Exact isolated PG loader lifetime repair; historical producers stay sealed.

The temporary Tech owner is replaced by a unique named strong owner retained
through the complete unchanged Native callback. Source-backed cause; successful
Native loading/PSM checks must still be observed under a new Root GO.
"""
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import sys
import types

import streaming_8x4_closure24_power_grid as BASE
import streaming_8x4_power_grid as NATIVE
import streaming_8x4_closure24_policy as POLICY

ROOT = Path(__file__).resolve().parents[1]
OWN = 'scripts/streaming_8x4_closure24_pg_lifetime_context.py'
ENTRY = 'scripts/streaming_8x4_closure24_pg_lifetime.py'
BASE_PATH = 'scripts/streaming_8x4_closure24_power_grid.py'
NATIVE_PATH = 'scripts/streaming_8x4_power_grid.py'
BASE_PIN = '97b24219e6537a9f5412c68da97e8c5d5abc7e5079228ed099bccf030ead4421'
NATIVE_PIN = 'da62b80874ee509c1e277d4d41b9076f98360b2c9ca0937b9cb2bac56c1395b5'
PRIMARY_PIN = '8ab5ad5fcab77443c603771eb245b42d9141b66da52655c3a333249ed3667b0b'
FAILED_REPORT_PIN = '3140bad96810c57a67f9dc7ce4c92c9fdb0d1a939c03a14e6cfeca09f1209371'
FAILED_RESOURCE_PIN = 'b3c8ac46266363c3f806cafc119e3f9058cd6c501a96b91cdfd322acd09b6e71'
CAMPAIGN = 'build/campaigns/8x4-20261024-01'
OLD_LOAD = "    design=Design(Tech());design.readDb(request['source_odb']);block=design.getBlock()"
NEW_LOAD = "    pg_tech_owner=Tech()\n    design=Design(pg_tech_owner);design.readDb(request['source_odb']);block=design.getBlock()"
OLD_IMPORT = 'from streaming_8x4_power_grid import native'
NEW_IMPORT = 'from streaming_8x4_closure24_pg_lifetime import native'
_native_module = None


def need(value, message):
    BASE.require(value, message)


def replace_once(text, old, new):
    need(text.count(old) == 1, 'Exact lifetime adaptation anchor differs: '+old[:100])
    return text.replace(old, new, 1)


def payload(path, pin):
    path = BASE.regular(ROOT/path)
    data = path.read_bytes()
    need(hashlib.sha256(data).hexdigest() == pin, 'Frozen PG source changed')
    return data.decode()


def native_source():
    original = payload(NATIVE_PATH, NATIVE_PIN)
    need('pg_tech_owner' not in original, 'Retained owner name collides with canonical source')
    text = replace_once(original, OLD_LOAD, NEW_LOAD)
    text = replace_once(text, OLD_IMPORT, NEW_IMPORT)
    diff = ''.join(difflib.unified_diff(original.splitlines(keepends=True), text.splitlines(keepends=True),
                                      fromfile='immutable/'+NATIVE_PATH, tofile='lifetime/native.py'))
    return text, diff


def native_module():
    global _native_module
    text, diff = native_source()  # Reopen pinned bytes even when definitions are cached.
    if _native_module is None:
        module = types.ModuleType('_streaming8_pg_lifetime_native')
        module.__file__ = str(ROOT/NATIVE_PATH)
        sys.modules[module.__name__] = module
        exec(compile(text, module.__file__+'::lifetime-body', 'exec'), module.__dict__)
        module.LIFETIME_DIFF = diff
        _native_module = module
    return _native_module


def primary_source(root):
    root = Path(root).resolve();manifest = BASE.regular(root/'manifest.json')
    need(BASE.sha(manifest) == PRIMARY_PIN, 'Exact lifetime primary source manifest differs')
    row = BASE.P.read(manifest)
    need(row['schema'] == 'pinwheel.closure24-pg-lifetime-source.v1' and
         row['commit'] == BASE.COMMIT and row['source_data_only'] is True and
         row['imported_or_executed'] is False and len(row['files']) == 6,
         'Lifetime primary source scope differs')
    expected = {'manifest.json': PRIMARY_PIN}
    for item in row['files']:
        name = item['name'];need(Path(name).name == name and name not in expected, 'Unsafe/duplicate source member')
        data = BASE.regular(root/name).read_bytes()
        need(len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'] and
             hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == item['git_blob'],
             'Lifetime primary source byte/blob differs')
        expected[name] = item['sha256']
    need(BASE.P.inventory(root) == expected, 'Lifetime primary source membership differs')
    return expected


def failed_admission():
    """Reopen the actual failed observer; no OOM or successful PG inference."""
    owner = ROOT/CAMPAIGN/'final24-PG-01'
    report_path = BASE.regular(owner/'report.json')
    resource_path = BASE.regular(ROOT/'build/streaming-tt-resources/8x4-24-final-PG-01/report.json')
    need(BASE.sha(report_path) == FAILED_REPORT_PIN and BASE.sha(resource_path) == FAILED_RESOURCE_PIN,
         'Original failed PG/resource receipt differs')
    report = BASE.P.read(report_path);resource = BASE.P.read(resource_path)
    packet = BASE.verify_preparation(owner)
    need(report['schema'] == 'pinwheel.closure24-power-grid-run.v1' and report['passed'] is False and
         report['geometric_open_path_connectivity'] is False and report['physical_acceptance'] is False and
         report['preparation'] == BASE.bound(owner/'preparation.json') and
         BASE.artifacts(owner) == report['artifact_sha256'], 'Original PG failure was changed/promoted')
    execution = BASE.P.read(owner/'execution.json');leaf = BASE.P.read(owner/'leaf.json')
    need(report['execution'] == execution and execution['status'] == 'completed' and execution['exit_code'] == 2 and
         execution['container_termination']['status'] == 'absent' and leaf['completed'] is False and
         leaf['exit_code'] == -11 and leaf['timeout_seconds'] == 180 and
         leaf['log_sha256'] == BASE.sha(owner/'openroad.log'), 'Original normal Signal11 failure differs')
    raw = (owner/'openroad.log').read_text()
    need('Signal 11 received' in raw and 'ord::OpenRoad::readDb' in raw and
         'PINWHEEL_PG_BEGIN' not in raw and not (owner/'native.json').exists() and
         not list(owner.glob('rail-*-errors.rpt')), 'Original failure phase/check absence differs')
    boundary = resource['campaign_boundary']
    need(resource['schema'] == 'pinwheel.streaming-tt-resource-job.v1' and resource['status'] == 'failed' and
         resource['exit_code'] == 2 and resource['cleanup_confirmed'] is True and
         resource['inputs_unchanged'] is True and resource['owned_processes_remaining'] == [] and
         resource['containers_remaining'] == [] and resource['cleanup_errors'] == [] and
         boundary['campaign_id'] == POLICY.CAMPAIGN and boundary['campaign_kind'] == 'fixed_cad' and
         boundary['shared_lease'] == POLICY.shared_lease_paths(ROOT), 'Original resource cleanup/lease differs')
    need(all(BASE.sha(BASE.regular(path)) == pin for path, pin in resource['input_sha256'].items()),
         'Original PG resource input changed')
    return dict(report=BASE.bound(report_path), resource_report=BASE.bound(resource_path),
                preparation=BASE.bound(owner/'preparation.json'), leaf=BASE.bound(owner/'leaf.json'),
                log=BASE.bound(owner/'openroad.log'), target=packet['target'],
                views_report=packet['views_report'], original_signal11_failure_preserved=True,
                original_PG_checks_executed=False, OOM_diagnosis_claimed=False)


def stage(inputs, source_root, views_report, source_odb):
    sources = primary_source(source_root);failure = failed_admission()
    need(failure['views_report'] == BASE.bound(views_report) and failure['target']['actual_odb'] == BASE.bound(source_odb),
         'Lifetime repair changes the failed observer target/views')
    shutil.copytree(source_root, inputs/'lifetime-source')
    need(primary_source(inputs/'lifetime-source') == sources, 'Staged lifetime source differs')
    return dict(schema='pinwheel.closure24-pg-lifetime-context.v1', primary_source_root=str(Path(source_root).resolve()),
                primary_source_sha256=sources, failed_admission=failure,
                native_source_pin=NATIVE_PIN, controller_source_pin=BASE_PIN,
                named_owner='pg_tech_owner', ownership_delta_only=True,
                actual_loader_repair_observed=False, physical_variant_changed=False)


def verify_context(inputs, context, views_report, source_odb):
    need(context['schema'] == 'pinwheel.closure24-pg-lifetime-context.v1' and
         primary_source(context['primary_source_root']) == context['primary_source_sha256'] ==
         primary_source(Path(inputs)/'lifetime-source') and
         failed_admission() == context['failed_admission'] and
         context['failed_admission']['views_report'] == views_report and
         context['failed_admission']['target']['actual_odb'] == source_odb and
         context['native_source_pin'] == NATIVE_PIN and context['controller_source_pin'] == BASE_PIN and
         context['named_owner'] == 'pg_tech_owner' and context['ownership_delta_only'] is True and
         all(context[k] is False for k in ('actual_loader_repair_observed', 'physical_variant_changed')),
         'Lifetime source/failure/target/context changed')
    native_source();controller_source()
    return context


def controller_source():
    original = payload(BASE_PATH, BASE_PIN)
    text = replace_once(original, 'import streaming_8x4_power_grid as ORIGINAL',
                        'import streaming_8x4_closure24_pg_lifetime_context as LIFETIME\nORIGINAL=LIFETIME.native_module()')
    text = replace_once(text, OLD_IMPORT, NEW_IMPORT)
    need(text.count('streaming_8x4_closure24_power_grid.py') == 2, 'PG controller entrypoint membership differs')
    text = text.replace('streaming_8x4_closure24_power_grid.py', 'streaming_8x4_closure24_pg_lifetime.py')
    text = replace_once(text, 'def prepare(views_path,source_root,output):',
                        'def prepare(views_path,source_root,lifetime_source,output):')
    text = replace_once(text, "    P.write(inputs/'request.json',request)",
                        "    P.write(inputs/'request.json',request)\n    lifetime_context=LIFETIME.stage(inputs,lifetime_source,views_path,source_odb)")
    text = replace_once(text, 'input_sha256=P.inventory(inputs),executed=False,qualified=False,physical_acceptance=False,boundary=BOUNDARY)',
                        'input_sha256=P.inventory(inputs),lifetime_context=lifetime_context,executed=False,qualified=False,physical_acceptance=False,boundary=BOUNDARY)')
    text = replace_once(text, "    request=P.read(output/'inputs/request.json')",
                        "    LIFETIME.verify_context(output/'inputs',packet['lifetime_context'],packet['views_report'],packet['source_odb'])\n    request=P.read(output/'inputs/request.json')")
    text = replace_once(text, "target=packet['target'],physical_candidate=packet['physical_candidate'],runtime=runtime,execution=execution,",
                        "target=packet['target'],physical_candidate=packet['physical_candidate'],runtime=runtime,execution=execution,\n        lifetime_context=packet['lifetime_context'],")
    text = replace_once(text, "    packet=verify_preparation(output);execution=P.read(output/'execution.json')",
                        "    packet=verify_preparation(output);execution=P.read(output/'execution.json')\n    require(report.get('lifetime_context')==packet['lifetime_context'],'PG lifetime context receipt changed')")
    text = replace_once(text, "for name in ('views-report','source-root','output'):",
                        "for name in ('views-report','source-root','lifetime-source','output'):")
    text = replace_once(text, 'prepare(args.views_report,args.source_root,args.output)',
                        'prepare(args.views_report,args.source_root,args.lifetime_source,args.output)')
    for old, new in [('pinwheel.closure24-power-grid-preparation.v1', 'pinwheel.closure24-power-grid-lifetime-preparation.v1'),
                     ('pinwheel.closure24-power-grid-run.v1', 'pinwheel.closure24-power-grid-lifetime-run.v1')]:
        need(old in text, 'Missing typed PG scope');text = text.replace(old, new)
    diff = ''.join(difflib.unified_diff(original.splitlines(keepends=True), text.splitlines(keepends=True),
                                      fromfile='immutable/'+BASE_PATH, tofile='lifetime/controller.py'))
    return text, diff


def load_controller(name, path):
    text, diff = controller_source();module = types.ModuleType(name+'.isolated_lifetime_body')
    module.__file__ = str(Path(path).resolve());sys.modules[module.__name__] = module
    exec(compile(text, module.__file__+'::lifetime-controller', 'exec'), module.__dict__)
    module.LIFETIME_CONTROLLER_DIFF = diff
    return module
