"""HOST admission of relocated historical source N for a fresh actual-M proof.

Original receipts, argv, paths and source bytes are never rewritten. New
records pair them with exactly restored bytes, independently regenerate every
source module, and stage only the395 positive imports. Historical private
controls stay outside that import root. No Lean or recovered tool runs here.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
import types

sys.dont_write_bytecode = True
import streaming_8x4_final_runtime as R
import streaming_tt_fresh_foundation as F

ROOT = Path(__file__).resolve().parents[1]
OLD = Path('/Users/attiliocastano/.codex/worktrees/1373/pinwheel')
N = 'build/streaming-physical-development/formal-balanced-e2-replay-unqualified-01'
PRIVATE = 'build/streaming-physical-development/formal-balanced-e2-private-unqualified-01'
WORKER = 'build/validation/streaming-tt-balanced-device-02/worker'
CONFIG = 'build/validation/streaming-tt-balanced-device-02/worker-config.json'
PINS = {'prepared.json':'9205b15a9efec38ee72c8f4e21e4971883faac9a63fdf5881caa4d276d9d1113',
    'plan.json':'152f1e5e3aeb0de339b6d0e35ce05724f31b4dd786ba78bfa0786c18b5e0bb0b',
    'positive-manifest.json':'d9f160f6483d74b88852e38ce6cfbc8473092519a23798f7d84299e0ef8e3b85',
    'report.json':'e0b3720a1207f91648a654583a4a33abaf91809104a4df6bc1e2ccb0b9c4de43'}
OWNERS = ('final-N-replay','final-N-worker','final-N-config','final-N-parent','final-N-private',
          'final-N-raw-frontend','final-N-raw-core','final-N-library')
SOURCE = 'e2e8e38aa0698a50eadc03ee2d8b58d2096a633a'
FORMAL = 'ca26fdfd7a93c1d12c831f3f399b5ea0d5d89534'


def bind(path): return dict(path=str(R.regular(path).resolve()), sha256=R.digest(path))


class Recovery:
    def __init__(self, root, owners=OWNERS):
        self.root = Path(root).resolve(strict=True); self.files = {}; self.seals = {}; self.aliases = {}
        for owner in owners:
            base = self.root / owner; metadata = R.regular(base / 'RESTORED-FILES-METADATA.jsonl')
            expected = {str(metadata.relative_to(base)):R.digest(metadata)}
            for line in metadata.read_text().splitlines():
                row = json.loads(line, object_pairs_hook=F.pairs)
                F.require(row['root'] == 'wt1373' and row['kind'] in ('file','dir'), 'Unexpected source-N archive owner/type')
                if row['kind'] == 'dir': continue
                relative = F.relative(row['restored_relative_path']); original = str(OLD / F.relative(row['path']))
                F.require(original not in self.files, 'Ambiguous source-N recovery ownership')
                actual = base / relative
                self.files[original] = dict(path=str(actual), sha256=row['sha']); expected[str(relative)] = row['sha']
            self.seals[str(base)] = expected
        self.intact()

    def intact(self):
        for base, expected in self.seals.items():
            F.require(F.manifest(base) == expected, 'Source-N recovery membership or bytes changed: ' + base)
        return True

    def file(self, original, expected=None):
        original = str(original); record = self.aliases.get(original, self.files.get(original))
        F.require(record is not None and (expected is None or record['sha256'] == expected),
                  'Missing/unbound source-N relocation: ' + original)
        actual = R.regular(record['path']).resolve()
        F.require(R.digest(actual) == record['sha256'], 'Relocated source-N bytes changed: ' + original)
        return actual

    def checked(self, value): return self.file(value['path'], value['sha256'])

    def alias(self, original, actual, expected):
        actual = R.regular(actual).resolve()
        F.require(str(original) not in self.files and str(original) not in self.aliases and R.digest(actual) == expected,
                  'Ambiguous or different source-N alias')
        self.aliases[str(original)] = dict(path=str(actual), sha256=expected)


def foundation(path):
    record = R.read(path)
    F.require(record.get('schema') == 'pinwheel.streaming-8x4-relocated-foundation.v1' and
        record.get('passed') is True and record.get('qualified') is False and record.get('native_executed') is False and
        record.get('historical_foundation_reused') is True and record.get('current_projection_identical') is True and
        record.get('runtime_identity_unchanged') is True and len(record.get('module_order', [])) == 649,
        'Complete independently reviewed relocated foundation required')
    positive = record['positive_library']
    F.require(len(positive['artifact_sha256']) == 1298 and F.CONTROL not in positive['artifact_sha256'] and
        F.manifest(positive['path']) == positive['artifact_sha256'] and
        all(R.digest(path) == pin for path, pin in record['input_sha256'].items()) and
        all(R.digest(ROOT / name) == pin for name, pin in record['producer_sha256'].items()),
        'Relocated positive foundation or its authority changed')
    return record


def worker_membership(worker_root, artifacts, report_path):
    """Original worker artifact keys are absolute, with the old authority kept."""
    expected = {}
    for original, pin in artifacts.items():
        name = Path(original)
        F.require(name.is_absolute() and name.is_relative_to(OLD / WORKER) and '..' not in name.parts,
                  'Original worker artifact escapes its authenticated owner')
        relative = str(name.relative_to(OLD / WORKER))
        F.require(relative != 'report.json' and relative not in expected, 'Original worker artifact aliases its report/another file')
        expected[relative] = pin
    expected['report.json'] = R.digest(report_path)
    F.require(F.manifest(worker_root) == expected, 'Original complete source-N input worker changed')


def native_replay(recovery, prepared, plan, positive, report):
    """Check the original complete positive+two-control intent/result evidence."""
    F.require(report.get('schema') == 'pinwheel.streaming-tt-optimization-frozen-replay.v1' and
        report.get('passed') is True and report.get('qualified') is False and report.get('stage') == 'closed' and
        report.get('module_count') == report.get('positive_native_checks') == 395 and
        report.get('negative_native_checks') == 2 and report.get('private_unused_axiom_rejected') is True and
        report.get('expected_positive_plus_private_commands') == 397 and
        positive.get('passed') is True and positive.get('schema') == 'pinwheel.streaming-tt-fresh-replay-positive.v1' and
        positive.get('source_commit') == positive.get('producer_commit') == prepared.get('source_commit') == SOURCE and
        prepared.get('source_only_staging') is True and prepared.get('native_lean_invoked') is False and
        prepared.get('fresh_foundation') == plan.get('foundation_binding') == positive.get('fresh_foundation') == report.get('fresh_foundation'),
        'Historical complete source-N boundary did not close')
    commands = report['commands']; rows = plan['rows']
    F.require(len(rows) == 395 and len(commands) == 397 and positive['commands'] == commands[:395] and
        [row['module'] for row in rows] == [row['module'] for row in commands[:395]] and
        len({row['module'] for row in rows}) == 395, 'Historical source-N module command order/membership differs')
    journal = recovery.checked(report['native_journal'])
    events = [json.loads(line, object_pairs_hook=F.pairs) for line in journal.read_text().splitlines()]
    F.require(len(events) == 794, 'Missing/extra original source-N native journal event')
    for index, row in enumerate(commands):
        negative = index >= 395; code = 1 if index == 396 else 0
        F.require(row.get('negative_control') is negative and type(row.get('exit_code')) is int and row['exit_code'] == code and
            row.get('timed_out') is False and row.get('native_process_group_closed') is True and
            row['source_sha256_before'] == row['source_sha256_after'] and
            row['compiler_sha256_before'] == row['compiler_sha256_after'] == R.HOST_PINS['lean'],
            'Historical source-N compiler/process/outcome differs')
        source = recovery.file(row['source'], row['source_sha256_before']); log = recovery.file(row['log'], row['log_sha256'])
        original = Path(row['source']); obj_original = str(original.with_suffix('.olean'))
        expected_argv = [R.HOST_TOOLS['lean'], '-M4096','-j1','-DElab.async=false','--root=' + str(original.parent),
            '-DwarningAsError=true','-DmaxErrors=1','-o',obj_original,str(original)]
        F.require(row['argv'] == expected_argv, 'Historical source-N native argv differs')
        if code == 0:
            recovery.file(obj_original, row['object_sha256'])
        else:
            F.require(row.get('object_sha256') is None and
                'Unapproved axioms in _private.StreamingOptimizedReplayExactPrivateAxiom' in log.read_text() and
                '.forbiddenUnused' in log.read_text(), 'Source-N private rejection is unrelated')
        intent, result = events[2 * index:2 * index + 2]
        F.require(intent.get('event') == 'intent' and result == dict(event='result', **row) and
            all(row.get(key) == value for key, value in intent.items() if key != 'event'),
            'Original source-N pre-use intent/result no longer equals its aggregate')
        if not negative:
            planned = rows[index]
            F.require(planned['source'] == row['source'] and planned['source_sha256'] == row['source_sha256_before'] and
                planned['target_olean'] == obj_original, 'Source-N import plan differs from original native source/object')
    audit = recovery.checked(positive['final_audit']).read_text()
    F.require('Mapped audit:' in audit and 'standard axioms only.' in audit, 'Historical whole-N private audit absent')


def prepare(recovery_root, foundation_report, runtime_report, output):
    start = time.monotonic(); output = Path(output).absolute()
    F.require(not output.exists(), 'Preserve earlier source-N dependency admission')
    own = Path(__file__).resolve(); commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip()
    F.require(hashlib.sha256(subprocess.check_output(['git','show',commit+':scripts/streaming_8x4_final_dependency.py'],cwd=ROOT,timeout=30)).hexdigest() == R.digest(own),
        'Commit exact source-N relocation producer before admission')
    f03 = foundation(foundation_report); runtime = R.closed_report(runtime_report)
    H = Recovery(recovery_root)
    records = {name:H.file(OLD / N / name, pin) for name, pin in PINS.items()}
    prepared, plan, positive, report = [R.read(records[name]) for name in ('prepared.json','plan.json','positive-manifest.json','report.json')]
    F.require(prepared['fresh_foundation']['sha256'] == f03['original_binding']['sha256'] and
        prepared['fresh_foundation']['path'] == f03['original_binding']['original_path'], 'Historical N and F03 selection differ')
    native_replay(H, prepared, plan, positive, report)
    original_cfg = R.read(H.checked(prepared['worker_config'])); worker_path = H.checked(prepared['worker_report'])
    original_worker = R.read(worker_path); worker_root = worker_path.parent
    worker_membership(worker_root,original_worker['artifact_sha256'],worker_path)
    cfg = copy.deepcopy(original_cfg); worker = copy.deepcopy(original_worker)
    cfg['library'] = str(H.file(original_cfg['library']))
    for label, stage in (('frontend','frontend'), ('core-d2','core-d2')):
        cfg['components'][label]['raw_json'] = str(H.file(original_cfg['components'][label]['raw_json'],
            prepared['closed_input_sha256_before'][original_cfg['components'][label]['raw_json']]))
        for name, path in original_cfg['components'][label]['raw_sources'].items():
            actual = H.file(OLD / N / stage / (name + '.lean'))
            H.alias(path, actual, prepared['closed_input_sha256_before'][path])
            cfg['components'][label]['raw_sources'][name] = str(actual)
    worker['outer']['restored_json'] = str(H.file(original_worker['outer']['restored_json']))
    # The canonical interpreter is independently regenerated from committed
    # source; arbitrary recovered Python is not imported by this admission.
    output.mkdir(parents=True)
    interpreter = output / 'historical-interpreter.py'
    interpreter.write_bytes(subprocess.check_output(['git','show',FORMAL+':scripts/streaming_tt_opt_intake.py'],cwd=ROOT,timeout=30))
    I = types.ModuleType('_streaming8_historical_N_interpreter'); I.__file__ = str(interpreter)
    sys.modules[I.__name__] = I
    exec(compile(interpreter.read_bytes(),str(interpreter),'exec'),I.__dict__)
    # This explicit authority is for the selected pure HOST functions only.
    # No old archive dispatcher/intake/native admission function is called.
    I.ROOT = ROOT
    old_functions = {name:getattr(subprocess,name) for name in ('Popen','run','call','check_call','check_output')}
    def forbidden(*args, **kwargs): raise RuntimeError('Native/tool execution forbidden during source-N HOST regeneration')
    try:
        for name in old_functions: setattr(subprocess,name,forbidden)
        modules, identities = I.regenerated_sources(cfg, worker, worker_root)
    finally:
        for name, function in old_functions.items(): setattr(subprocess,name,function)
    F.require([row['module'] for row in modules] == [row['module'] for row in plan['rows']],
        'Independent complete source-N generation changed the395-module inventory/order')
    by_name = {row['module']:row for row in modules}
    for row in plan['rows']:
        actual = H.file(row['source'], row['source_sha256'])
        F.require(R.digest(by_name[row['module']]['path']) == by_name[row['module']]['sha256'] == R.digest(actual),
            'Independent source-N regeneration differs from historical proof source')
    imports = {}
    for name, module in tuple(sys.modules.items()):
        path = getattr(module,'__file__',None)
        if path and Path(path).resolve().is_relative_to(ROOT / 'scripts'):
            path = Path(path).resolve(); relative = str(path.relative_to(ROOT))
            # The new scoped orchestration is committed at current HEAD;
            # mathematical/interpreter helpers must match original ca26 source.
            if relative.startswith('scripts/streaming_8x4_'): continue
            payload = subprocess.check_output(['git','show',FORMAL + ':' + relative],cwd=ROOT,timeout=30)
            F.require(hashlib.sha256(payload).hexdigest() == R.digest(path),
                'Historical source-N interpreter differs from committed formal producer: ' + relative)
            imports[relative] = R.digest(path)
    H.intact(); foundation(foundation_report)
    positive_root = output / 'positive-N'; positive_root.mkdir()
    rows = []
    for row, native in zip(plan['rows'], positive['commands']):
        name = row['module']; source = H.file(row['source'], row['source_sha256']); obj = H.file(row['target_olean'],native['object_sha256'])
        for suffix, actual in (('.lean',source),('.olean',obj)): shutil.copyfile(actual,positive_root / (name + suffix))
        rows.append(dict(module=name,source=str(positive_root/(name+'.lean')),source_sha256=row['source_sha256'],
            target_olean=str(positive_root/(name+'.olean')),object_sha256=native['object_sha256'],
            original_source=row['source'],original_target_olean=row['target_olean']))
    consumed = {str(path):R.digest(path) for path in records.values()}
    consumed.update({str(H.root/owner/'RESTORED-FILES-METADATA.jsonl'):R.digest(H.root/owner/'RESTORED-FILES-METADATA.jsonl') for owner in OWNERS})
    consumed.update({str(path):R.digest(path) for path in (foundation_report,runtime_report,worker_path,H.checked(prepared['worker_config']),own,interpreter)})
    value = dict(schema='pinwheel.streaming-8x4-relocated-source-N.v1',passed=True,qualified=False,native_executed=False,
        historical_source_N_reused=True,source_commit=SOURCE,formal_producer_commit=FORMAL,producer_commit=commit,
        original_records={name:dict(original_path=str(OLD/N/name),**bind(path)) for name,path in records.items()},
        foundation_report=bind(foundation_report),runtime_report=bind(runtime_report),
        positive_library=dict(path=str(positive_root),artifact_sha256=F.manifest(positive_root)),positive_import_rows=rows,
        independently_regenerated_modules=len(modules),historical_positive_commands=395,historical_negative_commands=2,
        historical_complete_native_journal=bind(H.checked(report['native_journal'])),input_sha256=consumed,
        recovered_owner_sha256=H.seals,explicit_equal_payload_aliases=H.aliases,canonical_formal_helper_sha256=imports,
        executed_historical_interpreter=dict(**bind(interpreter),original_commit=FORMAL,
            original_relative_path='scripts/streaming_tt_opt_intake.py',selected_functions=['regenerated_sources','restore_port_order']),
        original_worker_config=bind(H.checked(prepared['worker_config'])),original_worker_report=bind(worker_path),
        derived_generation_config=cfg,derived_generation_worker=worker,worker_root=str(worker_root),
        elapsed_seconds=round(time.monotonic()-start,3),
        boundary='Explicit historical source-N/F03 proof reuse with independently regenerated source identity. No fresh N execution or actual-M proof; old argv/receipt paths remain original.')
    R.write(output/'report.json',value); return value


def verify(path):
    record = R.read(path)
    F.require(record.get('schema') == 'pinwheel.streaming-8x4-relocated-source-N.v1' and record.get('passed') is True and
        record.get('qualified') is False and record.get('native_executed') is False and
        record.get('historical_source_N_reused') is True and record.get('independently_regenerated_modules') == 395 and
        record.get('historical_positive_commands') == 395 and record.get('historical_negative_commands') == 2,
        'Complete explicit relocated source-N dependency required')
    F.require(all(R.digest(path) == pin for path,pin in record['input_sha256'].items()) and
        F.manifest(record['positive_library']['path']) == record['positive_library']['artifact_sha256'] and
        len(record['positive_import_rows']) == 395, 'Relocated source-N custody changed')
    for base, expected in record['recovered_owner_sha256'].items(): F.require(F.manifest(base) == expected, 'Source-N recovered owner changed')
    foundation(record['foundation_report']['path']); R.closed_report(record['runtime_report']['path'])
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('recovery','foundation-report','runtime-report','output'): parser.add_argument('--'+name,required=True,type=Path)
    args = parser.parse_args(); value = prepare(args.recovery,args.foundation_report,args.runtime_report,args.output)
    print(json.dumps({key:value[key] for key in ('schema','passed','independently_regenerated_modules','elapsed_seconds')}))


if __name__ == '__main__': main()
