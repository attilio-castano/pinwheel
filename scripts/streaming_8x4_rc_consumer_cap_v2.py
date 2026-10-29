"""Separately typed version-2-only C diagnostic; all C1 physics/data stay frozen."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_cap as C

P = C.P
need, write = C.need, C.write
cgroups, parse_leaf, measurements = C.cgroups, C.parse_leaf, C.measurements
BASELINE_HASH = 'abc8418dab6fe1b93873861078bfad540017be3436dc951bbc75a5da5a496bf2'
CAUSAL_HASH = 'ef1c7ae013237229066e66c7032bdd161c1702f9b1b0ecee4843a8067d03c5f8'
OUTPUT = 'rc-consumer-cap-v2-01'
JOBS = C.JOBS
CASES, NATIVE_HASH, REFERENCE_HASH = C.CASES, C.NATIVE_HASH, C.REFERENCE_HASH
definition, vector, relative = C.definition, C.vector, C.relative
EXTRA = ('streaming_8x4_rc_consumer_cap_v2.py', 'streaming_8x4_rc_consumer_cap_v2_readback.py')


def protocol():
    value = C.protocol(); value['extractor_version'] = '2.0'
    value['qualification_scope'] = 'version-only consumer/table-format diagnostic; no coefficient repair or full model qualification'
    return value


def version2_tcl(original):
    need(original == C.tcl() and original.count('-version 1.0') == 1, 'Frozen C1 Tcl authority differs')
    return original.replace('-version 1.0', '-version 2.0')


def causal_intake(base):
    need(P.sha(base / 'manifest.json') == CAUSAL_HASH, 'Exact causal source manifest differs')
    m = json.loads((base / 'manifest.json').read_text())
    need(m['downloaded_code_executed'] is False, 'Causal source scope differs')
    for row in m['files']:
        path = base / row['name']; data = path.read_bytes()
        need(Path(row['name']).name == row['name'] and not path.is_symlink() and len(data) == row['bytes']
             and hashlib.sha256(data).hexdigest() == row['sha256']
             and hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['git_blob'],
             'Causal source byte/Git identity differs')
    return m


def prepare(baseline, causal_source, output):
    old = C.verify(baseline, BASELINE_HASH); causal_intake(causal_source)
    need(not output.exists() and output.parent.is_dir(), 'Fresh version2 preparation owner required')
    shutil.copytree(baseline, output); shutil.copytree(baseline, output / 'baseline')
    shutil.copytree(causal_source, output / 'causal-source')
    # Root authority is new; never overwrite the retained C1 baseline directory.
    (output / 'plan.json').unlink()
    new_tcl = version2_tcl((baseline / 'run.tcl').read_text()); (output / 'run.tcl').write_text(new_tcl)
    plan = copy.deepcopy(old); plan['schema'] = 'pinwheel.streaming-8x4-rc-consumer-cap-version2-plan.v1'
    plan['baseline_C1_plan_sha256'] = BASELINE_HASH; plan['causal_source_manifest_sha256'] = CAUSAL_HASH
    plan['protocol'] = protocol(); plan['files_sha256']['run.tcl'] = P.sha(output / 'run.tcl')
    plan['producer_sha256'].update({n: P.sha(Path(__file__).with_name(n)) for n in EXTRA})
    plan['producer_sha256'] = dict(sorted(plan['producer_sha256'].items()))
    plan['only_measurement_policy_delta'] = 'extract_parasitics -version 1.0 -> 2.0; all other Tcl/geometry/table/reference/units/gates/resources byte-identical'
    plan['source_predictions_not_guaranteed_repairs'] = {
        'isolated_OpenEnded2_pF_per_m': '110.7332',
        'isolated_source_mechanism': '2*(regular far coupling+fringe), not populated OVER0 isolated row',
        'pair_source_mechanism': 'one-open-side branch selects sparse OVER0 table; numerical/coupling/failure outcome must be measured'}
    write(output / 'plan.json', plan); verify(output, P.sha(output / 'plan.json'))
    return {'plan_sha256': P.sha(output / 'plan.json'), 'baseline_C1_plan_sha256': BASELINE_HASH,
            'native_executed': False, 'model_qualified': False}


def verify(base, plan_hash):
    need(P.sha(base / 'plan.json') == plan_hash, 'Version2 plan identity differs')
    old = C.verify(base / 'baseline', BASELINE_HASH); plan = json.loads((base / 'plan.json').read_text())
    expected = copy.deepcopy(old); expected['schema'] = 'pinwheel.streaming-8x4-rc-consumer-cap-version2-plan.v1'
    expected['baseline_C1_plan_sha256'] = BASELINE_HASH; expected['causal_source_manifest_sha256'] = CAUSAL_HASH
    expected['protocol'] = protocol()
    expected['files_sha256']['run.tcl'] = hashlib.sha256(version2_tcl((base / 'baseline/run.tcl').read_text()).encode()).hexdigest()
    expected['producer_sha256'].update({n: P.sha(Path(__file__).with_name(n)) for n in EXTRA})
    expected['producer_sha256'] = dict(sorted(expected['producer_sha256'].items()))
    expected['only_measurement_policy_delta'] = 'extract_parasitics -version 1.0 -> 2.0; all other Tcl/geometry/table/reference/units/gates/resources byte-identical'
    expected['source_predictions_not_guaranteed_repairs'] = {
        'isolated_OpenEnded2_pF_per_m': '110.7332',
        'isolated_source_mechanism': '2*(regular far coupling+fringe), not populated OVER0 isolated row',
        'pair_source_mechanism': 'one-open-side branch selects sparse OVER0 table; numerical/coupling/failure outcome must be measured'}
    need(plan == expected, 'Version2 exact typed C1 adaptation/producer policy differs')
    causal_intake(base / 'causal-source')
    for name, value in expected['files_sha256'].items():
        path = base / name
        need(path.is_file() and not path.is_symlink() and P.sha(path) == value, 'Version2 copied file changed')
        if name != 'run.tcl': need(path.read_bytes() == (base / 'baseline' / name).read_bytes(), 'Version2 changed non-Tcl input')
    for name in ('reference-plan.json', 'native-plan.json'):
        need((base / name).read_bytes() == (base / 'baseline' / name).read_bytes(), 'Version2 changed reference authority')
    return plan


def command_proposal(base, plan_hash, output_parent, require_fresh=True):
    plan = verify(base, plan_hash)
    need(not require_fresh or not (output_parent / OUTPUT).exists(), 'Version2 output must be fresh')
    old = C.command_proposal(base / 'baseline', BASELINE_HASH, output_parent, require_fresh=False)
    argv = list(old['argv'])
    replacements = {'pinwheel-8x4-rc-consumer-cap-01': 'pinwheel-8x4-rc-consumer-cap-v2-01',
        'type=bind,src=' + str((base / 'baseline').resolve()) + ',dst=/rc-inputs,readonly':
        'type=bind,src=' + str(base.resolve()) + ',dst=/rc-inputs,readonly',
        '/rc-source/streaming_8x4_rc_consumer_cap.py': '/rc-source/streaming_8x4_rc_consumer_cap_v2.py',
        BASELINE_HASH: plan_hash, '/rc-output-parent/' + C.OUTPUT: '/rc-output-parent/' + OUTPUT}
    for before, after in replacements.items():
        need(argv.count(before) == 1, 'Version2 exact command adaptation membership differs')
        argv[argv.index(before)] = after
    return {'schema': 'pinwheel.streaming-8x4-rc-consumer-cap-version2-command-proposal.v1', 'root_go_required': True,
        'admitted': False, 'native_executed': False, 'model_qualified': False, 'container_name': 'pinwheel-8x4-rc-consumer-cap-v2-01',
        'timeout_seconds': 180, 'work_seconds': 150, 'maximum_calls': 4, 'plan_path': str((base / 'plan.json').resolve()),
        'plan_sha256': plan_hash, 'producer_sha256': plan['producer_sha256'], 'argv': argv}


def run(base, plan_hash, output):
    plan = verify(base, plan_hash); cg = cgroups()
    need(not output.exists() and output.parent.is_dir(), 'Cap native output must be fresh')
    output.mkdir(); start = time.monotonic(); jobs = []
    report = {'schema': 'pinwheel.streaming-8x4-rc-consumer-cap-version2-execution.v1', 'plan_sha256': plan_hash,
        'qualified': False, 'model_qualified': False, 'passed': False, 'measurement_packet_completed': False,
        'accuracy_status': 'unmeasured', 'independent_accuracy_passed': False, 'jobs': jobs, 'cgroups': cg}
    try:
        for job in plan['jobs']:
            need(time.monotonic() - start < 115, 'Insufficient fixed cap packet work budget')
            owner = output / job['job']; owner.mkdir()
            for name in ('tech.lef', 'rules.txt', 'run.tcl'):
                shutil.copyfile(base / name, owner / name)
            shutil.copyfile(base / (job['job'] + '.def'), owner / 'fixture.def')
            before = {p.name: P.sha(p) for p in owner.iterdir()}; child = None; timed_out = False
            command = ['openroad', '-no_init', '-exit', 'run.tcl']; leaf = {'job': job['job'], 'passed': False}
            with (owner / 'native.log').open('wb') as stream:
                child = subprocess.Popen(command, cwd=owner, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    code = child.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    timed_out = True; os.killpg(child.pid, signal.SIGKILL); code = child.wait()
            try:
                os.killpg(child.pid, 0)
            except ProcessLookupError:
                reaped = True
            else:
                os.killpg(child.pid, signal.SIGKILL); raise ValueError('Cap child left a process group')
            need(all(P.sha(owner / n) == h for n, h in before.items()), 'Copied cap inputs changed')
            leaf.update(argv=command, exit_code=code, timed_out=timed_out, process_tree_reaped=reaped,
                        copied_inputs_unchanged=True, copied_input_sha256=before, native_log_sha256=P.sha(owner / 'native.log'))
            try:
                need(type(code) is int and code == 0 and not timed_out, 'Cap OpenROAD exit/timeout failed')
                leaf['values'] = parse_leaf(owner, job); leaf['passed'] = True
            except (ValueError, OSError) as error:
                leaf['error'] = type(error).__name__ + ': ' + str(error)
            leaf['raw_output_sha256'] = {n: P.sha(owner / n) for n in ('before.def', 'after.def', 'result.spef') if (owner / n).is_file()}
            write(owner / 'report.json', leaf); jobs.append(dict(job=job['job'], passed=leaf['passed'], report_sha256=P.sha(owner / 'report.json')))
            # Preserve numeric failures and finish the fixed four calls; no adaptive retry.
        report['measurement_packet_completed'] = len(jobs) == 4
        if all(j['passed'] for j in jobs):
            leaves = [json.loads((output / j['job'] / 'report.json').read_text()) for j in jobs]
            report['analysis'] = measurements(leaves); report['passed'] = report['analysis']['measurement_controls_passed']
    except Exception as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    report['inputs_unchanged'] = verify(base, plan_hash) == plan
    report['wall_seconds'] = time.monotonic() - start; write(output / 'report.json', report)
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare')
    for name in ('baseline', 'causal-source', 'output'): q.add_argument('--' + name, type=Path, required=True)
    for action in ('verify', 'proposal', 'run'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action != 'verify': q.add_argument('--output', type=Path, required=True)
        if action == 'proposal': q.add_argument('--output-parent', type=Path, required=True)
    a = p.parse_args()
    if a.action == 'prepare': result = prepare(a.baseline, a.causal_source, a.output)
    elif a.action == 'verify': result = verify(a.inputs, a.plan_sha256)
    elif a.action == 'run': result = run(a.inputs, a.plan_sha256, a.output)
    else:
        result = command_proposal(a.inputs, a.plan_sha256, a.output_parent); write(a.output, result)
    print(json.dumps(result, indent=2))
    if a.action == 'run' and not result['passed']: raise SystemExit(2)


if __name__ == '__main__': main()
