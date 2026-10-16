"""Bounded, owned diagnostic execution; does not launch on import."""
import hashlib
import importlib.util
import json
import math
import re
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[3]
IMAGE = 'sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92'
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('checkpoint_runner', ROOT / 'scripts/run-buffered-tt-physical.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + '\n')

def source_intakes():
    """Recheck both accepted core/ABI inventories without changing either receipt."""
    entries, hashes = {}, {}
    for name, expected_count in (('tt-buffered-boundary-01', 495), ('tt-buffered-digital-04', 494)):
        path = ROOT / 'build/tt-buffered' / name / 'report.json'
        receipt = read(path)
        assert receipt.get('status') == 'passed' and receipt.get('inputs_unchanged'), path
        inventory = {**receipt['source_sha256'], **receipt['predecessor']['implementation_source_sha256']}
        assert len(inventory) == expected_count, (name, len(inventory))
        changed = []
        hashes[str(path.resolve())] = sha(path)
        for relative, expected in inventory.items():
            source = (ROOT / relative).resolve()
            assert source.is_relative_to(ROOT.resolve()) and source.is_file(), source
            if sha(source) != expected:
                changed.append(relative)
            previous = hashes.get(str(source))
            assert previous in (None, expected), ('Conflicting source inventory', relative)
            hashes[str(source)] = expected
        entries[name] = dict(source_count=len(inventory), all_current=not changed,
                             changed=changed, receipt_sha256=sha(path))
        assert not changed, ('Core/ABI source intake changed', name, changed)
    return entries, hashes

def resolve_view(state, design, name):
    value = state.get(name)
    prefix = '/work/recovery/'
    assert isinstance(value, str) and value.startswith(prefix), (name, value)
    relative = Path(value[len(prefix):])
    assert not relative.is_absolute() and '..' not in relative.parts, (name, value)
    resolved = (design / relative).resolve()
    assert resolved.is_relative_to(design.resolve()) and resolved.is_file(), resolved
    return resolved

def bounded_cleanup(owner, log):
    query=['docker','container','ls','--all','--no-trunc','--filter','label=org.pinwheel.baseline_owner='+owner,'--format','{{.ID}}']
    receipt={'status':'unconfirmed','ownership_label':owner,'cleanup_subprocess_bound_seconds':30}
    try:
        first=subprocess.run(query,capture_output=True,text=True,timeout=5)
        if first.returncode:receipt['query_error']=first.stderr;return receipt
        ids=first.stdout.splitlines();assert len(ids)<=1 and all(re.fullmatch(r'[0-9a-f]{64}',n) for n in ids),'Invalid ownedcontainer inventory'
        receipt['owned_container_ids']=ids
        for identity in ids:subprocess.run(['docker','stop','--time','5',identity],stdout=log,stderr=subprocess.STDOUT,timeout=20)
        final=subprocess.run(query,capture_output=True,text=True,timeout=5)
        if final.returncode:receipt['final_query_error']=final.stderr
        elif not final.stdout.strip():receipt['status']='absent'
        else:receipt['remaining_ids']=final.stdout.splitlines()
    except (OSError,AssertionError,subprocess.TimeoutExpired) as e:receipt['cleanup_error']=str(e)
    return receipt

def execute(out, paths, argv, *, seconds, cpus, memory, schema, scope, extra=None,
            expected_hashes=None, absolute_work_stop=None, all_in_deadline_monotonic=None, phase_started_monotonic=None, host_stage_seconds=60):
    intakes, intake_hashes = source_intakes()
    paths = sorted({str(Path(p).resolve()) for p in [*paths, *intake_hashes]})
    hashes = {str(Path(path).resolve()): sha(path) for path in paths}
    for path, expected in {**intake_hashes, **(expected_hashes or {})}.items():
        assert hashes[str(Path(path).resolve())] == expected, ('Input changed while staging', path)
    assert absolute_work_stop is not None and all_in_deadline_monotonic is not None and phase_started_monotonic is not None
    assert time.monotonic()-phase_started_monotonic<=host_stage_seconds,'Full prelaunch verification/staging bound exceeded'
    seconds=min(seconds,math.floor(absolute_work_stop-time.time())-1,math.floor(all_in_deadline_monotonic-time.monotonic()-40))
    assert seconds>0,'No admitted nativework/cleanup reserve'
    owner = str(uuid.uuid4())
    command = ['docker', 'run', '--rm', '--pull', 'never', '--network', 'none',
               '--cpus', str(cpus), '--memory', memory, '--label', 'org.pinwheel.baseline_owner=' + owner,
               '--mount', 'type=bind,source=' + str(out) + ',target=/work/diagnostic',
               '--mount', 'type=bind,source=' + str(ROOT / 'build/physical/pdk') + ',target=/work/pdk,readonly',
               '--workdir', '/work/diagnostic', IMAGE, *argv]
    report = dict(schema=schema, status='running', input_sha256=hashes, command=command,
                  image_id=IMAGE, bounds=dict(docker_subprocess_seconds=seconds, cpus=cpus, memory=memory,
                                             network='none', cleanup_outside_subprocess_cap=True),
                  ownership_label=owner, scope=scope, core_abi_source_intakes=intakes, **(extra or {}))
    write(out / 'report.json', report)
    started = time.monotonic()
    previous = signal.getsignal(signal.SIGTERM)
    previous_int = signal.getsignal(signal.SIGINT)
    def interrupt(*_):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt('SIGTERM')
    signal.signal(signal.SIGTERM, interrupt)
    try:
        with (out / 'execution.log').open('w') as log:
            actual_timeout=min(seconds,max(0,math.floor(absolute_work_stop-time.time())-1),max(0,math.floor(all_in_deadline_monotonic-time.monotonic()-40)))
            assert actual_timeout>0,'NativeSTOP reached beforeactual launch'
            report['bounds']['actual_docker_subprocess_seconds']=actual_timeout
            write(out/'report.json',report)
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=actual_timeout)
        report.update(exit_code=result.returncode, status='passed' if result.returncode == 0 else 'failed')
        if result.returncode == 0:
            report['measurement'] = read(out / 'measurement.json')
            if report['measurement'].get('status') != 'measured':
                report['status'] = 'failed'
    except subprocess.TimeoutExpired as error:
        report.update(status='timed_out', error=str(error), exit_code=124)
    except KeyboardInterrupt as error:
        report.update(status='interrupted', error=str(error), exit_code=130)
    except BaseException as error:
        report.update(status='failed', error=repr(error), exit_code=1)
    finally:
        # A new interruption must not skip owned-container absence confirmation.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        try:
            report['container_termination'] = bounded_cleanup(owner, None)
            report['inputs_unchanged'] = all(sha(path) == digest for path, digest in hashes.items())
            report['elapsed_seconds'] = round(time.monotonic() - started, 3)
            report['elapsed_scope'] = 'Docker execution plus owned cleanup and source recustody; host staging precedes this timer.'
            report['artifact_sha256'] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
                                         if p.is_file() and p.name != 'report.json'}
            if not report['inputs_unchanged'] or report['container_termination']['status'] == 'unconfirmed':
                report['status'] = 'invalidated'
            write(out / 'report.json', report)
        finally:
            signal.signal(signal.SIGTERM, previous)
            signal.signal(signal.SIGINT, previous_int)
    return report
