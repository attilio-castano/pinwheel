"""Run the unchanged official TT precheck with frozen inputs and explicit tools.

This is one physical gate, never a whole-chip qualification verdict. Native
KLayout runs in the pinned image; exact official Python requirement versions
run in an isolated host environment. No layer or failed check is filtered.
"""
import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid
import xml.etree.ElementTree as ET

from validation_run import fresh_directory
import process_group

ROOT = Path(__file__).resolve().parents[1]
TOOL_LOCK = ROOT / 'tools/streaming-tt-signoff.json'


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def decode(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate signoff JSON key: ' + key)
            result[key] = value
        return result
    def constant(value):
        raise ValueError('Nonfinite signoff JSON value: ' + value)
    return json.loads(data, object_pairs_hook=pairs, parse_constant=constant)


def read(path):
    return decode(Path(path).read_bytes())


def write(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + '\n')
    temporary.replace(path)


def regular(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Missing/aliased signoff input: ' + str(path))
    return path.resolve()


def verify_support(directory, lock):
    directory = Path(directory).resolve()
    result = {}
    for name, identity in lock['support_files'].items():
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts, 'Escaping official source path')
        path = regular(directory / relative)
        require(path.is_relative_to(directory), 'Official source escaped selected root')
        data = path.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == identity['git_blob'] and sha(path) == identity['sha256'],
            'Official precheck source differs: ' + name)
        result[str(path)] = identity['sha256']
    return result


def selected_checks(source, tech):
    """Derive the required ordered check set from the actual official source."""
    module = ast.parse(source)
    main = [node for node in module.body if isinstance(node, ast.FunctionDef) and node.name == 'main']
    require(len(main) == 1, 'Ambiguous official precheck main')
    assignments = [node for node in ast.walk(main[0]) if isinstance(node, ast.Assign) and
        any(isinstance(target, ast.Name) and target.id == 'checks' for target in node.targets)]
    require(len(assignments) == 1 and isinstance(assignments[0].value, ast.List),
        'Unsupported official check inventory')
    result = []
    for value in assignments[0].value.elts:
        require(isinstance(value, ast.Dict), 'Unsupported official check declaration')
        entries = {ast.literal_eval(key): item for key, item in zip(value.keys, value.values)}
        name = ast.literal_eval(entries['name'])
        require(type(name) is str and name, 'Invalid official check name')
        technologies = ast.literal_eval(entries['techs']) if 'techs' in entries else None
        if technologies is None or tech in technologies:
            result.append(name)
    require(result and len(set(result)) == len(result), 'Missing/duplicate official checks')
    return result


def precheck_result(path, expected, exit_code):
    root = ET.parse(regular(path)).getroot()
    require(root.tag == 'testsuites' and len(root) == 1 and root[0].tag == 'testsuite',
        'Unexpected official precheck report shape')
    suite = root[0]
    require(suite.get('name') == 'Tiny Tapeout Prechecks', 'Wrong precheck test suite')
    cases = list(suite)
    require(all(case.tag == 'testcase' for case in cases) and
        [case.get('name') for case in cases] == expected, 'Incomplete/reordered/duplicate official checks')
    failures = []
    for case in cases:
        duration = float(case.get('time', 'nan'))
        require(math.isfinite(duration) and duration >= 0, 'Invalid official check duration')
        require(all(child.tag == 'error' for child in case), 'Unsupported/skipped official check')
        for child in case:
            failures.append(dict(check=case.get('name'), message=child.get('message'), detail=child.text))
    require((exit_code == 0) == (not failures), 'Native precheck exit/report disagreement')
    return dict(passed=not failures, checks=expected, executed_checks=len(cases), failures=failures)


def inventory(directory, *, aliases=None):
    result = {}
    directory = Path(directory).resolve()
    require(directory.is_dir(), 'Missing runtime payload directory: ' + str(directory))
    for path in sorted(directory.rglob('*')):
        if path.is_symlink():
            require(aliases is not None and path.is_file() and path.resolve().is_relative_to(directory),
                'Unexpected runtime file alias: ' + str(path))
            aliases[str(path.absolute())] = dict(target=os.readlink(path), resolved=str(path.resolve()))
        if path.is_file():
            # -B prevents writes, but Python can still read pre-existing pyc.
            result[str(path.resolve())] = sha(path)
    return result


def python_environment(environment):
    """Prevent inherited Python settings from changing official assertions/imports."""
    return dict({key: value for key, value in environment.items()
        if not key.startswith('PYTHON') and key != '__PYVENV_LAUNCHER__'},
        PYTHONDONTWRITEBYTECODE='1', PYTHONNOUSERSITE='1', PYTHONPATH='')


def container_name(out):
    tag = Path(out).name
    require(re.fullmatch(r'[A-Za-z0-9_-]+', tag), 'Unsafe signoff container tag')
    return 'pinwheel-signoff-' + tag


def native_journal(path, *, out, pdk, owner, image_id, gds):
    events = [decode(line) for line in regular(path).read_text().splitlines()]
    require(len(events) == 6, 'Missing/extra native official KLayout calls')
    reports = {}
    identities = set()
    checks = ('pin_label_purposes_overlapping_drawing', 'sg13cmos5l', 'zero_area')
    scripts = ('tech-files/pin_label_purposes_overlapping_drawing.rb.drc',
        str(pdk / 'ihp-sg13cmos5l/libs.tech/klayout/tech/drc/ihp-sg13cmos5l.drc'),
        'tech-files/zeroarea.rb.drc')
    prefix = ['docker', 'run', '--rm', '--pull', 'never', '--name', container_name(out),
        '--network', 'none', '--read-only',
        '--tmpfs', '/tmp:rw,size=256m', '--cpus', '1', '--memory', '2g', '--memory-swap', '2g',
        '--label', 'org.pinwheel.signoff_owner=' + owner,
        '--mount', 'type=bind,source=' + str(out) + ',target=' + str(out),
        '--mount', 'type=bind,source=' + str(pdk) + ',target=' + str(pdk) + ',readonly',
        '--workdir', str(out / 'tt/precheck'), '--entrypoint', 'klayout', image_id]
    for index, check in enumerate(checks):
        intent, result = events[2*index:2*index+2]
        identity = intent.get('identity')
        require(intent.get('event') == 'intent' and result.get('event') == 'result' and
            type(identity) is str and identity not in identities and result.get('identity') == identity,
            'Unclosed/duplicate native KLayout process')
        identities.add(identity)
        argv = intent.get('argv', [])
        report = out / 'tt/precheck/reports' / ('drc_' + check + '.xml')
        expected = prefix + ['-b', '-r', scripts[index], '-rd', check+'=true', '-rd',
            'input='+str(gds), '-rd', 'thr=1', '-rd', 'report='+str(report), '-rd', 'report_file='+str(report)]
        require(argv == expected, 'Native KLayout tool/mount/arguments/report differ')
        require(type(result.get('exit_code')) is int and type(result.get('seconds')) in (int, float) and
            math.isfinite(result['seconds']) and result['seconds'] >= 0, 'Invalid native process result')
        reports[check] = dict(exit_code=result['exit_code'], seconds=result['seconds'],
            report_sha256=sha(regular(report)) if report.exists() else None)
    return dict(closed_processes=3, passed=all(value['exit_code'] == 0 and value['report_sha256']
        for value in reports.values()), reports=reports, journal_sha256=sha(path))


def unchanged(mapping):
    for name, expected in mapping.items():
        require(sha(regular(name)) == expected, 'Signoff input/tool changed during execution: ' + name)


def unchanged_aliases(mapping):
    for name, identity in mapping.items():
        path = Path(name)
        require(path.is_symlink() and os.readlink(path) == identity['target'] and
            str(path.resolve()) == identity['resolved'], 'Signoff runtime alias changed: ' + name)


def cleanup(owner):
    query = ['docker', 'container', 'ls', '--all', '--no-trunc', '--filter',
        'label=org.pinwheel.signoff_owner=' + owner, '--format', '{{.ID}}']
    response = subprocess.run(query, capture_output=True, text=True, timeout=15)
    require(response.returncode == 0, 'Cannot inspect owned signoff containers')
    identities = response.stdout.splitlines()
    require(all(len(value) == 64 and all(c in '0123456789abcdef' for c in value) for value in identities),
        'Malformed owned signoff container ID')
    for identity in identities:
        stopped = subprocess.run(['docker', 'stop', '--time', '5', identity], capture_output=True, timeout=20)
        require(stopped.returncode == 0, 'Cannot stop owned signoff container')
    response = subprocess.run(query, capture_output=True, text=True, timeout=15)
    require(response.returncode == 0 and not response.stdout.strip(), 'Signoff container cleanup unconfirmed')
    return dict(status='absent', owned_container_ids=identities)


def native_klayout(config_path, arguments):
    """CLI adapter called by the unchanged official source, with actual argv."""
    config = read(config_path)
    out, pdk = Path(config['out']), Path(config['pdk'])
    cwd = Path.cwd().resolve()
    require(cwd.is_relative_to(out), 'Native precheck cwd escaped its attempt')
    require(config['container_name'] == container_name(out), 'Native precheck container name differs')
    command = ['docker', 'run', '--rm', '--pull', 'never', '--name', config['container_name'],
        '--network', 'none', '--read-only',
        '--tmpfs', '/tmp:rw,size=256m', '--cpus', '1', '--memory', '2g', '--memory-swap', '2g',
        '--label', 'org.pinwheel.signoff_owner=' + config['owner'],
        '--mount', 'type=bind,source=' + str(out) + ',target=' + str(out),
        '--mount', 'type=bind,source=' + str(pdk) + ',target=' + str(pdk) + ',readonly',
        '--workdir', str(cwd), '--entrypoint', 'klayout', config['image_id'], *arguments]
    journal = out / 'native-klayout.jsonl'
    started = time.monotonic()
    def event(value):
        with journal.open('a') as stream:
            stream.write(json.dumps(value, sort_keys=True) + '\n'); stream.flush(); os.fsync(stream.fileno())
    identity = str(uuid.uuid4())
    event(dict(event='intent', identity=identity, argv=command))
    result = subprocess.run(command)
    event(dict(event='result', identity=identity, exit_code=result.returncode,
        seconds=round(time.monotonic() - started, 3)))
    return result.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gds', type=Path, required=True)
    parser.add_argument('--lef', type=Path, required=True)
    parser.add_argument('--netlist', type=Path, required=True)
    parser.add_argument('--top', required=True)
    parser.add_argument('--pdk-root', type=Path, required=True)
    parser.add_argument('--support-root', type=Path, required=True)
    parser.add_argument('--python', type=Path, required=True)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--timeout-seconds', type=int, default=1800)
    args = parser.parse_args()
    require(re.fullmatch(r'tt_um_[A-Za-z0-9_]+', args.top), 'Invalid TT top name')
    require(1 <= args.timeout_seconds <= 3600, 'Bound official precheck to at most one hour')
    lock = read(TOOL_LOCK)
    frozen = verify_support(args.support_root, lock)
    for path in (Path(__file__), TOOL_LOCK, ROOT / 'scripts/validation_run.py', ROOT / 'scripts/process_group.py',
            ROOT / 'scripts/streaming_tt_physical.py', ROOT / 'tools/physical-toolchain.json',
            ROOT / 'scripts/streaming_tt_pdk.py', ROOT / 'test/test_streaming_tt_pdk.py',
            ROOT / 'test/test_streaming_tt_signoff.py'):
        path = regular(path)
        data = subprocess.check_output(['git', 'show', 'HEAD:' + str(path.relative_to(ROOT))], cwd=ROOT)
        require(path.read_bytes() == data, 'Commit signoff producer first: ' + str(path))
        frozen[str(path)] = sha(path)
    from streaming_tt_physical import inspect_runtime
    from streaming_tt_pdk import verify_complete_pdk
    docker = Path(shutil.which('docker') or '').resolve()
    frozen[str(regular(docker))] = sha(docker)
    runtime = inspect_runtime(read(ROOT / 'tools/physical-toolchain.json'))
    pdk = args.pdk_root.resolve()
    pdk_identity = verify_complete_pdk(pdk, read(ROOT / 'tools/physical-toolchain.json'), lock)
    # Freeze actual package payloads; versions alone do not bind imported code.
    python = args.python.absolute()
    require(python.is_file(), 'Missing isolated precheck interpreter')
    resolved_python = python.resolve()
    frozen[str(resolved_python)] = sha(resolved_python)
    aliases = {}
    link = python
    while link.is_symlink():
        aliases[str(link)] = dict(target=os.readlink(link), resolved=str(link.resolve()))
        link = (link.parent / os.readlink(link)).absolute()
    runtime_roots = [python.parent.parent / 'lib', resolved_python.parent.parent / 'lib']
    runtime_payload = {}
    for root in runtime_roots: runtime_payload.update(inventory(root, aliases=aliases))
    frozen.update(runtime_payload)
    environment = python_environment(os.environ)
    probe = 'import sys,json,importlib.metadata as m; print(json.dumps(dict(python=sys.version,executable=sys.executable,search_path=sys.path,optimize=sys.flags.optimize,no_user_site=sys.flags.no_user_site,packages={n:m.version(n) for n in ' + repr(list(lock['precheck_python_packages'])) + '})))'
    observed = subprocess.run([str(python), '-B', '-c', probe], env=environment, capture_output=True, text=True, timeout=30)
    require(observed.returncode == 0, 'Precheck Python environment unavailable')
    python_identity = json.loads(observed.stdout)
    require(python_identity['python'].startswith(lock['python_version_prefix']) and
        python_identity['packages'] == lock['precheck_python_packages'] and
        python_identity['optimize'] == 0 and python_identity['no_user_site'] == 1,
        'Official Python requirement versions or execution flags differ')
    out = fresh_directory(ROOT / 'build/streaming-tt-signoff', args.tag).resolve()
    copied = out / 'tt'; copied.mkdir()
    for name in lock['support_files']:
        target = copied / name; target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(args.support_root / name, target)
    frozen.update(verify_support(copied, lock))
    design = out / 'design'; design.mkdir()
    for name, source in [('gds', args.gds), ('lef', args.lef), ('v', args.netlist)]:
        source = regular(source); frozen[str(source)] = sha(source)
        target = design / (args.top + '.' + name); shutil.copyfile(source, target)
        frozen[str(target)] = sha(target)
    info = design / 'info.yaml'
    info.write_text(json.dumps(dict(project=dict(top_module=args.top, tiles='6x4', analog_pins=0, uses_3v3=False), pinout={})) + '\n')
    frozen[str(info)] = sha(info)
    owner = str(uuid.uuid4())
    wrapper_config = out / 'native-config.json'
    write(wrapper_config, dict(out=str(out), pdk=str(pdk), owner=owner, image_id=runtime['image_id'],
        container_name=container_name(out)))
    binary = out / 'bin'; binary.mkdir()
    wrapper = binary / 'klayout'
    wrapper.write_text('#!' + str(python) + '\nimport runpy,sys\nsys.path.insert(0,' + repr(str(ROOT / 'scripts')) +
        ')\nm=runpy.run_path(' + repr(str(Path(__file__).resolve())) +
        ')\nraise SystemExit(m["native_klayout"](' + repr(str(wrapper_config)) + ',sys.argv[1:]))\n')
    wrapper.chmod(0o755)
    frozen[str(wrapper)] = sha(wrapper); frozen[str(wrapper_config)] = sha(wrapper_config)
    expected = selected_checks((copied / 'precheck/precheck.py').read_text(), lock['tech'])
    report = dict(schema='pinwheel.streaming-tt-official-precheck.v1', passed=False,
        qualified=False, physical_acceptance_claim=False, started_utc=datetime.now(timezone.utc).isoformat(),
        source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip(),
        official_support_commit=lock['support_commit'], selected_checks=expected,
        container_name=container_name(out), cpus=1, memory='2g', memory_swap='2g',
        tools=runtime, pdk=pdk_identity, python=python_identity, input_sha256=frozen,
        runtime_aliases=aliases, interpreter_library_payload_frozen_before_probe=True,
        boundary=lock['scope'])
    report_path = out / 'report.json'
    write(report_path, report)
    overrides = dict(PDK_ROOT=str(pdk), PDK=lock['tech'],
        PATH=str(binary) + os.pathsep + os.environ['PATH'], PYTHONDONTWRITEBYTECODE='1',
        PYTHONNOUSERSITE='1', PYTHONPATH='')
    removed = sorted(key for key in os.environ if key.startswith('PYTHON') or key == '__PYVENV_LAUNCHER__')
    command = ['env', *[item for key in removed for item in ('-u', key)],
        *[name + '=' + value for name, value in overrides.items()],
        str(python), '-B', 'precheck.py', '--gds', str(design / (args.top + '.gds')), '--tech', lock['tech']]
    report['argv'] = command; write(report_path, report)
    started = time.monotonic()
    try:
        result = process_group.run_captured(command, cwd=copied / 'precheck',
            timeout=args.timeout_seconds, log_path=out / 'precheck.log')
        report['exit_code'] = result.returncode
        report['result'] = precheck_result(copied / 'precheck/reports/results.xml', expected, result.returncode)
        report['native'] = native_journal(out / 'native-klayout.jsonl',
            out=out, pdk=pdk, owner=owner, image_id=runtime['image_id'], gds=design/(args.top+'.gds'))
        report['passed'] = bool(report['result']['passed'] and report['native']['passed'])
    except BaseException as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        try:
            report['cleanup'] = cleanup(owner)
            unchanged(frozen)
            unchanged_aliases(aliases)
            current_runtime = {}
            for root in runtime_roots: current_runtime.update(inventory(root, aliases={}))
            require(current_runtime == runtime_payload, 'Runtime payload membership changed')
            require(verify_complete_pdk(pdk, read(ROOT / 'tools/physical-toolchain.json'), lock) == pdk_identity,
                'Completed PDK payload changed')
            require(inspect_runtime(read(ROOT / 'tools/physical-toolchain.json')) == runtime, 'Native tool identity changed')
            report['inputs_unchanged'] = True
        except BaseException as error:
            report['passed'] = False; report['closeout_error'] = type(error).__name__ + ': ' + str(error)
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        write(report_path, report)
    print(report_path, flush=True)
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
