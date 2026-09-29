"""Bounded, offline sensitivity runs on the retained filled chip.

Usage: python3 -B physical/fixtures/power-boundary/run.py STUDY CASE CAP_SECONDS
The request and per-case inputs are immutable for an invocation. Never reroute.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
from validation_run import Commands, sha


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    base = Path(sys.argv[1]).resolve()
    label, cap = sys.argv[2], int(sys.argv[3])
    require(re.fullmatch(r'[a-z0-9-]+', label), 'Invalid case name')
    case = base / label
    req = json.loads((base / 'request.json').read_text())
    spec = json.loads((case / 'case.json').read_text())
    receipt = base / (label + '-receipt.json')
    require(not receipt.exists() and not (case / 'output').exists(), 'Preserve previous run')
    require(0 < cap <= req['limits']['per_invocation_seconds'] <= 600, 'Invocation cap')
    used = 0
    for p in base.glob('*-receipt.json'):
        old = json.loads(p.read_text())
        require(old['sources_unchanged'] and old['status'] != 'running', 'Unsettled prior run')
        require(old.get('container_state', 'absent') == 'absent', 'Unsettled container')
        used += old['cad_seconds']
    require(used + cap <= req['limits']['continuation_cad_seconds'], 'Continuation budget')
    require(req['prior_campaign_cad_seconds'] + used + cap <= req['limits']['campaign_cad_seconds'], 'Campaign budget')
    inputs = dict(req['inputs_sha256'])
    inputs.update(spec.get('inputs_sha256', {}))
    for p in [Path(__file__), base / 'request.json', *case.iterdir()]:
        if p.is_file():
            inputs[str(p)] = sha(p)
    for p, digest in inputs.items():
        require(sha(p) == digest, 'Changed input: ' + p)
    commands = []
    name = None
    if spec['kind'] == 'native':
        im = json.loads(subprocess.check_output(['docker', 'image', 'inspect', req['image_id']], text=True))[0]
        lock = json.loads((ROOT / 'tools/physical-toolchain.json').read_text())
        runtime = {k: v for k, v in im['Config'].items() if v is not None}
        require(im['RootFS']['Layers'] == lock['container_rootfs_diff_ids'], 'Image layers')
        require(hashlib.sha256(json.dumps(runtime, sort_keys=True).encode()).hexdigest() == lock['container_runtime_config_sha256'], 'Image config')
        names = subprocess.check_output(['docker', 'ps', '-a', '--format', '{{.Names}}'], text=True).splitlines()
        require(not any(n.startswith('pinwheel-') for n in names), 'Existing Pinwheel container')
        name = 'pinwheel-power-boundary-' + label
        cmd = ['docker', 'run', '--rm', '--pull', 'never', '--network', 'none', '--read-only', '--name', name,
               '--cpus', '4', '--memory', '6g', '--tmpfs', '/tmp:rw,size=512m']
        for host, guest in [(req['design'], '/work/core'), (req['pdk_root'], '/work/pdk'),
                            (req['finalization_root'], '/probe'), (str(base), '/study'),
                            (str(ROOT / 'physical/fixtures/power-boundary'), '/fixtures')]:
            cmd += ['--mount', f'type=bind,source={host},target={guest},readonly']
        (case / 'output').mkdir()
        cmd += ['--mount', f'type=bind,source={case / "output"},target=/output', '--workdir', '/output',
                req['image_id'], 'python3', '-B', '/fixtures/native.py', f'/study/{label}/case.json']
        commands.append((cmd, label))
    elif spec['kind'] == 'simulation':
        (case / 'output').mkdir()
        commands = [(x['argv'], x['label']) for x in spec['commands']]
    else:
        raise ValueError('Unknown case kind')
    result = dict(status='running', qualification=False, full_flow_attempts=0,
                  limits=dict(seconds=cap, cpus=4, memory_gib=6), inputs_sha256=inputs, commands=[],
                  prior_campaign_cad_seconds=round(req['prior_campaign_cad_seconds'] + used, 3))
    receipt.write_text(json.dumps(result, indent=2) + '\n')
    start = time.monotonic()
    error = None
    try:
        runner = Commands(ROOT, case / 'output', records=result['commands'])
        for cmd, command_label in commands:
            remaining = cap - (time.monotonic() - start)
            require(remaining > 0, 'Invocation deadline')
            runner(cmd, command_label, timeout=remaining)
        result['status'] = 'completed'
    except BaseException as exc:
        error = exc
        result.update(status='failed', error=f'{type(exc).__name__}: {exc}')
    finally:
        if name:
            q = subprocess.run(['docker', 'container', 'inspect', name], capture_output=True, text=True, timeout=10)
            if q.returncode == 0:
                subprocess.run(['docker', 'stop', '--time', '2', name], capture_output=True, timeout=15)
                q = subprocess.run(['docker', 'container', 'inspect', name], capture_output=True, text=True, timeout=10)
            result['container_state'] = 'absent' if q.returncode and 'No such container' in q.stderr else 'unconfirmed'
        result.update(cad_seconds=round(time.monotonic() - start, 3),
                      sources_unchanged=all(sha(p) == h for p, h in inputs.items()))
        if not result['sources_unchanged'] or result.get('container_state', 'absent') != 'absent':
            result['status'] = 'failed'
        result['artifacts_sha256'] = {str(p.relative_to(base)): sha(p) for p in case.rglob('*') if p.is_file()}
        receipt.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ['commands', 'inputs_sha256', 'artifacts_sha256']}, indent=2))
    if error:
        raise error
    require(result['status'] == 'completed', 'Unsettled run')


if __name__ == '__main__':
    main()
