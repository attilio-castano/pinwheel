"""Prepare or perform a fresh HOST-only selected-runtime custody audit.

No recovered executable or version command is launched. The unchanged native
identity selector hashes the exact runtime used by the public-wire worker; the
unchanged archive auditor compares those CAD bytes and aliases to the pinned
official tarballs without extracting them. Lean, Python and OS provenance stay
outside that narrow archive claim. Run the audit only in a Root-approved slice.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SOURCES = ('scripts/streaming_8x4_final_runtime.py', 'scripts/check-streaming-uart.py',
           'scripts/check-buffered-rtl-sim.py', 'scripts/streaming_mapped_runtime.py',
           'tools/hardware-toolchain.json')
HOST_TOOLS = dict(
    python='/opt/homebrew/Cellar/python@3.13/3.13.5/Frameworks/Python.framework/Versions/3.13/bin/python3.13',
    lean='/Users/attiliocastano/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean',
    lake='/Users/attiliocastano/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake')
HOST_PINS = dict(python='a1f6d9dc20d4787a84dc2fe782094a7bac5946f49a962aa0af48a02f0e8d5bc5',
    lean='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554',
    lake='58261a1a2fa1a362376c71e02ca854a093e71cc5e6ea64b287a931cb2565273d')


def need(value, message):
    if not value: raise ValueError(message)


def regular(path):
    path = Path(path).absolute()
    need(path.is_file() and not path.is_symlink(), 'Regular runtime authority input required: ' + str(path))
    return path


def digest(path):
    with regular(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'Duplicate runtime JSON key'); result[key] = value
        return result
    def invalid(value): raise ValueError('Nonfinite runtime JSON: ' + value)
    return json.loads(regular(path).read_bytes(), object_pairs_hook=pairs, parse_constant=invalid)


def write(path, value):
    with Path(path).open('x') as stream:
        stream.write(json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n')


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, regular(path))
    module = importlib.util.module_from_spec(spec); sys.modules[name] = module
    spec.loader.exec_module(module); return module


def source_identity():
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True, timeout=30).strip()
    sources = {}
    for name in SOURCES:
        payload = subprocess.check_output(['git', 'show', commit + ':' + name], cwd=ROOT, timeout=30)
        need(hashlib.sha256(payload).hexdigest() == digest(ROOT / name),
             'Commit the exact fresh runtime-audit producer before preparing: ' + name)
        sources[name] = digest(ROOT / name)
    return commit, sources


def tools_from_assembly(assembly_path):
    assembly = read(assembly_path)
    need(assembly.get('schema') == 'pinwheel.streaming-8x4-common-cad-runtime.v1' and
         assembly.get('executable_launched') is False and assembly.get('qualified') is False,
         'Fresh recovered common runtime assembly required')
    tools = dict(assembly['tools'], **HOST_TOOLS)
    need(set(tools) == {'circt', 'yosys', 'abc', 'solver', 'iverilog', 'vvp', 'lean', 'lake', 'python'},
         'All nine exact native runtime tool paths required')
    for name, pin in HOST_PINS.items():
        need(digest(tools[name]) == pin, 'Pinned existing host executable changed: ' + name)
    return tools


def prepare(assembly_path, output):
    output = Path(output).absolute(); need(not output.exists(), 'Preserve earlier runtime preparation')
    commit, sources = source_identity(); assembly_path = regular(assembly_path).resolve()
    tools = tools_from_assembly(assembly_path)
    output.mkdir(parents=True)
    config = dict(schema='pinwheel.streaming-8x4-final-runtime-request.v1', producer_commit=commit,
        producer_sha256=sources, assembly=dict(path=str(assembly_path), sha256=digest(assembly_path)),
        tools=tools, executable_launched=False, native_versions_checked=False, qualified=False,
        boundary='HOST hashing and official CAD archive membership only. No native execution or proof qualification.')
    write(output / 'request.json', config)
    return config


def verify_request(request_path):
    request_path = regular(request_path).resolve(); config = read(request_path)
    need(config.get('schema') == 'pinwheel.streaming-8x4-final-runtime-request.v1' and
         config.get('executable_launched') is False and config.get('qualified') is False,
         'Expected fresh HOST runtime request')
    for name, expected in config['producer_sha256'].items():
        need(name in SOURCES and digest(ROOT / name) == expected, 'Runtime audit producer changed')
        committed = subprocess.check_output(['git', 'show', config['producer_commit'] + ':' + name], cwd=ROOT, timeout=30)
        need(hashlib.sha256(committed).hexdigest() == expected, 'Runtime source differs from recorded commit')
    need(set(config['producer_sha256']) == set(SOURCES), 'Runtime producer closure incomplete')
    need(digest(config['assembly']['path']) == config['assembly']['sha256'] and
         tools_from_assembly(config['assembly']['path']) == config['tools'], 'Recovered runtime assembly changed')
    return config


def audit(request_path, report_path):
    config = verify_request(request_path); before = digest(request_path); started = time.monotonic()
    report_path = Path(report_path).absolute(); need(not report_path.exists(), 'Preserve earlier runtime audit')
    raw = load('_streaming8_runtime_raw', ROOT / 'scripts/check-streaming-uart.py')
    helper = raw.helpers(); raw.check_environment(helper)
    membership = load('_streaming8_runtime_membership', ROOT / 'scripts/streaming_mapped_runtime.py')
    manifest = read(ROOT / 'tools/hardware-toolchain.json')
    identity = raw.tool_identity(helper, config['tools'], manifest)
    selected = membership.audit(identity, manifest, config['tools'])
    need(raw.tool_identity(helper, config['tools'], manifest) == identity, 'Selected runtime changed during audit')
    need(verify_request(request_path) == config and digest(request_path) == before, 'Runtime request changed during audit')
    report = dict(schema='pinwheel.streaming-8x4-final-runtime-audit.v1', passed=True,
        producer_commit=config['producer_commit'], producer_sha256=config['producer_sha256'],
        request=dict(path=str(regular(request_path).resolve()), sha256=before), tools=config['tools'],
        tool_identity_before=identity, tool_identity_after=identity, tool_identity_unchanged=True,
        cad_runtime_archive_membership=selected, executable_launched=False, native_versions_checked=False,
        qualified=False, completed_utc=datetime.now(timezone.utc).isoformat(),
        elapsed_seconds=round(time.monotonic() - started, 3),
        boundary='Fresh HOST selected-runtime custody only. Native behavior, Lean/Python/OS provenance and final proof remain separate gates.')
    write(report_path, report); return report


def closed_report(report_path):
    """Read a completed audit for a separately guarded fresh Native worker."""
    report_path = regular(report_path).resolve(); report = read(report_path)
    need(report.get('schema') == 'pinwheel.streaming-8x4-final-runtime-audit.v1' and report.get('passed') is True and
         report.get('executable_launched') is False and report.get('native_versions_checked') is False and
         report.get('qualified') is False and report.get('tool_identity_unchanged') is True and
         report.get('tool_identity_before') == report.get('tool_identity_after') and
         report.get('cad_runtime_archive_membership', {}).get('cad_selected_archive_membership_verified') is True,
         'Closed exact selected-runtime custody audit required')
    need(digest(report['request']['path']) == report['request']['sha256'], 'Runtime request changed after audit')
    request = verify_request(report['request']['path'])
    need(report['producer_commit'] == request['producer_commit'] and report['producer_sha256'] == request['producer_sha256'] and
         report['tools'] == request['tools'], 'Runtime audit differs from its request authority')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__); sub = parser.add_subparsers(dest='mode', required=True)
    prep = sub.add_parser('prepare'); prep.add_argument('--assembly', type=Path, required=True); prep.add_argument('--output', type=Path, required=True)
    run = sub.add_parser('audit'); run.add_argument('--request', type=Path, required=True); run.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    result = prepare(args.assembly, args.output) if args.mode == 'prepare' else audit(args.request, args.report)
    print(json.dumps({key: result[key] for key in ('schema', 'qualified')}, sort_keys=True))


if __name__ == '__main__': main()
