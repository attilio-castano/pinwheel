#!/usr/bin/env python3
"""Run the initialized serial/SRAM control from a fresh committed Lean closure.

This is finite native execution of the typed digital equations. Symbolic
refinement and the axiom audit remain separate foundation-gate obligations.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SUITE = 'test/SerialInitializedBoundary.lean'


def committed_sources(head):
    seen = set()
    def visit(path):
        if path in seen:
            return
        seen.add(path)
        for module in re.findall(r'^import (\S+)', path.read_text(), re.M):
            child = ROOT / (module.replace('.', '/') + '.lean')
            if child.is_file():
                visit(child)
    visit(ROOT / SUITE)
    seen.update(ROOT / name for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'))
    seen.add(Path(__file__).resolve())
    paths = sorted(str(path.relative_to(ROOT)) for path in seen)
    tree = subprocess.check_output(['git', 'ls-tree', '-r', '-z', head, '--', *paths], cwd=ROOT)
    blobs = {}
    for entry in tree.split(b'\0'):
        if entry:
            metadata, path = entry.split(b'\t', 1)
            blobs[path.decode()] = metadata.split()[2].decode()
    object_format = subprocess.check_output(
        ['git', 'rev-parse', '--show-object-format'], cwd=ROOT, text=True).strip()
    hashes = {}
    for relative in paths:
        data = (ROOT / relative).read_bytes()
        oid = hashlib.new(object_format, f'blob {len(data)}\0'.encode() + data).hexdigest()
        if blobs.get(relative) != oid:
            raise RuntimeError('Input differs from selected committed source: ' + relative)
        hashes[relative] = hashlib.sha256(data).hexdigest()
    return hashes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', args.tag):
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    out = ROOT / 'build/validation' / args.tag
    if out.exists():
        raise RuntimeError('Choose a fresh tag to preserve earlier validation evidence')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('The pinned Lean toolchain must be on PATH')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    hashes = committed_sources(head)
    archive = subprocess.check_output(['git', 'archive', '--format=tar', head, '--', *hashes], cwd=ROOT)
    out.mkdir(parents=True)
    started = time.monotonic()
    report = dict(passed=False, source_commit=head, source_sha256=hashes, commands=[],
                  producer_workspace='Fresh temporary git archive of the committed Lean dependency closure',
                  boundary='Finite native typed digital serial/SRAM execution with independent source and ABI controls. '
                           'No native compiler proof, emitter/RTL equivalence or electrical qualification.')
    try:
        with tempfile.TemporaryDirectory(prefix='pinwheel-serial-initialized-') as directory:
            snapshot = Path(directory)
            with tarfile.open(fileobj=io.BytesIO(archive)) as committed:
                committed.extractall(snapshot, filter='data')
            for relative, expected in hashes.items():
                if hashlib.sha256((snapshot / relative).read_bytes()).hexdigest() != expected:
                    raise RuntimeError('Archived input hash mismatch: ' + relative)
            imports = re.findall(r'^import (\S+)', (snapshot / SUITE).read_text(), re.M)
            commands = [('version', [lake, 'env', 'lean', '--version']),
                        ('build', [lake, 'build', *imports]),
                        ('execution', [lake, 'env', 'lean', '-DwarningAsError=true', '--run', SUITE])]
            for label, command in commands:
                print(f'{label}: started', flush=True)
                with (out / f'{label}.log').open('w') as log:
                    result = subprocess.run(command, cwd=snapshot, stdout=log, stderr=subprocess.STDOUT)
                report['commands'].append(dict(label=label, command=command, exit_code=result.returncode))
                if result.returncode:
                    raise RuntimeError(f'{label} failed; see {out / (label + ".log")}')
                if label == 'version':
                    version = (out / 'version.log').read_text().strip()
                    expected = (snapshot / 'lean-toolchain').read_text().strip().split(':v')[-1]
                    report['lean'] = version
                    report['expected_lean_version'] = expected
                    if not re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version):
                        raise RuntimeError(f'Expected repository toolchain {expected}, got {version}')
                print(f'{label}: passed', flush=True)
            output = (out / 'execution.log').read_text()
            if not re.search(r'Serial initialized boundaries: .*; passed\s*$', output):
                raise RuntimeError('Missing initialized execution completion marker')
            report['result'] = output.strip().splitlines()[-1]
            if committed_sources(head) != hashes:
                raise RuntimeError('Validation inputs changed during execution')
            report['passed'] = True
    except Exception as error:
        report['error'] = str(error)
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Initialized serial control passed: {out / "report.json"}', flush=True)


if __name__ == '__main__':
    main()
