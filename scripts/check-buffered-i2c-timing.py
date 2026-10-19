#!/usr/bin/env python3
"""Compare a committed typed I2C timing grid with the independent Python lowerer.

This is finite byte conformance. The symbolic Lean certificate and execution
proofs are checked by the foundation gate; no universal Python compiler or
electrical timing property is inferred from these comparisons.
"""
import argparse
import ast
import copy
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def fields(image):
    return dict(words=list(image.words), controls=list(image.controls),
                branch_indices=list(image.branch_indices), branch_table=list(image.branch_table),
                virtual_span=image.virtual_span, idle_levels=image.idle_levels,
                idle_enabled=image.idle_enabled, tx_bits=image.tx_bits,
                rx_reservation_bits=image.rx_bits)


def compare(actual, expected):
    for key, value in expected.items():
        if actual.get(key) != value:
            raise ValueError('Typed/Python timing image mismatch: ' + key)


def producer_sources():
    seen = set()
    def visit(path):
        if path in seen:
            return
        seen.add(path)
        for module in re.findall(r'^import (\S+)', path.read_text(), re.M):
            child = ROOT / (module.replace('.', '/') + '.lean')
            if child.is_file():
                visit(child)
    visit(ROOT / 'test/BufferedI2cTimingSource.lean')
    seen.update((ROOT / 'scripts').glob('buffered_*.py'))
    pending = [path for path in seen if path.suffix == '.py']
    visited_python = set()
    while pending:
        path = pending.pop()
        if path in visited_python:
            continue
        visited_python.add(path)
        for node in ast.walk(ast.parse(path.read_text())):
            modules = ([node.module] if isinstance(node, ast.ImportFrom) and node.module else
                       [alias.name for alias in node.names] if isinstance(node, ast.Import) else [])
            for module in modules:
                child = ROOT / 'scripts' / (module.split('.')[0] + '.py')
                if child.is_file() and child not in visited_python:
                    seen.add(child)
                    pending.append(child)
    seen.update(ROOT / name for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'))
    seen.add(Path(__file__).resolve())
    return sorted(seen)


def committed_hashes(head, sources):
    paths = [str(path.relative_to(ROOT)) for path in sources]
    tree = subprocess.check_output(['git', 'ls-tree', '-r', '-z', head, '--', *paths], cwd=ROOT)
    blobs = {}
    for entry in tree.split(b'\0'):
        if entry:
            metadata, path = entry.split(b'\t', 1)
            blobs[path.decode()] = metadata.split()[2].decode()
    object_format = subprocess.check_output(
        ['git', 'rev-parse', '--show-object-format'], cwd=ROOT, text=True).strip()
    hashes = {}
    for path, relative in zip(sources, paths):
        data = path.read_bytes()
        oid = hashlib.new(object_format, f'blob {len(data)}\0'.encode() + data).hexdigest()
        if blobs.get(relative) != oid:
            raise RuntimeError('Producer input is not the committed source at HEAD: ' + relative)
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
        raise RuntimeError('Choose a fresh tag to preserve previous validation evidence')
    lake = shutil.which('lake')
    if not lake:
        raise RuntimeError('The pinned Lean toolchain must be on PATH')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    sources = producer_sources()
    hashes = committed_hashes(head, sources)
    archive = subprocess.check_output(['git', 'archive', '--format=tar', head, '--', *hashes], cwd=ROOT)
    snapshot = tempfile.TemporaryDirectory(prefix='pinwheel-i2c-timing-')
    producer_root = Path(snapshot.name)
    with tarfile.open(fileobj=io.BytesIO(archive)) as committed:
        committed.extractall(producer_root, filter='data')
    for relative, expected_hash in hashes.items():
        if hashlib.sha256((producer_root / relative).read_bytes()).hexdigest() != expected_hash:
            raise RuntimeError('Archived producer input does not match committed hash: ' + relative)
    sys.path.insert(0, str(producer_root / 'scripts'))
    from buffered_reactive_hardware import compact_i2c_read
    from buffered_sram_hardware import lower_sram
    out.mkdir(parents=True)
    started = time.monotonic()
    commands = []
    build_command = [lake, 'build', 'Pinwheel.Hardware.Buffered.I2cTimingUpload']
    build = subprocess.run(build_command, cwd=producer_root, text=True, capture_output=True)
    (out / 'producer-build.log').write_text(build.stdout + build.stderr)
    commands.append(dict(command=build_command, exit_code=build.returncode))
    if build.returncode:
        raise RuntimeError('Timing producer dependency build failed: ' + build.stdout + build.stderr)
    command = [lake, 'env', 'lean', '-DwarningAsError=true', '--run', 'test/BufferedI2cTimingSource.lean']
    result = subprocess.run(command, cwd=producer_root, text=True, capture_output=True)
    commands.append(dict(command=command, exit_code=result.returncode))
    (out / 'typed-export.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError('Typed timing export failed: ' + result.stderr)
    exported = json.loads(result.stdout)
    if exported.get('schema') != 'pinwheel-buffered-i2c-timing-source-v1':
        raise RuntimeError('Wrong typed timing export schema')
    expected_pairs = {(phase, wait) for phase in (3, 4, 5, 128, 256) for wait in (4, 5, 32, 128, 256)}
    actual_pairs = [(case['phase_cycles'], case['wait_cycles']) for case in exported['cases']]
    if len(actual_pairs) != 25 or set(actual_pairs) != expected_pairs:
        raise RuntimeError('Missing, duplicate or unexpected timing-grid cases')
    cases = []
    for case in exported['cases']:
        phase, wait = case['phase_cycles'], case['wait_cycles']
        image = lower_sram(compact_i2c_read(4, phase, wait))
        compare(case['image'], fields(image))
        cases.append(dict(phase_cycles=phase, wait_cycles=wait, image_key=image.key, fields=9, passed=True))
    expected = fields(lower_sram(compact_i2c_read(4, 3, 4)))
    baseline = next(case['image'] for case in exported['cases']
                    if (case['phase_cycles'], case['wait_cycles']) == (3, 4))
    mutations = []
    for key in ('words', 'controls', 'branch_indices', 'branch_table'):
        changed = copy.deepcopy(baseline)
        changed[key][0] ^= 1
        try:
            compare(changed, expected)
        except ValueError:
            mutations.append(dict(field=key, rejected=True))
        else:
            raise RuntimeError('Timing conformance accepted changed ' + key)
    rejected_timings = []
    for phase, wait in ((1, 32), (2, 32), (4, 1), (4, 3)):
        try:
            compact_i2c_read(4, phase, wait)
        except ValueError:
            rejected_timings.append(dict(phase_cycles=phase, wait_cycles=wait, rejected=True))
        else:
            raise RuntimeError('Python public timing admission unexpectedly changed')
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() != head:
        raise RuntimeError('HEAD changed during timing validation')
    if committed_hashes(head, sources) != hashes:
        raise RuntimeError('Timing producer source changed during validation')
    report = dict(passed=True, source_commit=head, source_sha256=hashes, python=sys.version,
                  producer_workspace='Fresh temporary git archive of the committed dependency closure',
                  commands=commands, constructor_cases=cases, image_mutations=mutations,
                  rejected_python_timings=rejected_timings, elapsed_seconds=round(time.monotonic()-started, 3),
                  boundary='Finite typed/Python byte conformance for 25 supported public timing pairs. '
                           'The Lean digital field theorem also includes values below Python public timing bounds; '
                           'no Python API extension, universal compiler theorem or electrical qualification is claimed.')
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    snapshot.cleanup()
    print(f'I2C timing conformance: 25 images, 4 rejected byte mutations, 4 rejected public timings; {out / "report.json"}')


if __name__ == '__main__':
    main()
