#!/usr/bin/env python3
"""Reparse hash-bound diagnostic connection reports without running CAD.

The request binds a physical context, comparison SDC, saved measurements,
connection names, and each corner's raw report and Liberty files. Paths are
absolute or relative to the request. A successful replay does not qualify a chip.
"""
import argparse
import hashlib
import json
from pathlib import Path

from physical_organization import Library, parse_diagnostic_measurements


def replay(request_path):
    request_path = Path(request_path).resolve()
    request_bytes = request_path.read_bytes()
    request = json.loads(request_bytes)
    inputs = {str(request_path): hashlib.sha256(request_bytes).hexdigest()}

    def read(ref):
        if set(ref) != {'path', 'sha256'}:
            raise ValueError('Require a path and SHA-256 for every replay input')
        path = (request_path.parent / ref['path']).resolve()
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if digest != ref['sha256']:
            raise ValueError('Changed replay input: '+str(path))
        inputs[str(path)] = digest
        return data.decode()

    if (set(request) != {'schema', 'context', 'sdc', 'measurements', 'connections', 'corners'} or
            request['schema'] != 1 or not request['connections'] or
            len(set(request['connections'])) != len(request['connections']) or not request['corners']):
        raise ValueError('Incomplete or ambiguous replay request')
    context = json.loads(read(request['context']))
    sdc = read(request['sdc'])
    saved = json.loads(read(request['measurements']))
    if set(saved) != set(request['corners']):
        raise ValueError('Replay corners differ from saved measurements')
    texts, reports = {}, {}
    for corner, refs in request['corners'].items():
        if set(refs) != {'libraries', 'report'} or not refs['libraries']:
            raise ValueError('Missing corner libraries or raw connection report')
        texts[corner] = [read(ref) for ref in refs['libraries']]
        reports[corner] = read(refs['report'])
    library = Library(texts)
    missing = {}
    for corner, raw in reports.items():
        measured = parse_diagnostic_measurements(raw, request['connections'], context, library, corner, sdc)
        if measured != saved[corner]:
            raise ValueError('Replayed measurement differs from saved result: '+corner)
        missing[corner] = sorted(name for name, row in measured.items() if row['fanout'] is None)
    if any(hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest for path, digest in inputs.items()):
        raise ValueError('A replay input changed during verification')
    sources = [Path(__file__), *[Path(__file__).parent / name
        for name in ('physical_connections.py', 'physical_organization.py')]]
    return dict(schema=1, status='passed', measurements_equal=True,
        connection_corner_records=len(request['connections'])*len(reports),
        unreported_macro_fanout_limits=missing, physical_qualification=False,
        inputs_sha256=inputs, source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--request', type=Path, required=True)
    ap.add_argument('--output', type=Path, help='Optional new receipt; existing files are never overwritten')
    args = ap.parse_args()
    result = replay(args.request)
    text = json.dumps(result, indent=2, allow_nan=False)+'\n'
    if args.output:
        with args.output.open('x') as output:
            output.write(text)
    print(text, end='')


if __name__ == '__main__':
    main()
