#!/usr/bin/env python3
"""Reproduce the retained paired design's acceptance assessment without CAD.

Exit 0 means the assessment completed, not that the chip is accepted. Use
--require-accepted to return 2 for a complete assessment with open requirements.
Invalid/missing evidence returns 1. Every run requires a new output tag.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
import time

from design_acceptance import Evidence, POLICY, assess, markdown
from validation_run import Commands, fresh_directory

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--selection', type=Path, default=Path('physical/experiments/design-acceptance-inputs.json'))
    parser.add_argument('--require-accepted', action='store_true')
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/validation', args.tag)
    evidence = Evidence(ROOT)
    report = dict(schema=1, policy=POLICY, status='running', A_accepted=False,
        B_admitted=False, complete_design_iteration=False, cad_seconds=0,
        date=datetime.now(timezone.utc).isoformat(), commands=[])
    started = time.monotonic()
    try:
        selection_ref = evidence.ref(args.selection)
        selection = evidence.load(selection_ref)
        report['selection'] = selection_ref
        report['policy'] = selection.get('policy')
        # Freeze the executable checker and all already imported local helpers.
        source_paths = {Path(__file__), *(Path(m.__file__) for m in list(sys.modules.values())
            if getattr(m, '__file__', None) and Path(m.__file__).is_relative_to(ROOT / 'scripts'))}
        source_paths.add(ROOT / 'test/test_design_acceptance.py')
        # paired_execution loads this grammar with runpy, outside sys.modules.
        source_paths.add(ROOT / 'scripts/execution-vectors.py')
        report['checker_sources'] = [evidence.ref(p) for p in sorted(source_paths)]
        run = Commands(ROOT, out, records=report['commands'], default_timeout=120)
        report.update(assess(evidence, selection, out, run))
        evidence.close()
        report.update(status='assessed', inputs_unchanged=True)
    except (ValueError, KeyError, TypeError, OSError, RuntimeError) as error:
        report.update(status='invalid_evidence', A_accepted=False, B_admitted=False,
                      complete_design_iteration=False, error=f'{type(error).__name__}: {error}')
    report['seconds'] = round(time.monotonic() - started, 3)
    report['verified_files'] = dict(evidence.files)
    report['verified_file_count'] = len(evidence.files)
    report['artifacts_sha256'] = {p.name: evidence.ref(p)['sha256'] for p in sorted(out.iterdir()) if p.is_file()}
    with (out / 'report.json').open('x') as stream:
        stream.write(json.dumps(report, indent=2) + '\n')
    with (out / 'report.md').open('x') as stream:
        stream.write(markdown(report, ROOT))
    print(json.dumps({k: report.get(k) for k in ('status', 'A_accepted', 'blockers', 'seconds', 'verified_file_count', 'error')}))
    if report['status'] != 'assessed':
        return 1
    return 2 if args.require_accepted and not report['A_accepted'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
