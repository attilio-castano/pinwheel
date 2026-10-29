"""Explicit, bounded HOST execution of the predeclared independent RC reference.

The campaign owner launches this command under its resource supervisor.  No
execution occurs at import; the emitted report never qualifies a process model.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_reference as R


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--plan-sha256', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    P.need(sha(args.plan) == args.plan_sha256, 'Frozen reference plan hash differs')
    plan = json.loads(args.plan.read_text())
    P.validate_protocol(plan['protocol'])
    source = Path(__file__).resolve().parent
    for name in ('streaming_8x4_rc_protocol.py', 'streaming_8x4_rc_reference.py'):
        P.need(sha(source / name) == plan['producers_sha256'][name], 'Reference producer identity differs')
    P.need(args.output.is_absolute() and not args.output.exists() and args.output.parent.is_dir(),
           'Reference output owner must be fresh')
    args.output.mkdir()
    started = time.monotonic()
    report = {'schema': 'pinwheel.streaming-8x4-rc-reference-execution.v1',
              'started_utc': datetime.now(timezone.utc).isoformat(),
              'plan_sha256': args.plan_sha256, 'runner_sha256': sha(__file__),
              'producer_sha256': {name: sha(source / name) for name in
                                  ('streaming_8x4_rc_protocol.py', 'streaming_8x4_rc_reference.py')},
              'qualified': False, 'passed': False, 'cases': [],
              'scope': 'independent discrete equation solution; mesh/domain stability is empirical'}
    target = args.output / 'report.json'
    def save():
        target.write_bytes(P.canonical(report) + b'\n')
    save()
    try:
        p = plan['protocol']; g, r = p['geometry'], p['reference']
        for width in ('0.16', '0.32'):
            for step in r['mesh_steps_um']:
                for extent in r['domain_extents_um']:
                    P.need(time.monotonic() - started < 100, 'Independent reference work allowance exhausted')
                    result = R.solve_wire(float(width), float(g['gap_um']), float(g['thickness_um']),
                                          float(extent), float(step),
                                          layers=tuple(tuple(float(v) for v in row) for row in r['epsilon_layers']),
                                          tolerance=float(r['residual_relative_tolerance']),
                                          maximum_iterations=r['maximum_cg_iterations'], maximum_nodes=r['maximum_nodes'])
                    result['case_id'] = 'w' + width + '-h' + step + '-E' + extent
                    report['cases'].append(result); save()
        expected = ['w' + width + '-h' + step + '-E' + extent for width in ('0.16', '0.32')
                    for step in r['mesh_steps_um'] for extent in r['domain_extents_um']]
        P.need([x['case_id'] for x in report['cases']] == expected, 'Reference expected membership differs')
        report['passed'] = True
    except BaseException as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        report['inputs_unchanged'] = sha(args.plan) == args.plan_sha256 and all(
            sha(source / name) == value for name, value in report['producer_sha256'].items())
        report['passed'] = report['passed'] and report['inputs_unchanged']
        report['wall_seconds'] = time.monotonic() - started
        report['ended_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print(json.dumps({k: v for k, v in report.items() if k != 'cases'}, indent=2))
    return 0 if report['passed'] else 2


if __name__ == '__main__':
    raise SystemExit(main())
