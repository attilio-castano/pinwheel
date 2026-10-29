"""Run an explicitly selected RC case/mesh block in one campaign-owned lease.

The exact plan, block arguments and this producer must be admitted by Root.
No adaptive flag/geometry changes, skipped failures, or model promotion occur.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_protocol as P


def selection(plan, cases, meshes):
    P.need(cases and meshes and len(set(cases)) == len(cases) and len(set(meshes)) == len(meshes),
           'Missing/duplicate block selection')
    names = [x['name'] for x in plan['cases']]
    P.need(all(name in names for name in cases), 'Unadmitted block case')
    ladder = plan['protocol']['manual_solver']['mesh_ladder']
    P.need(all(mesh in ladder for mesh in meshes), 'Unadmitted block mesh')
    indices = [ladder.index(mesh) for mesh in meshes]
    P.need(indices == list(range(indices[0], indices[-1] + 1)), 'Skipped/reordered mesh block')
    P.need(len(cases) * len(meshes) <= plan['protocol']['resource_request']['maximum_solver_calls'],
           'Block solver-call allowance exceeded')
    return [(case, mesh) for case in cases for mesh in meshes]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('plan', 'plan-sha256', 'cases', 'runtime', 'output'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--case', action='append', required=True)
    parser.add_argument('--mesh', action='append', required=True)
    parser.add_argument('--work-seconds', type=int, required=True)
    args = parser.parse_args()
    plan = json.loads(Path(args.plan).read_text())
    P.need(E.sha(args.plan) == args.plan_sha256, 'Block frozen plan hash differs')
    P.validate_protocol(plan['protocol'])
    jobs = selection(plan, args.case, args.mesh)
    P.need(130 <= args.work_seconds <= 7200, 'Block work allowance outside declared campaign range')
    output = Path(args.output)
    P.need(output.is_absolute() and not output.exists() and output.parent.is_dir(), 'Block output must be fresh')
    output.mkdir()
    started = time.monotonic()
    report = {'schema': 'pinwheel.streaming-8x4-rc-explicit-block.v1',
              'started_utc': datetime.now(timezone.utc).isoformat(), 'plan_sha256': args.plan_sha256,
              'producer_sha256': E.sha(__file__), 'selected_jobs': jobs, 'actual_jobs': [],
              'passed': False, 'qualified': False, 'work_seconds': args.work_seconds}
    E.write(output / 'report.json', report)
    try:
        for index, (case, mesh) in enumerate(jobs):
            remaining = args.work_seconds - (time.monotonic() - started)
            P.need(remaining >= plan['protocol']['resource_request']['solver_seconds_per_call'] + 10,
                   'Not enough allowance remains for a full admitted solver call and cleanup')
            target = output / ('job-' + str(index).zfill(3))
            rc = E.run_one(SimpleNamespace(plan=args.plan, plan_sha256=args.plan_sha256, cases=args.cases,
                                          runtime=args.runtime, output=str(target), case=case, mesh=mesh))
            row = {'case': case, 'mesh': mesh, 'return_code': rc,
                   'report_sha256': E.sha(target / 'report.json'), 'directory': str(target)}
            report['actual_jobs'].append(row); E.write(output / 'report.json', report)
            P.need(rc == 0, 'Actual selected solver call failed; block stops without skipping it')
        P.need(len(report['actual_jobs']) == len(jobs), 'Incomplete selected solver block')
        report['passed'] = True
    except BaseException as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        report['ended_utc'] = datetime.now(timezone.utc).isoformat()
        report['wall_seconds'] = time.monotonic() - started
        E.write(output / 'report.json', report)
    print(json.dumps(report, indent=2))
    return 0 if report['passed'] else 2


if __name__ == '__main__':
    raise SystemExit(main())
