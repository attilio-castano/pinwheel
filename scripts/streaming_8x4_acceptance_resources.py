"""Campaign-owned adapter around the unchanged, four-hour resource supervisor.

Only Root launches real jobs. This adapter enforces the approved October 22
schedule and fixes all workers to one explicit campaign-root lock/sentinel.
The inherited supervisor still owns process cleanup, resource floors, Docker
bounds, immutable inputs and the four-hour maximum. Resource success never
establishes CAD/proof/RC acceptance. HOST tests below do not run CAD or Lean.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
from pathlib import Path
import sys

from streaming_8x4_acceptance import job_window, require, shared_lease_paths, timestamp


SCHEDULE = dict(start='2026-10-22T21:00:35Z', candidate_cutoff='2026-10-23T03:00:35Z',
                rc_experiment_cutoff='2026-10-23T05:00:35Z', heavy_cutoff='2026-10-23T08:00:35Z',
                hard_deadline='2026-10-23T09:00:35Z')
KINDS = {'cad': ('candidate_cad', 'cad'), 'cad-validation': ('fixed_cad', 'cad-validation'),
         'lean': ('proof', 'lean'), 'solver': ('rc_experiment', 'host'),
         'solver-validation': ('rc_validation', 'host'), 'host': ('host_closeout', 'host')}


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument('--campaign-root', type=Path, required=True)
    result.add_argument('--kind', choices=tuple(KINDS), required=True)
    result.add_argument('--tag', required=True)
    result.add_argument('--timeout-seconds', type=int, required=True)
    result.add_argument('--rss-mib', type=int, default=4096)
    result.add_argument('--container-name')
    result.add_argument('--input', type=Path, action='append', default=[])
    result.add_argument('--validation-parent', type=Path)
    result.add_argument('--deadline', default=SCHEDULE['heavy_cutoff'],
                        help='Must equal the approved heavy cutoff; new work has earlier enforced limits')
    result.add_argument('argv', nargs=argparse.REMAINDER)
    return result


def load_guard(root):
    path = root / 'scripts/streaming_tt_resources.py'
    require(path.is_file() and not path.is_symlink(), 'Missing regular inherited supervisor')
    spec = importlib.util.spec_from_file_location('streaming_8x4_inherited_resources', path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def run(args, *, guard=None, now=None):
    root = args.campaign_root
    leases = shared_lease_paths(root)
    root = root.resolve(strict=True)
    require(timestamp(args.deadline) == timestamp(SCHEDULE['heavy_cutoff']), 'Cannot override approved heavy cutoff')
    require(type(args.timeout_seconds) is int and 1 <= args.timeout_seconds <= 14400,
            'Inherited four-hour per-job bound remains unchanged')
    campaign_kind, inherited_kind = KINDS[args.kind]
    fixed = campaign_kind in {'fixed_cad', 'proof', 'rc_validation'}
    require(fixed == (args.validation_parent is not None), 'Fixed-target jobs require one explicit frozen parent')
    parent_hash = None
    if fixed:
        require(args.validation_parent.is_file() and not args.validation_parent.is_symlink(),
                'Validation parent must be a regular file')
        parent_hash = sha(args.validation_parent)
    initial_now = now or datetime.now(timezone.utc).isoformat()
    window = job_window(campaign_kind, SCHEDULE, initial_now, args.timeout_seconds,
                        frozen_parent_sha256=parent_hash)
    guard = guard or load_guard(root)
    guard.ROOT = root
    guard.BASE = Path(leases['heavy_lock']).parent
    inherited_write = guard.write
    wrapper = Path(__file__).resolve()
    policy_module = wrapper.with_name('streaming_8x4_acceptance.py')
    guard_path = root / 'scripts/streaming_tt_resources.py'
    metadata = dict(schema='pinwheel.streaming-8x4-resource-boundary.v1', schedule=SCHEDULE,
                    campaign_root=str(root), shared_lease=leases, campaign_kind=campaign_kind,
                    root_go_required=True, root_go_is_external_authority=True,
                    actual_wrapper_argv=list(getattr(sys, 'orig_argv', sys.argv)),
                    wrapper_path=str(wrapper), wrapper_sha256=sha(wrapper),
                    policy_path=str(policy_module), policy_sha256=sha(policy_module),
                    inherited_supervisor_path=str(guard_path), inherited_supervisor_sha256=sha(guard_path),
                    frozen_parent_sha256=parent_hash, initial_window=window,
                    acceptance_claim=False)

    def enriched_write(path, value):
        if value.get('schema') == 'pinwheel.streaming-tt-resource-job.v1':
            value['campaign_boundary'] = metadata
        inherited_write(path, value)

    def admission(kind, deadline, actual_now):
        # Preserve actual execution-time rechecking after parsing and before lock.
        require(kind == inherited_kind, 'Inherited resource kind changed')
        require(deadline == timestamp(SCHEDULE['heavy_cutoff']), 'Inherited deadline changed')
        fresh = job_window(campaign_kind, SCHEDULE,
                           now or actual_now.isoformat(), args.timeout_seconds,
                           frozen_parent_sha256=parent_hash)
        return fresh['timeout_seconds'] + fresh['cleanup_reserve_seconds']

    guard.write = enriched_write
    guard.admission_window = admission
    forwarded = ['resource', '--tag', args.tag, '--kind', inherited_kind,
                 '--timeout-seconds', str(args.timeout_seconds), '--rss-mib', str(args.rss_mib),
                 '--deadline', SCHEDULE['heavy_cutoff']]
    if args.container_name:
        forwarded += ['--container-name', args.container_name]
    inputs = list(args.input) + [wrapper, policy_module, guard_path]
    if args.validation_parent:
        inputs.append(args.validation_parent)
        if inherited_kind == 'cad-validation':
            forwarded += ['--validation-parent', str(args.validation_parent)]
    for path in inputs:
        forwarded += ['--input', str(path)]
    worker = args.argv[1:] if args.argv[:1] == ['--'] else args.argv
    require(worker, 'Missing worker command')
    forwarded += ['--'] + worker
    original_argv = sys.argv
    try:
        sys.argv = forwarded
        return guard.main()
    finally:
        sys.argv = original_argv


def main():
    return run(parser().parse_args())


if __name__ == '__main__':
    raise SystemExit(main())
