"""Approved 48h clock only; the original engineering acceptance gates are reused."""
from datetime import timedelta
import hashlib
from pathlib import Path

import streaming_8x4_acceptance as ORIGINAL

require, timestamp, digest = ORIGINAL.require, ORIGINAL.timestamp, ORIGINAL.digest
shared_lease_paths = ORIGINAL.shared_lease_paths
GATES, MODEL_COVERAGE, CAPACITY = ORIGINAL.GATES, ORIGINAL.MODEL_COVERAGE, ORIGINAL.CAPACITY
summarize, pass_gate, model_qualification = ORIGINAL.summarize, ORIGINAL.pass_gate, ORIGINAL.model_qualification

CAMPAIGN = '8x4-20261025-01'
SCHEDULE = dict(start='2026-10-25T22:38:17Z', reference_decision='2026-10-26T02:38:17Z',
    model_cutoff='2026-10-26T22:38:17Z', candidate_freeze='2026-10-27T10:38:17Z',
    final_checks_cutoff='2026-10-27T20:38:17Z', heavy_cutoff='2026-10-27T21:38:17Z',
    hard_deadline='2026-10-27T22:38:17Z')
OFFSETS = dict(zip(SCHEDULE, (0, 4, 24, 36, 46, 47, 48)))
HISTORICAL = {
    'scripts/streaming_8x4_acceptance.py':'041956f82a38b99eece59e62f04d67f654862ebd4178b7805d2f596d3caeb9b1',
    'scripts/streaming_8x4_acceptance_resources.py':'0afc16f13edaee2bf0513b9dd5cfc09290e75ce13ac497c742ecbd8ff5cac1cf',
    'scripts/streaming_tt_resources.py':'7eaaa1bbefd6daf6fce52b9e97156bea80e6c984feb7698e3c9fc2c0d70a66a5',
    'scripts/streaming_8x4_closure24_policy.py':'a6825d9de9662d9e645a61d089c69f4358776f28372269620dab109a6450d3d4',
    'scripts/streaming_8x4_closure24_resources.py':'be106c9be03d75ff532eaa5cd40f01017070b1be94dd567ce4129c343ed9effc'}
KINDS = {
    'reference-probe':('rc_reference_probe','host','reference_decision'),
    'cad':('candidate_cad','cad','candidate_freeze'),
    'timing-eco-cad':('timing_eco_cad','cad-validation','candidate_freeze'),
    'cad-validation':('fixed_cad','cad-validation','heavy_cutoff'),
    'fixed-cad':('fixed_cad','cad-validation','heavy_cutoff'),
    'final-checks':('final_checks','cad-validation','final_checks_cutoff'),
    'qualified-timing':('qualified_timing','cad-validation','final_checks_cutoff'),
    'lean':('proof','lean','heavy_cutoff'),
    'public-wire':('public_wire','host','heavy_cutoff'),
    'solver':('rc_experiment','host','model_cutoff'),
    'solver-validation':('rc_validation','host','model_cutoff'),
    'host':('host_closeout','host','hard_deadline')}
FIXED = {'timing_eco_cad','fixed_cad','final_checks','qualified_timing','proof','public_wire','rc_validation'}
NUMERICAL = {'rc_reference_probe','rc_experiment','rc_validation'}
# This clock cannot qualify a model. Admission must be added through a separately
# reviewed adapter after the actual canonical closed_authority exists and passes.
UNAVAILABLE = {'timing-eco-cad','qualified-timing'}
QUALIFICATION_ENDPOINT = 'streaming_8x4_closure48_model_authority.closed_authority'


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def historical_sources(root):
    result={}
    for name,expected in HISTORICAL.items():
        path=Path(root)/name
        require(path.is_file() and not path.is_symlink() and sha(path)==expected,
            'Historical campaign producer changed: '+name)
        result[str(path.resolve())]=expected
    return result


def schedule_values(schedule):
    require(type(schedule) is dict and set(schedule)==set(SCHEDULE), 'Every approved48h boundary is required')
    values={key:timestamp(schedule[key]) for key in SCHEDULE}
    require(values=={key:timestamp(value) for key,value in SCHEDULE.items()}, 'Cannot alter approved48h clock')
    require(all(values[key]-values['start']==timedelta(hours=offset) for key,offset in OFFSETS.items()),
        'Approved48h offsets differ')
    require(values['hard_deadline']-values['heavy_cutoff']==timedelta(hours=1), 'Protected closeout hour changed')
    return values


def resource_limits(kind):
    require(kind in KINDS,'Unknown closure48 kind')
    family=KINDS[kind][0]
    return dict(container_cpus=1 if family in {'proof','public_wire'}|NUMERICAL else 4,
        container_memory_bytes=(4 if family in {'proof','public_wire'} else 6)*1024**3,
        maximum_host_rss_mib=4096, extra_swap_bytes=0, network='none',
        host_proof_threads=1 if family=='proof' else None,
        host_proof_thread_enforcement='exact reviewed worker driver; resource guard bounds aggregate RSS',
        maximum_job_seconds=14400)


def job_window(kind,schedule,now,timeout_seconds,*,frozen_parent_sha256=None):
    values=schedule_values(schedule)
    require(kind in KINDS,'Unknown closure48 resource job kind')
    family,_,cut=KINDS[kind]
    require(type(timeout_seconds) is int and 1<=timeout_seconds<=14400,'Unchanged four-hour per-job maximum')
    current=timestamp(now)
    require(current>=values['start'],'Campaign has not started')
    require((family in FIXED)==digest(frozen_parent_sha256), 'Fixed job requires exact frozen parent; experiment cannot claim one')
    if family not in FIXED:require(frozen_parent_sha256 is None,'New experiment cannot claim frozen parent')
    seconds=min(timeout_seconds,(values[cut]-current).total_seconds()-20)
    require(seconds>0,'Execution cutoff reached or cleanup reserve unavailable')
    return dict(kind=family,requested_timeout_seconds=timeout_seconds,timeout_seconds=seconds,
        execution_cutoff=values[cut].isoformat(),cleanup_reserve_seconds=20,root_go_required=True,
        acceptance_claim=False,candidate_count_or_model_qualification_verified=False)
