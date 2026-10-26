"""Explicit approved 24h clock; original acceptance mathematics is unchanged."""
from datetime import timedelta
import hashlib
from pathlib import Path

import streaming_8x4_acceptance as ORIGINAL

require, timestamp, digest = ORIGINAL.require, ORIGINAL.timestamp, ORIGINAL.digest
shared_lease_paths = ORIGINAL.shared_lease_paths
GATES, MODEL_COVERAGE, CAPACITY = ORIGINAL.GATES, ORIGINAL.MODEL_COVERAGE, ORIGINAL.CAPACITY
summarize, pass_gate, model_qualification = ORIGINAL.summarize, ORIGINAL.pass_gate, ORIGINAL.model_qualification

CAMPAIGN = '8x4-20261024-01'
SCHEDULE = dict(start='2026-10-24T14:38:15Z', primary_route_cutoff='2026-10-24T20:38:15Z',
    model_cutoff='2026-10-25T02:38:15Z', candidate_freeze='2026-10-25T03:38:15Z',
    qualified_timing_cutoff='2026-10-25T04:38:15Z', heavy_cutoff='2026-10-25T13:38:15Z',
    hard_deadline='2026-10-25T14:38:15Z')
OFFSETS = dict(zip(SCHEDULE, (0, 6, 12, 13, 14, 23, 24)))
HISTORICAL = {
    'scripts/streaming_8x4_acceptance.py':'041956f82a38b99eece59e62f04d67f654862ebd4178b7805d2f596d3caeb9b1',
    'scripts/streaming_8x4_acceptance_resources.py':'0afc16f13edaee2bf0513b9dd5cfc09290e75ce13ac497c742ecbd8ff5cac1cf',
    'scripts/streaming_tt_resources.py':'7eaaa1bbefd6daf6fce52b9e97156bea80e6c984feb7698e3c9fc2c0d70a66a5'}
KINDS = {
    'cad':('candidate_cad','cad','primary_route_cutoff'),
    'timing-eco-cad':('timing_eco_cad','cad-validation','candidate_freeze'),
    'cad-validation':('fixed_cad','cad-validation','heavy_cutoff'),
    'fixed-cad':('fixed_cad','cad-validation','heavy_cutoff'),
    'qualified-timing':('qualified_timing','cad-validation','qualified_timing_cutoff'),
    'lean':('proof','lean','heavy_cutoff'),
    'public-wire':('public_wire','host','heavy_cutoff'),
    'solver':('rc_experiment','host','model_cutoff'),
    'solver-validation':('rc_validation','host','model_cutoff'),
    'host':('host_closeout','host','hard_deadline')}
FIXED = {'timing_eco_cad','fixed_cad','qualified_timing','proof','public_wire','rc_validation'}


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
    require(type(schedule) is dict and set(schedule)==set(SCHEDULE), 'Every approved24h boundary is required')
    values={key:timestamp(schedule[key]) for key in SCHEDULE}
    require(values=={key:timestamp(value) for key,value in SCHEDULE.items()}, 'Cannot alter approved24h clock')
    require(all(values[key]-values['start']==timedelta(hours=offset) for key,offset in OFFSETS.items()),
        'Approved24h offsets differ')
    require(values['hard_deadline']-values['heavy_cutoff']==timedelta(hours=1), 'Protected closeout hour changed')
    return values


def resource_limits(kind):
    require(kind in KINDS,'Unknown closure24 kind')
    family=KINDS[kind][0]
    return dict(container_cpus=1 if family in {'proof','public_wire','rc_experiment','rc_validation'} else 4,
        container_memory_bytes=(4 if family in {'proof','public_wire'} else 6)*1024**3,
        maximum_host_rss_mib=4096, extra_swap_bytes=0, network='none',
        host_proof_threads=1 if family=='proof' else None,
        host_proof_thread_enforcement='exact reviewed worker driver; resource guard bounds aggregate RSS',
        maximum_job_seconds=14400)


def job_window(kind,schedule,now,timeout_seconds,*,frozen_parent_sha256=None):
    values=schedule_values(schedule)
    require(kind in KINDS,'Unknown closure24 resource job kind')
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
