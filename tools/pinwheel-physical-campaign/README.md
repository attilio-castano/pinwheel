# Pinwheel physical campaign host helpers

These modules perform host parsing and explicitly requested execution. Importing
them does not run CAD. Existing receipts are never rewritten. Physical scope,
clock/TAPER preservation, complete terminal connectivity, STA, GDS and official
precheck require separate gates.

## DRC evidence

Add this directory to `sys.path`, then:

```python
from drc import parse_native_log, compare_native_stages

evidence = parse_native_log(native_log_text, report_text,
                            category_limit=10000,
                            producer_status=producer_report["status"])
comparison = compare_native_stages(control_evidence, candidate_evidence,
                                   required_candidate_iteration=3)
```

The category limit must come from the actual pinned native source; omit it when
unknown. The parser still reconciles report/native counts without that limit.
Native tables have variable row counts: zero-valued rows may be absent. Each
table is paired with its adjacent native counter and its entire sum is checked.
The latest route must have completed, and its latest table must match; the parser
never falls back to an older valid table after a corrupt or incomplete stage.
Progress observations and capped report records remain separate ledgers.

CLI (stdout JSON only):

```sh
python3 -B tools/pinwheel-physical-campaign/drc.py NATIVE_LOG --report REPORT --category-limit 10000
```

## Owned execution

```python
from runner import JobSpec, run_owned_job

receipt = run_owned_job(JobSpec(
    output_dir=staged_new_job_directory,
    heavy_lock_path=campaign_directory / "heavy-job.lock",
    image_id=pinned_image_id,
    command=["python3", "-B", "/work/diagnostic/coordinator.py"],
    campaign_id="tt-overnight-20261015-000717",
    hard_end_epoch=campaign_manifest["hard_end_epoch"],
    input_sha256=all_protected_reference_and_staged_input_hashes,
    native_seconds=3600,
    readonly_mounts=[(pdk_directory, "/work/pdk")],
    environment={"PYTHONPATH": "/work/diagnostic"},
))
```

The common heavy lock must be shared by every campaign job. `O_EXCL` acquisition
rejects overlap. Jobs are at most 5,400 seconds **including** cleanup and host
recustody. Native timeout is clipped to the absolute campaign deadline and job
deadline minus the closeout reserve (45 seconds by default). Source/output
hashing checks that remaining deadline between 1 MiB reads. Every job carries
the campaign label and a unique owner label. Cleanup queries both labels,
stops only the observed exact owned container, and confirms absence; failure
invalidates the receipt and retains the heavy lock. The independent campaign
watchdog should query only `org.pinwheel.campaign=tt-overnight-20261015-000717`.

Staged output directories are permitted, but an existing `report.json` is an
immutable prior job and causes rejection. The runner records actual retained
`.odb`/`.def` files, without claiming that incomplete output is a usable checkpoint.
`passed` means process exit zero with custody and cleanup, not physical acceptance.
Honor `controller_must_stop`, and independently stop on the campaign deadline.
No helper buys compute, pulls images, or enables container networking.

## Verification

```sh
python3 -B -m unittest discover -s tools/pinwheel-physical-campaign/tests -v
```

Tests read retained four-row/three-row/partial native logs and capped marker
reports, and use fake process executors for all Docker execution, timeout,
interruption, cleanup, lock and custody cases. They do not launch CAD.
