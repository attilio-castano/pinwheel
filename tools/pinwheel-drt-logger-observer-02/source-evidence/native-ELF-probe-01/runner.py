"""Owned, sequential Docker execution for an explicitly authorized campaign.

No work is launched on import. A job is not physical acceptance: callers must
apply their independent readback, DRC, connectivity and timing gates.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import threading
import time
from typing import Any, Callable, Mapping, Sequence
import uuid

MAX_JOB_SECONDS = 90 * 60


class DeadlineExceeded(RuntimeError):
    pass


@dataclass(frozen=True)
class JobSpec:
    output_dir: Path
    heavy_lock_path: Path
    image_id: str
    command: Sequence[str]
    campaign_id: str
    hard_end_epoch: float
    input_sha256: Mapping[str, str]
    native_seconds: float
    max_job_seconds: float = MAX_JOB_SECONDS
    closeout_reserve_seconds: float = 45
    minimum_native_seconds: float = 1
    cpus: int = 4
    memory: str = "6g"
    readonly_mounts: Sequence[tuple[Path, str]] = field(default_factory=tuple)
    environment: Mapping[str, str] = field(default_factory=dict)
    scope: str = "authorized physical campaign job; acceptance is a separate gate"


def _atomic_json(path: Path, value: Any) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def sha256_file(path: Path, remaining: Callable[[], float] | None = None) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while True:
            if remaining is not None and remaining() <= 0:
                raise DeadlineExceeded("Deadline during file recustody")
            chunk = stream.read(1024 * 1024)
            if not chunk:
                return digest.hexdigest()
            digest.update(chunk)


def cleanup_owned(owner: str, campaign_id: str, remaining: Callable[[], float], *,
                  process_run: Callable[..., Any] = subprocess.run) -> dict[str, Any]:
    """Only stop a container matching BOTH unique owner and campaign labels."""
    query = ["docker", "container", "ls", "--all", "--no-trunc",
             "--filter", "label=org.pinwheel.baseline_owner=" + owner,
             "--filter", "label=org.pinwheel.campaign=" + campaign_id,
             "--format", "{{.ID}}"]
    result: dict[str, Any] = {"status": "unconfirmed", "owner": owner,
                              "campaign_id": campaign_id}

    def call(argv: list[str], cap: float) -> Any:
        seconds = min(cap, remaining())
        if seconds <= 0:
            raise DeadlineExceeded("No time remains for owned cleanup")
        return process_run(argv, capture_output=True, text=True, timeout=seconds)

    def identities() -> list[str]:
        response = call(query, 3)
        if response.returncode:
            raise RuntimeError("Owned-container query failed: " + response.stderr)
        ids = response.stdout.splitlines()
        if len(ids) > 1 or any(not re.fullmatch(r"[0-9a-f]{64}", value) for value in ids):
            raise RuntimeError("Unexpected owned-container identities")
        return ids

    try:
        ids = identities()
        result["observed_owned_container_ids"] = ids
        if ids:
            stopped = call(["docker", "stop", "--time", "2", ids[0]], 6)
            result["stop_exit_code"] = stopped.returncode
            ids = identities()
            if ids:
                killed = call(["docker", "kill", ids[0]], 3)
                result["kill_exit_code"] = killed.returncode
                ids = identities()
        if ids:
            result["remaining_ids"] = ids
        else:
            result["status"] = "absent"
    except BaseException as error:
        result["error"] = repr(error)
    return result


def run_owned_job(spec: JobSpec, *, process_run: Callable[..., Any] = subprocess.run,
                  monotonic: Callable[[], float] = time.monotonic,
                  wall_time: Callable[[], float] = time.time,
                  owner_factory: Callable[[], Any] = uuid.uuid4) -> dict[str, Any]:
    """Run at most one heavy job under a shared O_EXCL lock.

    The output folder may contain freshly staged inputs, but an existing receipt
    is never overwritten. Limits include cleanup and host recustody, not just
    the native subprocess. `process_run` injection supports no-CAD tests.
    """
    assert re.fullmatch(r"sha256:[0-9a-f]{64}", spec.image_id), "Pin the exact image ID"
    assert spec.campaign_id and spec.command and all(isinstance(v, str) for v in spec.command)
    assert 0 < spec.max_job_seconds <= MAX_JOB_SECONDS and spec.native_seconds > 0
    assert 15 <= spec.closeout_reserve_seconds < spec.max_job_seconds
    assert 0 < spec.minimum_native_seconds <= spec.native_seconds
    assert 1 <= spec.cpus <= 4 and re.fullmatch(r"[1-6]g", spec.memory)
    assert spec.input_sha256, "Frozen source hashes are required"
    out = Path(spec.output_dir)
    out.mkdir(parents=True, exist_ok=True)
    receipt_path = out / "report.json"
    if receipt_path.exists():
        raise FileExistsError("Immutable prior job receipt: " + str(receipt_path))
    owner = str(owner_factory())
    start_wall, start_mono = wall_time(), monotonic()
    job_seconds = min(spec.max_job_seconds, spec.hard_end_epoch - start_wall)
    if job_seconds <= spec.closeout_reserve_seconds:
        raise DeadlineExceeded("Campaign deadline leaves no native+closeout window")
    end_mono = start_mono + job_seconds

    def remaining() -> float:
        return min(end_mono - monotonic(), spec.hard_end_epoch - wall_time())

    lock = Path(spec.heavy_lock_path)
    lock.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    with os.fdopen(descriptor, "w") as stream:
        json.dump({"owner": owner, "pid": os.getpid(), "campaign_id": spec.campaign_id}, stream)
    receipt: dict[str, Any] = {
        "schema": "pinwheel-owned-campaign-job-v1", "status": "preparing",
        "owner": owner, "campaign_id": spec.campaign_id, "scope": spec.scope,
        "image_id": spec.image_id, "hard_end_epoch": spec.hard_end_epoch,
        "started_epoch": start_wall, "input_sha256": dict(spec.input_sha256),
        "bounds": {"max_all_in_job_seconds": spec.max_job_seconds,
                   "closeout_reserve_seconds": spec.closeout_reserve_seconds,
                   "requested_native_seconds": spec.native_seconds, "cpus": spec.cpus,
                   "memory": spec.memory, "network": "none"},
        "physical_acceptance_claim": False, "launched": False,
    }
    previous: dict[int, Any] = {}
    if threading.current_thread() is threading.main_thread():
        def interrupt(signum: int, _frame: Any) -> None:
            raise KeyboardInterrupt("Signal " + str(signum))
        for signum in (signal.SIGTERM, signal.SIGINT):
            previous[signum] = signal.signal(signum, interrupt)
    try:
        for path, expected in spec.input_sha256.items():
            if sha256_file(Path(path), remaining) != expected:
                raise RuntimeError("Frozen input mismatch: " + path)
        timeout = min(spec.native_seconds, math.floor(remaining() - spec.closeout_reserve_seconds))
        if timeout < spec.minimum_native_seconds:
            raise DeadlineExceeded("Native launch window below required minimum")
        argv = ["docker", "run", "--rm", "--pull", "never", "--network", "none",
                "--cpus", str(spec.cpus), "--memory", spec.memory,
                "--label", "org.pinwheel.baseline_owner=" + owner,
                "--label", "org.pinwheel.campaign=" + spec.campaign_id,
                "--env", "PYTHONDONTWRITEBYTECODE=1",
                "--mount", "type=bind,source=" + str(out.resolve()) + ",target=/work/diagnostic",
                "--workdir", "/work/diagnostic"]
        for source, target in spec.readonly_mounts:
            argv.extend(["--mount", "type=bind,source=" + str(Path(source).resolve())
                         + ",target=" + target + ",readonly"])
        for name, value in spec.environment.items():
            assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name)
            argv.extend(["--env", name + "=" + value])
        argv.extend([spec.image_id, *spec.command])
        receipt.update(status="running", launched=True, command=argv,
                       native_stop_epoch=min(spec.hard_end_epoch, wall_time() + timeout))
        receipt["bounds"]["actual_native_timeout_seconds"] = timeout
        _atomic_json(receipt_path, receipt)
        with (out / "execution.log").open("w") as log:
            completed = process_run(argv, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
        receipt.update(status="passed" if completed.returncode == 0 else "failed",
                       exit_code=completed.returncode)
    except subprocess.TimeoutExpired as error:
        receipt.update(status="timed_out", exit_code=124, error=str(error))
    except KeyboardInterrupt as error:
        receipt.update(status="interrupted", exit_code=130, error=str(error))
    except BaseException as error:
        receipt.update(status="failed", exit_code=1, error=repr(error))
    finally:
        # The root watchdog also queries the campaign label if this process dies.
        for signum in previous:
            signal.signal(signum, signal.SIG_IGN)
        try:
            receipt["container_termination"] = cleanup_owned(owner, spec.campaign_id, remaining,
                                                             process_run=process_run) if receipt["launched"] else {"status": "not_launched"}
            try:
                custody = {p: sha256_file(Path(p), remaining) == h for p, h in spec.input_sha256.items()}
                receipt["input_recustody"] = custody
                receipt["inputs_unchanged"] = all(custody.values())
                artifacts = {}
                for path in sorted(out.rglob("*")):
                    if path.is_file() and path.name not in ("report.json", "report.json.tmp"):
                        artifacts[str(path.relative_to(out))] = sha256_file(path, remaining)
                receipt["artifact_sha256"] = artifacts
                receipt["retained_checkpoint_paths"] = [p for p in artifacts if p.endswith((".odb", ".def"))]
            except BaseException as error:
                receipt.update(inputs_unchanged=False, closeout_error=repr(error))
            if receipt["container_termination"]["status"] not in ("absent", "not_launched") or not receipt.get("inputs_unchanged"):
                receipt["producer_status_before_invalidation"] = receipt["status"]
                receipt["status"] = "invalidated"
            receipt["elapsed_all_in_seconds"] = monotonic() - start_mono
            receipt["finished_epoch"] = wall_time()
            receipt["within_absolute_and_job_deadlines"] = remaining() >= 0
            if not receipt["within_absolute_and_job_deadlines"]:
                receipt["producer_status_before_deadline_failure"] = receipt["status"]
                receipt["status"] = "deadline_exceeded"
            receipt["controller_must_stop"] = receipt["status"] in ("interrupted", "invalidated", "deadline_exceeded")
            _atomic_json(receipt_path, receipt)
        finally:
            for signum, handler in previous.items():
                signal.signal(signum, handler)
            # Never unlink another owner's replacement lock.
            try:
                if (receipt.get("container_termination", {}).get("status") in ("absent", "not_launched")
                        and json.loads(lock.read_text()).get("owner") == owner):
                    lock.unlink()
            except (OSError, ValueError):
                pass
    return receipt
