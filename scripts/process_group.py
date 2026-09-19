"""Capture local command output and stop its entire POSIX process group on timeout."""
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

_PROC = Path("/proc")


def _signal(group, kind):
    try:
        os.killpg(group, kind)
    except ProcessLookupError:
        pass
    except PermissionError:
        return False
    return True


def _proc_stat(entry):
    # comm (field 2) may contain spaces and parentheses. Fields after its
    # final ')' begin with state, ppid and pgrp; num_threads is field 20.
    head, separator, tail = (entry / "stat").read_text().rpartition(") ")
    fields = tail.split()
    if not separator or len(fields) < 18:
        raise ValueError("Malformed /proc stat record")
    threads = int(fields[17])
    if threads < 1:
        raise ValueError("Unknown thread count")
    return int(head.split(" ", 1)[0]), int(fields[2]), fields[0], threads


def _proc_visible():
    """Require the caller's PID view and an unrestricted procfs root mount."""
    pid, group, _, _ = _proc_stat(_PROC / "self")
    if (pid, group) != (os.getpid(), os.getpgrp()):
        return False
    mounts = []
    for line in (_PROC / "self/mountinfo").read_text().splitlines():
        before, separator, after = line.partition(" - ")
        fields, filesystem = before.split(), after.split()
        if len(fields) >= 6 and fields[4] == str(_PROC):
            mounts.append((fields, filesystem if separator else []))
    if len(mounts) != 1:
        return False
    fields, filesystem = mounts[0]
    if fields[3] != "/" or len(filesystem) != 3 or filesystem[0] != "proc":
        return False
    options = fields[5].split(",") + filesystem[2].split(",")
    return not any(option.startswith("hidepid=") and option not in {"hidepid=0", "hidepid=off"}
                   for option in options)


def _linux_group_alive(group):
    """Inspect Linux group members; an incomplete observation stays unknown."""
    try:
        if not _proc_visible():
            return None
        entries = list(_PROC.iterdir())
    except (OSError, ValueError):
        return None
    found, uncertain = False, False
    for entry in entries:
        if not entry.name.isdecimal():
            continue
        try:
            pid, member_group, state, threads = _proc_stat(entry)
            if pid != int(entry.name):
                raise ValueError("Mismatched /proc PID")
            if member_group != group:
                continue
            found = True
            if state in {"R", "S", "D", "T", "t", "W", "K", "P", "I"}:
                return True
            # A thread-group leader can exit while sibling threads still run.
            if state not in {"Z", "X", "x"} or threads != 1:
                uncertain = True
        except (FileNotFoundError, ProcessLookupError):
            # Processes may disappear between listing /proc and reading stat.
            continue
        except (OSError, ValueError):
            uncertain = True
    # Finding no members after a successful killpg probe may mean incomplete
    # visibility. Let a later probe confirm disappearance instead of guessing.
    return False if found and not uncertain else None


def _group_alive(group):
    """Return True for live members, False for terminated, None if unknown.

    A zombie has terminated execution but retains its PID until its parent
    reaps it. killpg(0) alone cannot distinguish it from a live process.
    """
    try:
        os.killpg(group, 0)
    except ProcessLookupError:
        return False
    except OSError:
        return None
    return _linux_group_alive(group) if sys.platform == "linux" else None


def _stop(process, grace):
    signaled = _signal(process.pid, signal.SIGTERM)
    try:
        process.communicate(timeout=grace)
    except subprocess.TimeoutExpired:
        pass
    # The direct child may have exited while a descendant with redirected
    # output is still alive. Reap/kill by group even after communicate returns.
    signaled = _signal(process.pid, signal.SIGKILL) and signaled
    try:
        stdout, stderr = process.communicate(timeout=grace)
    except subprocess.TimeoutExpired as error:
        # A descendant that created a different session could retain the pipes.
        # Bound cleanup as well, and report it as unconfirmed rather than hang.
        stdout = (error.output or b"").decode(process.encoding, errors="replace")
        stderr = (error.stderr or b"").decode(process.encoding, errors="replace")
        process.stdout.close()
        process.stderr.close()
        try:
            process.wait(timeout=grace)
        except subprocess.TimeoutExpired:
            return stdout, stderr, False
        return stdout, stderr, False
    deadline = time.monotonic() + grace
    while True:
        if _group_alive(process.pid) is False:
            return stdout, stderr, signaled
        if time.monotonic() >= deadline:
            return stdout, stderr, False
        time.sleep(0.01)


def run_captured(command, *, cwd, timeout, log_path, terminate_grace=2.0):
    """Return the usual text CompletedProcess; retain output before timeout errors.

    CAD subprocesses inherit a new process group. A timeout signals the group,
    escalates to SIGKILL, drains output, reaps the direct child and waits for
    the group to have no live members. Linux zombie descendants may await
    collection by their parent. Other hosts require group disappearance to
    confirm termination. A program that creates another session is outside
    this group; this helper does not adopt orphaned descendants.
    """
    process = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        stdout, stderr, stopped = _stop(process, terminate_grace)
        status = "stopped" if stopped else "termination unconfirmed"
        Path(log_path).write_text(stdout + stderr + f"\nTimeout after {timeout} seconds; process group {process.pid}: {status}.\n")
        error = subprocess.TimeoutExpired(command, timeout, output=stdout, stderr=stderr)
        error.process_group_stopped = stopped
        error.add_note(f"Process group {process.pid}: {status}; diagnostics retained in {log_path}")
        raise error from None
    except BaseException:
        _stop(process, terminate_grace)
        raise
    Path(log_path).write_text(stdout + stderr)
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
