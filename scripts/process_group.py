"""Capture local command output and stop its entire POSIX process group on timeout."""
import os
from pathlib import Path
import signal
import subprocess
import time


def _signal(group, kind):
    try:
        os.killpg(group, kind)
    except ProcessLookupError:
        pass
    except PermissionError:
        return False
    return True


def _exists(group):
    try:
        os.killpg(group, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # Permission failure cannot establish that the group has disappeared.
        return True


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
    while _exists(process.pid) and time.monotonic() < deadline:
        time.sleep(0.01)
    return stdout, stderr, signaled and not _exists(process.pid)


def run_captured(command, *, cwd, timeout, log_path, terminate_grace=2.0):
    """Return the usual text CompletedProcess; retain output before timeout errors.

    CAD subprocesses inherit a new process group. A timeout signals the group,
    escalates to SIGKILL, drains output, and waits for group disappearance. A
    program that deliberately creates another session is outside this group.
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
