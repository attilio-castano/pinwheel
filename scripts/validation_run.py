"""Shared local validation commands; callers own their independent oracles."""
import hashlib
from pathlib import Path
import re
import time

import process_group


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def fresh_directory(root, tag):
    if not re.fullmatch(r"[A-Za-z0-9_-]+", tag):
        raise ValueError("Use letters, numbers, hyphens or underscores in tags")
    out = Path(root) / tag
    out.mkdir(parents=True, exist_ok=False)
    return out


class Commands:
    """Capture every command and require the expected reason for negative checks."""

    def __init__(self, root, out, records=None, default_timeout=900):
        self.root, self.out = Path(root), Path(out)
        self.records = [] if records is None else records
        self.default_timeout = default_timeout

    def __call__(self, command, label, timeout=None, reject=None):
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", label):
            raise ValueError("Invalid command label")
        log = self.out / (label + ".log")
        if log.exists():
            raise FileExistsError(f"Preserve the earlier command log: {log}")
        argv = list(map(str, command))
        started = time.monotonic()
        record = {"label": label, "argv": argv, "expected_failure": bool(reject)}
        self.records.append(record)
        try:
            result = process_group.run_captured(
                argv, cwd=self.root,
                timeout=self.default_timeout if timeout is None else timeout,
                log_path=log)
        except BaseException as error:
            record.update(error=type(error).__name__, seconds=round(time.monotonic()-started, 3))
            raise
        record.update(exit_code=result.returncode, seconds=round(time.monotonic()-started, 3))
        text = result.stdout + result.stderr
        if reject:
            if result.returncode == 0 or reject not in text:
                raise RuntimeError(f"{label}: expected rejection containing {reject!r}; see {log}")
        elif result.returncode:
            raise RuntimeError(f"{label}: {text[-3000:]}; see {log}")
        print(label + (": expected rejection" if reject else ": passed"), flush=True)
        return text
