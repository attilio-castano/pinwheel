"""Compile generated artifact proof modules with retained bounded diagnostics."""
from __future__ import annotations

import os
from pathlib import Path
import time

import process_group

ROOT = Path(__file__).resolve().parents[1]


def compile_modules(run, directory, modules, *, timeout=300):
    for module in modules:
        lean_path = str(directory) + os.pathsep + str(ROOT / ".lake/build/lib/lean")
        argv = ["env", "LEAN_PATH=" + lean_path, "lake", "env", "lean", "-DwarningAsError=true",
                "-o", directory / f"{module}.olean", directory / f"{module}.lean"]
        log, started = directory / f"{module}.log", time.monotonic()
        record = {"argv": list(map(str, argv)), "label": directory.name + "-" + module,
                  "timeout_seconds": timeout}
        run.records.append(record)
        try:
            result = process_group.run_captured(record["argv"], cwd=ROOT, timeout=timeout, log_path=log)
        except BaseException as error:
            record.update(error=type(error).__name__, seconds=round(time.monotonic() - started, 3))
            raise
        record.update(exit_code=result.returncode, seconds=round(time.monotonic() - started, 3))
        if result.returncode:
            raise RuntimeError(f"{module} certificate failed: {log}\n{result.stdout[-3000:]}{result.stderr[-1000:]}")
        print(f"{directory.name}/{module}: checked", flush=True)
