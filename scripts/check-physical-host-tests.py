#!/usr/bin/env python3
"""Run one portable physical-tool suite without CAD or ignored build inputs.

The audit hook is a regression guard for these cooperative tests, not a security
sandbox for hostile Python code. Run each suite in its own interpreter: observer
versions intentionally use colliding module names such as ``analyze``.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest

if sys.platform == "darwin":
    import fcntl


ROOT = Path(__file__).resolve().parents[1]
SUITES = {
    "campaign": ("tools/pinwheel-physical-campaign/tests", 52),
    "drt-logger-observer": ("tools/pinwheel-drt-logger-observer/tests", 16),
    "drt-logger-observer-02": ("tools/pinwheel-drt-logger-observer-02/tests", 21),
    "drt-logger-observer-03": ("tools/pinwheel-drt-logger-observer-03/tests", 26),
}
PROCESS_EVENTS = {
    "subprocess.Popen", "os.system", "os.posix_spawn", "os.posix_spawnp",
    "os.spawn", "os.exec", "os.fork", "os.forkpty",
}
PATH_ARGUMENTS = {
    "open": (0,), "os.listdir": (0,), "os.scandir": (0,),
    "os.mkdir": (0,), "os.remove": (0,), "os.rmdir": (0,),
    "os.chmod": (0,), "os.chown": (0,), "os.truncate": (0,),
    "os.utime": (0,), "os.rename": (0, 1), "os.link": (0, 1),
    "os.symlink": (1,),
}
DIR_FD_ARGUMENTS = {
    "os.mkdir": {0: 2}, "os.remove": {0: 1}, "os.rmdir": {0: 1},
    "os.chmod": {0: 2}, "os.chown": {0: 3}, "os.utime": {0: 3},
    "os.rename": {0: 2, 1: 3}, "os.link": {0: 2, 1: 3},
    "os.symlink": {1: 2},
}


class HostGateViolation(PermissionError):
    """An attempted operation outside the portable host-test contract."""


class HostAuditGuard:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.build = self.root / "build"
        self.violations: list[dict[str, str]] = []
        self.active = True
        self.open_context = threading.local()
        self.original_open = os.open

    def deny(self, event: str, reason: str, path: str = "") -> None:
        self.violations.append({"event": event, "reason": reason, "path": path})
        raise HostGateViolation(f"Host-only gate blocked {event}: {reason}: {path}")

    def descriptor_path(self, event: str, descriptor: int) -> Path:
        try:
            if sys.platform == "linux":
                return Path(os.readlink(f"/proc/self/fd/{descriptor}"))
            if sys.platform == "darwin":
                raw = fcntl.fcntl(descriptor, fcntl.F_GETPATH, b"\0" * 1024)
                return Path(os.fsdecode(raw.split(b"\0", 1)[0]))
        except OSError as error:
            self.deny(event, "directory descriptor cannot be resolved", str(error))
        self.deny(event, "directory descriptor attribution unsupported on this host")

    def guarded_open(self, path, flags, mode=0o777, *, dir_fd=None):
        # CPython's `open` audit event omits dir_fd. Attribute relative opens
        # using their real directory descriptor, rather than the process cwd.
        previous = getattr(self.open_context, "path", None)
        if self.active and dir_fd is not None and not os.path.isabs(path):
            self.open_context.path = self.descriptor_path("open", dir_fd) / os.fsdecode(path)
        try:
            return self.original_open(path, flags, mode, dir_fd=dir_fd)
        finally:
            self.open_context.path = previous

    def install(self) -> None:
        os.open = self.guarded_open
        if self.original_open in os.supports_dir_fd:
            os.supports_dir_fd.add(os.open)
        sys.addaudithook(self)

    def check_path(self, event: str, value: object, dir_fd=None) -> None:
        if isinstance(value, int) and event in {"os.listdir", "os.scandir"}:
            value = self.descriptor_path(event, value)
        if not isinstance(value, (str, bytes, os.PathLike)):
            return  # Existing descriptors are used by tempfile and Python I/O.
        if isinstance(dir_fd, int) and dir_fd >= 0 and not os.path.isabs(value):
            value = self.descriptor_path(event, dir_fd) / os.fsdecode(value)
        lexical = Path(os.path.abspath(os.fsdecode(value)))
        resolved = Path(os.path.realpath(lexical))
        for path in {lexical, resolved}:
            if path == self.build or path.is_relative_to(self.build):
                self.deny(event, "current repository build tree is forbidden", str(path))
            parts = path.parts
            captured_worktree = any(
                parts[i:i + 2] == (".codex", "worktrees") and len(parts) > i + 3
                for i in range(len(parts) - 1)
            )
            if captured_worktree and not path.is_relative_to(self.root):
                self.deny(event, "another captured worktree is forbidden", str(path))

    def __call__(self, event: str, args: tuple) -> None:
        if not self.active:
            return
        if event in PROCESS_EVENTS:
            self.deny(event, "child processes and shell/CAD execution are forbidden")
        if event == "open" and getattr(self.open_context, "path", None) is not None:
            self.check_path(event, self.open_context.path)
            return
        for position in PATH_ARGUMENTS.get(event, ()):
            if len(args) > position:
                fd_position = DIR_FD_ARGUMENTS.get(event, {}).get(position)
                descriptor = args[fd_position] if fd_position is not None and len(args) > fd_position else None
                self.check_path(event, args[position], descriptor)


def build_exists(root: Path) -> bool:
    return os.path.lexists(root / "build")


def self_test_guards() -> dict:
    """Exercise real audit events; process attempts must fail before launch."""
    with tempfile.TemporaryDirectory(prefix="pinwheel-host-guard-") as temporary:
        base = Path(temporary)
        allowed = base / "repo/build/input.txt"
        allowed.parent.mkdir(parents=True)
        allowed.write_text("synthetic fixture")
        retired = base / ".codex/worktrees/retired/pinwheel/input.txt"
        retired.parent.mkdir(parents=True)
        retired.write_text("must remain unread")
        alias = base / "real-build-alias"
        alias.symlink_to(ROOT / "build", target_is_directory=True)
        guard = HostAuditGuard(ROOT)
        guard.install()

        def blocked(operation):
            count = len(guard.violations)
            try:
                operation()
            except HostGateViolation:
                pass
            else:
                raise AssertionError("Forbidden operation was not blocked")
            assert len(guard.violations) == count + 1

        try:
            assert allowed.read_text() == "synthetic fixture"
            assert Path(__file__).read_text()
            blocked(lambda: (ROOT / "build/forbidden-input.fixture").read_bytes())
            working_directory = Path.cwd()
            os.chdir(ROOT)
            try:
                blocked(lambda: Path("build/forbidden-input.fixture").read_bytes())
            finally:
                os.chdir(working_directory)
            blocked(lambda: (alias / "forbidden-input.fixture").read_bytes())
            blocked(lambda: list((ROOT / "build").iterdir()))
            blocked(retired.read_bytes)
            temporary_fd = os.open(allowed.parent.parent, os.O_RDONLY)
            repository_fd = os.open(ROOT, os.O_RDONLY)
            try:
                with os.fdopen(os.open("build/input.txt", os.O_RDONLY, dir_fd=temporary_fd)) as stream:
                    assert stream.read() == "synthetic fixture"
                blocked(lambda: os.open("build", os.O_RDONLY, dir_fd=repository_fd))
            finally:
                os.close(temporary_fd)
                os.close(repository_fd)
            blocked(lambda: subprocess.run([sys.executable, "-c", "raise SystemExit(99)"]))
            blocked(lambda: os.system("exit 99"))
            if hasattr(os, "posix_spawn"):
                blocked(lambda: os.posix_spawn(
                    sys.executable, [sys.executable, "-c", "raise SystemExit(99)"], dict(os.environ)))
            assert any(v["event"] == "subprocess.Popen" for v in guard.violations)
            return {"status": "guard_self_tests_passed", "blocked_attempts": len(guard.violations),
                    "temporary_repo_build_fixture_allowed": True,
                    "real_build_and_symlink_alias_blocked": True,
                    "directory_descriptor_attribution_verified": True,
                    "captured_worktree_input_blocked": True,
                    "child_processes_launched": 0}
        finally:
            # Audit hooks cannot be removed; only this self-test hook is disarmed
            # for cleanup of its deliberately forbidden synthetic old-worktree tree.
            guard.active = False
            os.supports_dir_fd.discard(os.open)
            os.open = guard.original_open


def run_suite(name: str, require_fresh: bool) -> tuple[dict, bool]:
    if require_fresh and build_exists(ROOT):
        raise SystemExit("Fresh-checkout gate requires the repository build/ tree to be absent")
    relative, minimum = SUITES[name]
    tests = ROOT / relative
    os.chdir(ROOT)
    sys.dont_write_bytecode = True
    guard = HostAuditGuard(ROOT)
    guard.install()
    suite = unittest.TestLoader().discover(str(tests), pattern="test_*.py", top_level_dir=str(tests))
    discovered = suite.countTestCases()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    fresh_after = not build_exists(ROOT)
    passed = (result.wasSuccessful() and result.testsRun == discovered and discovered >= minimum and not result.skipped
              and not guard.violations and (not require_fresh or fresh_after))
    report = {
        "schema": "pinwheel-portable-physical-host-tests-v1",
        "suite": name, "status": "passed" if passed else "failed",
        "tests_run": result.testsRun, "tests_discovered": discovered, "minimum_tests": minimum,
        "skipped": len(result.skipped), "errors": len(result.errors),
        "failures": len(result.failures), "guard_violations": guard.violations,
        "fresh_checkout_required": require_fresh,
        "repository_build_absent_after": fresh_after,
        "child_processes_and_CAD_allowed": False,
        "physical_acceptance_claim": False,
    }
    return report, passed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("--suite", choices=SUITES)
    choice.add_argument("--self-test-guards", action="store_true")
    parser.add_argument("--require-fresh-checkout", action="store_true")
    args = parser.parse_args()
    if args.self_test_guards:
        print(json.dumps(self_test_guards(), indent=2, sort_keys=True))
    else:
        report, passed = run_suite(args.suite, args.require_fresh_checkout)
        print(json.dumps(report, indent=2, sort_keys=True))
        raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
