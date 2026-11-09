"""Verify a physically relocated ECO package under a cooperative Python read guard."""

import argparse
from hashlib import file_digest
import json
import os
from pathlib import Path
import runpy
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import time


VERIFIER = "scripts/streaming_8x4_hold_cap_rehearsal.py"
STALE_GDS = "dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82"
CURRENT_GDS = "d4cd48f0919ac47ec4b2ceb061bc5dc6a217ce730b02b819a6b7e09d9e73c832"
CURRENT_ODB = "dc654986c54512095c243407ea481ad3675a0269870ee4715dcbd1bd632c6a73"


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    with path.open("rb") as stream:
        return file_digest(stream, "sha256").hexdigest()


def write(path, value, mode="x"):
    with path.open(mode, encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write("\n")


def guarded(argv):
    archive, bundle, expected, live, history, main_repo = argv
    archive, bundle = Path(archive), Path(bundle)
    blocked = tuple(Path(path).resolve() for path in (live, history, main_repo))
    require(archive.is_dir() and bundle.is_dir() and not (archive / ".git").exists()
            and not (archive / "build").exists() and Path.cwd() == archive,
            "Verifier is not running in a clean Git archive")
    require(all(not path.is_relative_to(root) for root in blocked for path in (archive, bundle)),
            "Archive or relocated bundle remains within the blocked trees")
    attempts = []
    path_events = {"open", "os.listdir", "os.scandir", "os.chdir"}
    bypass = {"subprocess.Popen", "os.system", "os.posix_spawn", "os.exec", "os.fork", "os.forkpty",
              "socket.connect", "socket.bind", "ctypes.dlopen"}

    def audit(event, args):
        if event in bypass:
            attempts.append(event)
            raise PermissionError(f"Verifier cannot bypass the in-process read guard: {event}")
        if event not in path_events or not args or not isinstance(args[0], (str, bytes, os.PathLike)):
            return
        path = Path(os.path.abspath(os.fsdecode(args[0])))
        if any(path.is_relative_to(root) or path.resolve().is_relative_to(root) for root in blocked):
            attempts.append(f"{event} {path}")
            raise PermissionError(f"Verifier read blocked by clean-archive guard: {path}")

    sys.addaudithook(audit)
    for root in blocked:
        for operation in ((lambda: (root / "AGENTS.md").read_bytes()), (lambda: list(root.iterdir()))):
            try:
                operation()
            except PermissionError as error:
                require(str(error).startswith("Verifier read blocked"), "Self-test failed for an unrelated reason")
            else:
                raise ValueError(f"Audit guard self-test unexpectedly read {root}")
    self_tests = len(attempts)
    attempts.clear()
    sys.path.insert(0, str(archive / "scripts"))
    script = archive / VERIFIER
    sys.argv = [str(script), "verify", str(bundle), "--manifest-sha256", expected]
    try:
        runpy.run_path(str(script), run_name="__main__")
    except SystemExit as error:
        code = error.code
    else:
        code = 0
    finally:
        print(json.dumps(dict(audit_guard_self_tests_blocked=self_tests,
                              audit_guard_runtime_denials=attempts), sort_keys=True), file=sys.stderr)
    return 74 if attempts else code


def run_verifier(archive, bundle, expected, workspace, history, main_repo):
    launcher = archive.parent / "rehearsal-verify-clean.py"
    argv = [sys.executable, "-I", "-B", str(launcher), "guarded", str(archive), str(bundle), expected,
            str(workspace), str(history), str(main_repo)]
    done = subprocess.run(argv, cwd=archive, capture_output=True, text=True, timeout=240)
    lines = done.stderr.splitlines()
    require(lines, "Clean-archive child produced no audit closeout")
    guard = json.loads(lines[-1])
    require(guard == {"audit_guard_runtime_denials": [], "audit_guard_self_tests_blocked": 6},
            "Read guard failed its self-test or verifier attempted a denied access")
    return dict(exit_code=done.returncode, stdout=done.stdout.strip(), stderr="\n".join(lines[:-1]), **guard)


def run(workspace, history, main_repo, source_commit, bundle, bundle_archive, expected, stale_path, receipt):
    require(not receipt.exists() and receipt.parent == bundle.parent and bundle.is_relative_to(workspace),
            "Use a fresh receipt adjacent to the real bundle")
    manifest_path = bundle / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    require(sha(manifest_path) == expected and manifest["source_commit"] == source_commit
            and manifest["target_odb_sha256"] == CURRENT_ODB and manifest["gds_sha256"] == CURRENT_GDS,
            "Wrong manifest, source commit or layout")
    payload = Path(manifest["payload"]["gds"]["path"])
    require(not payload.is_absolute() and ".." not in payload.parts and sha(bundle / payload) == CURRENT_GDS
            and sha(stale_path) == STALE_GDS, "Wrong original or stale GDS")
    archive_digest = sha(bundle_archive)
    original_files = sorted(path for path in bundle.rglob("*") if path.is_file())
    require(original_files and all(not path.is_symlink() and stat.S_ISREG(path.stat().st_mode)
                                   and path.stat().st_nlink == 1 for path in original_files), "Unexpected bundle alias")
    require(not any(path.is_symlink() for path in bundle.rglob("*")), "Unexpected original bundle symlink")
    initial_stats = {path: (path.stat().st_ino, path.stat().st_size, path.stat().st_mtime_ns) for path in original_files}
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="pinwheel-eco-clean-", dir="/private/tmp") as temp:
        scratch = Path(temp)
        archive = scratch / "source"
        archive.mkdir()
        tar_path = scratch / "source.tar"
        with tar_path.open("xb") as stream:
            subprocess.run(["git", "archive", "--format=tar", source_commit], cwd=workspace, stdout=stream,
                           stderr=subprocess.PIPE, timeout=120, check=True)
        archive_sha = sha(tar_path)
        with tarfile.open(tar_path) as tar:
            require(tar.pax_headers.get("comment") == source_commit, "Git archive commit header differs")
            archive_members = len(tar.getmembers())
            tar.extractall(archive, filter="data")
        shutil.copyfile(Path(__file__).resolve(), scratch / "rehearsal-verify-clean.py")
        copy = scratch / "relocated" / "rehearsal-package"
        copy.parent.mkdir(parents=True)
        with tarfile.open(bundle_archive) as packaged:
            members = packaged.getmembers()
            names = [item.name for item in members]
            require(len(names) == len(set(names)) and all(
                not Path(name).is_absolute() and ".." not in Path(name).parts
                and Path(name).parts[0] == "bundle" for name in names)
                and all(item.isfile() or item.isdir() for item in members), "Unsafe bundle archive members")
            packaged.extractall(copy.parent, filter="data")
        (copy.parent / "bundle").rename(copy)
        require(not copy.is_relative_to(workspace) and len(original_files) == sum(path.is_file() for path in copy.rglob("*"))
                and all(not os.path.samestat(path.stat(), (copy / path.relative_to(bundle)).stat())
                        for path in original_files), "Relocated package is missing files or shares live inodes")
        positive = run_verifier(archive, copy, expected, workspace, history, main_repo)
        require(positive["exit_code"] == 0 and not positive["stderr"], "Relocated verification failed: " + positive["stderr"])
        verified = json.loads(positive.pop("stdout"))
        require(verified["verified"] is True and verified["manifest_sha256"] == expected
                and verified["source_commit"] == source_commit and verified["target_odb_sha256"] == CURRENT_ODB
                and verified["gds_sha256"] == CURRENT_GDS and verified["fabrication_decision"] == "no-go",
                "Relocated verifier returned different identities")
        positive["verification"] = verified

        original_manifest = (copy / "manifest.json").read_bytes()
        shutil.copyfile(stale_path, copy / payload)
        manifest["payload"]["gds"].update(bytes=(copy / payload).stat().st_size, sha256=STALE_GDS)
        forged_manifest = copy / "manifest.json"
        write(forged_manifest, manifest, "w")
        forged_sha = sha(forged_manifest)
        require(forged_sha != expected and sha(copy / payload) == manifest["payload"]["gds"]["sha256"]
                and (copy / payload).stat().st_size == manifest["payload"]["gds"]["bytes"],
                "Negative payload and its re-sealed manifest are inconsistent")
        negative = run_verifier(archive, copy, forged_sha, workspace, history, main_repo)
        require(negative["exit_code"] == 2 and not negative["stdout"]
                and any(word in negative["stderr"].lower() for word in ("manifest", "payload", "gds")),
                "Re-sealed stale GDS was not rejected at the expected semantic comparison")
        negative.update(resealed_manifest_sha256=forged_sha, stale_gds_sha256=STALE_GDS, replaced_payload=str(payload))

        shutil.copyfile(bundle / payload, copy / payload)
        (copy / "manifest.json").write_bytes(original_manifest)
        verifier = archive / VERIFIER
        verifier.write_bytes(verifier.read_bytes() + b"\n# Disposable source-integrity control.\n")
        changed_source = run_verifier(archive, copy, expected, workspace, history, main_repo)
        require(changed_source["exit_code"] == 2 and not changed_source["stdout"]
                and any(word in changed_source["stderr"].lower() for word in ("source", "verifier", "tracked")),
                "Changed archived verifier source was not rejected")
    require(initial_stats == {path: (path.stat().st_ino, path.stat().st_size, path.stat().st_mtime_ns)
                              for path in original_files}
            and sha(manifest_path) == expected and sha(bundle / payload) == CURRENT_GDS and sha(stale_path) == STALE_GDS
            and sha(bundle_archive) == archive_digest,
            "Original bundle or historical stale GDS changed")
    write(receipt, dict(schema="pinwheel.hold-cap-clean-archive-check.v1", passed=True, source_commit=source_commit,
                        archive_sha256=archive_sha, archive_members=archive_members,
                        verifier_sha256=manifest["source_sha256"][VERIFIER], manifest_sha256=expected,
                        bundle=str(bundle), original_bundle_unchanged=True, original_historical_gds_unchanged=True,
                        relocated_file_count=len(original_files), physically_separate_inodes=True,
                        bundle_archive_sha256=archive_digest, archive_extracted=True,
                        positive=positive, negative=negative, changed_source_negative=changed_source, elapsed_seconds=time.monotonic() - started))


def main(argv):
    if argv and argv[0] == "guarded":
        return guarded(argv[1:])
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("workspace", "history", "main-repo", "bundle", "bundle-archive", "stale-gds", "receipt"):
        parser.add_argument("--" + name, required=True, type=lambda value: Path(value).resolve())
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    args = parser.parse_args(argv)
    run(args.workspace, args.history, args.main_repo, args.source_commit, args.bundle, args.bundle_archive, args.manifest_sha256,
        args.stale_gds, args.receipt)
    print(args.receipt)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
