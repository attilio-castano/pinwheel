"""Capture and verify LibreLane checkpoint contents, including nested views."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil

CORE = Path(__file__).resolve().parents[1] / "build/physical/core"
PREFIX = "/work/core/"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def artifact_path(name, core):
    if not isinstance(name, str) or not name.startswith(PREFIX):
        raise ValueError(f"Unsupported checkpoint artifact path: {name!r}")
    relative = Path(name.removeprefix(PREFIX))
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError(f"Invalid checkpoint artifact path: {name}")
    path = core / relative
    if not path.resolve().is_relative_to(core.resolve()) or not path.is_file():
        raise ValueError(f"Missing or out-of-root checkpoint artifact: {name}")
    return path


def map_views(state, transform):
    def visit(value):
        if value is None:
            return None
        if isinstance(value, dict):
            return {k: visit(v) for k, v in value.items()}
        if isinstance(value, list):
            return [visit(v) for v in value]
        if isinstance(value, str):
            return transform(value)
        raise ValueError(f"Unsupported checkpoint view: {value!r}")
    if not isinstance(state, dict):
        raise ValueError("Checkpoint state must be an object")
    return {k: v if k == "metrics" else visit(v) for k, v in state.items()}


def inspect(state, core=CORE):
    state = state.resolve()
    relative = state.relative_to(core.resolve())
    raw = state.read_bytes()
    files = {}

    def record(name):
        files[name] = sha(artifact_path(name, core))
        return name

    map_views(json.loads(raw), record)
    return {
        "state": PREFIX + relative.as_posix(),
        "state_sha256": hashlib.sha256(raw).hexdigest(),
        "artifacts_sha256": dict(sorted(files.items())),
    }


def capture(state, output, core=CORE):
    identity = inspect(state, core)
    manifest = {
        "schema": 1,
        "captured_at": datetime.now(timezone.utc).isoformat(),
        "provenance": "Contents observed at capture time; no claim about earlier runs.",
        **identity,
    }
    # Never silently replace an earlier identity with newly observed contents.
    with output.open("x") as stream:
        stream.write(json.dumps(manifest, indent=2) + "\n")
    return manifest


def verify(state, manifest_path, core=CORE):
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != 1:
        raise ValueError("Unsupported checkpoint manifest schema")
    current = inspect(state, core)
    for key, value in current.items():
        if manifest.get(key) != value:
            raise ValueError(f"Checkpoint differs from captured manifest: {key}")
    return manifest


def snapshot(state, manifest_path, destination, core=CORE):
    """Verify copies, then rebase the state to a dedicated read-only mount."""
    container_path = PREFIX + destination.resolve().relative_to(core.resolve()).as_posix()
    manifest = verify(state, manifest_path, core)
    destination.mkdir(parents=True, exist_ok=False)
    source_state = destination / "source-state.json"
    shutil.copyfile(state, source_state)
    if sha(source_state) != manifest["state_sha256"]:
        raise ValueError("Checkpoint state changed during snapshot")
    for name, expected in manifest["artifacts_sha256"].items():
        target = destination / "artifacts" / expected / Path(name).name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(artifact_path(name, core), target)
        if sha(target) != expected:
            raise ValueError(f"Checkpoint artifact changed during snapshot: {name}")

    def rebase(name):
        return f"{container_path}/artifacts/{manifest['artifacts_sha256'][name]}/{Path(name).name}"

    rewritten = map_views(json.loads(source_state.read_text()), rebase)
    (destination / "state.json").write_text(json.dumps(rewritten, indent=2) + "\n")
    (destination / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return {
        "source_state_sha256": manifest["state_sha256"],
        "mount_path": container_path,
        "state_path": container_path + "/state.json",
        "manifest_sha256": sha(destination / "manifest.json"),
        "snapshot_state_sha256": sha(destination / "state.json"),
        "artifact_count": len(manifest["artifacts_sha256"]),
        "captured_at": manifest["captured_at"],
        "provenance": manifest["provenance"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["capture", "verify"])
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    if args.action == "capture":
        capture(args.state, args.manifest)
    else:
        verify(args.state, args.manifest)
    print(f"Checkpoint {args.action} succeeded: {args.manifest}")


if __name__ == "__main__":
    main()
