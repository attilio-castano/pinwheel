"""Tracked, provenance-checked inputs for all three observer host test suites."""
from contextlib import contextmanager
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from unittest import mock


REPOSITORY = Path(__file__).resolve().parents[3]
FIXTURES = Path(__file__).with_name("fixtures")


def checked_bytes(path, record):
    data = path.read_bytes()
    if len(data) != record["size_bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
        raise AssertionError(f"Tracked observer test input changed: {path}")
    return data


def provenance():
    record = json.loads((FIXTURES / "provenance.json").read_text())
    if record["schema"] != "pinwheel-observer-host-test-fixture-provenance-v1":
        raise AssertionError("Unknown observer host-fixture provenance")
    return record


def build_reference():
    record = provenance()["build_reference"]
    return json.loads(checked_bytes(FIXTURES / record["fixture"], record))


@contextmanager
def local_stage():
    """Load current tracked stage code with a temporary, exact tracked bootstrap.

    Neither the bootstrap nor generated Python is executed. This changes the
    loaded test module's ORIGINAL path only, preserving production launchers.
    """
    path = REPOSITORY / "tools/pinwheel-physical-campaign/stage.py"
    sys.path.insert(0, str(path.parent))
    try:
        spec = importlib.util.spec_from_file_location("observer_host_test_stage", path)
        stage = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(stage)
        record = provenance()["native_bootstrap"]
        source = REPOSITORY / record["tracked_repository_path"]
        data = checked_bytes(source, record)
        with tempfile.TemporaryDirectory() as folder:
            original = Path(folder)
            (original / "native.py").write_bytes(data)
            with mock.patch.object(stage, "ORIGINAL", original):
                yield stage
    finally:
        sys.path.pop(0)
