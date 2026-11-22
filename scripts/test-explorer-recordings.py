#!/usr/bin/env python3
"""Exercise Explorer publication, recording admission and corruption checks."""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


spec = importlib.util.spec_from_file_location("explorer_builder", Path(__file__).with_name("build-explorer.py"))
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)


def page_payload(page):
    marker = '<script id="explorer-data" type="application/json">'
    _, encoded = page.split(marker, 1)
    return builder.read_json(encoded.split("</script>", 1)[0])


class ExplorerRecordings(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.explorer = builder.EXPLORER
        cls.cache = builder.CACHE
        cls.output = builder.OUTPUT
        cls.recordings = builder.read_recordings()

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="pinwheel-explorer-recordings-")
        base = Path(self.directory.name)
        builder.EXPLORER = base / "explorer"
        builder.CACHE = base / "cache"
        builder.OUTPUT = base / "site" / "index.html"
        builder.EXPLORER.mkdir()
        builder.CACHE.mkdir()
        for name in ("content.json", "explorer.template.html", "recordings.json", *builder.RECORDING_FILES):
            shutil.copyfile(self.explorer / name, builder.EXPLORER / name)

    def tearDown(self):
        builder.EXPLORER, builder.CACHE, builder.OUTPUT = self.explorer, self.cache, self.output
        self.directory.cleanup()

    def write_cache(self, name, recording):
        (builder.CACHE / name).write_text(json.dumps(recording))

    def changed_recording(self, name):
        recording = copy.deepcopy(self.recordings[name])
        trace = recording["traces"][0] if "traces" in recording else recording
        trace["title"] += " changed"
        return recording

    def test_clean_build_reads_only_retained_recordings(self):
        self.assertFalse(builder.OUTPUT.exists())
        (builder.CACHE / "buffered-session.json").write_text("{")
        with patch.object(sys, "argv", ["build-explorer.py", "--check"]):
            builder.main()
        self.assertFalse(builder.OUTPUT.exists())
        with patch.object(sys, "argv", ["build-explorer.py"]):
            builder.main()
        payload = page_payload(builder.OUTPUT.read_text())
        self.assertEqual(payload["trace"], self.recordings["uart-trace.json"])
        self.assertEqual(payload["bufferedSession"], self.recordings["buffered-session.json"])
        self.assertEqual(payload["protocolTraces"],
            self.recordings["spi-traces.json"]["traces"] + self.recordings["i2c-traces.json"]["traces"])
        self.assertFalse((builder.EXPLORER / "index.html").exists())

    def test_digest_ignores_json_layout_and_member_order(self):
        for recording in self.recordings.values():
            reordered = {key: recording[key] for key in reversed(recording)}
            self.assertEqual(builder.canonical_sha256(recording),
                builder.canonical_sha256(json.loads(json.dumps(reordered, indent=4))))

    def test_refresh_rejects_malformed_candidate(self):
        (builder.CACHE / "buffered-session.json").write_text("{")
        with patch.object(sys, "argv", ["build-explorer.py", "--refresh-receipts"]):
            with self.assertRaises(json.JSONDecodeError):
                builder.main()
        self.assertFalse(builder.OUTPUT.exists())

    def test_refresh_promotes_valid_candidate_to_retained_json(self):
        name = "i2c-traces.json"
        candidate = self.changed_recording(name)
        self.write_cache(name, candidate)
        with patch.object(sys, "argv", ["build-explorer.py", "--refresh-receipts"]):
            builder.main()
        (builder.CACHE / name).unlink()
        self.assertEqual(builder.read_recordings()[name], candidate)
        self.assertEqual(builder.read_receipts()["recordings"][name]["sha256"],
            builder.canonical_sha256(candidate))
        with patch.object(sys, "argv", ["build-explorer.py", "--check"]):
            builder.main()

    def test_changed_recordings_fail_before_writing_html(self):
        for name in builder.RECORDING_FILES:
            with self.subTest(recording=name):
                path = builder.EXPLORER / name
                original = path.read_bytes()
                path.write_text(json.dumps(self.changed_recording(name)))
                with patch.object(sys, "argv", ["build-explorer.py"]):
                    with self.assertRaisesRegex(ValueError, "Recording data or receipt changed"):
                        builder.main()
                self.assertFalse(builder.OUTPUT.exists())
                path.write_bytes(original)

    def test_missing_recording_cannot_fall_back_to_generated_assets(self):
        name = "buffered-session.json"
        self.write_cache(name, self.recordings[name])
        with patch.object(sys, "argv", ["build-explorer.py"]):
            builder.main()
            (builder.EXPLORER / name).unlink()
            with self.assertRaises(FileNotFoundError):
                builder.main()

    def test_source_tree_binding_cannot_fall_back_to_checkout(self):
        path = builder.EXPLORER / "recordings.json"
        original = json.loads(path.read_text())
        generation = self.recordings["buffered-session.json"]["sourceRevision"]
        for tree, error in (
            ("HEAD", "full Git commit ID"),
            ("0" * 40, "Missing source at recording tree"),
            ("6c3233654f3054bc370e024677d76dbd3d37324e", "Missing source at recording tree"),
        ):
            with self.subTest(tree=tree):
                receipt = copy.deepcopy(original)
                receipt["sourceTrees"][generation] = tree
                path.write_text(json.dumps(receipt))
                with self.assertRaisesRegex(ValueError, error):
                    builder.bundle()

    def test_recorded_source_excerpts_ignore_checkout_edits(self):
        page, _ = builder.bundle()
        before = page_payload(page)
        trace = before["bufferedSession"]
        tree = before["snapshot"]["recordingSourceTrees"][trace["id"]]
        reference = trace["stages"][0]["sources"][0]
        path = reference["path"]
        key = f"{tree}:{path}:{reference['start']}:{reference['end']}"
        excerpt = before["sources"][key]
        self.assertEqual(excerpt["revision"], tree)
        self.assertEqual(excerpt["sha256"], hashlib.sha256(builder.git_source(tree, path)).hexdigest())
        self.assertEqual(excerpt["text"], "\n".join(
            builder.git_source(tree, path).decode().splitlines()[reference["start"] - 1:reference["end"]]))

        read_bytes = Path.read_bytes

        def changed_checkout(file):
            data = read_bytes(file)
            if file in {builder.ROOT / path, builder.ROOT / "lakefile.toml"}:
                return b"-- Changed working-tree source\n" + data
            return data

        with patch.object(Path, "read_bytes", changed_checkout):
            page, _ = builder.bundle()
        after = page_payload(page)
        self.assertEqual(after["sources"][key], excerpt)
        self.assertEqual(after["bufferedSession"], trace)

    def test_receipt_hash_and_summary_changes_fail(self):
        original = json.loads((builder.EXPLORER / "recordings.json").read_text())
        for field, changed in (("sha256", "0" * 64), ("frameCount", 0)):
            with self.subTest(field=field):
                receipt = copy.deepcopy(original)
                receipt["recordings"]["buffered-session.json"][field] = changed
                (builder.EXPLORER / "recordings.json").write_text(json.dumps(receipt))
                with self.assertRaisesRegex(ValueError, "Recording data or receipt changed"):
                    builder.bundle()

    def test_missing_receipt_fails_normal_build(self):
        (builder.EXPLORER / "recordings.json").unlink()
        with self.assertRaisesRegex(ValueError, "Missing recordings.json"):
            builder.bundle()

    def test_refresh_rejects_stale_sources_before_any_write(self):
        name = "buffered-session.json"
        recording = copy.deepcopy(self.recordings[name])
        recording["sourceHashes"][next(iter(recording["sourceHashes"]))] = "0" * 64
        self.write_cache(name, recording)
        receipt = builder.EXPLORER / "recordings.json"
        retained = builder.EXPLORER / name
        before = receipt.read_bytes(), retained.read_bytes()
        with patch.object(sys, "argv", ["build-explorer.py", "--refresh-receipts"]):
            with self.assertRaisesRegex(ValueError, "Recorded trace source changed"):
                builder.main()
        self.assertEqual((receipt.read_bytes(), retained.read_bytes()), before)
        self.assertFalse(builder.OUTPUT.exists())


if __name__ == "__main__":
    unittest.main()
