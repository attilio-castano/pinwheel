#!/usr/bin/env python3
"""Exercise explorer recording fallback and receipt rejection without editing evidence."""

from __future__ import annotations

import copy
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


class ExplorerRecordings(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.explorer = builder.EXPLORER
        cls.cache = builder.CACHE
        cls.recordings = builder.large_recordings()
        cls.payload = builder.snapshot_payload(cls.explorer / "index.html")

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="pinwheel-explorer-recordings-")
        base = Path(self.directory.name)
        builder.EXPLORER = base / "explorer"
        builder.CACHE = base / "cache"
        builder.EXPLORER.mkdir()
        builder.CACHE.mkdir()
        for name in ("content.json", "uart-trace.json", "spi-traces.json",
                "explorer.template.html", "index.html", "recordings.json"):
            shutil.copyfile(self.explorer / name, builder.EXPLORER / name)

    def tearDown(self):
        builder.EXPLORER, builder.CACHE = self.explorer, self.cache
        self.directory.cleanup()

    def write_cache(self, name, recording):
        (builder.CACHE / name).write_text(json.dumps(recording))

    def write_snapshot(self, payload):
        data = json.dumps(payload).replace("<", "\\u003c")
        (builder.EXPLORER / "index.html").write_text(
            '<script id="explorer-data" type="application/json">' + data + '</script>')

    def changed_recording(self, name):
        recording = copy.deepcopy(self.recordings[name])
        if name == "buffered-session.json":
            recording["title"] += " changed"
        else:
            recording["traces"][0]["title"] += " changed"
        return recording

    def test_clean_checkout_fallback_matches_generated_cache(self):
        fallback = builder.large_recordings()
        self.assertEqual(fallback, self.recordings)
        _, receipts = builder.bundle()
        for name, recording in self.recordings.items():
            self.write_cache(name, recording)
        self.assertEqual(builder.large_recordings(), fallback)
        self.assertEqual(builder.bundle()[1], receipts)

    def test_digest_ignores_json_layout_and_member_order(self):
        for recording in self.recordings.values():
            reordered = {key: recording[key] for key in reversed(recording)}
            self.assertEqual(builder.canonical_sha256(recording),
                builder.canonical_sha256(json.loads(json.dumps(reordered, indent=4))))

    def test_changed_cache_is_not_replaced_by_good_snapshot(self):
        for name in builder.LARGE_RECORDINGS:
            with self.subTest(recording=name):
                self.write_cache(name, self.changed_recording(name))
                with self.assertRaisesRegex(ValueError, "Recording data or receipt changed"):
                    builder.bundle()
                (builder.CACHE / name).unlink()

    def test_malformed_cache_is_not_replaced_by_good_snapshot(self):
        (builder.CACHE / "buffered-session.json").write_text("{")
        with self.assertRaises(json.JSONDecodeError):
            builder.bundle()

    def test_changed_embedded_recordings_fail_receipts(self):
        for name in builder.LARGE_RECORDINGS:
            with self.subTest(recording=name):
                payload = copy.deepcopy(self.payload)
                changed = self.changed_recording(name)
                if name == "buffered-session.json":
                    payload["bufferedSession"] = changed
                else:
                    payload["protocolTraces"] = [trace for trace in payload["protocolTraces"]
                        if trace["protocol"] != "i2c"] + changed["traces"]
                self.write_snapshot(payload)
                with self.assertRaisesRegex(ValueError, "Recording data or receipt changed"):
                    builder.bundle()

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
        recording = copy.deepcopy(self.recordings["buffered-session.json"])
        recording["sourceHashes"][next(iter(recording["sourceHashes"]))] = "0" * 64
        self.write_cache("buffered-session.json", recording)
        receipt = builder.EXPLORER / "recordings.json"
        page = builder.EXPLORER / "index.html"
        before = receipt.read_bytes(), page.read_bytes()
        with patch.object(sys, "argv", ["build-explorer.py", "--refresh-receipts"]):
            with self.assertRaisesRegex(ValueError, "Recorded trace source changed"):
                builder.main()
        self.assertEqual((receipt.read_bytes(), page.read_bytes()), before)

    def test_snapshot_data_is_inert_and_requires_one_complete_json_script(self):
        self.write_snapshot(self.payload)
        path = builder.EXPLORER / "index.html"
        path.write_text('<script>throw new Error("must not execute")</script>' + path.read_text())
        self.assertEqual(builder.snapshot_payload(path), self.payload)
        path.write_text(path.read_text() + '<script id="explorer-data" type="application/json">{}</script>')
        with self.assertRaisesRegex(ValueError, "exactly one complete JSON data script"):
            builder.snapshot_payload(path)


if __name__ == "__main__":
    unittest.main()
