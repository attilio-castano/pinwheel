import importlib.util
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock


SPEC = importlib.util.spec_from_file_location("retain_build", Path(__file__).with_name("retain_build.py"))
retain = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(retain)


class WholeBuildRetentionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.source = self.base / "original build"
        self.source.mkdir()
        (self.source / "nested").mkdir()
        (self.source / "nested" / "payload ü.txt").write_text("immutable historical evidence\n")
        (self.source / "empty").write_bytes(b"")
        (self.source / "relative-link").symlink_to("nested/payload ü.txt")
        (self.source / "directory-link").symlink_to("nested", target_is_directory=True)
        self.archive = self.base / "archive"

    @unittest.skipUnless(sys.platform == "darwin", "Collection uses macOS clone-copy")
    def test_clone_independence_links_and_later_offline_tamper_detection(self):
        report = retain.collect(self.source, self.archive)
        self.assertEqual(report["status"], "copied_and_fully_verified")
        self.assertEqual(report["entry_counts"], {"file": 2, "directory": 2, "symlink": 2})
        copied = self.archive / "build" / "nested" / "payload ü.txt"
        original = self.source / "nested" / "payload ü.txt"
        self.assertNotEqual(copied.stat().st_ino, original.stat().st_ino)
        self.assertEqual(os.readlink(self.archive / "build" / "directory-link"), "nested")
        self.assertEqual(retain.verify(self.archive, report["manifest_sha256"])["status"],
                         "verified_retained_build")
        copied.write_text("changed destination bytes\n")
        self.assertEqual(original.read_text(), "immutable historical evidence\n")
        with self.assertRaisesRegex(ValueError, "Retained destination mismatch"):
            retain.verify(self.archive, report["manifest_sha256"])

    def test_existing_archive_is_never_overwritten(self):
        self.archive.mkdir()
        sentinel = self.archive / "sentinel"
        sentinel.write_text("keep")
        with self.assertRaises(FileExistsError):
            retain.collect(self.source, self.archive)
        self.assertEqual(list(self.archive.iterdir()), [sentinel])
        self.assertEqual(sentinel.read_text(), "keep")

    @unittest.skipUnless(sys.platform == "darwin", "Collection uses macOS clone-copy")
    def test_source_edit_during_copy_rejects_partial_archive(self):
        real_copy = retain.clone_copy
        def edit_after_copy(source, destination, log):
            real_copy(source, destination, log)
            (source / "empty").write_bytes(b"unexpected concurrent producer")
        with mock.patch.object(retain, "clone_copy", side_effect=edit_after_copy):
            with self.assertRaisesRegex(ValueError, "Source stability"):
                retain.collect(self.source, self.archive)
        self.assertTrue((self.archive / "retention-failed.json").is_file())
        self.assertFalse((self.archive / "retention-report.json").exists())

    def test_external_symlink_and_source_nested_destination_are_rejected(self):
        external = self.base / "outside"
        external.write_text("outside retention scope")
        (self.source / "escape").symlink_to("../outside")
        with self.assertRaisesRegex(ValueError, "Symlink leaves"):
            retain.collect(self.source, self.archive)
        with self.assertRaisesRegex(ValueError, "disjoint"):
            retain.collect(self.source, self.source / "new-archive")

    def test_replacing_clone_with_hardlink_is_rejected(self):
        before = retain.inventory(self.source)
        destination = self.base / "hardlinks"
        destination.mkdir()
        os.link(self.source / "empty", destination / "same-inode")
        with self.assertRaisesRegex(ValueError, "shares source file inodes"):
            retain.independent_inodes(before, retain.inventory(destination))

    @unittest.skipUnless(sys.platform == "darwin", "Collection uses macOS clone-copy")
    def test_mode_and_manifest_tampering_are_rejected(self):
        report = retain.collect(self.source, self.archive)
        (self.archive / "build" / "empty").chmod(0o600)
        with self.assertRaisesRegex(ValueError, "Retained destination mismatch"):
            retain.verify(self.archive, report["manifest_sha256"])
        with (self.archive / "manifest.json").open("ab") as stream:
            stream.write(b" ")
        with self.assertRaisesRegex(ValueError, "external pin"):
            retain.verify(self.archive, report["manifest_sha256"])

    @unittest.skipUnless(sys.platform == "darwin", "Collection uses macOS clone-copy")
    def test_offline_verifier_rejects_build_root_retargeted_to_source(self):
        report = retain.collect(self.source, self.archive)
        (self.archive / "build").rename(self.archive / "retained-original")
        (self.archive / "build").symlink_to(self.source, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "root must be a real directory"):
            retain.verify(self.archive, report["manifest_sha256"])


if __name__ == "__main__":
    unittest.main()
