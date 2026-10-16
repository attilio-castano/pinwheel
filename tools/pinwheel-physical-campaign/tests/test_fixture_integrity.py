"""Captured parser fixtures must remain exact, bounded and distinct from passes."""
import gzip
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import campaign_fixtures as fixtures


class FixtureIntegrityTest(unittest.TestCase):
    def copy_report(self, root):
        manifest = fixtures.load_manifest()
        shutil.copyfile(fixtures.FIXTURES / "manifest.json", root / "manifest.json")
        record = manifest["files"]["p2-onepass-report"]
        shutil.copyfile(fixtures.FIXTURES / record["stored_path"], root / record["stored_path"])
        return manifest, record, root / record["stored_path"]

    def test_all_captures_and_native_source_match_recorded_identity(self):
        manifest = fixtures.load_manifest()
        self.assertEqual(manifest["runtime"], {
            "image_id": "sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92",
            "native_binary_sha256": "6ba87b45c762ee8c9670375c204cd03d801a6da98cd6e056a1c73027aad68a7c",
            "native_revision": "dcf36133a369abc8f3c5e5738cd4d82e4903c0e0"})
        for name, record in manifest["files"].items():
            raw = fixtures.load_text(name).encode("utf-8")
            self.assertEqual((len(raw), fixtures.sha(raw)), (record["raw_bytes"], record["raw_sha256"]))
        self.assertEqual(len(fixtures.native_program_bytes()), 9073)
        self.assertFalse(manifest["native_or_physical_acceptance_claim"])
        self.assertEqual(manifest["files"]["p2-control-native"]["producer_receipt"]["status"], "failed")
        self.assertEqual(manifest["files"]["p2-partial-native"]["producer_receipt"]["status"], "timed_out")

    def test_changed_stored_payload_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, _, path = self.copy_report(root)
            data = bytearray(path.read_bytes()); data[-1] ^= 1; path.write_bytes(data)
            with self.assertRaisesRegex(ValueError, "Stored fixture digest mismatch"):
                fixtures.load_text("p2-onepass-report", root)

    def test_wrong_raw_digest_rejected_after_decompression(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, record, _ = self.copy_report(root)
            record["raw_sha256"] = "0" * 64
            (root / "manifest.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "Raw fixture digest or size mismatch"):
                fixtures.load_text("p2-onepass-report", root)

    def test_nondeterministic_gzip_timestamp_rejected_after_stored_hash_reseal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest, record, path = self.copy_report(root)
            stored = gzip.compress(gzip.decompress(path.read_bytes()), compresslevel=9, mtime=1)
            path.write_bytes(stored)
            record.update(stored_sha256=fixtures.sha(stored), stored_bytes=len(stored))
            (root / "manifest.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "mtime=0"):
                fixtures.load_text("p2-onepass-report", root)

    def test_unknown_name_cannot_read_an_arbitrary_path(self):
        with self.assertRaisesRegex(ValueError, "Unknown fixture"):
            fixtures.load_text("../../build/physical/arbitrary.log")


if __name__ == "__main__":
    unittest.main()
