"""Exercise real Lean import resolution using an isolated disposable workspace."""
import os
import importlib.util
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import typed_artifact_runner

SPEC = importlib.util.spec_from_file_location("artifact_negatives", ROOT / "scripts/check-switch-artifact-negatives.py")
artifact_negatives = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(artifact_negatives)


@unittest.skipUnless(shutil.which("lake"), "Lean integration test requires the pinned Lake toolchain")
class PrivateModuleResolutionTests(unittest.TestCase):
    def test_private_module_wins_over_same_named_lake_cache_module(self):
        with tempfile.TemporaryDirectory(prefix="pinwheel-lean-resolution-") as temporary:
            workspace = Path(temporary).resolve()
            (workspace / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            (workspace / "lakefile.toml").write_text('name = "resolution_fixture"\nversion = "0.1.0"\n')
            cache = workspace / ".lake/build/lib/lean"
            private = workspace / "generated"
            cache.mkdir(parents=True)
            private.mkdir()

            def run(argv):
                return subprocess.run(list(map(str, argv)), cwd=workspace, text=True,
                                      capture_output=True, timeout=60)

            # Both valid modules export the same declaration with different
            # definitions. The witness can pass only with the private module.
            for directory, value in ((cache, 11), (private, 7)):
                source = directory / "ResolutionOrigin.lean"
                source.write_text(f"namespace ResolutionOrigin\ndef value : Nat := {value}\nend ResolutionOrigin\n")
                result = run(["lake", "env", "lean", "-o", directory / "ResolutionOrigin.olean", source])
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            witness = private / "ResolutionWitness.lean"
            witness.write_text("import ResolutionOrigin\n"
                               "theorem private_resolution : ResolutionOrigin.value = 7 := rfl\n")
            lean_path = str(private) + os.pathsep + str(cache)

            # Demonstrate the original failure mode without touching any
            # repository, user, or toolchain cache.
            inherited = ["env", "LEAN_PATH=" + lean_path, "lake", "env", "lean"]
            dependencies = run([*inherited, "--deps", witness])
            self.assertEqual(dependencies.returncode, 0, dependencies.stdout + dependencies.stderr)
            self.assertIn(str(cache / "ResolutionOrigin.olean"), dependencies.stdout.splitlines())
            wrong = run([*inherited, witness])
            self.assertNotEqual(wrong.returncode, 0, "The ambient module unexpectedly proved the private witness")
            self.assertIn("Type mismatch", wrong.stdout + wrong.stderr)

            # The production compiler must recover the exact private theorem.
            records = SimpleNamespace(records=[])
            with patch.object(typed_artifact_runner, "ROOT", workspace):
                typed_artifact_runner.compile_modules(records, private, ["ResolutionWitness"], timeout=60)
            self.assertTrue((private / "ResolutionWitness.olean").is_file())
            self.assertEqual(records.records[0]["exit_code"], 0)
            command = records.records[0]["argv"]
            dependencies = run([*command[:command.index("-DwarningAsError=true")], "--deps", witness])
            self.assertEqual(dependencies.returncode, 0, dependencies.stdout + dependencies.stderr)
            self.assertIn(str(private / "ResolutionOrigin.olean"), dependencies.stdout.splitlines())
            self.assertNotIn(str(cache / "ResolutionOrigin.olean"), dependencies.stdout.splitlines())

            # Negative-control witnesses have their own compiler because they
            # inspect expected failures. It must use the same private binding.
            negative_witness = private / "NegativeResolution.lean"
            negative_witness.write_text(witness.read_text())
            negative_records = SimpleNamespace(records=[])
            with patch.object(artifact_negatives, "ROOT", workspace):
                result = artifact_negatives.compile_lean(negative_records, private, "NegativeResolution")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            command = negative_records.records[0]["argv"]
            dependencies = run([*command[:command.index("-DwarningAsError=true")], "--deps", negative_witness])
            self.assertEqual(dependencies.returncode, 0, dependencies.stdout + dependencies.stderr)
            self.assertIn(str(private / "ResolutionOrigin.olean"), dependencies.stdout.splitlines())
            self.assertNotIn(str(cache / "ResolutionOrigin.olean"), dependencies.stdout.splitlines())


if __name__ == "__main__":
    unittest.main()
