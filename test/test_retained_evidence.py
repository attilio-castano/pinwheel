import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from retained_evidence import (BLOCKERS, DESIGN_PINS, POLICY, PROGRAMS, RESULT, SELECTION,
    compare_current_design, create_bundle, digest, load_bundle, load_seed,
    preflight, relocated_evidence_class, relocations)
from design_acceptance import Evidence


class RetainedEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source, self.current = self.root / 'source', self.root / 'current'
        self.source.mkdir()
        self.current.mkdir()
        self.external = self.root / 'old' / 'library.lib'
        self.put(self.external, 'original library')
        self.files = {str(self.external): digest(self.external)}
        for name in (*DESIGN_PINS, 'Pinwheel/Design.lean', 'scripts/design_acceptance.py'):
            value = 'leanprover/lean4:v4.33.1\n' if name == 'lean-toolchain' else 'original ' + name
            self.put(self.source / name, value)
            self.put(self.current / name, value)
            self.files[name] = digest(self.source / name)
        self.put(self.source / SELECTION, dict(schema=1, policy=POLICY, roots={}))
        self.put(self.current / SELECTION, (self.source / SELECTION).read_bytes())
        self.files[SELECTION] = digest(self.source / SELECTION)
        self.index = 'build/validation/retained/report.json'
        self.write_index()

    def tearDown(self):
        self.temporary.cleanup()

    def put(self, path, value):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(value if isinstance(value, bytes) else
                         (json.dumps(value).encode() if isinstance(value, dict) else value.encode()))

    def write_index(self, policy=POLICY):
        report = dict(status='assessed', policy=policy, A_accepted=False,
                      blockers=sorted(BLOCKERS), verified_files=self.files,
                      verified_file_count=len(self.files),
                      selection=dict(path=SELECTION, sha256=digest(self.source / SELECTION)),
                      commands=[dict(label=name + '-certificate', exit_code=0, expected_failure=False,
                                     argv=['lake', 'env', 'lean', '-DwarningAsError=true',
                                           str(self.source / Path(self.index).parent /
                                               (name + '-certificate.lean'))]) for name in PROGRAMS])
        self.put(self.source / self.index, report)
        anchor = dict(schema=1, status='assessed', policy=policy,
                      report=dict(path=self.index, sha256=digest(self.source / self.index)),
                      selection=report['selection'])
        self.put(self.source / RESULT, anchor)
        self.put(self.current / RESULT, anchor)

    def bundle(self):
        seed = load_seed(self.source, self.current)
        prepared = preflight(seed, self.source)
        destination = self.root / 'bundle'
        create_bundle(destination, seed, prepared)
        return destination

    def test_complete_inventory_reports_all_missing_and_changed_before_mutation(self):
        seed = load_seed(self.source, self.current)
        (self.source / 'Pinwheel/Design.lean').write_text('changed')
        self.external.unlink()
        report = preflight(seed, self.source)
        self.assertEqual(report['status'], 'invalid_evidence')
        self.assertEqual({item['reason'] for item in report['issues']}, {'changed', 'missing_or_unreadable'})
        destination = self.root / 'refused'
        with self.assertRaisesRegex(ValueError, 'Complete preflight'):
            create_bundle(destination, seed, report)
        self.assertFalse(destination.exists())

    def test_explicit_relocation_requires_identical_bytes(self):
        seed = load_seed(self.source, self.current)
        new = self.root / 'recovered' / 'library.lib'
        self.put(new, self.external.read_bytes())
        self.external.unlink()
        moves = relocations([str(self.external.parent) + '=' + str(new.parent)])
        self.assertEqual(preflight(seed, self.source, moves)['status'], 'ready')
        new.write_text('substitution')
        self.assertEqual(preflight(seed, self.source, moves)['issues'][0]['reason'], 'changed')

    def test_bundle_moves_without_receipt_rewriting_or_original_worktree(self):
        destination = self.bundle()
        original = (self.source / self.index).read_bytes()
        moved = self.root / 'relocated-bundle'
        shutil.move(destination, moved)
        shutil.rmtree(self.source)
        self.external.unlink()
        manifest = load_bundle(moved, self.current)
        self.assertEqual((moved / 'root' / self.index).read_bytes(), original)
        self.assertEqual(compare_current_design(moved, manifest, self.current)['status'], 'identical')

    def test_snapshot_is_independent_of_current_checker_edits(self):
        destination = self.bundle()
        (self.current / 'scripts/design_acceptance.py').write_text('new checker')
        manifest = load_bundle(destination, self.current)
        self.assertEqual(compare_current_design(destination, manifest, self.current)['status'], 'identical')
        self.assertEqual((destination / 'root/scripts/design_acceptance.py').read_text(),
                         'original scripts/design_acceptance.py')

    def test_current_design_emit_format_and_module_changes_refuse(self):
        destination = self.bundle()
        manifest = load_bundle(destination, self.current)
        (self.current / 'scripts/paired_execution.py').write_text('different encoder')
        with self.assertRaisesRegex(ValueError, 'differs from retained candidate'):
            compare_current_design(destination, manifest, self.current)
        self.put(self.current / 'scripts/paired_execution.py', 'original scripts/paired_execution.py')
        self.put(self.current / 'Pinwheel/Extra.lean', 'extra theorem')
        with self.assertRaisesRegex(ValueError, 'module inventory'):
            compare_current_design(destination, manifest, self.current)

    def test_bundle_changed_missing_and_escaping_files_refuse(self):
        destination = self.bundle()
        manifest = load_bundle(destination, self.current)
        item = manifest['files'][str(self.external)]
        path = destination / item['path']
        path.chmod(0o644)
        path.write_text('corrupt')
        with self.assertRaisesRegex(ValueError, 'Invalid bundle dependencies'):
            load_bundle(destination, self.current)
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'Invalid bundle dependencies'):
            load_bundle(destination, self.current)
        path.symlink_to(self.external)
        with self.assertRaisesRegex(ValueError, 'escapes'):
            load_bundle(destination, self.current)

    def test_v1_and_changed_index_refuse(self):
        self.write_index(policy='pinwheel-paired-a-acceptance-v1')
        with self.assertRaisesRegex(ValueError, 'tracked current-v2'):
            load_seed(self.source, self.current)
        self.write_index()
        (self.source / self.index).write_text('{}')
        with self.assertRaisesRegex(ValueError, 'Changed retained assessment index'):
            load_seed(self.source, self.current)

    def test_incomplete_inventory_and_noncanonical_paths_refuse(self):
        report = json.loads((self.source / self.index).read_text())
        report['verified_file_count'] += 1
        self.put(self.source / self.index, report)
        anchor = json.loads((self.current / RESULT).read_text())
        anchor['report']['sha256'] = digest(self.source / self.index)
        self.put(self.current / RESULT, anchor)
        with self.assertRaisesRegex(ValueError, 'Incomplete retained inventory'):
            load_seed(self.source, self.current)
        self.files['../outside'] = '0' * 64
        self.write_index()
        with self.assertRaisesRegex(ValueError, 'Noncanonical'):
            load_seed(self.source, self.current)

    def test_relocated_evidence_preserves_logical_identity_and_consumption(self):
        destination = self.bundle()
        manifest = load_bundle(destination, self.current)
        relocated = relocated_evidence_class(Evidence, destination, manifest)
        evidence = relocated(destination / 'root')
        reference = evidence.ref(str(self.external), self.files[str(self.external)])
        self.assertEqual(reference['path'], str(self.external))
        evidence.consumed('external library', dict(path='receipt', sha256='0' * 64),
                          dict(inputs_sha256={str(self.external): reference['sha256']}), reference)
        evidence.same('relocated alias', reference,
                      dict(path=str(destination / manifest['files'][str(self.external)]['path']),
                           sha256=reference['sha256']))
        evidence.close()
        with self.assertRaisesRegex(ValueError, 'Unindexed retained dependency'):
            evidence.ref('unlisted.txt')
        with self.assertRaisesRegex(ValueError, 'Unindexed retained dependency'):
            evidence.ref(self.root / 'unlisted-external.lib')

    def test_only_new_assessment_outputs_can_extend_inventory(self):
        destination = self.bundle()
        manifest = load_bundle(destination, self.current)
        output = Path('build/validation/new')
        self.put(destination / 'root' / output / 'proof.log', 'fresh')
        self.put(destination / 'root' / 'unrecorded.v', 'unrecorded')
        relocated = relocated_evidence_class(Evidence, destination, manifest, output)
        evidence = relocated(destination / 'root')
        evidence.ref(output / 'proof.log')
        with self.assertRaisesRegex(ValueError, 'Unindexed retained dependency'):
            evidence.ref('unrecorded.v')
        outside = self.root / 'outside'
        self.put(outside / 'fresh.log', 'outside')
        (destination / 'root' / output / 'escape').symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'Fresh assessment output escapes'):
            evidence.ref(output / 'escape/fresh.log')

    def test_absolute_original_root_reference_uses_relative_bundle_identity(self):
        name = 'build/validation/previous/input.json'
        self.put(self.source / name, dict(value='retained'))
        self.files[name] = digest(self.source / name)
        self.write_index()
        destination = self.bundle()
        manifest = load_bundle(destination, self.current)
        old_absolute = str(self.source / name)
        shutil.rmtree(self.source)
        relocated = relocated_evidence_class(Evidence, destination, manifest)
        evidence = relocated(destination / 'root')
        reference = evidence.ref(old_absolute, self.files[name])
        self.assertEqual(reference['path'], name)
        self.assertEqual(evidence.load(reference), dict(value='retained'))
        evidence.consumed('original-root input', dict(path='receipt', sha256='0' * 64),
                          dict(inputs_sha256={old_absolute: reference['sha256']}), reference)
        evidence.same('absolute / relative', reference,
                      dict(path=old_absolute, sha256=reference['sha256']))
        evidence.close()
        with self.assertRaisesRegex(ValueError, 'Unindexed retained dependency'):
            evidence.ref(old_absolute + '.unrecorded')

    def test_original_root_metadata_must_match_all_pinned_commands(self):
        destination = self.bundle()
        inventory = destination / 'inventory.json'
        inventory.chmod(0o644)
        manifest = json.loads(inventory.read_text())
        manifest['original_root'] = str(self.root / 'unauthorized-alias')
        inventory.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'original root disagrees'):
            load_bundle(destination, self.current)

    def test_prior_bundle_derives_alias_without_rewriting_inventory(self):
        destination = self.bundle()
        inventory = destination / 'inventory.json'
        inventory.chmod(0o644)
        manifest = json.loads(inventory.read_text())
        del manifest['original_root']
        inventory.write_text(json.dumps(manifest))
        before = inventory.read_bytes()
        loaded = load_bundle(destination, self.current)
        self.assertEqual(loaded['original_root'], str(self.source))
        self.assertEqual(inventory.read_bytes(), before)

    def test_no_overwrite_or_live_symlink_dependency(self):
        destination = self.bundle()
        seed = load_seed(self.source, self.current)
        with self.assertRaises(FileExistsError):
            create_bundle(destination, seed, preflight(seed, self.source))


if __name__ == '__main__':
    unittest.main()
