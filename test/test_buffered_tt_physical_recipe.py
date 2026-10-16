"""Recipe admission/custody controls; temporary fixtures only, no CAD launch."""
from contextlib import ExitStack
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / 'scripts'))
import buffered_tt_physical as physical

spec = importlib.util.spec_from_file_location(
    'buffered_tt_recipe', REPO / 'scripts/apply-buffered-tt-physical-recipe.py')
recipe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(recipe)


class BufferedTTPhysicalRecipeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.stage = self.root / 'build/physical/unused'
        self.stage.mkdir(parents=True)
        self.helper = self.root / 'scripts/apply-buffered-tt-physical-recipe.py'
        self.helper.parent.mkdir()
        self.helper.write_bytes((REPO / 'scripts/apply-buffered-tt-physical-recipe.py').read_bytes())
        self.source = self.root / 'scripts/original-preparer.py'
        self.source.write_text('original preparation source\n')
        self.measurement = self.root / 'build/measurement.json'
        self.measurement.write_text('{"status": "measured", "overflow": 2255}\n')
        self.validation = self.root / 'build/validation.json'
        self.validation.write_text('{"status": "passed"}\n')
        self.profile = self.root / recipe.CAPACITY_TCL
        self.profile.parent.mkdir(parents=True)
        self.profile.write_bytes((REPO / recipe.CAPACITY_TCL).read_bytes())
        self.config = dict(CLOCK_PERIOD=20, PNR_SDC_FILE='dir::core.sdc',
                           VERILOG_FILES=['dir::design.sv'], RT_MAX_LAYER='Metal4',
                           PDN_MULTILAYER=False, PDN_CONNECT_MACROS_TO_GRID=True,
                           RUN_KLAYOUT_DRC=True, RUN_MAGIC_DRC=True,
                           PL_TARGET_DENSITY_PCT=50,
                           MACROS={'example': {'instances': {'m': {'location': [252, 30]}}}},
                           meta=deepcopy(recipe.BASE_META))
        for name in recipe.REQUIRED_FILES:
            path = self.stage / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('bound original staged file ' + name + '\n')
        (self.stage / 'core.json').write_bytes(recipe.encode(self.config))
        self.intake = dict(schema='pinwheel-buffered-tt-physical-input-v1',
                           status='ready', missing_macro_views=[],
                           files_sha256={n: physical.sha(self.stage / n) for n in recipe.REQUIRED_FILES},
                           source_sha256={'scripts/original-preparer.py': physical.sha(self.source)},
                           validation_receipt=str(self.validation),
                           validation_receipt_sha256=physical.sha(self.validation))
        (self.stage / 'inputs.json').write_bytes(recipe.encode(self.intake))
        self.original_inputs = (self.stage / 'inputs.json').read_bytes()
        self.original_config = (self.stage / 'core.json').read_bytes()
        self.request_path = self.root / 'build/physical/recipe.json'
        self.request = dict(schema='pinwheel-buffered-tt-physical-recipe-v1',
                            source_inputs_sha256=recipe.digest(self.original_inputs),
                            source_config_sha256=recipe.digest(self.original_config),
                            physical_knobs={'PL_TIMING_DRIVEN': True},
                            evidence=[{'path': 'build/measurement.json',
                                       'sha256': physical.sha(self.measurement)}],
                            rationale='Use measured timing and congestion to select physical repair.')
        stack = ExitStack()
        self.addCleanup(stack.close)
        stack.enter_context(patch.object(recipe, 'ROOT', self.root))
        stack.enter_context(patch.object(recipe, 'SOURCE', self.helper))
        stack.enter_context(patch.object(physical, 'ROOT', self.root))

    def apply(self):
        self.request_path.write_bytes(recipe.encode(self.request))
        return recipe.apply_recipe(self.stage, self.request_path)

    def assert_no_application(self):
        self.assertTrue(all(not (self.stage / n).exists()
                            for n in (*recipe.SNAPSHOTS, 'gpl_capacity.tcl')))

    def test_admitted_recipe_preserves_originals_and_binds_every_new_input(self):
        self.request['physical_knobs'] = {
            'PL_TIMING_DRIVEN': True, 'PL_KEEP_RESIZE_BELOW_OVERFLOW': 0,
            'DESIGN_REPAIR_BUFFER_OUTPUT_PORTS': True,
            'PL_RESIZER_SETUP_SLACK_MARGIN': 1.0,
            'GRT_RESIZER_SETUP_SLACK_MARGIN': 1.0,
            'PL_RESIZER_SETUP_REPAIR_TNS_PCT': 100,
            'GRT_RESIZER_SETUP_REPAIR_TNS_PCT': 100,
            'PL_RESIZER_FIX_HOLD_FIRST': True, 'SYNTH_STRATEGY': 'DELAY 1'}
        result = self.apply()
        intake = physical.verify_prepared(self.stage)
        after = json.loads((self.stage / 'core.json').read_bytes())
        self.assertEqual({k: v for k, v in after.items() if k not in recipe.ALLOWLIST},
                         {k: v for k, v in self.config.items() if k not in recipe.ALLOWLIST})
        self.assertEqual((self.stage / 'pre-recipe-inputs.json').read_bytes(), self.original_inputs)
        self.assertEqual((self.stage / 'pre-recipe-core.json').read_bytes(), self.original_config)
        self.assertEqual(len(intake['files_sha256']), 21)
        self.assertEqual(result['unchanged_staged_files'],
                         {k: v for k, v in self.intake['files_sha256'].items() if k != 'core.json'})
        for name, expected in result['source_sha256'].items():
            self.assertEqual(physical.sha(self.root / name), expected)
        for name, expected in self.intake['files_sha256'].items():
            if name != 'core.json':
                self.assertEqual(physical.sha(self.stage / name), expected)
        self.assertFalse((self.stage / 'runs').exists())

    def test_capacity_profile_copies_only_the_fixed_bound_tcl(self):
        self.request['physical_knobs'] = {
            'meta': deepcopy(recipe.CAPACITY_META), 'PL_TARGET_DENSITY_PCT': 55}
        result = self.apply()
        intake = physical.verify_prepared(self.stage)
        self.assertEqual(len(intake['files_sha256']), 22)
        self.assertEqual((self.stage / 'gpl_capacity.tcl').read_bytes(), self.profile.read_bytes())
        self.assertEqual(result['added_profile_files'], {'gpl_capacity.tcl': physical.sha(self.profile)})
        self.assertEqual(intake['source_sha256'][recipe.CAPACITY_TCL], physical.sha(self.profile))
        self.assertEqual(json.loads((self.stage / 'core.json').read_bytes())['meta'], recipe.CAPACITY_META)

    def test_protected_knobs_and_arbitrary_plugins_are_rejected(self):
        for knobs in ({'CLOCK_PERIOD': 25}, {'GRT_ALLOW_CONGESTION': True},
                      {'RSZ_CORNERS': ['typical']}, {'PDN_VPITCH': 89.92},
                      {'VERILOG_FILES': ['dir::other.sv']},
                      {'meta': {'flow': 'Classic', 'substituting_steps': {'OpenROAD.GlobalPlacement': 'Arbitrary.Step'}}},
                      {'meta': {**recipe.CAPACITY_META, 'other': True}}):
            with self.subTest(knobs=knobs):
                self.request['physical_knobs'] = knobs
                with self.assertRaises(ValueError): self.apply()
                self.assert_no_application()
                self.assertEqual((self.stage / 'core.json').read_bytes(), self.original_config)

    def test_knob_type_range_headroom_and_exact_strategy_guards(self):
        cases = [('PL_TIMING_DRIVEN', 1), ('PL_KEEP_RESIZE_BELOW_OVERFLOW', False),
                 ('PL_KEEP_RESIZE_BELOW_OVERFLOW', .1), ('PL_RESIZER_SETUP_REPAIR_TNS_PCT', True),
                 ('PL_RESIZER_SETUP_REPAIR_TNS_PCT', 99), ('PL_RESIZER_SETUP_SLACK_MARGIN', 2.01),
                 ('PL_RESIZER_SETUP_SLACK_MARGIN', .01), ('PL_RESIZER_SETUP_SLACK_MARGIN', float('inf')),
                 ('SYNTH_STRATEGY', 'DELAY 0'), ('SYNTH_STRATEGY', 'AREA 0'),
                 ('PL_TARGET_DENSITY_PCT', 45), ('PL_TARGET_DENSITY_PCT', 60)]
        for key, value in cases:
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                recipe.updated_config(self.config, {key: value})
        raised = {**self.config, 'PL_RESIZER_SETUP_SLACK_MARGIN': 1.5}
        with self.assertRaises(ValueError):
            recipe.updated_config(raised, {'PL_RESIZER_SETUP_SLACK_MARGIN': 1})

    def test_existing_runs_or_dangling_receipt_are_rejected(self):
        (self.stage / 'runs').mkdir()
        with self.assertRaisesRegex(ValueError, 'run directory'): self.apply()
        (self.stage / 'runs').rmdir()
        (self.stage / recipe.SNAPSHOTS[0]).symlink_to(self.root / 'missing')
        with self.assertRaisesRegex(ValueError, 'path is occupied'): self.apply()
        self.assertEqual((self.stage / 'inputs.json').read_bytes(), self.original_inputs)

    def test_reapplication_is_rejected_without_touching_the_first_receipt(self):
        self.apply()
        first = {n: (self.stage / n).read_bytes() for n in (*recipe.SNAPSHOTS, 'core.json', 'inputs.json')}
        with self.assertRaisesRegex(ValueError, 'already applied'): self.apply()
        self.assertEqual(first, {n: (self.stage / n).read_bytes() for n in first})

    def test_evidence_and_baseline_hash_mismatches_are_rejected(self):
        for field in ('source_inputs_sha256', 'source_config_sha256'):
            old = self.request[field]
            self.request[field] = '0' * 64
            with self.assertRaisesRegex(ValueError, 'does not bind'): self.apply()
            self.request[field] = old
        self.request['evidence'][0]['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Changed recipe evidence'): self.apply()
        self.assert_no_application()

    def test_evidence_path_duplicate_and_mutable_reference_guards(self):
        refs = [
            [{'path': '../outside.json', 'sha256': '0' * 64}],
            [self.request['evidence'][0], self.request['evidence'][0]],
            [{'path': 'build/physical/unused/inputs.json', 'sha256': recipe.digest(self.original_inputs)}],
            [{'path': str(self.measurement), 'sha256': physical.sha(self.measurement)}],
        ]
        for evidence in refs:
            with self.subTest(evidence=evidence):
                self.request['evidence'] = evidence
                with self.assertRaises(ValueError): self.apply()
                self.assert_no_application()

    def test_rtl_sdc_pdn_template_and_plugin_mutations_fail_before_writing(self):
        for name in ('design.sv', 'core.sdc', 'pdn.tcl', 'tt_block_6x4_pgvdd.def',
                     'librelane_plugin_buffered_tt.py'):
            path = self.stage / name
            old = path.read_bytes()
            with self.subTest(name=name):
                path.write_bytes(old + b'changed\n')
                with self.assertRaisesRegex(ValueError, 'Changed staged input'): self.apply()
                self.assert_no_application()
                path.write_bytes(old)

    def test_postapplication_changed_recipe_evidence_helper_or_profile_invalidates_custody(self):
        self.request['physical_knobs']['meta'] = deepcopy(recipe.CAPACITY_META)
        self.apply()
        for path in (self.request_path, self.measurement, self.helper, self.profile,
                     self.stage / 'gpl_capacity.tcl'):
            old = path.read_bytes()
            with self.subTest(path=path.name):
                path.write_bytes(old + b'changed\n')
                with self.assertRaisesRegex(ValueError, 'Changed (preparation source|staged input)'):
                    physical.verify_prepared(self.stage)
                path.write_bytes(old)

    def test_run_created_during_validation_is_rejected(self):
        original = physical.verify_prepared
        calls = 0
        def check_and_create(design):
            nonlocal calls
            result = original(design)
            calls += 1
            if calls == 2: (self.stage / 'runs').mkdir()
            return result
        with patch.object(physical, 'verify_prepared', side_effect=check_and_create):
            with self.assertRaisesRegex(ValueError, 'run directory'): self.apply()
        self.assert_no_application()
        self.assertEqual((self.stage / 'core.json').read_bytes(), self.original_config)

    def test_evidence_changed_during_validation_is_rejected(self):
        original = physical.verify_prepared
        calls = 0
        def check_and_change(design):
            nonlocal calls
            result = original(design)
            calls += 1
            if calls == 2: self.measurement.write_text('changed after first evidence check\n')
            return result
        with patch.object(physical, 'verify_prepared', side_effect=check_and_change):
            with self.assertRaisesRegex(ValueError, 'changed before application'): self.apply()
        self.assert_no_application()

    def test_failed_or_interrupted_commit_rolls_back_intake_config_and_owned_new_files(self):
        original = recipe.atomic_replace
        for failure in (OSError('injected commit failure'), KeyboardInterrupt('injected signal')):
            calls = 0
            def replace_once(path, data):
                nonlocal calls
                calls += 1
                if calls == 2: raise failure
                return original(path, data)
            with self.subTest(failure=type(failure).__name__), \
                 patch.object(recipe, 'atomic_replace', side_effect=replace_once):
                with self.assertRaises(type(failure)): self.apply()
            self.assert_no_application()
            self.assertEqual((self.stage / 'core.json').read_bytes(), self.original_config)
            self.assertEqual((self.stage / 'inputs.json').read_bytes(), self.original_inputs)
            physical.verify_prepared(self.stage)

    def test_symlinked_staged_files_are_rejected_even_with_matching_bytes(self):
        path = self.stage / 'core.sdc'
        original = path.read_bytes()
        path.unlink()
        other = self.stage / 'other-sdc'
        other.write_bytes(original)
        path.symlink_to(other)
        with self.assertRaisesRegex(ValueError, 'ordinary files'): self.apply()
        self.assert_no_application()


if __name__ == '__main__':
    unittest.main()
