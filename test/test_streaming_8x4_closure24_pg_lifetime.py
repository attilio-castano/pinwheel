"""Portable loader lifetime/canonical body controls; no CAD or campaign reads."""
import ast
from copy import deepcopy
import gc
import hashlib
import inspect
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import weakref

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_pg_lifetime_context as C
import streaming_8x4_closure24_pg_lifetime as P
import streaming_tt_export_odb as EXPORT


def function(text, name):
    return next(n for n in ast.parse(text).body if isinstance(n, ast.FunctionDef) and n.name == name)


class LifetimeControls(unittest.TestCase):
    def test_complete_native_text_has_only_named_owner_and_launcher_delta(self):
        text, diff = C.native_source();original = (C.ROOT/C.NATIVE_PATH).read_text()
        self.assertEqual(text.replace(C.NEW_LOAD, C.OLD_LOAD).replace(C.NEW_IMPORT, C.OLD_IMPORT), original)
        self.assertEqual(text.count('pg_tech_owner'), 2)
        self.assertTrue(diff)
        for name in ('census', 'validate_census', 'validate_shapes', 'native_result', 'native_supervise', 'parse_log'):
            self.assertEqual(ast.dump(function(text, name)), ast.dump(function(original, name)), name)

    def test_temporary_owner_fails_named_owner_survives_complete_native_callback(self):
        class Tech:
            pass
        class Design:
            latest = None
            def __init__(self, tech):
                self.owner = weakref.ref(tech);Design.latest = self
            def alive(self):
                gc.collect()
                if self.owner() is None:raise RuntimeError('Tech owner was destroyed')
            def readDb(self, path):self.alive()
            def getBlock(self):self.alive();return 'same block'
        request = dict(schema='pinwheel.streaming-8x4-power-grid-request.v1', floorplanning=False,
                       dont_require_terminals=False, openroad_source_commit=P.COMMIT,
                       leaf_timeout_seconds=180, outer_timeout_seconds=240, source_odb='/actual.odb',
                       source_odb_sha256='sealed', inventory_sha256='sealed', reference_sha256='sealed',
                       top='actual', rails={'VPWR': {}, 'VGND': {}})
        inventory = {'inventory': 'same'};writes = [];commands = [];checks = []
        def alive(*args):
            Design.latest.alive();checks.append(True)
        def caught(design, command):
            alive();commands.append(command)
            return '1' if command.startswith('check_power_grid ') else ''
        module = C.native_module()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def read(path):
                return request if str(path) == 'request' else inventory if Path(path).name == 'inventory.json' else {}
            fakeP = SimpleNamespace(read=read, write=lambda path, row: writes.append(row))
            with patch.dict(sys.modules, {'openroad': SimpleNamespace(Tech=Tech, Design=Design)}),\
                    patch.object(EXPORT, 'export_block', lambda *args: (None, inventory)),\
                    patch.object(module, 'P', fakeP),patch.object(module, 'sha', lambda path: 'sealed'),\
                    patch.object(module, 'Path', lambda path: root if str(path) == '/work/pg' else Path(path)),\
                    patch.object(module, 'expected_rails', lambda value: request['rails']),\
                    patch.object(module, 'census', lambda *args: (alive(), {'same': 'census'})[1]),\
                    patch.object(module, 'validate_census', lambda *args: alive()),\
                    patch.object(module, 'inventory_totals', lambda *args: {'same': 'totals'}),\
                    patch.object(module, 'caught', caught),\
                    patch.object(module, 'observe_revision', lambda design: (alive(), dict(openroad_version=P.COMMIT, openroad_git_describe=''))[1]):
                namespace = dict(vars(module))
                exec(compile(inspect.getsource(C.NATIVE.native), '<unsafe-canonical-frame>', 'exec'), namespace)
                with self.assertRaisesRegex(RuntimeError, 'owner was destroyed'):namespace['native']('request')
                module.native('request')
        self.assertGreater(len(checks), 6)
        self.assertEqual([s for s in commands if s.startswith('check_power_grid ')],
                         ['check_power_grid -net VPWR -error_file '+str(root/'rail-0-errors.rpt'),
                          'check_power_grid -net VGND -error_file '+str(root/'rail-1-errors.rpt')])
        self.assertEqual(len(writes), 1);self.assertTrue(writes[0]['completed'])
        self.assertEqual(len(writes[0]['checks']), 2)
        self.assertFalse(writes[0]['physical_acceptance']);self.assertFalse(writes[0]['shorts_checked'])
        self.assertIsNone(Design.latest.owner())  # Lifetime ends after the callback, not before its checks.

    def test_old_module_globals_remain_unmodified_and_new_owner_isolated(self):
        self.assertIs(C.BASE.native, C.NATIVE.native)
        self.assertIsNot(P.native, C.BASE.native)
        self.assertIs(P.native, C.native_module().native)
        self.assertEqual(C.NATIVE.LAUNCHER.splitlines()[0], C.OLD_IMPORT)
        self.assertEqual(P.LAUNCHER.splitlines()[0], C.NEW_IMPORT)
        self.assertEqual(Path(P.run.__globals__['__file__']).resolve(), Path(P.__file__).resolve())
        self.assertNotEqual(P.run.__globals__, C.BASE.run.__globals__)

    def test_unchanged_scope_census_resources_and_reader_bodies(self):
        for name in ('LEAF_SECONDS', 'OUTER_SECONDS', 'BOUNDARY', 'COMMIT'):
            self.assertEqual(getattr(P, name), getattr(C.BASE, name))
        for name in ('census', 'validate_census', 'validate_shapes', 'native_result', 'native_supervise',
                     'expected_rails', 'inventory_totals', 'parse_log'):
            self.assertEqual(ast.dump(function(C.native_source()[0], name)),
                             ast.dump(function((C.ROOT/C.NATIVE_PATH).read_text(), name)), name)
        text, diff = C.controller_source()
        self.assertIn('pinwheel.closure24-power-grid-lifetime-preparation.v1', text)
        self.assertIn('pinwheel.closure24-power-grid-lifetime-run.v1', text)
        self.assertIn("LIFETIME.verify_context(output/'inputs'", text)
        self.assertIn("lifetime_context=packet['lifetime_context']", text)
        self.assertIn("'--memory','2g','--memory-swap','2g'", text)
        self.assertTrue(diff)

    def test_frozen_sources_and_unique_owner_anchor_fail_closed(self):
        with patch.object(C, 'NATIVE_PIN', '0'*64):
            with self.assertRaises(ValueError):C.native_source()
        with patch.object(C, 'BASE_PIN', '0'*64):
            with self.assertRaises(ValueError):C.controller_source()
        for text in ('absent', C.OLD_LOAD+'\n'+C.OLD_LOAD):
            with self.assertRaises(ValueError):C.replace_once(text, C.OLD_LOAD, C.NEW_LOAD)
        with patch.object(C, 'payload', return_value='pg_tech_owner already exists'):
            with self.assertRaises(ValueError):C.native_source()

    def test_primary_data_files_bytes_membership_and_nonexecution_are_sealed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);rows = []
            for i in range(6):
                p = root/f'source-{i}.cc';p.write_text(f'data only {i}\n');b = p.read_bytes()
                rows.append(dict(name=p.name, bytes=len(b), sha256=hashlib.sha256(b).hexdigest(),
                                 git_blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()))
            manifest = root/'manifest.json'
            value = dict(schema='pinwheel.closure24-pg-lifetime-source.v1', commit=P.COMMIT,
                         source_data_only=True, imported_or_executed=False, files=rows)
            manifest.write_text(json.dumps(value))
            with patch.object(C, 'PRIMARY_PIN', C.BASE.sha(manifest)):
                self.assertEqual(len(C.primary_source(root)), 7)
                (root/'extra').write_text('extra')
                with self.assertRaises(ValueError):C.primary_source(root)
                (root/'extra').unlink();(root/'source-0.cc').write_text('changed')
                with self.assertRaises(ValueError):C.primary_source(root)
            value['imported_or_executed'] = True;manifest.write_text(json.dumps(value))
            with patch.object(C, 'PRIMARY_PIN', C.BASE.sha(manifest)):
                with self.assertRaises(ValueError):C.primary_source(root)

    def test_context_cannot_change_target_sources_failure_or_claim_fix_observed(self):
        context = dict(schema='pinwheel.closure24-pg-lifetime-context.v1', primary_source_root='source',
                       primary_source_sha256={'sealed': 'data'}, failed_admission={'views_report': {'same': 'views'},
                       'target': {'actual_odb': {'same': 'ODB'}}}, native_source_pin=C.NATIVE_PIN,
                       controller_source_pin=C.BASE_PIN, named_owner='pg_tech_owner', ownership_delta_only=True,
                       actual_loader_repair_observed=False, physical_variant_changed=False)
        with patch.object(C, 'primary_source', return_value=context['primary_source_sha256']),\
                patch.object(C, 'failed_admission', return_value=context['failed_admission']),\
                patch.object(C, 'native_source'),patch.object(C, 'controller_source'):
            self.assertEqual(C.verify_context(Path('inputs'), context, {'same': 'views'}, {'same': 'ODB'}), context)
            for key, value in [('actual_loader_repair_observed', True), ('physical_variant_changed', True),
                               ('named_owner', 'different'), ('native_source_pin', '0'*64)]:
                bad = deepcopy(context);bad[key] = value
                with self.assertRaises(ValueError):C.verify_context(Path('inputs'), bad, {'same': 'views'}, {'same': 'ODB'})
            with self.assertRaises(ValueError):C.verify_context(Path('inputs'), context, {'changed': 'views'}, {'same': 'ODB'})
            with self.assertRaises(ValueError):C.verify_context(Path('inputs'), context, {'same': 'views'}, {'changed': 'ODB'})

    def test_existing_native_request_and_no_skip_flags_are_not_relaxed(self):
        text = C.native_source()[0];native = ast.unparse(function(text, 'native'))
        for token in ('dont_require_terminals', 'floorplanning', 'check_power_grid -net ',
                      "result == '1'", 'canonical_inventory_rederived=True', 'source_odb_unchanged=True'):
            self.assertIn(token, native)
        self.assertNotIn('-dont_require_terminals', native)
        self.assertNotIn('-floorplanning', native)
        self.assertIn('shorts_checked=False', native);self.assertIn('ir_drop_qualified=False', native)


if __name__ == '__main__':
    unittest.main()
