"""New24 HOST admission controls; no exporter, recovered tool or Native runs."""
import ast
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_closure24_final_target as T
import streaming_8x4_closure24_final_connectivity as C
import streaming_8x4_closure24_final_authority as A
import streaming_8x4_final_target as OLD_T
import streaming_8x4_final_connectivity as OLD_C
import streaming_8x4_final_authority as OLD_A
import streaming_8x4_closure24_final_m as M
import streaming_8x4_final_m as OLD_M
import streaming_8x4_closure24_final_m_execute as X
import streaming_8x4_final_m_execute as OLD_X
import streaming_8x4_closure24_final_wire as W
import streaming_8x4_final_wire as OLD_W
import streaming_8x4_closure24_signoff_plan as Q
import streaming_8x4_signoff_plan as OLD_Q
import streaming_8x4_closure24_signoff_execute as V
import streaming_8x4_signoff_execute as OLD_V
import streaming_8x4_closure24_power_grid as G
import streaming_8x4_power_grid as OLD_G


class Final24Controls(unittest.TestCase):
    def fixture(self, root):
        base = root / 'base'; base.mkdir(); (base / 'preparation.json').write_text('{}')
        files = {}
        for name in ('physical_state', 'actual_odb', 'pg_preparation'):
            path = root / (name + '.data'); path.write_text(name); files[name] = T.bound(path)
        report = root / 'report.json'
        report.write_text(json.dumps(dict(schema='pinwheel.closure24-pg-native-run.v1',
            original_preparation=T.bound(base / 'preparation.json'))))
        target = dict(schema=T.TARGET_SCHEMA, **files, physical_report=T.bound(report),
            original_preparation=T.bound(base / 'preparation.json'), parent_is_not_final_target=True,
            physical_candidate_kind='pg-aware-antenna-access24', physical_acceptance=False,
            post_pnr_equivalence_proved=False, model_qualified=False,
            variant=dict(ordinal=1, policy='A', maximum_variants=2, semantic_state_bits=6039, clock_period_ns=20))
        return base, report, target

    def test_canonical_reference_exporter_and_mapping_are_reused_exactly(self):
        for name in ('TOP', 'FLAT_REFERENCE_SHA256', 'NATIVE_EXPORTER_SHA256'):
            self.assertEqual(getattr(T, name), getattr(OLD_T, name))
        self.assertIs(A.map_all_state, OLD_A.map_all_state)
        self.assertIs(A.corners, OLD_A.corners); self.assertIs(A.LIBRARIES, OLD_A.LIBRARIES)
        def body(module, name):
            tree = ast.parse(Path(module.__file__).read_text())
            return ast.dump(next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name))
        for name in ('command', 'validate_native'):
            self.assertEqual(body(C, name), body(OLD_C, name))

    def test_new_selector_is_reopened_and_legacy_authority_never_disguised(self):
        with tempfile.TemporaryDirectory() as temp:
            base, report, target = self.fixture(Path(temp)); packet = {'certified': True}
            with patch.object(T.P, 'verify', return_value=packet), patch.object(T.PG, 'select_report', return_value=target) as select:
                self.assertEqual(T.select_report(report, T.sha(report), base, packet), target)
                select.assert_called_once_with(report, T.sha(report), workspace=T.P.ROOT)
                for key, value in [('schema', 'pinwheel.streaming-8x4-final-target.v1'),
                    ('parent_is_not_final_target', False), ('model_qualified', True)]:
                    bad = dict(target, **{key: value}); select.return_value = bad
                    with self.assertRaises(ValueError): T.select_report(report, T.sha(report), base, packet)
            old = json.loads(report.read_text()); old['schema'] = 'pinwheel.streaming-8x4-native-run.v1'
            report.write_text(json.dumps(old))
            with self.assertRaises(ValueError): T.base_preparation(report)

    def test_new_candidate_identity_binds_every_target_and_variant(self):
        with tempfile.TemporaryDirectory() as temp:
            base, _, target = self.fixture(Path(temp)); identity = T.candidate_identity(target, base)
            self.assertEqual(identity['schema'], 'pinwheel.closure24-final-physical-candidate.v1')
            self.assertEqual(identity['actual_odb'], target['actual_odb'])
            for key, value in [('ordinal', 3), ('clock_period_ns', 10), ('semantic_state_bits', 1), ('policy', 'C')]:
                bad = copy.deepcopy(target); bad['variant'][key] = value
                with self.assertRaises(ValueError): T.candidate_identity(bad, base)
            Path(target['actual_odb']['path']).write_text('different target')
            with self.assertRaises(ValueError): T.candidate_identity(target, base)

    def test_new_owner_cannot_write_old_campaign_or_campaign_root(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); campaign = root / C.CAMPAIGN
            self.assertEqual(C.owned(campaign / 'new-final-export', root), campaign / 'new-final-export')
            for path in (campaign, root / 'build/campaigns/8x4-20261022-01/old-owner', root / 'elsewhere'):
                with self.assertRaises(ValueError): C.owned(path, root)

    def test_complete_GEN04_math_body_is_unchanged_and_new_names_are_explicit(self):
        payload = (ROOT / 'test/fixtures/streaming_8x4/GEN04-generate.py.txt').read_bytes()
        original, _ = OLD_M.adapted_generator(payload); current, _ = M.adapted_generator(payload)
        expected = original.replace('import streaming_8x4_final_m as D',
            'import streaming_8x4_closure24_final_m as D').replace(
            "PROFILE='pinwheel.streaming-8x4-actual-target-M.v1'", "PROFILE='pinwheel.closure24-actual-target-M.v1'").replace(
            "SCHEMA='pinwheel.streaming-8x4-actual-M-generation.v1'", "SCHEMA='pinwheel.closure24-actual-M-generation.v1'")
        self.assertEqual(current, expected)
        self.assertIs(M.dependency_context, OLD_M.dependency_context)
        with self.assertRaises(ValueError): M.adapted_generator(payload + b'\n')
        for name in ('compile_one', 'imports', 'verify_imports', 'observe_foundation_runtime',
            'command_timeout', 'budget_policy', 'private_texts', 'verify_private_import_inventory'):
            self.assertIs(getattr(X, name), getattr(OLD_X, name))
        self.assertIs(W.worker_result, OLD_W.worker_result)
        self.assertEqual(X.command_timeout('PhysicalGRTActualProof'), 600)
        self.assertEqual(X.command_timeout('PhysicalGRTActualProofOther'), 180)

    def test_reused_N_and_fresh_M_have_distinct_owners_and_one_namespace(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve(); n = root / 'build/campaigns/8x4-20261022-01/N'
            stage = root / C.CAMPAIGN / 'M/stage'; n.mkdir(parents=True); stage.mkdir(parents=True)
            (n / 'SourceN.lean').write_text(''); (stage / 'PhysicalM.lean').write_text('')
            with patch.object(X, 'ROOT', root):
                X.generated_roots_owned(n, [stage])
                (stage / 'SourceN.lean').write_text('')
                with self.assertRaisesRegex(ValueError, 'Duplicate'): X.generated_roots_owned(n, [stage])
                (stage / 'SourceN.lean').unlink()
                with self.assertRaises(ValueError): X.generated_roots_owned(n, [n])
                with self.assertRaises(ValueError): X.generated_roots_owned(stage, [stage])

    def test_original_native_signoff_and_strict_power_bodies_are_reused(self):
        for name in ('native_views', 'native_layout', 'owned_native', 'master_libraries', 'layout_budget'):
            self.assertIs(getattr(V, name), getattr(OLD_V, name))
        for name in ('native', 'native_supervise', 'census', 'validate_census', 'parse_log',
            'native_result', 'expected_rails', 'revision_identity'):
            self.assertIs(getattr(G, name), getattr(OLD_G, name))
        self.assertEqual(G.LAUNCHER, OLD_G.LAUNCHER)
        self.assertIs(Q.official_sources, OLD_Q.official_sources)
        self.assertEqual(Q.OFFICIAL_CHECKS, OLD_Q.OFFICIAL_CHECKS)
        self.assertEqual(len(Q.OFFICIAL_CHECKS), 9)
        self.assertEqual(Q.INHERITED_DISABLED, ('RUN_EQY', 'RUN_KLAYOUT_XOR', 'RUN_LINTER'))
        self.assertEqual(V.layout_budget(1800), 750)

    def test_fresh_views_command_binds_new_owner_and_same_target(self):
        packet = dict(prepared='/source-base', source_flow='/new-candidate/flow', pdk_root='/pdk')
        argv = V.views_command(Path('/new-view'), packet, dict(image_id='sha256:'+'a'*64),
            '00000000-0000-4000-8000-000000000000', 'pinwheel-new-views')
        self.assertIn('/work/export/inputs/producer/scripts/streaming_8x4_closure24_signoff_execute.py', argv)
        self.assertIn('type=bind,source=/new-candidate/flow,target=/work/source,readonly', argv)
        self.assertEqual(argv[argv.index('--cpus')+1], '1')
        self.assertEqual(argv[argv.index('--memory')+1], '2g')
        self.assertEqual(argv[argv.index('--memory-swap')+1], '2g')
        self.assertEqual(argv[argv.index('--network')+1], 'none')
        with self.assertRaises(ValueError): V.views_command(Path('/new-view'), packet, {}, 'bad-owner', 'pinwheel-name')

    def test_view_request_rederives_actual_ODB_config_and_reference_bindings(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve(); flow=root/'flow'; stage=flow/'41-drt'; stage.mkdir(parents=True)
            odb=stage/'design.odb'; odb.write_text('actual'); (flow/'resolved.json').write_text('{}')
            reference=root/'reference.json'; reference.write_text('source reference')
            target=dict(actual_odb=T.bound(odb)); base=dict(input_sha256={'logical-input':'a'*64})
            request=V.views_request(target,flow,base,reference)
            self.assertEqual(request['source_odb'],'/work/source/41-drt/design.odb')
            self.assertEqual(request['resolved_config_sha256'],T.sha(flow/'resolved.json'))
            self.assertEqual(request['reference_sha256'],T.sha(reference))
            original=dict(request); (flow/'resolved.json').write_text('{"other":true}')
            self.assertNotEqual(V.views_request(target,flow,base,reference),original)
            bad=dict(actual_odb=dict(target['actual_odb'],sha256='b'*64))
            with self.assertRaises(ValueError): V.views_request(bad,flow,base,reference)
            with self.assertRaises(ValueError): V.views_request(target,root/'foreign-flow',base,reference)

    def test_view_artifacts_include_nested_reports_and_reject_aliases(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve(); (root/'report.json').write_text('outer')
            nested = root/'signoff-views'; nested.mkdir(); (nested/'report.json').write_text('native')
            self.assertEqual(V.artifact_membership(root), {'signoff-views/report.json': T.sha(nested/'report.json')})
            (root/'foreign').write_text('new')
            self.assertIn('foreign', V.artifact_membership(root))
            (root/'alias').symlink_to(nested/'report.json')
            with self.assertRaises(ValueError): V.artifact_membership(root)

    def test_old_host_signoff_receipts_are_not_new24_authority(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve(); owner = root/C.CAMPAIGN/'old'; owner.mkdir(parents=True)
            report = owner/'report.json'
            with patch.object(V.P, 'ROOT', root):
                for schema, function in [('pinwheel.streaming-8x4-signoff-plan.v1', V.checked_plan),
                    ('pinwheel.streaming-8x4-final-views-run.v1', V.closed_views),
                    ('pinwheel.streaming-8x4-power-grid-run.v1', G.verify)]:
                    report.write_text(json.dumps(dict(schema=schema, completed=True, passed=True, executed=False)))
                    with self.assertRaises(ValueError): function(report)

    def test_views_reopener_rejects_consistently_rewritten_execution_or_foreign_artifact(self):
        # Isolate custody/command validation; canonical raw view parsing has
        # its own unchanged native producers and is deliberately mocked here.
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve(); owner = root/C.CAMPAIGN/'views'; owner.mkdir(parents=True)
            physical = root/'physical.json'; runtime = dict(image_id='sha256:'+'a'*64)
            physical.write_text(json.dumps(dict(runtime=runtime)))
            (owner/'preparation.json').write_text('{}'); (owner/'final-views-native.json').write_text('{}')
            prep = dict(prepared='/base', source_flow='/flow', pdk_root='/pdk',
                target=dict(physical_report=T.bound(physical)), physical_candidate={'new': True})
            execution = dict(owner='00000000-0000-4000-8000-000000000000', status='completed',
                exit_code=0, timeout_seconds=300, container_termination=dict(status='absent'))
            execution['argv'] = V.views_command(owner, prep, runtime, execution['owner'], 'pinwheel-views-control')
            report = dict(schema='pinwheel.closure24-final-views-run.v1', completed=True,
                inputs_pdk_runtime_unchanged=True, physical_acceptance=False, target=prep['target'],
                physical_candidate=prep['physical_candidate'], preparation_sha256=T.sha(owner/'preparation.json'),
                runtime=runtime, native_report=T.bound(owner/'final-views-native.json'))
            def write(row):
                (owner/'execution.json').write_text(json.dumps(row))
                value = dict(report, execution=row, artifact_sha256=V.artifact_membership(owner))
                (owner/'report.json').write_text(json.dumps(value))
            with patch.object(V.P, 'ROOT', root), patch.object(V, 'verify_views_preparation', return_value=prep), \
                    patch.object(V, 'checked_view_outputs'):
                write(execution); V.closed_views(owner/'report.json')
                bad = copy.deepcopy(execution); bad['argv'][bad['argv'].index('--cpus')+1] = '2'; write(bad)
                with self.assertRaisesRegex(ValueError, 'command/status/resources'): V.closed_views(owner/'report.json')
                bad = dict(execution, exit_code=1); write(bad)
                with self.assertRaisesRegex(ValueError, 'command/status/resources'): V.closed_views(owner/'report.json')
                write(execution); (owner/'foreign').write_text('not in terminal inventory')
                with self.assertRaisesRegex(ValueError, 'complete artifact'): V.closed_views(owner/'report.json')


if __name__ == '__main__': unittest.main()
