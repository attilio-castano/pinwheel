"""Final selection controls never treat partial/probe or stale state as routed."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_final_target as F


class FinalTargetTests(unittest.TestCase):
    def fixture(self, temporary):
        root = Path(temporary)
        prepared = root / 'prepared'; prepared.mkdir()
        (prepared / 'preparation.json').write_text('prepared seal fixture')
        output = root / 'run'; output.mkdir()
        rows, artifacts = [], {}
        # Intentionally use ordinals whose lexical ordering differs.
        for step in ('09-openroad-stamidpnr-3', '10-openroad-detailedrouting', '100-openroad-fillinsertion'):
            directory = output / 'flow' / step; directory.mkdir(parents=True)
            odb = directory / 'actual.odb'; odb.write_bytes(('fixture ODB ' + step).encode())
            container = '/work/run/' + step + '/actual.odb'
            state = directory / 'state_out.json'; state.write_text(json.dumps({'odb': container}))
            rows.append(dict(step_directory=step, state=str(state), state_sha256=F.sha(state),
                        views=dict(odb=dict(path=str(odb), sha256=F.sha(odb), container=container))))
            artifacts[str(odb.relative_to(output))] = F.sha(odb)
            artifacts[str(state.relative_to(output))] = F.sha(state)
        directory = output / 'flow/01-yosys-jsonheader'; directory.mkdir()
        state = directory / 'state_out.json'; state.write_text(json.dumps({'nl': '/work/inputs/design.v', 'odb': None}))
        rows.insert(0, dict(step_directory=directory.name, state=str(state), state_sha256=F.sha(state),
                            views=dict(odb=None, nl='/work/inputs/design.v')))
        artifacts[str(state.relative_to(output))] = F.sha(state)
        packet = dict(tiles='8x4', source_ff_bits=6039, clock_period_ns=20)
        report = dict(schema='pinwheel.streaming-8x4-native-run.v1', mode='full', status='flow_completed', exit_code=0,
            inputs_pdk_runtime_unchanged=True, container_termination=dict(status='absent'),
            qualified=False, physical_acceptance=False, prepared=str(prepared),
            prepared_input_sha256=F.sha(prepared / 'preparation.json'), artifact_sha256=artifacts,
            states=rows, **packet)
        return output / 'report.json', prepared, packet, report

    def select(self, path, prepared, packet, report):
        path.write_text(json.dumps(report))
        return F.select_report(path, F.sha(path), prepared, packet)

    def test_selects_numeric_latest_odb_and_preserves_physical_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            path, prepared, packet, report = self.fixture(temporary)
            target = self.select(path, prepared, packet, report)
            self.assertEqual(target['latest_step'], '100-openroad-fillinsertion')
            self.assertFalse(target['physical_acceptance'])
            report.update(status='failed', exit_code=2)
            target = self.select(path, prepared, packet, report)
            self.assertEqual(target['physical_exit_code'], 2)
            self.assertFalse(target['post_pnr_equivalence_proved'])

    def test_probe_coarse_timeout_and_missing_completed_route_reject(self):
        with tempfile.TemporaryDirectory() as temporary:
            path, prepared, packet, original = self.fixture(temporary)
            for field, value in [('mode', 'probe'), ('mode', 'coarse'), ('status', 'timed_out'),
                                 ('exit_code', False), ('inputs_pdk_runtime_unchanged', False),
                                 ('source_ff_bits', 6038), ('clock_period_ns', 30)]:
                report = copy.deepcopy(original); report[field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    self.select(path, prepared, packet, report)
            report = copy.deepcopy(original)
            report['states'] = [row for row in report['states'] if 'detailedrouting' not in row['step_directory']]
            with self.assertRaisesRegex(ValueError, 'completed DetailedRouting'):
                self.select(path, prepared, packet, report)

    def test_changed_odb_or_escaping_artifact_never_refreshes_closed_hashes(self):
        with tempfile.TemporaryDirectory() as temporary:
            path, prepared, packet, report = self.fixture(temporary)
            odb = Path(report['states'][-1]['views']['odb']['path'])
            odb.write_bytes(b'tampered target')
            with self.assertRaisesRegex(ValueError, 'artifact changed'):
                self.select(path, prepared, packet, report)
        with tempfile.TemporaryDirectory() as temporary:
            path, prepared, packet, report = self.fixture(temporary)
            report['artifact_sha256']['../unrelated'] = 'a' * 64
            with self.assertRaisesRegex(ValueError, 'Escaping'):
                self.select(path, prepared, packet, report)

    def test_old_report_hash_and_stale_state_pointer_reject(self):
        with tempfile.TemporaryDirectory() as temporary:
            path, prepared, packet, report = self.fixture(temporary)
            path.write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError, 'report changed'):
                F.select_report(path, 'a' * 64, prepared, packet)
            report['states'][-1]['views']['odb']['container'] = '/work/run/stale.odb'
            with self.assertRaisesRegex(ValueError, 'does not select'):
                self.select(path, prepared, packet, report)

    def test_nested_repair_substeps_keep_local_ordinals_but_never_replace_top_level_target(self):
        with tempfile.TemporaryDirectory() as temporary:
            path, prepared, packet, report = self.fixture(temporary)
            for parent,step in [('100-openroad-fillinsertion','01-openroad-diodeinsertion'),
                                ('100-openroad-fillinsertion','999-openroad-checkantennas')]:
                directory=path.parent/'flow'/parent/step;directory.mkdir()
                odb=directory/'nested.odb';odb.write_bytes(b'authenticated nested substep')
                container='/work/run/'+str(odb.relative_to(path.parent/'flow'))
                state=directory/'state_out.json';state.write_text(json.dumps({'odb':container}))
                report['states'].append(dict(step_directory=step,state=str(state),state_sha256=F.sha(state),
                    views={'odb':dict(path=str(odb),sha256=F.sha(odb),container=container)}))
                for item in (state,odb):report['artifact_sha256'][str(item.relative_to(path.parent))]=F.sha(item)
            target=self.select(path,prepared,packet,report)
            self.assertEqual(target['latest_step'],'100-openroad-fillinsertion')
            self.assertEqual(len(target['authenticated_nested_states']),2)
            odb.write_bytes(b'changed nested evidence')
            with self.assertRaisesRegex(ValueError,'artifact changed'):self.select(path,prepared,packet,report)

    def test_explicit_repair_schema_dispatch_preserves_original_preparation_and_rejects_parent_fallback(self):
        import streaming_8x4_postantenna_repair as repair
        with tempfile.TemporaryDirectory() as temporary:
            path,prepared,packet,original=self.fixture(temporary)
            self.select(path,prepared,packet,original)
            self.assertEqual(F.base_preparation(path),prepared.resolve())
            report=dict(schema='pinwheel.streaming-8x4-postantenna-repair-run.v1',
                original_preparation=F.bound(prepared/'preparation.json'))
            path.write_text(json.dumps(report));expected={'schema':'separately-verified-repair-target'}
            with patch.object(repair,'select_report',return_value=expected) as select:
                self.assertEqual(F.select_report(path,F.sha(path),prepared,packet),expected)
                select.assert_called_once_with(path.resolve(),F.sha(path),prepared,packet)
            path.write_text(json.dumps(dict(report,schema='pinwheel.streaming-8x4-unrecognized-run.v1')))
            with self.assertRaisesRegex(ValueError,'Unknown physical'):F.base_preparation(path)
            with patch.object(repair,'select_report',side_effect=AssertionError('must not use repair fallback')):
                with self.assertRaises(ValueError):F.select_report(path,F.sha(path),prepared,packet)
            report['original_preparation']['sha256']='a'*64;path.write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError,'binding changed'):F.base_preparation(path)

    def test_original_and_repaired_candidate_identities_never_alias(self):
        with tempfile.TemporaryDirectory() as temporary:
            path,prepared,packet,report=self.fixture(temporary);target=self.select(path,prepared,packet,report)
            original=F.candidate_identity(target,prepared)
            self.assertEqual(original['kind'],'original-8x4')
            repaired=copy.deepcopy(target);repaired.update(schema='pinwheel.streaming-8x4-repair-final-target.v1',
                physical_candidate_kind='canonical-postantenna-repair',original_preparation=F.bound(prepared/'preparation.json'))
            for name in ('repair_preparation','original_parent_report','measured_fanout','actual_repair_state'):
                source=path.parent/(name+'.json');source.write_text(name);repaired[name]=F.bound(source)
            identity=F.candidate_identity(repaired,prepared)
            self.assertEqual(identity['kind'],'canonical-postantenna-repair');self.assertNotEqual(identity,original)
            with self.assertRaisesRegex(ValueError,'mixes separate repair'):F.candidate_identity(dict(target,physical_candidate_kind='canonical-postantenna-repair'),prepared)
            Path(repaired['original_parent_report']['path']).write_text('changed original parent')
            with self.assertRaisesRegex(ValueError,'authority changed'):F.candidate_identity(repaired,prepared)


if __name__ == '__main__':
    unittest.main()
