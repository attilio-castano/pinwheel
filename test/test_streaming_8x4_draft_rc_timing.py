"""HOST controls for the separate unqualified fixed-target diagnostic."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_draft_rc_timing as D
import streaming_8x4_draft_rc_timing_observe as O


def config(flow='Streaming8x4Certified'):
    return dict(STA_CORNERS=list(D.CORNERS), CLOCK_PERIOD=20, PL_TARGET_DENSITY_PCT=85,
        RCX_MERGE_VIA_WIRE_RES=True, RCX_SDC_FILE=None, SIGNOFF_SDC_FILE='/work/inputs/core.sdc',
        PNR_SDC_FILE='/work/inputs/core.sdc', STA_EXTRA_CORNER_TCL_FILE=None, STA_THREADS=None,
        OPENROAD_THREADS=4, DRT_OPT_ITERS=64, meta=dict(flow=flow, version=1),
        RCX_RULESETS={'nom_*': '/work/pdk/inherited7.rules'}, CELL_LIBS={'unchanged': ['all original libs']})


def inventory():
    signature = {'A': dict(direction='INPUT', signal_type='SIGNAL'),
        'X': dict(direction='OUTPUT', signal_type='SIGNAL')}
    return dict(schema='pinwheel.streaming-tt-odb-inventory.v1',
        nets={'a': dict(wire=1, signal_type='SIGNAL'), 'z': dict(wire=2, signal_type='SIGNAL')},
        masters={'buf': signature, 'diode': {'A': signature['A']}},
        instances={'buffer': dict(master='buf', terminals={pin: dict(row, net='a' if pin == 'A' else 'z')
            for pin, row in signature.items()}),
            'ANTENNA0': dict(master='diode', terminals={'A': dict(signature['A'], net='z')})},
        unconnected_signal_outputs={}, public_bterms={'a': dict(net='a', direction='input'),
            'z': dict(net='z', direction='output')}, power_bterms={})


SPEF = '''*SPEF "IEEE 1481-1998"
*DELIMITER :
*NAME_MAP
*1 a
*2 z
*3 buffer
*4 ANTENNA0
*PORTS
*1 I
*2 O
*D_NET *1 0.1
*CONN
*P *1 I
*I *3:A I
*CAP
1 *1 0.1
*RES
*END
*D_NET *2 0.2
*CONN
*P *2 O
*I *3:X O
*I *4:A I
*CAP
1 *2 0.2
*RES
*END
'''


class DraftTiming(unittest.TestCase):
    def test_config_only_has_declared_deltas_and_complete_matrix(self):
        for flow in ('Streaming8x4Certified', 'Streaming8x4PostAntennaRepair'):
            before = config(flow)
            for model in D.MODELS:
                after = D.diagnostic_config(before, model)
                delta = D.config_delta(before, after, model)
                self.assertEqual(set(delta), {'RCX_RULESETS', 'STA_EXTRA_CORNER_TCL_FILE'} |
                    ({'meta'} if flow.endswith('Repair') else set()))
                self.assertEqual(after['CELL_LIBS'], before['CELL_LIBS'])
                changed = deepcopy(after); changed['CLOCK_PERIOD'] = 21
                with self.assertRaises(ValueError): D.config_delta(before, changed, model)
        self.assertEqual(D.policy()['cases'], 9); self.assertEqual(D.policy()['direct_native_calls'], 21)
        self.assertEqual(D.policy()['openlane_max_cores'], 1)
        self.assertEqual(D.policy()['canonical_corner_workers'], 1)
        self.assertFalse(D.policy()['model_qualified']); self.assertFalse(D.policy()['qualified_timing'])

    def test_corner_reduction_relaxed_constraints_and_unknown_model_reject(self):
        for key, value in [('STA_CORNERS', list(D.CORNERS[:1])), ('PNR_SDC_FILE', '/new.sdc'),
            ('RCX_MERGE_VIA_WIRE_RES', False), ('STA_THREADS', 4), ('STA_EXTRA_CORNER_TCL_FILE', '/old.tcl')]:
            changed = config(); changed[key] = value
            with self.assertRaises(ValueError): D.diagnostic_config(changed, 'TYP')
        with self.assertRaises(ValueError): D.diagnostic_config(config(), 'typ')

    def test_probe_or_unclosed_views_rejects_before_snapshot_or_native(self):
        with tempfile.TemporaryDirectory() as temporary:
            report = Path(temporary).resolve() / 'report.json'
            for value in [dict(schema='pinwheel.streaming-8x4-fixed-export-run.v1', status='export_completed'),
                dict(schema='pinwheel.streaming-8x4-final-views-run.v1', completed=False)]:
                report.write_text(json.dumps(value))
                with patch.object(D, 'snapshot', side_effect=AssertionError('not admitted')), \
                    patch.object(D.subprocess, 'Popen', side_effect=AssertionError('no Native')):
                    with self.assertRaises(ValueError): D.prepare(report, report, report, report.parent / 'new')

    def test_observer_requires_actual_passive_loads_and_no_mutating_commands(self):
        script, expected = O.observer(inventory(), 'a' * 64, 'b' * 64)
        self.assertIn('dict set expected_all {ANTENNA0} {diode}', script)
        self.assertIn('{ANTENNA0/A}', script); self.assertIn('is_propagated', script)
        self.assertEqual(expected['passive_pin_counts'], [1])
        self.assertEqual(expected['signal_instances'], 2)
        for forbidden in ('read_spef', 'read_verilog', 'set_propagated_clock', 'create_clock',
            'set_input_delay', 'set_load', 'repair_design', 'estimate_parasitics'):
            self.assertNotIn(forbidden, script)
        changed = inventory(); del changed['instances']['ANTENNA0']
        with self.assertRaises(ValueError): O.observer(changed, 'a' * 64, 'b' * 64)
        for value in ('x\\escaped', 'x} ; error bad', 'x\nnext'):
            with self.assertRaises(ValueError): O.literal(value)

    def test_observer_missing_passive_propagation_or_raw_report_rejects(self):
        _, expected = O.observer(inventory(), 'a' * 64, 'b' * 64); corner = D.CORNERS[0]
        log = f'PINWHEEL_DRAFT_QUERY_BEGIN {"a" * 64} {"b" * 64} {corner}\n' + \
            f'PINWHEEL_DRAFT_PASSIVE 0 1\nPINWHEEL_DRAFT_CLOCK clk 20.0 1\n' + \
            f'PINWHEEL_DRAFT_QUERY_COMPLETE {"a" * 64} {"b" * 64} 2 1\n'
        raw = 'Clock: clk\nPeriod: 20.0\nPropagated: no\n'
        self.assertTrue(O.check_observer(log, expected, corner, raw, '')['propagated_clock'])
        for changed in (log.replace('PASSIVE 0 1', 'PASSIVE 0 0'), log.replace('clk 20.0 1', 'clk 20.0 0'),
            log + 'PINWHEEL_DRAFT_PASSIVE 1 1\n'):
            with self.assertRaises(ValueError): O.check_observer(changed, expected, corner, raw, '')
        with self.assertRaises(ValueError): O.check_observer(log, expected, corner, raw, 'clk\n')

    def test_spef_connection_join_detects_missing_physical_load_and_extra_pin(self):
        good = O.spef_coverage(SPEF, inventory()); self.assertTrue(good['complete'])
        self.assertEqual(good['spef_connections'], 5)
        missing = O.spef_coverage(SPEF.replace('*I *4:A I\n', ''), inventory())
        self.assertFalse(missing['complete']); self.assertIn(['z', 'I', 'ANTENNA0', 'A'], missing['missing_connections'])
        extra = O.spef_coverage(SPEF.replace('*I *4:A I', '*I *4:A I\n*I *4:UNKNOWN I'), inventory())
        self.assertFalse(extra['complete']); self.assertTrue(extra['extra_connections'])
        for changed in (SPEF.replace('*4 ANTENNA0', '*4 \\ANTENNA0'), SPEF.replace('*4:A', '*99:A'),
            SPEF.replace('*4 ANTENNA0', '*4 ANTENNA0\n*4 duplicate')):
            with self.assertRaises(ValueError): O.spef_coverage(changed, inventory())

    def test_native_journal_requires_every_original_call_and_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary).resolve() / 'journal.jsonl'; rows = []
            for index in range(7):
                argv = ['/bin/openroad', '/src/openroad/rcx.tcl'] if index == 0 else \
                    (['sta', '/src/openroad/sta/corner.tcl'] if index % 2 else ['/bin/openroad', '/src/filter_unannotated.py'])
                rows.extend([dict(event='start', call=index, step='OpenROAD.RCX' if index == 0 else 'OpenROAD.STAPostPNR', argv=argv,
                    env={'_OPENLANE_MAX_CORES':'1'}),
                    dict(event='finish', call=index, exit_code=0)])
            path.write_text(''.join(json.dumps(row) + '\n' for row in rows)); self.assertEqual(len(D.calls(path)), 7)
            for changed in (rows[:-2], [dict(row, exit_code=1) if row['event'] == 'finish' else row for row in rows]):
                path.write_text(''.join(json.dumps(row) + '\n' for row in changed))
                with self.assertRaises(ValueError): D.calls(path)

    def test_seed_has_no_carried_metrics_parasitics_or_proof_netlist(self):
        target = dict(actual_odb=dict(path='/candidate/flow/45-final/design.odb', sha256='a' * 64))
        seed = D.seed_for(target, '/candidate/flow')
        self.assertEqual(seed['odb'], '/work/source/45-final/design.odb')
        self.assertEqual(seed['nl'], '/work/views/signoff-views/implemented.v')
        self.assertEqual(seed['def'], '/work/views/design.def')
        self.assertEqual([seed[key] for key in ('spef', 'sdf', 'lib', 'metrics')], [{}, {}, {}, {}])
        changed = deepcopy(target); changed['actual_odb']['path'] = '/other/design.odb'
        with self.assertRaises(ValueError): D.seed_for(changed, '/candidate/flow')

    def test_incomplete_or_promoted_diagnostic_cannot_reopen(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary).resolve() / 'report.json'
            for update in ({'measurements_completed': False}, {'model_qualified': True}, {'qualified_timing': True}):
                report = dict(schema='pinwheel.streaming-8x4-draft-rc-timing-run.v1', measurements_completed=True,
                    inputs_pdk_runtime_unchanged=True, model_qualified=False, qualified_timing=False,
                    physical_acceptance=False, policy=D.policy())
                report.update(update); path.write_text(json.dumps(report))
                with patch.object(D, 'verify', side_effect=AssertionError('reject first')):
                    with self.assertRaises(ValueError): D.closed_report(path)

    def test_retained_execution_rederives_resources_mounts_environment_and_budget(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); lock = D.P.read(D.P.ROOT / 'tools/physical-toolchain.json')
            image = 'sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92'
            self.assertNotEqual(image, lock['container_config_digest'])
            runtime = dict(image_id=image, architecture='arm64', os='linux',
                rootfs_diff_ids=lock['container_rootfs_diff_ids'], runtime_config_sha256=lock['container_runtime_config_sha256'])
            D.P.write(root / 'physical-report.json', {'runtime':runtime})
            D.P.write(root / 'native-source-manifest.json', {'image_id':image})
            record = dict(original_preparation={'path':'/base/preparation.json'}, views_report={'path':'/views/report.json'},
                source_flow='/actual/flow', pdk_root='/actual/pdk',
                target={'physical_report': {'path':str(root / 'physical-report.json')}},
                native_source_manifest={'path':str(root / 'native-source-manifest.json')})
            owner = '00000000-0000-4000-8000-000000000001'
            command = D.container_command(root / 'prepared', root, record, runtime, owner, 'pinwheel-draft-control')
            execution = dict(argv=command, owner=owner, status='completed', exit_code=0, timeout_seconds=1080,
                container_termination={'status':'absent'})
            D.P.write(root / 'execution.json', execution)
            self.assertEqual(D.checked_execution(root, root / 'prepared', record, runtime), execution)
            changed_env = deepcopy(execution); changed_env['argv'][command.index('_OPENLANE_MAX_CORES=1')] = '_OPENLANE_MAX_CORES=4'
            changed_cpu = deepcopy(execution); changed_cpu['argv'][command.index('--cpus') + 1] = '8'
            for changed in (dict(execution, timeout_seconds=1081), changed_env, changed_cpu,
                dict(execution, container_termination={'status':'unconfirmed'})):
                D.P.write(root / 'execution.json', changed)
                with self.assertRaises(ValueError): D.checked_execution(root, root / 'prepared', record, runtime)
            for changed in (dict(runtime, image_id=lock['container_config_digest']),
                dict(runtime, architecture='amd64'), dict(runtime, rootfs_diff_ids=['changed'])):
                with self.assertRaises(ValueError):
                    D.container_command(root / 'prepared', root, record, changed, owner, 'pinwheel-draft-control')
            D.P.write(root / 'native-source-manifest.json', {'image_id':lock['container_config_digest']})
            with self.assertRaises(ValueError):
                D.container_command(root / 'prepared', root, record, runtime, owner, 'pinwheel-draft-control')

    def test_exact_three_pass_commands_and_300s_allowances_reopen(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); interpreter = '/nix/store/fixture-python3-3.13.13/bin/python3'
            identity = dict(schema='pinwheel.streaming-8x4-draft-rc-native-python.v1', executable=interpreter,
                executable_sha256='a' * 64, version='3.13.13 (fixture)', model_qualified=False, qualified_timing=False)
            D.P.write(root / 'native-python.json', identity); rows = []; record = {'request': {'source_odb_sha256':'b' * 64}}
            for model in D.MODELS:
                (root / model).mkdir(); D.P.write(root / model / 'invocation.json', D.invocation(model, 'b' * 64))
                rows.append(dict(model=model, argv=D.pass_command(interpreter, model), status='completed',
                    timeout_seconds=300, exit_code=0, elapsed_seconds=2.5))
            D.P.write(root / 'native-passes.json', rows); self.assertEqual(D.checked_passes(root, record), rows)
            over = deepcopy(rows); over[1]['timeout_seconds'] = 301
            wrong = deepcopy(rows); wrong[2]['argv'][wrong[2]['argv'].index('--model') + 1] = 'TYP'
            for changed in (rows[:2], [*rows, rows[0]], list(reversed(rows)), over, wrong):
                D.P.write(root / 'native-passes.json', changed)
                with self.assertRaises(ValueError): D.checked_passes(root, record)
            D.P.write(root / 'native-passes.json', rows)
            changed = D.invocation('TYP', 'b' * 64); changed['argv'][changed['argv'].index('--from') + 1] = 'OpenROAD.STAPostPNR'
            D.P.write(root / 'TYP/invocation.json', changed)
            with self.assertRaises(ValueError): D.checked_passes(root, record)


if __name__ == '__main__': unittest.main()
