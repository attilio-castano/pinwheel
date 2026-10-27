"""Focused HOST controls for a diagnostic replay; no CAD, Docker or solver."""
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from historical_evidence import historical_evidence

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_8x4_route_replay as X


def fixture(diodes=0):
    rows = ['TOP\t' + X.TOP, 'INST\tdriver\tbuf\t0\t0\tR0\tPLACED',
        'INST\tload\tinv\t100\t0\tR0\tPLACED', 'ITERM\tdriver\tX\tOUTPUT\tSIGNAL\tn',
        'ITERM\tload\tA\tINPUT\tSIGNAL\tn', 'NET\tn\tSIGNAL\t' + str(2 + diodes) + '\t1',
        'BTERM\tport\tOUTPUT\tSIGNAL\tn']
    for i in range(diodes):
        rows.extend(['INST\tANTENNA_' + str(i) + '\tsg13cmos5l_antennanp\t' + str(i) + '\t0\tR0\tPLACED',
            'ITERM\tANTENNA_' + str(i) + '\tA\tINPUT\tSIGNAL\tn'])
    return '\n'.join(rows) + '\n'


class Replay(unittest.TestCase):
    def test_fixed_route_config_rejects_policy_drift_without_historical_inputs(self):
        config = dict(OPENROAD_THREADS=4, RT_MIN_LAYER='Metal2', RT_MAX_LAYER='Metal4',
            CLOCK_PERIOD=20, DRT_OPT_ITERS=64, GRT_ANTENNA_REPAIR_MARGIN=10,
            DRT_ANTENNA_REPAIR_MARGIN=10, GRT_ALLOW_CONGESTION=False,
            DRT_ANTENNA_REPAIR_JUMPER_ONLY=False, DRT_ANTENNA_REPAIR_DIODE_ONLY=False,
            DRT_SAVE_SNAPSHOTS=False, DRT_SAVE_DRC_REPORT_ITERS=None,
            NON_DEFAULT_RULES=None, DRT_ASSIGN_NDR=None, DRT_DISABLE_AUTO_TAPER=None,
            DIODE_CELL='sg13cmos5l_antennanp', PNR_SDC_FILE='/work/inputs/core.sdc',
            DESIGN_NAME='tt_um_pinwheel_streaming_ready_d2')
        self.assertEqual(X.validate_config(config), config)
        for key, value in [('OPENROAD_THREADS', 2), ('RT_MIN_LAYER', 'Metal1'),
            ('DRT_OPT_ITERS', 6), ('DRT_ANTENNA_REPAIR_DIODE_ONLY', True),
            ('GRT_ANTENNA_REPAIR_MARGIN', 11)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                X.validate_config(dict(config, **{key: value}))

    @historical_evidence
    def test_actual_parent_config_and_source_reopen(self):
        b = X.P.ROOT / 'build/campaigns/8x4-20261022-01'
        config = X.P.read(b / 'native-repair-02/flow/03-openroad-detailedrouting/config.json')
        X.validate_config(config)
        source = b / 'intake/routing-replay-source-02'
        self.assertEqual(len(X.source_evidence(source)), 13)
        self.assertEqual(X.sha(source / 'manifest.json'), X.SOURCE_SHA)
        for key, value in [('OPENROAD_THREADS', 2), ('RT_MIN_LAYER', 'Metal1'), ('DRT_OPT_ITERS', 6),
            ('DRT_ANTENNA_REPAIR_DIODE_ONLY', True), ('GRT_ANTENNA_REPAIR_MARGIN', 11)]:
            bad = dict(config, **{key: value})
            with self.assertRaises(ValueError): X.validate_config(bad)

    def test_complete_census_and_exact_39_diodes(self):
        result = X.fanout_delta(fixture(), fixture(39))
        self.assertEqual(len(result['added_diodes']), 39)
        self.assertEqual(result['touched_nets'][0]['before_loads_per_single_driver'], 2)
        self.assertEqual(result['touched_nets'][0]['after_loads_per_single_driver'], 41)
        for text in [fixture(38), fixture(40), fixture(39).replace('sg13cmos5l_antennanp', 'other', 1),
            fixture(39).replace('ITERM\tload\tA\tINPUT\tSIGNAL\tn', 'ITERM\tload\tA\tINPUT\tSIGNAL\t')]:
            with self.assertRaises(ValueError): X.fanout_delta(fixture(), text)

    def test_census_omission_duplicate_wrong_top_reject(self):
        for text in [fixture().replace(X.TOP, 'wrong'), fixture() + 'NET\tn\tSIGNAL\t2\t1\n',
            fixture().replace('ITERM\tload\tA\tINPUT\tSIGNAL\tn\n', ''),
            fixture().replace('NET\tn\tSIGNAL\t2\t1', 'NET\tn\tPOWER\t2\t1'),
            fixture().replace('INST\tload\tinv\t100\t0\tR0\tPLACED\n', '')]:
            with self.assertRaises(ValueError): X.census(text)

    def test_reproduction_all_counts_strict(self):
        text = 'net_violations\t35\npin_violations\t36\ninserted_diodes\t39\nbefore_instances\t42138\nafter_instances\t42177\n'
        self.assertEqual(X.reproduction(text)['inserted_diodes'], 39)
        for bad in [text.replace('35', '34'), text.replace('36', '35'), text.replace('39', '38'),
            text.replace('42177', '42178'), text + 'pin_violations\t36\n']:
            with self.assertRaises(ValueError): X.reproduction(bad)

    def test_gate_precedes_route_and_snapshots_survive_later_failure(self):
        body = X.replay_tcl()
        self.assertLess(body.index('35net/36pin'), body.index('repair_antennas sg13'))
        self.assertLess(body.index('replay_capture $replay/postdiode'), body.index('39diode reproduction failed'))
        self.assertLess(body.index('39diode reproduction failed'), body.index('log_cmd detailed_route'))
        self.assertIn('-droute_end_iter 6 -or_seed 42 -verbose 1 -drc_report_iter_step 1', body)
        self.assertNotIn('repair_design', body)
        self.assertNotIn('write_views', body)

    def test_closed_controller_required_for_diagnostic_success(self):
        observed = dict(bounded_route_returned=True)
        closed = dict(status='completed', exit_code=0, container_termination=dict(status='absent'))
        self.assertTrue(X.diagnostic_completed(observed, closed))
        for key, value in [('status', 'timed_out'), ('status', 'interrupted'), ('exit_code', 124),
            ('container_termination', dict(status='remaining'))]:
            self.assertFalse(X.diagnostic_completed(observed, dict(closed, **{key: value})))

    @historical_evidence
    def test_pinned_source_extra_member_rejects(self):
        source = X.P.ROOT / 'build/campaigns/8x4-20261022-01/intake/routing-replay-source-02'
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary).resolve() / 'source'; shutil.copytree(source, target)
            X.source_evidence(target); (target / 'extra').write_text('extra')
            with self.assertRaises(ValueError): X.source_evidence(target)

    def test_actual_command_journal_requires_one_closed_four_thread_call(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); (root / 'inputs').mkdir()
            config = dict(DEFAULT_CORNER='nom', CELL_LIBS=dict(nom=['/a.lib', '/b.lib']))
            X.P.write(root / 'inputs/config.json', config)
            env = dict(CURRENT_ODB='/work/seed.odb', PNR_SDC_FILE='/work/inputs/core.sdc',
                _SDC_IN='/work/inputs/core.sdc', OPENROAD_THREADS='4', RT_MIN_LAYER='Metal2', RT_MAX_LAYER='Metal4',
                DRT_OPT_ITERS='64', GRT_ANTENNA_REPAIR_MARGIN='10', DIODE_CELL='sg13cmos5l_antennanp',
                _LIB_CORNER_0='nom /a.lib /b.lib')
            row = dict(event='start', step='Pinwheel.RouteReplayDiagnostic', executable_sha256='a' * 64, env=env,
                argv=['/nix/store/runtime/bin/openroad', '-exit', '-threads', '4', '-no_splash', '-metrics',
                    '/work/replay/step/or_metrics_out.json', '/work/replay/inputs/replay.tcl'])
            rows = [row, dict(event='finish', exit_code=0)]
            def write(value): (root / 'native-journal.jsonl').write_text(''.join(json.dumps(v) + '\n' for v in value))
            write(rows); X.journal(root)
            for key, value in [('CURRENT_ODB', '/wrong.odb'), ('_SDC_IN', '/wrong.sdc'), ('OPENROAD_THREADS', '2')]:
                bad = copy.deepcopy(rows); bad[0]['env'][key] = value; write(bad)
                with self.assertRaises(ValueError): X.journal(root)
            for bad in [rows[:1], rows + rows, [row, dict(event='finish', exit_code=1)]]:
                write(bad)
                with self.assertRaises(ValueError): X.journal(root)

    def test_resource_policy_never_conveys_final_target(self):
        policy = X.policy()
        self.assertEqual((policy['cpus'], policy['memory_gib'], policy['leaf_seconds'], policy['work_seconds'], policy['outer_seconds']),
            (4, 6, 1770, 1800, 1860))
        for key in ('new_physical_candidate', 'physical_delta', 'completed_DetailedRouting', 'eligible_final_target',
            'qualified', 'physical_acceptance', 'historical_placements_identical'):
            self.assertIs(policy[key], False)

    def test_empty_return_printed_revision_is_strictly_observed(self):
        observations = {'describe-return': '', 'describe-printed': X.COMMIT + '\n',
            'version-return': '', 'version-printed': ''}
        self.assertEqual(X.version_identity(observations), X.COMMIT)
        self.assertEqual(X.version_identity(dict(observations, **{'describe-printed': '', 'version-return': X.COMMIT})), X.COMMIT)
        for bad in [dict(observations, **{'describe-printed': ''}),
            dict(observations, **{'describe-printed': 'a' * 40}),
            dict(observations, **{'version-return': 'a' * 40}),
            dict(observations, **{'describe-printed': X.COMMIT[:8]}),
            dict(observations, **{'describe-printed': X.COMMIT + '0'}),
            dict(observations, **{'version-return': '0' + X.COMMIT})]:
            with self.assertRaises(ValueError): X.version_identity(bad)
        body = X.replay_tcl()
        self.assertIn('tee -variable describe_printed {ord::openroad_git_describe}', body)
        self.assertIn('tee -variable version_printed {ord::openroad_version}', body)
        self.assertLess(body.index('Pinned OpenROAD revision mismatch'), body.index('replay_capture $replay/before'))


if __name__ == '__main__': unittest.main()
