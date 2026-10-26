"""HOST exact command adaptation and separate failed-resource custody controls."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_rc_consumer_semantic_closeout as X


class SemanticCloseoutControls(unittest.TestCase):
    def record(self):
        return X.proposal(X.BASE / 'rc-consumer-ndr-command-proposal-01.json',
            X.BASE / 'rc-consumer-semantic-preparation-01', require_fresh=False)

    def test_only_five_command_identity_tokens_change_and_all_resources_stay(self):
        old = X.OLD.checked_proposal(X.BASE / 'rc-consumer-ndr-command-proposal-01.json'); new = self.record()
        self.assertEqual(len(new['argv']), len(old['argv']))
        self.assertEqual(sum(a != b for a, b in zip(old['argv'], new['argv'])), 5)
        self.assertEqual(new['timeout_seconds'], 300); self.assertEqual(new['work_seconds'], 210)
        self.assertEqual(new['maximum_calls'], 6); self.assertFalse(new['native_executed'])
        self.assertEqual(new['container_name'], 'pinwheel-8x4-rc-consumer-semantic-01')
        for path, pin in new['input_seals_required'].items(): self.assertEqual(X.N.C.P.sha(path), pin)

    def resource(self, record, proposal):
        seals = dict(record['input_seals_required']); seals[str(proposal.resolve())] = X.N.C.P.sha(proposal)
        supervisor = X.N.C.P.sha(ROOT / 'scripts/streaming_tt_resources.py')
        return dict(schema='pinwheel.streaming-tt-resource-job.v1', status='failed', exit_code=2,
            argv=record['argv'], timeout_seconds=300, cleanup_confirmed=True, inputs_unchanged=True,
            containers_remaining=[], owned_processes_remaining=[], cleanup_errors=[], input_sha256=seals,
            supervisor_sha256=supervisor, campaign_boundary=dict(schema='pinwheel.streaming-8x4-resource-boundary.v1',
                campaign_root=str(ROOT), campaign_kind='rc_experiment',
                shared_lease=dict(heavy_lock=str(ROOT / 'build/streaming-tt-resources/heavy.lock')),
                wrapper_sha256=X.N.C.P.sha(ROOT / 'scripts/streaming_8x4_acceptance_resources.py'),
                inherited_supervisor_sha256=supervisor))

    def test_failed_numeric_worker_can_close_custody_without_numeric_promotion(self):
        record = self.record(); worker = dict(schema='pinwheel.streaming-8x4-rc-consumer-route-execution.v1',
            plan_sha256=X.PLAN_SHA, passed=False, qualified=False, model_qualified=False)
        with tempfile.TemporaryDirectory() as temporary:
            p = Path(temporary) / 'proposal.json'; p.write_text(json.dumps(record))
            facts = X.resource_facts(self.resource(record, p), record, p, worker)
            self.assertTrue(facts['resource_custody_closed']); self.assertFalse(facts['numeric_acceptance_claim'])
            self.assertTrue(facts['exact_worker_numeric_exit_contract_checked'])
            for changes in ({'timeout_seconds':301}, {'argv':['foreign']}, {'input_sha256':{}},
                {'cleanup_confirmed':False}, {'containers_remaining':['live']}, {'exit_code':1}):
                resource = self.resource(record, p); resource.update(changes)
                with self.assertRaises(ValueError): X.resource_facts(resource, record, p, worker)

    def test_launch_reopen_binds_exact_root_lease_and_separate_raw_outputs(self):
        record = self.record()
        with tempfile.TemporaryDirectory() as temporary:
            p = Path(temporary) / 'proposal.json'; p.write_text(json.dumps(record))
            packet = X.launch_reopen(p, record); argv = packet['resource_supervisor_argv']
            self.assertEqual(argv[argv.index('--tag') + 1], X.TAG)
            self.assertEqual(argv[argv.index('--timeout-seconds') + 1], '300')
            self.assertEqual(argv[argv.index('--kind') + 1], 'solver')
            self.assertEqual(argv[argv.index('--') + 1:], record['argv'])
            self.assertTrue(packet['HOST_only_after_actual_terminal_and_Root_signal'])
            self.assertTrue(packet['resource_cleanup_does_not_promote_numeric_result'])


if __name__ == '__main__': unittest.main()
