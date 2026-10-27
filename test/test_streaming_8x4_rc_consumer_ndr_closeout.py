"""HOST proposal/resource/error-preservation controls; no Native command runs."""
import copy
from historical_evidence import historical_evidence
import streaming_8x4_consumer_fixtures as F
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_rc_consumer_ndr_closeout as W


class NDRCloseout(unittest.TestCase):
    def proposal(self):
        return W.proposal(W.BASE/'rc-consumer-units-command-proposal-01.json',W.BASE/'rc-consumer-ndr-preparation-01',require_fresh=False)

    def resource(self,record,path):
        required=dict(record['input_seals_required']);required[str(path.resolve())]=W.N.C.P.sha(path)
        supervisor=W.N.C.P.sha(W.ROOT/'scripts/streaming_tt_resources.py')
        return dict(schema='pinwheel.streaming-tt-resource-job.v1',argv=record['argv'],timeout_seconds=300,
            status='failed',exit_code=2,cleanup_confirmed=True,inputs_unchanged=True,containers_remaining=[],
            owned_processes_remaining=[],cleanup_errors=[],input_sha256=required,supervisor_sha256=supervisor,
            campaign_boundary=dict(schema='pinwheel.streaming-8x4-resource-boundary.v1',campaign_root=str(W.ROOT),
                campaign_kind='rc_experiment',shared_lease=dict(heavy_lock=str(W.ROOT/'build/streaming-tt-resources/heavy.lock')),
                wrapper_sha256=W.N.C.P.sha(W.ROOT/'scripts/streaming_8x4_acceptance_resources.py'),
                inherited_supervisor_sha256=supervisor))

    @historical_evidence
    def test_real_frozen_proposal_changes_exactly_five_identity_tokens(self):
        result=self.proposal();old=json.loads((W.BASE/'rc-consumer-units-command-proposal-01.json').read_text())
        self.assertEqual(sum(a!=b for a,b in zip(result['argv'],old['argv'])),5)
        self.assertEqual(len(result['argv']),len(old['argv']))
        for flag in ('--network','--cpus','--memory','--memory-swap','--pids-limit','--tmpfs','--entrypoint'):
            self.assertEqual(result['argv'][result['argv'].index(flag)+1],old['argv'][old['argv'].index(flag)+1])
        self.assertEqual(result['timeout_seconds'],300);self.assertEqual(result['maximum_calls'],6)
        self.assertEqual(result['plan_sha256'],W.PLAN_SHA)
        self.assertFalse(result['admitted']);self.assertFalse(result['native_executed'])

    def test_numeric_failure_still_has_separate_exact_resource_custody(self):
        record=F.resource_record(W.ROOT)
        worker=dict(schema='pinwheel.streaming-8x4-rc-consumer-DEF-NDR-execution.v1',plan_sha256=W.PLAN_SHA,
            passed=False,qualified=False,model_qualified=False)
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'proposal.json';W.N.write(path,record);resource=self.resource(record,path)
            facts=W.resource_facts(resource,record,path,worker)
            self.assertTrue(facts['resource_custody_closed']);self.assertFalse(facts['numeric_acceptance_claim'])
            self.assertEqual(facts['actual_exit_code'],2);self.assertTrue(facts['exact_worker_numeric_exit_contract_checked'])
            for changed in [dict(resource,timeout_seconds=301),dict(resource,cleanup_confirmed=False),
                dict(resource,input_sha256={}),dict(resource,owned_processes_remaining=[123]),
                dict(resource,status='completed',exit_code=0),dict(resource,argv=['different'])]:
                with self.assertRaises(ValueError):W.resource_facts(changed,record,path,worker)
            stopped=dict(resource,status='stopped',exit_code=124)
            facts=W.resource_facts(stopped,record,path,None)
            self.assertTrue(facts['resource_custody_closed']);self.assertFalse(facts['worker_report_available'])

    def test_raw_prefix_error_is_retained_without_losing_resource_artifact(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();directory=root/'native';directory.mkdir();inputs=root/'inputs';inputs.mkdir()
            proposal=root/'proposal.json';proposal.write_text('{}')
            resource=root/'build/streaming-tt-resources'/W.TAG/'report.json';resource.parent.mkdir(parents=True)
            resource.write_text('{}');resource_out=root/'resource.json';raw_out=root/'raw.json';output=root/'closeout.json'
            record=dict(plan_path=str(inputs/'plan.json'),output_directory=str(directory))
            with patch.object(W,'ROOT',root),patch.object(W,'checked_proposal',return_value=record),\
                 patch.object(W,'resource_facts',return_value=dict(resource_custody_closed=True)),\
                 patch.object(W.R,'readback',side_effect=ValueError('Incomplete strict six-call packet')):
                result=W.closeout(proposal,resource,resource_out,raw_out,output)
            self.assertTrue(result['resource_custody_closed']);self.assertFalse(result['numeric_passed'])
            self.assertFalse(result['all_six_native_calls_closed'])
            self.assertTrue(resource_out.is_file());self.assertIn('Incomplete strict six-call',json.loads(raw_out.read_text())['error'])
            self.assertFalse(result['native_executed_by_closeout'])


if __name__=='__main__':unittest.main()
