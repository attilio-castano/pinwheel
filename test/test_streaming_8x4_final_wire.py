"""Focused rejection tests; never launch the final-wire Native worker."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_final_wire as W


class FinalWire(unittest.TestCase):
    def test_unbounded_allowance_rejects_before_authority_or_execution(self):
        with patch.object(W.A,'verify',side_effect=AssertionError('must not use authority')):
            for timeout in (0,7201,True,900.0):
                with self.assertRaises(ValueError):W.run('/missing','/missing',timeout)

    def test_complete_actual_worker_contract_is_required(self):
        config=dict(source_commit='a'*40,producer_commit='a'*40,physical_stage='actual-final')
        value=dict(passed=True,qualified=False,physical_acceptance_claim=False,source_commit='a'*40,
            producer_commit='a'*40,physical_ff_bits=6039,native_processes=14,inputs_unchanged=True,
            generated_inputs_unchanged=True,clock_contraction=False,stage='closed',physical_stage='actual-final')
        W.worker_result(value,config)
        for key,bad in [('native_processes',13),('physical_ff_bits',6038),('clock_contraction',True),
            ('stage','running'),('physical_stage','probe'),('qualified',True)]:
            with self.subTest(key=key):
                with self.assertRaises(ValueError):W.worker_result(dict(value,**{key:bad}),config)


if __name__=='__main__':unittest.main()
