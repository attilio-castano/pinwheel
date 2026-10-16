import copy
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lvs_case_verdict_v7 import native_case_verdict as check

class CaseVerdict(unittest.TestCase):
    def test_exact_macro_open_native_shape(self):
        top={'pins':[['P'+str(i) for i in range(349)]+['M0','(no pin)'], ['P'+str(i) for i in range(349)]+['(no matching pin)','M0']], 'badnets':[], 'badelements':[]}
        fault={'changed_terminals':[{'instance':'memory','pin':'A_ADDR[5]','before':'M0','after':'PW_LVS_NEG_MACRO_OPEN'}]}
        self.assertTrue(check('macro-detached-signal','Final result: Top level cell failed pin matching.\n',top,fault)['targeted_native_evidence_verified'])
        wrong=copy.deepcopy(top);wrong['pins'][0][-2]='M8';wrong['pins'][1][-1]='M8'
        self.assertFalse(check('macro-detached-signal','Final result: Top level cell failed pin matching.\n',wrong,fault)['targeted_native_evidence_verified'])
        self.assertFalse(check('macro-detached-signal','Final result: Circuits match uniquely.\n',top,fault)['targeted_native_evidence_verified'])
    def test_unknown_or_ambiguous_verdict_rejected(self):
        top={'pins':[[],[]]}
        for text in ['Final result: Unexpected failure.\n','Final result: Circuits match uniquely.\nFinal result: Netlists do not match.\n']:
            with self.assertRaises(AssertionError):check('positive',text,top,{})
    def test_empty_or_wrong_target_graph_is_not_sensitivity(self):
        top={'pins':[[],[]],'badnets':[]}
        mutation={'changed_terminals':[{}]}
        self.assertFalse(check('removed-terminal','Final result: Netlists do not match.\n',top,mutation)['targeted_native_evidence_verified'])
        top['badnets']=[['unrelated-net']]
        self.assertFalse(check('removed-terminal','Final result: Netlists do not match.\n',top,mutation)['targeted_native_evidence_verified'])
    def test_macro_pin_failure_not_generic_widening(self):
        top={'pins':[['M0'],['(no matching pin)']],'badnets':[]}
        self.assertFalse(check('macro-detached-VSS','Final result: Top level cell failed pin matching.\n',top,{'changed_terminals':[]})['targeted_native_evidence_verified'])

if __name__=='__main__':unittest.main()
