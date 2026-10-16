import copy
import unittest
from lvs_case_verdict_v8 import EXPECTED,native_case_verdict

class ObservedCases(unittest.TestCase):
    def test_exact_observed_semantics_and_corrupt_contact_graph(self):
        for case,e in EXPECTED.items():
            text='Final result: '+e['final']+'\n'
            self.assertTrue(native_case_verdict(case,text,e['top'],e['mutation'])['targeted_native_evidence_verified'])
            for key in ('devices','nets','pins','badnets'):
                top=copy.deepcopy(e['top']);top[key]=[] if top[key] else [['unrelated fault']]
                self.assertFalse(native_case_verdict(case,text,top,e['mutation'])['targeted_native_evidence_verified'])
    def test_wrong_verdict_or_source_mutation_rejected(self):
        e=EXPECTED['macro-detached-VSS']
        with self.assertRaises(AssertionError):native_case_verdict('macro-detached-VSS','Final result: Circuits match uniquely.\n',e['top'],e['mutation'])
        with self.assertRaises(AssertionError):native_case_verdict('macro-detached-VSS','Final result: '+e['final']+'\n',e['top'],{})

if __name__=='__main__':unittest.main()
