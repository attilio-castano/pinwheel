"""The physical mapped factory must instantiate every inherited semantic API."""
from pathlib import Path
import re
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_mapped_composition import generate
from streaming_mapped_device import JOIN_THEOREMS


class CompositionTests(unittest.TestCase):
    def test_both_factories_bind_actual_mapped_components_package_and_pads(self):
        for a in (1,2):
            depth=2**a;texts=generate(a);self.assertEqual(list(texts),['StreamingMappedSessionD'+str(depth)])
            text=next(iter(texts.values()))
            for name in ('MappedCoreD'+str(depth)+'Proof','MappedFrontendProof','StreamingMappedPackageD'+str(depth),'StreamingMappedTinyD'+str(depth)):
                self.assertIn('import '+name,text)
            for name in JOIN_THEOREMS:self.assertEqual(len(re.findall(r'(?m)^theorem '+name+r'\b',text)),1)
            self.assertEqual(len(JOIN_THEOREMS),22);self.assertEqual(len(set(JOIN_THEOREMS)),22)
            self.assertIn('Pinwheel.Artifact.StreamingMappedFrontend.behavior',text)
            self.assertIn('Pinwheel.Artifact.StreamingMappedCoreD'+str(depth)+'.behavior',text)
            for forbidden in ('import ReadyCore','import ReadyQuadFrontend','StreamingReadyWrappers','native_decide','bv_decide','sorry','axiom '):
                self.assertNotIn(forbidden,text)

    def test_unsupported_or_boolean_queue_width_refuses(self):
        for a in (True,False,0,3,'1',None):
            with self.subTest(a=a),self.assertRaises(ValueError):generate(a)


if __name__=='__main__':unittest.main()
