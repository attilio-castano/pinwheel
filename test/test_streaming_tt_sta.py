"""Timing cannot inherit earlier metrics or substitute estimates for SPEF."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_sta import fresh_views


class FreshSTATests(unittest.TestCase):
    def test_only_explicit_odb_and_empty_metrics_for_nominal_probe(self):
        request=dict(schema='pinwheel.streaming-tt-fresh-sta-request.v1',mode='nominal',views={'odb':'actual.odb'})
        self.assertEqual(fresh_views(request),dict(odb='actual.odb',metrics={}))
        for key,value in [('metrics',{'timing__setup__ws':42}),('sdf','old.sdf'),('spef',{'nom_*':'old.spef'}),('nl','old.v')]:
            bad=deepcopy(request);bad['views'][key]=value
            with self.assertRaisesRegex(ValueError,'inherited/missing'):fresh_views(bad)

    def test_extracted_probe_requires_all_final_views_and_exact_parasitic_scope(self):
        request=dict(schema='pinwheel.streaming-tt-fresh-sta-request.v1',mode='extracted',
            views=dict(odb='actual.odb',nl='exported-from-actual-odb.v',spef={'nom_*':'actual.spef'}))
        self.assertEqual(fresh_views(request)['metrics'],{})
        for value in (None,'actual.spef',{}, {'min_*':'nominal-disguised.spef'}, {'nom_*':'actual.spef','max_*':'invented.spef'}):
            bad=deepcopy(request);bad['views']['spef']=value
            with self.assertRaisesRegex(ValueError,'nominal extracted SPEF'):fresh_views(bad)
        for key in ('odb','nl','spef'):
            bad=deepcopy(request);del bad['views'][key]
            with self.assertRaisesRegex(ValueError,'inherited/missing'):fresh_views(bad)


if __name__=='__main__':unittest.main()
