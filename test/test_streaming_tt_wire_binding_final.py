#!/usr/bin/env python3
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_wire_binding_final as W


class FinalBindingTests(unittest.TestCase):
    def test_derivative_requires_exact_original_source_lineage_and_closed_actual(self):
        with tempfile.TemporaryDirectory() as temporary:
            admission=Path(temporary)/'admission';admission.write_text('{}')
            report=dict(schema='pinwheel.streaming-tt-final-run.v1',status='failed',exit_code=1,
                inputs_unchanged_after_run=True,container_termination={'status':'absent'},source_commit='source',producer_commit='actual')
            change=dict(schema='pinwheel.streaming-tt-fanout-derivative.v1',source_odb_sha256='original',
                inherited_metrics=False,inherited_parasitics=False)
            metadata=dict(schema='pinwheel.streaming-tt-final-input.v1',admission=str(admission),admission_sha256='pin',
                source_commit='source',producer_commit='actual',transformation=change)
            def check(r=report,m=metadata):return W.derivative(r,m,admission_path=admission,admission_sha256='pin',
                source_commit='source',source_odb_sha256='original')
            check()
            for bad in (dict(report,exit_code=False),dict(report,status='running'),dict(report,source_commit='other'),
                    dict(report,container_termination={'status':'unknown'}),dict(report,inputs_unchanged_after_run=False)):
                with self.assertRaises(ValueError):check(r=bad)
            for bad in (dict(metadata,admission_sha256='other'),dict(metadata,producer_commit='other'),
                    dict(metadata,transformation=dict(change,source_odb_sha256='different')),
                    dict(metadata,transformation=dict(change,inherited_parasitics=True))):
                with self.assertRaises(ValueError):check(m=bad)

    def test_import_closure_keeps_original_binder_checkpoint_and_actual_exporter(self):
        closure=W.W.dependency_closure(W.P.ROOT,W.ENTRIES)
        for name in ('streaming_tt_wire_binding.py','streaming_tt_export_odb.py','run-streaming-tt-wire.py','run-streaming-tt-sta.py'):
            self.assertIn('scripts/'+name,closure['files'])

    def test_ordinary_route_requires_exact_initial_odb_and_original_native_range(self):
        with tempfile.TemporaryDirectory() as temporary:
            admission=Path(temporary)/'admission';admission.write_text('{}')
            metadata=dict(schema='pinwheel.streaming-tt-final-input.v1',admission=str(admission),admission_sha256='pin',
                source_commit='source',producer_commit='actual',tag='candidate')
            command=['docker','run','image','python3','-B','-m','librelane','--manual-pdk','--pdk-root','/work/pdk',
                '--pdk','ihp-sg13cmos5l','--jobs','4','--run-tag','candidate','--force-run-dir','/work/run',
                '--with-initial-state','/work/inputs/seed.json','--from','OpenROAD.DetailedRouting',
                '--to','Misc.ReportManufacturability','/work/inputs/core.json']
            report=dict(schema='pinwheel.streaming-tt-final-run.v1',status='failed',exit_code=1,
                inputs_unchanged_after_run=True,container_termination={'status':'absent'},source_commit='source',
                producer_commit='actual',from_step='OpenROAD.DetailedRouting',stop_step='Misc.ReportManufacturability',
                native_step_ids=['OpenROAD.STAMidPNR-3',*W.W.F.TAIL],command=command)
            def check(r=report,m=metadata,initial='original'):
                return W.derivative(r,m,admission_path=admission,admission_sha256='pin',source_commit='source',
                    source_odb_sha256='original',initial_snapshot_sha256=initial)
            self.assertEqual(check(),'admitted-detailed-routing')
            for initial in (None,'different'):
                with self.assertRaises(ValueError):check(initial=initial)
            for changed in (dict(report,from_step='OpenROAD.GlobalRouting'),dict(report,command=command+['--skip','Checker.TrDRC']),
                    dict(report,native_step_ids=['OpenROAD.STAMidPNR-3',*W.W.F.TAIL[:-1]])):
                with self.assertRaises(ValueError):check(r=changed)
            with self.assertRaises(ValueError):check(m=dict(metadata,admission_sha256='other'))
            with self.assertRaises(ValueError):check(m=dict(metadata,source_commit='other'))

    def test_explicit_source_selection_and_unknown_transformations_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            source=Path(temporary)/'source';source.write_text('{}');other=Path(temporary)/'other';other.write_text('{}')
            metadata={'transformation':{'schema':'pinwheel.streaming-tt-fanout-derivative.v1',
                'source_readback_host':{'path':str(source),'sha256':W.P.sha(source)}}}
            self.assertEqual(W.source_selection({},source),source.resolve())
            self.assertEqual(W.source_selection(metadata,None),source.resolve())
            for m,explicit in [({},None),(metadata,other),({'transformation':None},source),
                    ({'transformation':{'schema':'unknown'}},source)]:
                with self.assertRaises(ValueError):W.source_selection(m,explicit)
            source.write_text('{"changed":true}')
            with self.assertRaises(ValueError):W.source_selection(metadata,source)


if __name__=='__main__':unittest.main()
