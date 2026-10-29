"""Scoped HOST controls for a new repair authority; no CAD runs."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_postantenna_repair as C


class PostAntennaRepair(unittest.TestCase):
    def test_only_declared_step_and_resource_delta(self):
        # Exact observed native schedule: the gated resizer remains scheduled
        # even though original RUN_POST_GRT_RESIZER_TIMING=false skipped it.
        base=['OpenROAD.RepairAntennas','OpenROAD.ResizerTimingPostGRT','OpenROAD.STAMidPNR-3',*C.R.TAIL]
        added=[base[0],C.STEP,*base[1:]]
        self.assertEqual(C.validate_order(base,added)['added_canonical_step'],C.STEP)
        for changed in (base,[*added,'Unapproved.Step'],[base[0],C.STEP,*base[2:]],
            [base[0],base[1],C.STEP,*base[2:]], [base[0],C.STEP,base[2],base[1],*base[3:]]):
            with self.assertRaises(ValueError):C.validate_order(base,changed)
        for threads in (1,2,4):
            value=C.candidate_delta(threads)
            self.assertEqual((value['placement_density_pct'],value['clock_ns'],value['drt_opt_iters']),(85,20,64))
            self.assertEqual(value['resource_override'],{'OPENROAD_THREADS':{'before':4,'after':threads}})
        for threads in (0,3,8,True,2.0):
            with self.assertRaises(ValueError):C.candidate_delta(threads)
        original=dict(OPENROAD_THREADS=4,GRT_DESIGN_REPAIR_RUN_GRT=True,DRT_OPT_ITERS=64,
            PL_TARGET_DENSITY_PCT=85,CLOCK_PERIOD=20)
        self.assertEqual(C.resolved_delta(original,dict(original,OPENROAD_THREADS=2),2),{'OPENROAD_THREADS':{'before':4,'after':2}})
        for key,value in [('DRT_OPT_ITERS',32),('PL_TARGET_DENSITY_PCT',65),('CLOCK_PERIOD',30),('GRT_DESIGN_REPAIR_RUN_GRT',False)]:
            with self.assertRaises(ValueError):C.resolved_delta(original,dict(original,OPENROAD_THREADS=2,**{key:value}),2)

    def test_seed_translates_only_explicit_readonly_parent_views_and_keeps_raw_metrics(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();flow=root/'parent/flow';stage=flow/'35-openroad-repairantennas'
            actual=stage/'1-openroad-diodeinsertion/design.odb';actual.parent.mkdir(parents=True);actual.write_bytes(b'actual diode ODB')
            prepared=root/'prepared';(prepared/'inputs').mkdir(parents=True);(prepared/'inputs/core.sdc').write_text('create_clock')
            pdk=root/'pdk';pdk.mkdir();state=stage/'state_out.json'
            raw=dict(odb='/work/run/35-openroad-repairantennas/1-openroad-diodeinsertion/design.odb',
                sdc='/work/inputs/core.sdc',metrics={'native_nonfinite':float('inf')})
            state.write_text(json.dumps(raw)+'\n');before=C.sha(state)
            seed,views=C.seed_from_parent(root/'parent',state,prepared,pdk)
            self.assertEqual(seed['odb'],'/work/parent/35-openroad-repairantennas/1-openroad-diodeinsertion/design.odb')
            self.assertEqual(seed['sdc'],raw['sdc']);self.assertEqual(seed['metrics'],raw['metrics']);self.assertEqual(C.sha(state),before)
            self.assertEqual(views[raw['odb']]['sha256'],C.sha(actual))
            stage36=flow/'36-openroad-stamidpnr-3';stage36.mkdir();state36=stage36/'state_out.json'
            state36.write_text(json.dumps(raw));C.seed_from_parent(root/'parent',state36,prepared,pdk)
            other=actual.with_name('another.odb');other.write_bytes(b'another database in same directory')
            state36.write_text(json.dumps(dict(raw,odb='/work/run/35-openroad-repairantennas/1-openroad-diodeinsertion/another.odb')))
            with self.assertRaisesRegex(ValueError,'measured actual'):C.seed_from_parent(root/'parent',state36,prepared,pdk)
            raw['odb']='/work/run/../../unowned.odb';state.write_text(json.dumps(raw))
            with self.assertRaises(ValueError):C.seed_from_parent(root/'parent',state,prepared,pdk)

    def test_closed_failed137_parent_is_seed_evidence_without_final_route(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();run=root/'failed';run.mkdir();prepared=root/'prepared';prepared.mkdir()
            C.P.write(prepared/'preparation.json',{});artifact=run/'native.log';artifact.write_text('failed137; no DRT state')
            report=dict(schema='pinwheel.streaming-8x4-native-run.v1',mode='full',status='failed',exit_code=137,
                inputs_pdk_runtime_unchanged=True,container_termination={'status':'absent'},qualified=False,physical_acceptance=False,
                prepared=str(prepared),prepared_input_sha256=C.sha(prepared/'preparation.json'),producer_sha256={},
                source_ff_bits=6039,clock_period_ns=20,tiles='8x4',artifact_sha256={'native.log':C.sha(artifact)})
            C.P.write(run/'report.json',report)
            resource=dict(schema='pinwheel.streaming-tt-resource-job.v1',cleanup_confirmed=True,inputs_unchanged=True,
                containers_remaining=[],owned_processes_remaining=[],exit_code=137,pid=21023,argv=['runner','--output',str(run)])
            C.P.write(root/'resource.json',resource)
            self.assertEqual(C.closed_parent(run/'report.json',root/'resource.json',prepared,{'producer_sha256':{}})['exit_code'],137)
            identity=dict(pid=21023,pgid=21023,birth='Thu Oct 22 17:33:52 2026',command='exact frozen owned worker command')
            intent=dict(schema='pinwheel.streaming-8x4-root-stop-intent.v1',root_owned=True,
                parent_report_path=str(run/'report.json'),parent_resource_path=str(root/'resource.json'),
                resource_argv=resource['argv'],identity=identity,signal_number=15,intent_utc='2026-10-22T22:30:00Z')
            C.P.write(root/'intent.json',intent)
            dispatch=dict(schema='pinwheel.streaming-8x4-root-stop-authority.v1',intent=C.bound(root/'intent.json'),
                observations=[identity,identity],signal_number=15,signal_returncode=0,signal_sent=True,dispatched_utc='2026-10-22T22:30:01Z')
            C.P.write(root/'stop.json',dispatch)
            for status,code in [('interrupted',130),('timed_out',124)]:
                report.update(status=status,exit_code=code);resource['exit_code']=code
                if status=='timed_out':report['stop_reason']='native_wall_time_limit'
                else:report['stop_reason']='signal 15'
                C.P.write(run/'report.json',report);C.P.write(root/'resource.json',resource)
                stop=root/'stop.json' if status=='interrupted' else None
                if status=='interrupted':
                    with self.assertRaisesRegex(ValueError,'stop authority'):C.closed_parent(run/'report.json',root/'resource.json',prepared,{'producer_sha256':{}})
                    changed=dict(dispatch,observations=[identity,dict(identity,birth='different PID lifetime')]);C.P.write(root/'stop.json',changed)
                    with self.assertRaises(ValueError):C.closed_parent(run/'report.json',root/'resource.json',prepared,{'producer_sha256':{}},stop)
                    C.P.write(root/'stop.json',dispatch)
                self.assertEqual(C.closed_parent(run/'report.json',root/'resource.json',prepared,{'producer_sha256':{}},stop)['exit_code'],code)
            report.update(status='failed',exit_code=137);resource['exit_code']=137
            C.P.write(run/'report.json',report);C.P.write(root/'resource.json',resource)
            with self.assertRaises(ValueError):C.select_report(run/'report.json',C.sha(run/'report.json'),prepared,{})
            resource['cleanup_confirmed']=False;C.P.write(root/'resource.json',resource)
            with self.assertRaises(ValueError):C.closed_parent(run/'report.json',root/'resource.json',prepared,{'producer_sha256':{}})

    def test_final_selection_requires_fresh_repair_and_detailed_route(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary).resolve();run=root/'repair';(run/'flow').mkdir(parents=True);(run/'metadata').mkdir()
            original=root/'original';original.mkdir();C.P.write(original/'preparation.json',{})
            prep=root/'prepared';prep.mkdir();C.P.write(prep/'preparation.json',{})
            base=['OpenROAD.RepairAntennas','OpenROAD.ResizerTimingPostGRT','OpenROAD.STAMidPNR-3',*C.R.TAIL];actual=[base[0],C.STEP,*base[1:]]
            order=C.validate_order(base,actual);order.update(schema='pinwheel.streaming-8x4-repair-native-order.v1',openroad_threads=2,qualified=False)
            C.P.write(run/'metadata/flow-order.json',order)
            rowroot=run/'flow/01-openroad-postantennadesignrepair';rowroot.mkdir();odb=rowroot/'design.odb';odb.write_bytes(b'fresh repaired ODB')
            state=rowroot/'state_out.json';C.P.write(state,{'odb':'/work/run/01-openroad-postantennadesignrepair/design.odb'})
            row=dict(state=str(state),state_sha256=C.sha(state),step_directory=rowroot.name,
                views={'odb':dict(path=str(odb),sha256=C.sha(odb),container='/work/run/01-openroad-postantennadesignrepair/design.odb')})
            record=dict(original_preparation=C.bound(original/'preparation.json'),delta=C.candidate_delta(2),
                request={'openroad_threads':2},parent_report={'path':'historical','sha256':'a'*64},measured_fanout={'path':'observation','sha256':'b'*64})
            baseline=dict(OPENROAD_THREADS=4,GRT_DESIGN_REPAIR_RUN_GRT=True,DRT_OPT_ITERS=64,PL_TARGET_DENSITY_PCT=85,CLOCK_PERIOD=20)
            C.P.write(original/'resolved.json',baseline);record['original_resolved_config']=C.bound(original/'resolved.json')
            C.P.write(run/'flow/resolved.json',dict(baseline,OPENROAD_THREADS=2))
            report=dict(schema='pinwheel.streaming-8x4-postantenna-repair-run.v1',mode='full',status='failed',exit_code=1,
                inputs_pdk_runtime_unchanged=True,container_termination={'status':'absent'},qualified=False,physical_acceptance=False,
                parent_is_not_final_target=True,preparation=C.bound(prep/'preparation.json'),original_preparation=record['original_preparation'],
                delta=record['delta'],states=[row],actual_resolved_delta={'OPENROAD_THREADS':{'before':4,'after':2}})
            def save():
                report['artifact_sha256']={str(p.relative_to(run)):C.sha(p) for p in run.rglob('*') if p.is_file() and p.name!='report.json'}
                C.P.write(run/'report.json',report)
            save()
            with patch.object(C,'verify',return_value=record),patch.object(C.P,'verify',return_value={}):
                with self.assertRaisesRegex(ValueError,'DetailedRouting'):C.select_report(run/'report.json',C.sha(run/'report.json'),original,{})
                newroot=run/'flow/03-openroad-detailedrouting';newroot.mkdir();newodb=newroot/'design.odb';newodb.write_bytes(b'fresh completed routed ODB')
                newstate=newroot/'state_out.json';newcontainer='/work/run/03-openroad-detailedrouting/design.odb';C.P.write(newstate,{'odb':newcontainer})
                report['states'].append(dict(state=str(newstate),state_sha256=C.sha(newstate),step_directory=newroot.name,
                    views={'odb':dict(path=str(newodb),sha256=C.sha(newodb),container=newcontainer)}));save()
                target=C.select_report(run/'report.json',C.sha(run/'report.json'),original,{})
                self.assertEqual(target['actual_odb'],C.bound(newodb));self.assertEqual(target['physical_candidate_kind'],'canonical-postantenna-repair')


if __name__=='__main__':unittest.main()
