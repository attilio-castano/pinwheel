"""Portable controls for the single same-target layout resource replay."""
import ast
import copy
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_closure24_layout_resource as L


class LayoutResourceTests(unittest.TestCase):
    def test_only_declared_run_body_changes(self):
        original=L.pinned_source(L.CONTROLLER);node=next(x for x in ast.parse(original).body
            if isinstance(x,ast.FunctionDef) and x.name=='run_layout')
        expected=''.join(original.splitlines(True)[node.lineno-1:node.end_lineno])
        text,diff=L.run_source()
        restored=text.replace("'--memory','6g','--memory-swap','6g'","'--memory','2g','--memory-swap','2g'",1)
        restored=restored.replace('/worker/'+L.OWN,'/worker/scripts/streaming_8x4_closure24_signoff_execute.py',1)
        restored=restored.replace(L.RUN,'pinwheel.closure24-layout-run.v1',1)
        self.assertEqual(restored,expected)
        self.assertIn('6g',diff)

    def test_original_view_namespace_is_independent(self):
        entries=L.BASE.SOURCE_ENTRIES;view=L.BASE.closed_views
        result=L.runner()
        self.assertIs(result.__globals__['closed_views'],view)
        self.assertIs(view.__globals__,vars(L.BASE))
        self.assertIsNot(result.__globals__,vars(L.BASE))
        self.assertIs(result.__globals__['stage_producer'],L.stage_producer)
        self.assertIs(L.BASE.SOURCE_ENTRIES,entries)
        self.assertNotIn(L.OWN,entries)

    def test_native_and_readers_stay_canonical(self):
        self.assertIs(L.BASE.native_layout,L.BASE.ORIGINAL.native_layout)
        self.assertIs(L.runner().__globals__['native_layout'],L.BASE.native_layout)
        for name in L.PINS:self.assertEqual(L.sha(L.ROOT/name),L.PINS[name])

    def test_exact_resources_and_time(self):
        value=L.policy();self.assertEqual(L.BASE.layout_budget(value['worker_seconds']),750)
        self.assertEqual(2*value['deck_seconds']+value['reader_cleanup_reserve_seconds'],1800)
        argv=L.command(Path('/out/inputs'),Path('/view/design.gds'),Path('/view/reference.cdl'),
            {'pdk_root':'/pdk'},Path('/out'),{'image_id':'sha256:actual'},'owner','pinwheel-example')
        for option,value in [('--cpus','1'),('--memory','6g'),('--memory-swap','6g'),('--network','none')]:
            self.assertEqual(argv[argv.index(option)+1],value)
        self.assertIn('--read-only',argv);self.assertIn('/tmp:rw,size=256m',argv)
        self.assertEqual(argv[-3:],['native-layout','--request','/input/requests/request.json'])

    def test_all_categories_and_no_scope_promotion(self):
        self.assertEqual(len(L.categories()),23)
        self.assertEqual(len({tuple(x)for x in L.categories()}),23)
        p=L.policy()
        for name in ('model_qualified','qualified_timing','physical_acceptance','physical_variant_changed',
                     'readers_or_flags_changed'):self.assertIs(p[name],False)
        self.assertIs(p['OpenROAD_antenna_failure_remains_open'],True)

    def failure(self):
        execution=dict(status='interrupted',exit_code=130,error='signal 15',timeout_seconds=1800,
            container_termination=dict(status='absent'))
        report=dict(schema='pinwheel.closure24-layout-run.v1',completed=False,passed=False,
            physical_acceptance=False,error='ValueError: Final native layout execution failed',execution=execution)
        guard=dict(schema='pinwheel.streaming-tt-resource-job.v1',kind='cad-validation',status='stopped',
            exit_code=124,timeout_seconds=1920,stop_reason='ValueError: Container approaching memory limit',
            cleanup_confirmed=True,inputs_unchanged=True,owned_processes_remaining=[],containers_remaining=[],cleanup_errors=[])
        return report,guard,execution

    def test_original_memory_stop_admitted_only_as_failed(self):
        L.validate_failed(*self.failure())
        for section,key,value in [(0,'passed',True),(0,'completed',True),(1,'status','completed'),
            (1,'cleanup_confirmed',False),(1,'inputs_unchanged',False),(2,'exit_code',0)]:
            values=copy.deepcopy(self.failure());values[section][key]=value
            with self.assertRaises(ValueError):L.validate_failed(*values)

    def resource_fixture(self):
        launch=dict(resource_supervisor_argv=['python','-B','guard','--','worker'],
            proposal=dict(path='/launch/proposal.json'),external_Root_GO='/launch/Root-GO.json')
        row=dict(input_sha256={},views_report=dict(path='/views/report.json',sha256='v'))
        pins={name:'0'*64 for name in ('/launch/proposal.json','/launch/launch.json','/launch/Root-GO.json')}
        boundary=dict(campaign_id=L.POLICY.CAMPAIGN,campaign_kind='fixed_cad',campaign_root=str(L.ROOT),
            schedule=L.POLICY.SCHEDULE,shared_lease=L.POLICY.shared_lease_paths(L.ROOT),frozen_parent=row['views_report'],
            actual_wrapper_argv=[sys.orig_argv[0],'-B','guard','--','worker'],historical_producer_sha256={})
        for key in ('wrapper','policy','inherited_supervisor'):
            boundary[key+'_path']='/'+key;boundary[key+'_sha256']='0'*64
        resource=dict(schema='pinwheel.streaming-tt-resource-job.v1',kind='cad-validation',timeout_seconds=1920,
            rss_mib=2048,argv=['worker'],validation_parent=row['views_report'],input_sha256=pins,status='stopped',
            cleanup_confirmed=True,inputs_unchanged=True,owned_processes_remaining=[],containers_remaining=[],
            cleanup_errors=[],campaign_boundary=boundary)
        return resource,launch,row

    def check_resource(self,values):
        with patch.object(L,'sha',return_value='0'*64),patch.object(L,'regular',side_effect=Path),\
             patch.object(L.POLICY,'historical_sources',return_value={}):
            L.validate_resource(*values)

    def test_complete_guard_join(self):
        self.check_resource(self.resource_fixture())

    def test_guard_omissions_and_foreign_policy_reject(self):
        for key,value in [('timeout_seconds',1800),('rss_mib',4096),('cleanup_confirmed',False),
                          ('inputs_unchanged',False),('containers_remaining',['foreign'])]:
            values=copy.deepcopy(self.resource_fixture());values[0][key]=value
            with self.assertRaises(ValueError):self.check_resource(values)
        for key,value in [('campaign_kind','host'),('shared_lease',{}),('historical_producer_sha256',{'foreign':'x'}),
                          ('wrapper_sha256','wrong')]:
            values=copy.deepcopy(self.resource_fixture());values[0]['campaign_boundary'][key]=value
            with self.assertRaises(ValueError):self.check_resource(values)

    def test_extra_or_missing_outer_input_reject(self):
        for name in ('/foreign','/launch/Root-GO.json'):
            values=copy.deepcopy(self.resource_fixture());pins=values[0]['input_sha256']
            if name in pins:del pins[name]
            else:pins[name]='0'*64
            with self.assertRaises(ValueError):self.check_resource(values)


if __name__=='__main__':unittest.main()
