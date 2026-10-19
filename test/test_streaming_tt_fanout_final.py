"""Fanout derivatives cannot inherit stale views or loosen the admitted budget."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock,patch
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import streaming_tt_fanout_final as C


class FanoutFinalTests(unittest.TestCase):
    def test_route_directory_exists_for_native_cli_and_refuses_reuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            self.assertEqual(C.fresh_route_directory(root),root/'route')
            self.assertTrue((root/'route').is_dir())
            with self.assertRaises(FileExistsError):C.fresh_route_directory(root)

    def test_exact_four_approved_recipe_changes_and_no_input_mutation(self):
        before=dict(CLOCK_PERIOD=20,RUN_POST_GRT_RESIZER_TIMING=False,RT_MAX_LAYER='Metal4',
            DRT_OPT_ITERS=64,RUN_KLAYOUT_DRC=True,RUN_CTS=True)
        resolved=dict(GRT_ADJUSTMENT=0.3,PL_MAX_DISPLACEMENT_X=500,PL_MAX_DISPLACEMENT_Y=100)
        original=deepcopy(before);after=C.derive_config(before,resolved)
        self.assertEqual(before,original);self.assertEqual(after['GRT_ADJUSTMENT'],0.19)
        self.assertTrue(after['RUN_POST_GRT_RESIZER_TIMING'])
        self.assertEqual((after['PL_MAX_DISPLACEMENT_X'],after['PL_MAX_DISPLACEMENT_Y']),(1500,800))
        for key,value in [('CLOCK_PERIOD',21),('RT_MAX_LAYER','TopMetal1'),('RUN_KLAYOUT_DRC',False),
                ('DRT_OPT_ITERS',1),('GRT_ADJUSTMENT',0.2),('CLOCK_PERIOD',20.0),('extra_unapproved',True),
                ('PL_MAX_DISPLACEMENT_X',1501),('PL_MAX_DISPLACEMENT_Y',800.0)]:
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'Unapproved'):
                C.validate_config_delta(before,dict(after,**{key:value}))
        with self.assertRaisesRegex(ValueError,'original 30 percent'):
            C.derive_config(before,dict(resolved,GRT_ADJUSTMENT=0.4))
        with self.assertRaises(ValueError):C.derive_config(before,dict(resolved,PL_MAX_DISPLACEMENT_Y=101))

    def test_fresh_seed_contains_only_actual_three_views_and_empty_metrics(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name in ('implemented.odb','implemented.def','implemented.v','old.sdf','old.spef','old.guide'):
                (root/name).write_text('actual '+name)
            seed=C.fresh_seed(root)
            self.assertEqual(set(seed),{'odb','def','nl','metrics'});self.assertEqual(seed['metrics'],{})
            self.assertEqual(seed['odb'],str(root/'implemented.odb'))
            self.assertNotIn('spef',seed);self.assertNotIn('sdf',seed);self.assertNotIn('guide',seed)
            (root/'implemented.v').write_bytes(b'')
            with self.assertRaisesRegex(ValueError,'Empty derivative'):C.fresh_seed(root)

    def test_every_repair_route_and_original_tail_step_remains_scheduled(self):
        ids=[C.START,'OpenROAD.STAMidPNR-2','OpenROAD.GlobalRouting','OpenROAD.RepairDesignPostGRT',
            'OpenROAD.RepairAntennas','OpenROAD.ResizerTimingPostGRT','OpenROAD.STAMidPNR-3',*C.F.TAIL]
        self.assertEqual(C.validate_order(ids),ids)
        for missing in (C.START,'OpenROAD.GlobalRouting','OpenROAD.RepairAntennas','OpenROAD.RCX','Checker.HoldViolations'):
            with self.subTest(missing=missing),self.assertRaises(ValueError):C.validate_order([name for name in ids if name!=missing])
        wrong=list(ids);wrong[0],wrong[2]=wrong[2],wrong[0]
        with self.assertRaises(ValueError):C.validate_order(wrong)

    def transformation(self,root):
        root=root.resolve()
        for name in ('implemented.odb','implemented.def','implemented.v'):(root/name).write_text('actual '+name)
        C.P.write(root/'inventory.json',{'top':'tt_um_pinwheel_streaming_ready_d2'})
        C.P.write(root/'connectivity.json',{'modules':{'tt_um_pinwheel_streaming_ready_d2':{}}})
        request=dict(source_odb_sha256='a'*64,plan_sha256='b'*64,top='tt_um_pinwheel_streaming_ready_d2',
            expected_added_cells=650,expected_original_instances=41239)
        packet=dict(schema='pinwheel.streaming-tt-native-fanout-partition.v1',passed=True,completed=True,
            inputs_unchanged=True,exact_source_inventory_re_read=True,exact_topology_checked=True,placement_passed=True,
            native_detailed_placement_executed=True,native_check_placement_executed=True,actual_odb_roundtrip_checked=True,
            qualified=False,physical_acceptance_claim=False,inherited_netlist=False,original_ff_bits=6039,
            source_odb_sha256=request['source_odb_sha256'],plan_sha256=request['plan_sha256'],
            topology=dict(passed=True,exact_pin_partition_checked=True,all_signal_and_clock_loads_at_most_eight=True,
                positive_clone_cells=650,original_instances_retained=41239),
            native_tcl_all_success=True,native_tcl_commands=[dict(command=command,tcl_catch_status='0',tcl_result='')
                for command in C.TCL_COMMANDS],
            artifacts_sha256={path.name:C.P.sha(path) for path in root.iterdir()})
        C.P.write(root/'report.json',packet);return request,packet

    def test_complete_exact_native_topology_and_actual_outputs_accept(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);request,packet=self.transformation(root)
            self.assertEqual(C.validate_transformation(root,request),packet)

    def test_missing_kernel_input_state_placement_or_roundtrip_cannot_route(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);request,packet=self.transformation(root)
            for key,value in [('exact_topology_checked',False),('placement_passed',False),('original_ff_bits',6038),
                    ('actual_odb_roundtrip_checked',False),('inputs_unchanged',False),('inherited_netlist',True),
                    ('source_odb_sha256','c'*64),('qualified',True)]:
                C.P.write(root/'report.json',dict(packet,**{key:value}))
                with self.subTest(key=key),self.assertRaisesRegex(ValueError,'incomplete'):
                    C.validate_transformation(root,request)
            for key,value in [('passed',False),('exact_pin_partition_checked',False),
                    ('all_signal_and_clock_loads_at_most_eight',False),('positive_clone_cells',649)]:
                changed=deepcopy(packet);changed['topology'][key]=value;C.P.write(root/'report.json',changed)
                with self.subTest(topology=key),self.assertRaisesRegex(ValueError,'full topology/load/instance'):
                    C.validate_transformation(root,request)
            C.P.write(root/'report.json',packet);(root/'implemented.v').write_text('old or substituted view')
            with self.assertRaisesRegex(ValueError,'bytes/membership'):C.validate_transformation(root,request)

    def test_printed_tcl_error_cannot_hide_behind_exit_zero_or_placement_flags(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);request,packet=self.transformation(root)
            for status in ('1','',None,False,0):
                changed=deepcopy(packet);changed['native_tcl_commands'][2]['tcl_catch_status']=status
                C.P.write(root/'report.json',changed)
                with self.subTest(status=status),self.assertRaisesRegex(ValueError,'Tcl placement/check/write status'):
                    C.validate_transformation(root,request)
            changed=deepcopy(packet);changed['native_tcl_commands'].pop(3);C.P.write(root/'report.json',changed)
            with self.assertRaisesRegex(ValueError,'Tcl placement/check/write status'):C.validate_transformation(root,request)

    def test_declared_python_alias_is_preserved_and_both_native_events_retained(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp).resolve();executable=root/'real-python';executable.write_text('actual runtime');executable.chmod(0o755)
            declared=root/'venv-python';declared.symlink_to(executable);journal=root/'native.jsonl'
            with patch.object(C.subprocess,'run',return_value=SimpleNamespace(returncode=0)) as run:
                self.assertEqual(C.native_command([str(declared),'-B','-m','librelane'],'route',root,journal),0)
            self.assertEqual(run.call_args.args[0][0],str(declared))
            events=[json.loads(line) for line in journal.read_text().splitlines()]
            self.assertEqual([row['event'] for row in events],['intent','result'])
            self.assertEqual(events[0]['resolved_executable'],str(executable))
            self.assertEqual(events[1]['executable_sha256_before'],events[1]['executable_sha256_after'])

    def closed_native(self,root):
        root=root.resolve();transformation=root/'transformation';transformation.mkdir()
        request,transformed=self.transformation(transformation)
        request.update(tag='attempt',launch='/work/inputs/fanout/launch.py')
        seed={key:'/work/run/transformation/implemented.'+suffix for key,suffix in [('odb','odb'),('def','def'),('nl','v')]}
        seed['metrics']={};C.P.write(root/'fresh-seed.json',seed)
        route=root/'route';route.mkdir();(route/'resolved.json').write_text('{"CLOCK_PERIOD":20}')
        (root/'resolved.json').write_bytes((route/'resolved.json').read_bytes())
        events=[]
        for name,argv in [('transformation',['/native/openroad','-exit','-python',request['launch']]),
                ('route',C.route_arguments('/native/python3',request['tag']))]:
            (root/(name+'.log')).write_text('actual '+name+' log')
            intent=dict(name=name,argv=argv,resolved_executable=argv[0],executable_sha256_before='e'*64)
            result=dict(intent,executable_sha256_after='e'*64,exit_code=0,elapsed_seconds=1,
                log_sha256=C.P.sha(root/(name+'.log')))
            events.extend([dict(event='intent',**intent),dict(event='result',**result)])
        journal=root/'native-journal.jsonl';journal.write_text(''.join(json.dumps(row)+'\n' for row in events))
        ids=[C.START,'OpenROAD.GlobalRouting','OpenROAD.RepairDesignPostGRT','OpenROAD.RepairAntennas',
            'OpenROAD.ResizerTimingPostGRT','OpenROAD.STAMidPNR-3',*C.F.TAIL]
        packet=dict(schema='pinwheel.streaming-tt-fanout-native-run.v1',completed=True,exit_code=0,status='completed',
            request_sha256='c'*64,native_step_ids=ids,executed_suffix=ids,transformation=transformed,
            transformation_report_sha256=C.P.sha(transformation/'report.json'),fresh_seed_keys=sorted(seed),
            fresh_seed_sha256=C.P.sha(root/'fresh-seed.json'),native_journal_sha256=C.P.sha(journal),
            resolved_config_sha256=C.P.sha(root/'resolved.json'))
        C.P.write(root/'native-report.json',packet);return request,packet,events

    def test_full_native_closeout_checks_actual_two_processes_and_no_stale_seed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);request,packet,events=self.closed_native(root)
            result=C.validate_native_closeout(root,request,request_sha256='c'*64)
            self.assertTrue(result['passed']);self.assertEqual(result['closed_native_commands'],2)
            seed=C.P.read(root/'fresh-seed.json');seed['spef']={'nom_*':'old.spef'}
            C.P.write(root/'fresh-seed.json',seed);changed=dict(packet,fresh_seed_sha256=C.P.sha(root/'fresh-seed.json'))
            C.P.write(root/'native-report.json',changed)
            with self.assertRaisesRegex(ValueError,'stale views'):C.validate_native_closeout(root,request,request_sha256='c'*64)

    def test_journal_mutation_cannot_change_routing_start_while_claiming_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);request,packet,events=self.closed_native(root)
            for row in events[2:]:row['argv'][row['argv'].index('--from')+1]='OpenROAD.DetailedRouting'
            journal=root/'native-journal.jsonl';journal.write_text(''.join(json.dumps(row)+'\n' for row in events))
            C.P.write(root/'native-report.json',dict(packet,native_journal_sha256=C.P.sha(journal)))
            with self.assertRaisesRegex(ValueError,'repair range'):
                C.validate_native_closeout(root,request,request_sha256='c'*64)

    def test_native_success_cannot_clear_unconfirmed_owned_container_lock(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);base=root/'physical';out=base/'attempt';(out/'inputs').mkdir(parents=True)
            (root/'tools').mkdir();(root/'tools/physical-toolchain.json').write_text('{}')
            path=out/'inputs.json';path.write_text('{}')
            metadata=dict(tag='attempt',producer_sha256={},producer_commit='p',source_commit='s',timeout_seconds=1,
                pdk=str(root/'pdk'),transformation={'schema':'pinwheel.streaming-tt-fanout-derivative.v1'})
            process=Mock();process.wait.return_value=0;process.poll.return_value=0
            cleanup=SimpleNamespace(cleanup=Mock(return_value={'status':'unconfirmed','remaining':['owned']}))
            with patch.object(C.P,'ROOT',root),patch.object(C.P,'BASE',base),\
                    patch.object(C,'verify',return_value=metadata),patch.object(C.F,'common_runner',return_value=cleanup),\
                    patch.object(C.P,'inspect_runtime',return_value={'image_id':'pinned-image'}),\
                    patch.object(C.subprocess,'Popen',return_value=process),patch.object(C.F,'collect_states',return_value=[]):
                result=C.run(path)
            report=C.P.read(out/'report.json')
            self.assertEqual(result,3);self.assertEqual(report['status'],'cleanup_unconfirmed')
            self.assertEqual(report['exit_code'],0);self.assertTrue((base/'streaming-tt-active.json').exists())

    def test_busy_cad_lock_does_not_create_or_consume_prepared_derivative_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);base=root/'physical';out=base/'attempt';out.mkdir(parents=True)
            path=out/'inputs.json';path.write_text('{}');lock=base/'streaming-tt-active.json'
            lock.write_text('{"owner":"other-active-run"}')
            metadata=dict(tag='attempt',producer_sha256={},transformation={'schema':'pinwheel.streaming-tt-fanout-derivative.v1'})
            with patch.object(C.P,'ROOT',root),patch.object(C.P,'BASE',base),patch.object(C,'verify',return_value=metadata),\
                    self.assertRaises(FileExistsError):C.run(path)
            self.assertFalse((out/'flow').exists());self.assertEqual(C.P.read(lock)['owner'],'other-active-run')

    def test_frozen_project_closure_includes_native_executor_and_all_planning_helpers(self):
        closure=C.dependency_closure(ROOT,C.ENTRIES)
        for name in ('scripts/streaming_tt_apply_fanout.py','scripts/streaming_tt_fanout.py',
                'scripts/streaming_tt_export_odb.py','scripts/streaming_tt_simulation.py',
                'scripts/streaming_tt_final.py','scripts/run-streaming-tt-physical.py'):
            self.assertIn(name,closure['files'])


if __name__=='__main__':unittest.main()
