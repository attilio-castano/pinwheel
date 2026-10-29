"""Portable controls for diagnostic scope, failure retention and Native binding."""
import ast
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_antenna48_probe as A

CANONICAL='''source $::env(SCRIPTS_DIR)/openroad/common/io.tcl
read_current_odb
set diode_cell [lindex [split $::env(DIODE_CELL) "/"] 0]
set arg_list [list $diode_cell -iterations $::env(GRT_ANTENNA_REPAIR_ITERS) -ratio_margin $::env(GRT_ANTENNA_REPAIR_MARGIN)]
append_if_flag arg_list GRT_ALLOW_CONGESTION -allow_congestion
log_cmd repair_antennas {*}$arg_list
write_views
'''


def snapshot():
    return dict(instances={'victim':{'master':'buffer'}},terminals={('victim','A'):('INPUT','SIGNAL',A.NET)},
        pg=[('VDD','Metal1',(0,0,1,1),'0')],special=[('VDD','Metal1',(0,0,1,1),'STRIPE')],
        ports={'port':('INPUT','SIGNAL',A.NET)},public=[('port','Metal4',0,0,1,1,'PLACED')])


class ProbeTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.before=snapshot();self.after=copy.deepcopy(self.before)
        self.native=dict(mode='initial-failure-capture',completed=False,exit_code=1,
            source_odb_unchanged=True,inputs_unchanged=True,original_hook_inputs_unchanged=True)
        self.execution=dict(status='completed',exit_code=1,container_termination={'status':'absent'})

    def initial_files(self):
        self.after=copy.deepcopy(self.before)
        self.after['instances'].update({f'D{i}':{'master':A.G.MASTER,'box':(i,0,i+1,1),
            'orient':'R0','status':'PLACED'} for i in range(94)})
        for name in ('before.tsv','postcanonical.tsv','postcanonical.odb','postcanonical.def',
                     'canonical-result.tcllist','capture-result.tcllist'):
            (self.root/name).write_text('fixture\n')
        for name in ('before.guides.tsv','postcanonical.guides.tsv'):(self.root/name).write_text('')
        (self.root/'capture-status.tsv').write_text('CAPTURE\t0\n')
        result='GRT-0116 Global routing finished with congestion.'
        options='-code 1 -level 0 -errorinfo {strict original error grt::end_incremental}'
        (self.root/'canonical-result.tsv').write_text('STATUS\t1\nRESULT_HEX\t'+result.encode().hex()+
            '\nOPTIONS_HEX\t'+options.encode().hex()+'\n')
        current=self.root/'pg-diode/call-001';previous=self.root/'previous-call'
        current.mkdir(parents=True);previous.mkdir()
        plan=dict(schema='fixture',policy='B',policy_definition={'exact':'old'},physical_acceptance=False,
            targets=[f'D{i}' for i in range(94)],moves=[dict(instance=f'D{i}',x=i,y=0,orient='R0',box=[i,0,i+1,1],
            before=dict(box=[i,0,i+1,1],orient='R0')) for i in range(94)])
        for parent in (current,previous):
            for name in ('before.tsv','postcanonical.tsv','postcanonical.def','moves.tsv'):(parent/name).write_text('fixture\n')
            (parent/'plan.json').write_text(json.dumps(plan))
        self.previous_call={n:A.bound(previous/n) for n in ('before.tsv','postcanonical.tsv','postcanonical.def','plan.json','moves.tsv')}

    def classify_initial(self):
        def read(path):return self.before if Path(path).name=='before.tsv' else self.after
        with patch.object(A.G,'read_snapshot',side_effect=read):
            return A.classify('initial-failure-capture',self.root,self.native,self.execution,self.previous_call)

    def final_files(self):
        self.native.update(mode='final-observe',completed=True,exit_code=0);self.execution['exit_code']=0
        for name in ('baseline.tsv','after.tsv','baseline.def','placement.json'):(self.root/name).write_text('fixture\n')
        for name in ('baseline.guides.tsv','after.guides.tsv'):(self.root/name).write_text('')
        (self.root/'observation.tsv').write_text('OBSERVATION\tfinal-observe\t1\t1\n')
        (self.root/'target-antenna.rpt').write_text(A.NET+' fanout276 Metal3 CAR 213.80 VIOLATED\n')

    def classify_final(self):
        with patch.object(A.G,'read_snapshot',return_value=self.before):
            return A.classify('final-observe',self.root,self.native,self.execution)

    def test_final_tcl_has_no_repair_or_route(self):
        text=A.tcl('final-observe',CANONICAL)
        for forbidden in ('repair_antennas','global_route','detailed_route','setLocation','setOrient','write_db'):
            # write_db exists only in the capture procedure's gated branch;
            # both actual final calls pass the false DB-output argument.
            if forbidden!='write_db':self.assertNotIn(forbidden,text)
        self.assertIn('antenna48_capture $out/baseline 0',text)
        self.assertNotIn('antenna48_capture $out/baseline 1',text)
        self.assertIn('-net engine.core._0083_.Y',text)
        self.assertIn('::pgd::capture $out/after.tsv',text)

    def test_initial_catches_only_unchanged_call_and_rethrows(self):
        text=A.tcl('initial-failure-capture',CANONICAL)
        self.assertEqual(text.count('log_cmd repair_antennas {*}$arg_list'),1)
        self.assertIn('set status [catch {log_cmd repair_antennas {*}$arg_list} result options]',text)
        self.assertIn('append_if_flag arg_list GRT_ALLOW_CONGESTION -allow_congestion',text)
        self.assertIn('if {$status != 0} {return -options $options $result}',text)
        self.assertLess(text.index('canonical-result.tcllist'),text.index('antenna48_capture $out/postcanonical 1'))
        self.assertLess(text.index('capture-status.tsv'),text.index('return -options $options $result'))
        self.assertNotIn('::pgd::apply',text)
        self.assertIn('source /work/probe/inputs/frozen-initial-hook.tcl',text)
        with self.assertRaises(ValueError):A.tcl('initial-failure-capture',CANONICAL.replace('read_current_odb\n',''))

    def test_expected_initial_failure_never_becomes_physical_pass(self):
        self.initial_files();result=self.classify_initial()
        self.assertTrue(result['measurement_complete']);self.assertTrue(result['expected_failure_captured'])
        self.assertEqual(result['diode_count'],94)
        for key in A.FALSE_SCOPE:self.assertIs(result[key],False)
        self.assertEqual(self.execution['exit_code'],1)

    def test_initial_success_or_timeout_or_cleanup_failure_rejects(self):
        self.initial_files()
        for field,value in (('exit_code',0),('status','timed_out'),('container_termination',{'status':'unknown'})):
            saved=copy.deepcopy(self.execution);self.execution[field]=value
            with self.assertRaises(ValueError):self.classify_initial()
            self.execution=saved
        self.native['completed']=True
        with self.assertRaises(ValueError):self.classify_initial()

    def test_initial_exact94_and_unchanged_pg_required(self):
        self.initial_files();saved=copy.deepcopy(self.after)
        del self.after['instances']['D93']
        with self.assertRaises(ValueError):self.classify_initial()
        self.after=copy.deepcopy(saved);self.after['instances']['D1']['master']='wrong'
        with self.assertRaises(ValueError):self.classify_initial()
        self.after=copy.deepcopy(saved);self.after['pg']=[]
        with self.assertRaises(ValueError):self.classify_initial()

    def test_initial_error_and_complete_capture_required(self):
        self.initial_files();(self.root/'capture-status.tsv').write_text('CAPTURE\t1\n')
        with self.assertRaises(ValueError):self.classify_initial()
        (self.root/'capture-status.tsv').write_text('CAPTURE\t0\n')
        (self.root/'postcanonical.odb').unlink()
        with self.assertRaises(ValueError):self.classify_initial()

    def test_exact_original_hook_plan_and_failure_phase_required(self):
        self.initial_files()
        self.assertTrue(self.classify_initial()['canonical_repair_returned'])
        current=self.root/'pg-diode/call-001'
        (current/'applied.tsv').write_text('should not exist\n')
        with self.assertRaises(ValueError):self.classify_initial()
        (current/'applied.tsv').unlink()
        plan=json.loads((current/'plan.json').read_text());plan['moves'][0]['x']=999
        (current/'plan.json').write_text(json.dumps(plan))
        with self.assertRaises(ValueError):self.classify_initial()

    def test_final_exact_residual_and_guide_identity(self):
        self.final_files();result=self.classify_final()
        self.assertTrue(result['measurement_complete']);self.assertFalse(result['antenna_acceptance'])
        (self.root/'after.guides.tsv').write_text('changed\n')
        with self.assertRaises(ValueError):self.classify_final()
        (self.root/'after.guides.tsv').write_text('')
        (self.root/'observation.tsv').write_text('OBSERVATION\tfinal-observe\t0\t0\n')
        with self.assertRaises(ValueError):self.classify_final()

    def test_exact_container_resources_and_readonly_inputs(self):
        packet=dict(original_preparation={'path':'/base/preparation.json'},pdk_root='/pdk',
            source_odb={'path':'/old/f516.odb'},runtime={'image_id':'sha256:582'},mode='final-observe')
        argv=A.command(Path('/prep'),Path('/output'),packet,'pinwheel-test','00000000-0000-0000-0000-000000000001')
        self.assertEqual(argv[argv.index('--cpus')+1],'2')
        self.assertEqual(argv[argv.index('--memory')+1],'6g')
        self.assertEqual(argv[argv.index('--memory-swap')+1],'6g')
        self.assertIn('--read-only',argv);self.assertIn('none',argv)
        self.assertIn('type=bind,source=/old/f516.odb,target=/work/seed.odb,readonly',argv)
        self.assertEqual(A.LIMITS,{'final-observe':120,'initial-failure-capture':180})
        self.assertEqual(A.OUTER_LIMITS,{'final-observe':150,'initial-failure-capture':240})
        self.assertEqual(sum(A.OUTER_LIMITS.values()),390)
        packet.update(mode='initial-failure-capture',context={'initial_preparation':{'path':'/old/preparation.json'}})
        initial=A.command(Path('/prep'),Path('/output'),packet,'pinwheel-test','00000000-0000-0000-0000-000000000001')
        self.assertIn('type=bind,source=/old/inputs,target=/work/closure/inputs,readonly',initial)

    def test_exclusive_writer_preserves_earlier_packet(self):
        path=self.root/'packet.json';A.write(path,{'a':1})
        with self.assertRaises(FileExistsError):A.write(path,{'a':2})
        self.assertEqual(json.loads(path.read_text()),{'a':1})

    def test_complete_guide_records_and_empty_scope(self):
        line='GUIDE\t'+A.NET+'\tMetal3\t\t10\t20\t30\t40\t1\t0\t1\n'
        result=A.guide_census(line)
        self.assertEqual(result['stored_guides'],1)
        self.assertEqual(result['congested_by_layer'],{'Metal3':1})
        self.assertEqual(len(result['target_net_guides']),1)
        self.assertEqual(A.guide_census('')['stored_guides'],0)
        for broken in (line.replace('Metal3','Unknown'),line.replace('\t1\t0\t1','\t2\t0\t1'),line+'unknown\n'):
            with self.assertRaises(ValueError):A.guide_census(broken)

    def test_actual_journal_config_and_cgroup_join(self):
        metadata=self.root/'metadata';metadata.mkdir();config=self.root/'config.json'
        config.write_text(json.dumps(dict(DEFAULT_CORNER='typ',CELL_LIBS={'typ':['/work/pdk/cell.lib']})))
        packet=dict(mode='final-observe',source_config={'path':str(config),'sha256':A.sha(config)})
        A.write(metadata/'native-limits.json',{'cpu.max':'200000 100000','memory.max':str(6*1024**3),
            'memory.swap.max':'0','pids.max':'256'})
        A.write(metadata/'config-binding.json',dict(mode='final-observe',source_config=packet['source_config'],
            actual_sha256=A.sha(config),exact_membership_and_values=True,added_config_fields=[],
            changed_config_fields=[],physical_acceptance=False))
        start=dict(event='start',step='Pinwheel.Antenna48Observe',argv=['openroad','-exit','-threads','2',
            '-no_splash','-metrics','/work/run/step/or_metrics_out.json','/work/probe/inputs/observe.tcl'],
            resolved_executable='/nix/bin/openroad',executable_sha256=A.OPENROAD_SHA,
            env=dict(CURRENT_ODB='/work/seed.odb',PNR_SDC_FILE='/work/inputs/core.sdc',
            _SDC_IN='/work/inputs/core.sdc',OPENROAD_THREADS='2',_LIB_CORNER_0='typ /work/pdk/cell.lib'))
        finish=dict(event='finish',exit_code=0,resolved_executable_after='/nix/bin/openroad',executable_sha256_after=A.OPENROAD_SHA)
        journal=metadata/'native-journal.jsonl'
        journal.write_text(json.dumps(start)+'\n'+json.dumps(finish)+'\n')
        self.assertEqual(len(A.native_evidence(self.root,packet)['native_journal']),2)
        for field,value in (('argv',['/nix/bin/openroad',*start['argv'][1:]]),('executable_sha256','0'*64),
                            ('resolved_executable','relative/openroad')):
            bad=copy.deepcopy(start);bad[field]=value
            journal.write_text(json.dumps(bad)+'\n'+json.dumps(finish)+'\n')
            with self.assertRaises(ValueError):A.native_evidence(self.root,packet)
        finish['exit_code']=1;journal.write_text(json.dumps(start)+'\n'+json.dumps(finish)+'\n')
        with self.assertRaises(ValueError):A.native_evidence(self.root,packet)
        finish['exit_code']=0;start['env']['CURRENT_ODB']='/wrong.odb'
        journal.write_text(json.dumps(start)+'\n'+json.dumps(finish)+'\n')
        with self.assertRaises(ValueError):A.native_evidence(self.root,packet)

    def test_defensive_delegate_exception_preserves_raw_exit_and_exception(self):
        tree=ast.parse(Path(A.__file__).read_text())
        node=next(n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef) and n.name=='observed')
        journal=self.root/'exception-journal.jsonl'
        executable=self.root/'openroad';executable.write_bytes(b'fake fixture, never executed')
        error=A.subprocess.CalledProcessError(1,['fake-observation'])
        def delegate(*args,**kwargs):raise error
        namespace=dict(Path=Path,shutil=A.shutil,sha=A.sha,json=json,subprocess=A.subprocess,require=A.require,
                       OPENROAD_SHA=A.sha(executable),
                       delegate=delegate,journal=journal)
        exec(compile(ast.Module(body=[node],type_ignores=[]),'actual-observer','exec'),namespace)
        instance=type('Fake',(),{'id':'Pinwheel.Antenna48Observe'})()
        with patch.object(A.shutil,'which',return_value=str(executable)),self.assertRaises(A.subprocess.CalledProcessError) as caught:
            namespace['observed'](instance,['openroad'],env={})
        self.assertIs(caught.exception,error)
        rows=[json.loads(line) for line in journal.read_text().splitlines()]
        self.assertEqual([r['event'] for r in rows],['start','finish'])
        self.assertEqual(rows[1]['exit_code'],1)


if __name__=='__main__':unittest.main()
