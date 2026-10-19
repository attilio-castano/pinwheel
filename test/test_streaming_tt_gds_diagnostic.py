#!/usr/bin/env python3
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_gds_diagnostic as G


class GDSDiagnosticTests(unittest.TestCase):
    def test_terminal_producer_requires_typed_exit_and_closeout(self):
        for status,code in [('flow_completed',0),('failed',1),('timed_out',124)]:
            packet=dict(status=status,exit_code=code,inputs_unchanged_after_run=True,container_termination={'status':'absent'})
            G.terminal(packet)
            for changed in (dict(packet,exit_code=False),dict(packet,exit_code=None),dict(packet,status='running'),
                    dict(packet,inputs_unchanged_after_run=False),dict(packet,container_termination={'status':'unknown'})):
                with self.assertRaises(ValueError):G.terminal(changed)
        with self.assertRaises(ValueError):G.terminal(dict(status='failed',exit_code=0))

    def test_exact_latest_state_ordinal_including_nested_subflows(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);paths=[]
            for name in ('35-repair/3-subflow/state_out.json','36-sta/state_out.json','39-check/state_out.json'):
                path=root/name;path.parent.mkdir(parents=True);path.write_text('{}');paths.append(path)
            report={'states':[{'state':str(path),'state_sha256':G.sha(path)} for path in paths]}
            G.latest_state(report,paths[-1],root)
            with self.assertRaises(ValueError):G.latest_state(report,paths[1],root)
            paths[0].write_text('{"changed":true}')
            with self.assertRaises(ValueError):G.latest_state(report,paths[-1],root)

    def test_external_tcl_checks_every_actual_def_command(self):
        commands=G.def_commands('/work/run/actual.odb','top');script=G.def_script(commands)
        self.assertEqual(script.count('[catch {'),3);self.assertEqual(script.count('exit 1'),3)
        self.assertIn('read_db {/work/run/actual.odb}',script);self.assertIn('write_def {/probe/def/implemented.def}',script)
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'status';path.write_text('0 0\n1 0\n2 0\n');self.assertEqual(len(G.validate_tcl(path,commands)),3)
            for bad in ('0 0\n1 0\n','0 0\n1 1\n2 0\n','0 0\n1 False\n2 0\n','0 0\n1 0\n2 0\n3 0\n'):
                path.write_text(bad)
                with self.assertRaises(ValueError):G.validate_tcl(path,commands)

    def test_only_exact_native_streamout_range_and_fresh_def_seed(self):
        argv=G.flow_arguments('probe')
        self.assertEqual(argv[argv.index('--from')+1],G.STEP);self.assertEqual(argv[argv.index('--to')+1],G.STEP)
        self.assertNotIn('--skip',argv);self.assertNotIn('--config-override',argv)
        self.assertEqual(argv[-1],'/work/run/resolved.json')
        with tempfile.TemporaryDirectory() as temporary:
            directory=G.prepare_flow_directory(temporary);self.assertTrue(directory.is_dir())
            with self.assertRaises(FileExistsError):G.prepare_flow_directory(temporary)

    def test_actual_streamout_must_contain_one_step_and_two_identical_gds(self):
        with tempfile.TemporaryDirectory() as temporary:
            out=Path(temporary);step=out/'streamout/51-klayout-streamout';step.mkdir(parents=True)
            for name in ('top.gds','top.klayout.gds'):(step/name).write_bytes(b'actual-gds')
            state={'def':'/probe/def/implemented.def','gds':'/probe/streamout/51-klayout-streamout/top.gds',
                'klayout_gds':'/probe/streamout/51-klayout-streamout/top.klayout.gds','metrics':{},'odb':None}
            path=step/'state_out.json';G.write(path,state);views=G.streamout_state(out)
            self.assertEqual(set(views['views']),{'gds','klayout_gds'})
            for changed in (dict(state,odb='/work/run/stale.odb'),dict(state,metrics={'old':1}),dict(state,**{'def':'/work/run/stale.def'})):
                G.write(path,changed)
                with self.assertRaises(ValueError):G.streamout_state(out)
            G.write(path,state);(step/'top.gds').write_bytes(b'changed')
            with self.assertRaises(ValueError):G.streamout_state(out)

    def test_observer_preserves_actual_subprocess_argv_and_logs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);exe=root/'python3';exe.symlink_to(Path(sys.executable).resolve());log=root/'native.log';journal=root/'journal'
            called=[]
            with log.open('w') as stream:
                result=G.observe_command([str(exe),'-c','print(17)'],'probe',journal,stream,
                    lambda argv:(called.append(argv) or subprocess.run(argv,stdout=stream,stderr=subprocess.STDOUT,check=True)))
            events=[json.loads(line) for line in journal.read_text().splitlines()]
            self.assertEqual(result.returncode,0);self.assertEqual(called[0][0],str(exe))
            self.assertEqual([event['event'] for event in events],['intent','result'])
            self.assertEqual(events[1]['log_sha256'],G.sha(log));self.assertEqual(events[1]['exit_code'],0)

    def test_native_streamout_requires_exact_layers_lefs_and_master_gds(self):
        config=dict(KLAYOUT_DEF_LAYER_MAP='/pdk/map',KLAYOUT_TECH='/pdk/lyt',KLAYOUT_PROPERTIES='/pdk/lyp',
            DESIGN_NAME='top',DEFAULT_CORNER='nom_typ',TECH_LEFS={'nom_*':'/pdk/tech.lef'},
            CELL_LEFS=['/pdk/cells.lef'],CELL_GDS=['/pdk/cells.gds'],PAD_GDS=['/pdk/pads.gds'])
        argv=['/python3','/native/klayout/stream_out.py','/probe/def/implemented.def','--top','top',
            '--lym','/pdk/map','--lyt','/pdk/lyt','--lyp','/pdk/lyp',
            '--input-lef','/pdk/tech.lef','--input-lef','/pdk/cells.lef',
            '--with-gds-file','/pdk/cells.gds','--with-gds-file','/pdk/pads.gds']
        G.validate_streamout_argv(argv,config)
        for old in ('/probe/def/implemented.def','/pdk/map','/pdk/lyt','/pdk/lyp','/pdk/cells.lef','/pdk/cells.gds'):
            changed=['wrong' if value==old else value for value in argv]
            with self.assertRaises(ValueError):G.validate_streamout_argv(changed,config)
        with self.assertRaises(ValueError):G.validate_streamout_argv(argv+['--lym','/pdk/map'],config)

    def test_unchanged_four_view_exporter_runs_through_observer_proxy(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);database=root/'actual.odb';database.write_bytes(b'odb')
            config=root/'config.json';G.write(config,dict(DESIGN_NAME='tt_um_pinwheel_streaming_ready_d2',
                RT_MAX_LAYER='Metal4',CLOCK_PERIOD=20,CELL_CDLS=['/work/pdk/masters.cdl'],
                CELL_LIBS={'nom':['/work/pdk/cells.lib']},DEFAULT_CORNER='nom'))
            called=[];out=root/'native'
            def fake_native(argv,**kwargs):
                called.append((argv,kwargs['stderr']))
                for name in ('implemented.v','implemented.power.v','implemented.cdl','implemented.lef'):(out/name).write_text('actual-view')
                return G.SimpleNamespace(returncode=0)
            with patch.object(G.E,'subprocess',G.signoff_subprocess_proxy(fake_native)),\
                    patch.object(G.E,'regular',lambda path:Path(path).resolve()),\
                    patch.object(G.E,'sha',lambda path:'0'*64),\
                    patch.object(G.E.shutil,'which',lambda name:sys.executable):
                packet=G.E.export(database,config,out)
            self.assertTrue(packet['completed']);self.assertEqual(called[0][1],subprocess.STDOUT)
            self.assertEqual(called[0][0][1:],['-exit','-no_init',str(out/'export.tcl')])

    def test_complete_ast_closure_includes_original_exporter_and_checkpoint(self):
        closure=G.dependency_closure(G.P.ROOT,G.ENTRIES)
        self.assertIn('scripts/streaming_tt_export_signoff.py',closure['files'])
        self.assertIn('scripts/run-streaming-tt-sta.py',closure['files'])
        self.assertIn('scripts/run-streaming-tt-signoff-export.py',closure['files'])


if __name__=='__main__':unittest.main()
