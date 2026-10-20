"""Actual ODB export evidence must close its inputs, native call and views."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
spec=importlib.util.spec_from_file_location('signoff_export_host',ROOT/'scripts/run-streaming-tt-signoff-export.py')
host=importlib.util.module_from_spec(spec);spec.loader.exec_module(host)


class SignoffExportHostTests(unittest.TestCase):
    def fixture(self,root):
        root=root.resolve();native=root/'native';native.mkdir()
        database=root/'actual.odb';database.write_bytes(b'actual implemented connectivity')
        config=root/'resolved.json';host.write(config,{'DESIGN_NAME':'tt_um_pinwheel_streaming_ready_d2'})
        for name in host.OUTPUTS:(native/name).write_bytes(b'actual native view '+name.encode())
        (native/'export.tcl').write_text('read_db {actual.odb}\nwrite_verilog {implemented.v}\n')
        (native/'native.log').write_text('actual native export completed\n')
        packet=dict(schema='pinwheel.streaming-tt-signoff-export.v1',completed=True,status='completed',
            qualified=False,physical_acceptance_claim=False,exit_code=0,inputs_unchanged=True,
            inherited_netlist=False,top='tt_um_pinwheel_streaming_ready_d2',
            actual_database='/work/run/actual.odb',actual_database_sha256=host.sha(database),
            input_sha256_before={'/work/run/actual.odb':host.sha(database),
                '/work/run/resolved.json':host.sha(config),'/probe/native/export.tcl':host.sha(native/'export.tcl')},
            argv=['/nix/store/tool/bin/openroad','-exit','-no_init','/probe/native/export.tcl'],
            native_log_sha256=host.sha(native/'native.log'),
            artifacts_sha256={name:host.sha(native/name) for name in host.OUTPUTS})
        host.write(native/'report.json',packet)
        return native,database,config,packet

    def validate(self,native,database,config):
        return host.validate_native(native,database=('/work/run/actual.odb',database),config=config)

    def test_closed_native_views_bind_actual_checkpoint_and_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            native,database,config,packet=self.fixture(Path(tmp))
            result=self.validate(native,database,config)
            self.assertEqual(result['artifacts_sha256'],packet['artifacts_sha256'])
            self.assertEqual(result['actual_database_sha256'],host.sha(database))

    def test_post_freeze_odb_or_configuration_change_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            native,database,config,_=self.fixture(Path(tmp))
            for path in (database,config):
                before=path.read_bytes();path.write_bytes(before+b'\n')
                with self.subTest(path=path.name),self.assertRaisesRegex(ValueError,'exact checkpoint ODB/configuration'):
                    self.validate(native,database,config)
                path.write_bytes(before)

    def test_success_exit_cannot_hide_stale_or_inherited_netlist(self):
        with tempfile.TemporaryDirectory() as tmp:
            native,database,config,packet=self.fixture(Path(tmp))
            for field,value in [('completed',False),('inputs_unchanged',False),('inherited_netlist',True),
                    ('qualified',True),('physical_acceptance_claim',True),('exit_code',1)]:
                host.write(native/'report.json',dict(packet,**{field:value}))
                with self.subTest(field=field),self.assertRaisesRegex(ValueError,'not closed successfully'):
                    self.validate(native,database,config)

    def test_all_four_actual_views_required_and_byte_bound(self):
        with tempfile.TemporaryDirectory() as tmp:
            native,database,config,packet=self.fixture(Path(tmp))
            for name in host.OUTPUTS:
                path=native/name;before=path.read_bytes();path.write_bytes(before+b'changed')
                with self.subTest(name=name),self.assertRaisesRegex(ValueError,'changed actual ODB export view'):
                    self.validate(native,database,config)
                path.write_bytes(before)
            for artifacts in [dict(packet['artifacts_sha256'],extra='0'*64),
                    {key:value for key,value in packet['artifacts_sha256'].items() if key!='implemented.cdl'}]:
                host.write(native/'report.json',dict(packet,artifacts_sha256=artifacts))
                with self.assertRaisesRegex(ValueError,'view inventory'):self.validate(native,database,config)

    def test_changed_native_argv_script_log_or_top_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            native,database,config,packet=self.fixture(Path(tmp))
            changed=dict(packet,argv=['openroad','-exit','-no_init','/probe/native/export.tcl'])
            host.write(native/'report.json',changed)
            with self.assertRaisesRegex(ValueError,'argv/script/log'):self.validate(native,database,config)
            host.write(native/'report.json',packet)
            for name in ('export.tcl','native.log'):
                path=native/name;before=path.read_bytes();path.write_bytes(before+b'changed')
                with self.subTest(name=name),self.assertRaisesRegex(ValueError,'argv/script/log'):
                    self.validate(native,database,config)
                path.write_bytes(before)
            host.write(native/'report.json',dict(packet,top='tt_um_pinwheel_streaming_ready_d4'))
            with self.assertRaisesRegex(ValueError,'top differs'):self.validate(native,database,config)

    def test_cleanup_requires_exact_owned_ids_and_confirmed_absence(self):
        with tempfile.TemporaryDirectory() as tmp,(Path(tmp)/'log').open('w') as log:
            with patch.object(host.subprocess,'check_output',side_effect=['bad-id\n']):
                with self.assertRaisesRegex(ValueError,'Invalid owned'):host.owned_cleanup('label',log)
            with patch.object(host.subprocess,'check_output',side_effect=['','still-present']),\
                    patch.object(host.subprocess,'run') as stop:
                with self.assertRaisesRegex(ValueError,'remains'):host.owned_cleanup('label',log)
                stop.assert_not_called()
            identifier='a'*64
            with patch.object(host.subprocess,'check_output',side_effect=[identifier+'\n','']),\
                    patch.object(host.subprocess,'run') as stop:
                self.assertEqual(host.owned_cleanup('label',log)['status'],'absent')
                self.assertEqual(stop.call_args.args[0],['docker','stop','--time','5',identifier])

    def test_inherited_loader_or_compiler_override_refuses(self):
        host.check_environment({'PATH':'/usr/bin','PYTHONDONTWRITEBYTECODE':'1'})
        for name in ('PYTHONPATH','LD_PRELOAD','DYLD_INSERT_LIBRARIES','OPENROAD_INIT'):
            with self.subTest(name=name),self.assertRaisesRegex(ValueError,'inherited export'):
                host.check_environment({name:'/unqualified/override'})

    def test_frozen_closure_includes_actual_native_and_checkpoint_parsers(self):
        closure=host.dependency_closure(ROOT,host.PRODUCER_ENTRIES)
        self.assertIn('scripts/run-streaming-tt-sta.py',closure['files'])
        self.assertIn('scripts/streaming_tt_intake.py',closure['files'])
        self.assertIn('scripts/streaming_tt_export_signoff.py',closure['files'])


if __name__=='__main__':unittest.main()
