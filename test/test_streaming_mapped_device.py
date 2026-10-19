"""Full hook preflight cannot start native tools with incomplete boundaries."""
from pathlib import Path
import json
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock,patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_mapped_device import wrapper_hook,NativeAudit


class DeviceTests(unittest.TestCase):
    def test_missing_component_refuses_before_device_creation_or_native_tools(self):
        with tempfile.TemporaryDirectory() as temporary:
            out=Path(temporary);worker=SimpleNamespace(out=out,run=Mock())
            for contexts in ([],[dict(label='frontend')],[dict(label='frontend'),dict(label='core-d2'),dict(label='unexpected')]):
                with self.subTest(contexts=contexts),self.assertRaisesRegex(ValueError,'component contexts'):wrapper_hook(worker,contexts)
            worker.run.assert_not_called();self.assertFalse((out/'device').exists())

    def test_missing_depth_or_changed_wrapper_abi_refuses_before_native_use(self):
        for device in ({},{'2':{}},{'2':dict(tiny='relative',package='relative',bridge='relative'),'4':{}}):
            with tempfile.TemporaryDirectory() as temporary:
                out=Path(temporary);worker=SimpleNamespace(out=out,config=dict(device=device),run=Mock(),library=object())
                contexts=[dict(label=label,proof=out/label) for label in ('frontend','core-d2','core-d4')]
                with self.assertRaises(ValueError):wrapper_hook(worker,contexts)
                worker.run.assert_not_called()

    def native(self,root,*,returncode=0):
        import streaming_rtl,streaming_ready_wire_cases,streaming_wire_cases
        log=root/'journal.jsonl';exe=root/'native.vvp';exe.write_bytes(b'actual selected executable')
        calls=[]
        class Native:
            def __init__(self,vvp,executable,**options):
                # The fsynced intent must already exist when the native client
                # constructor (and therefore Popen) is reached.
                event=json.loads(log.read_text().splitlines()[-1]);calls.append(event)
                if event['event']!='intent':raise RuntimeError('Popen preceded intent')
                self.process=SimpleNamespace(args=[str(vvp),str(executable)],returncode=returncode);self.cycle=3
            def __enter__(self):return self
            def __exit__(self,*args):return False
        aliases=(streaming_rtl,streaming_ready_wire_cases,streaming_wire_cases)
        return log,exe,calls,Native,aliases

    def test_native_intent_precedes_every_start_and_all14_closed_processes_are_bound(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);log,exe,calls,Native,aliases=self.native(root)
            with patch.object(aliases[0],'QuadRTL',Native),patch.object(aliases[1],'QuadRTL',Native),patch.object(aliases[2],'QuadRTL',Native):
                with NativeAudit(log,'selected-vvp',[exe]) as audit:
                    for scope in ['uart']*2+['legacy']*2+['i2c']*10:
                        audit.scope=scope
                        with aliases[0].QuadRTL('selected-vvp',exe):pass
                self.assertTrue(all(module.QuadRTL is Native for module in aliases))
            events=[json.loads(line) for line in log.read_text().splitlines()]
            self.assertEqual(len(calls),14);self.assertEqual(len(events),28)
            for index,record in enumerate(audit.records):
                self.assertEqual(record['index'],index);self.assertEqual(record['argv'],record['actual_argv'])
                self.assertEqual(record['native_exit_code'],0);self.assertTrue(record['client_succeeded'])
                self.assertEqual(record['executable_sha256_before'],record['executable_sha256_after'])
                self.assertEqual([event['event'] for event in events[2*index:2*index+2]],['intent','result'])

    def test_native_unselected_tool_executable_or_scope_refuses_before_Popen(self):
        for mode in ('tool','executable','scope'):
            with tempfile.TemporaryDirectory() as temporary:
                root=Path(temporary);log,exe,calls,Native,aliases=self.native(root);other=root/'other';other.write_bytes(b'other')
                with patch.object(aliases[0],'QuadRTL',Native),patch.object(aliases[1],'QuadRTL',Native),patch.object(aliases[2],'QuadRTL',Native):
                    with self.assertRaisesRegex(ValueError,'Unexpected native'):
                        with NativeAudit(log,'selected-vvp',[exe]) as audit:
                            audit.scope='invalid' if mode=='scope' else 'uart'
                            aliases[0].QuadRTL('other-vvp' if mode=='tool' else 'selected-vvp',other if mode=='executable' else exe)
                    self.assertTrue(all(module.QuadRTL is Native for module in aliases))
                self.assertFalse(log.exists());self.assertEqual(calls,[])

    def test_native_crash_changed_executable_and_missing_processes_refuse_at_closeout(self):
        for mode in ('crash','changed','missing'):
            with tempfile.TemporaryDirectory() as temporary:
                root=Path(temporary);log,exe,calls,Native,aliases=self.native(root,returncode=1 if mode=='crash' else 0)
                with patch.object(aliases[0],'QuadRTL',Native),patch.object(aliases[1],'QuadRTL',Native),patch.object(aliases[2],'QuadRTL',Native):
                    with self.assertRaises(ValueError):
                        with NativeAudit(log,'selected-vvp',[exe]) as audit:
                            scopes=['uart']*2+['legacy']*2+['i2c']*(9 if mode=='missing' else 10)
                            for index,scope in enumerate(scopes):
                                audit.scope=scope
                                with aliases[0].QuadRTL('selected-vvp',exe):
                                    if mode=='changed' and index==len(scopes)-1:exe.write_bytes(b'changed after native start')
                    self.assertTrue(all(module.QuadRTL is Native for module in aliases))

    def test_native_body_exception_is_preserved_and_all_client_aliases_restore(self):
        class OriginalFailure(Exception):pass
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);log,exe,calls,Native,aliases=self.native(root)
            with patch.object(aliases[0],'QuadRTL',Native),patch.object(aliases[1],'QuadRTL',Mock),patch.object(aliases[2],'QuadRTL',SimpleNamespace):
                original=[module.QuadRTL for module in aliases]
                with self.assertRaisesRegex(OriginalFailure,'native caller failed'):
                    with NativeAudit(log,'selected-vvp',[exe]) as audit:
                        audit.scope='uart'
                        with aliases[1].QuadRTL('selected-vvp',exe):raise OriginalFailure('native caller failed')
                self.assertEqual([module.QuadRTL for module in aliases],original)
                self.assertFalse(audit.records[0]['client_succeeded'])


if __name__=='__main__':unittest.main()
