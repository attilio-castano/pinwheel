"""Actual validation launch argv must satisfy the campaign's resource guard.

All CAD processes and artifact verdicts are mocked; these tests exercise the
host dispatch paths and their recorded bounds, never claim physical results.
"""
from contextlib import ExitStack
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_tt_gds_diagnostic as G
import streaming_tt_native_layout as L
import streaming_tt_resources as R


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


STA = load('validation_resource_sta', 'run-streaming-tt-sta.py')
EXPORT = load('validation_resource_export', 'run-streaming-tt-signoff-export.py')


class ValidationResourceTests(unittest.TestCase):
    def fixture(self, root):
        root = root.resolve(); flow = root/'flow'; flow.mkdir(); inputs = root/'inputs'; inputs.mkdir()
        out = root/'attempt'; out.mkdir()
        for path in (flow/'actual.odb', flow/'actual.gds', root/'actual.cdl', inputs/'core.sdc',
                root/'physical.json', root/'state.json'):
            path.write_bytes(b'frozen host fixture')
        (flow/'resolved.json').write_text('{"DESIGN_NAME":"tt_um_pinwheel_streaming_ready_d2"}')
        return dict(root=root, out=out, flow=flow, roots={'/work/run':flow, '/work/inputs':inputs, '/work/pdk':root/'pdk'},
            report=dict(source_commit='a'*40, producer_commit='a'*40, status='flow_completed', exit_code=0),
            runtime=dict(image_id='sha256:'+'b'*64), physical=root/'physical.json', state=root/'state.json',
            odb=flow/'actual.odb', gds=flow/'actual.gds', cdl=root/'actual.cdl')

    @staticmethod
    def check_output(argv, **options):
        value = 'a'*40+'\n' if argv[0] == 'git' else ''
        return value if options.get('text') else value.encode()

    def verify_resources(self, argv, packet, name, memory):
        for flag, value in [('--name',name), ('--memory',memory), ('--memory-swap',memory),
                ('--cpus','1'), ('--network','none')]:
            self.assertEqual(argv.count(flag), 1)
            self.assertEqual(argv[argv.index(flag)+1], value)
        self.assertEqual(packet['memory'], memory); self.assertEqual(packet['memory_swap'], memory)
        self.assertEqual(packet['cpus'], 1); self.assertEqual(packet['network'], 'none')
        multiplier = 1024**3 if memory.endswith('g') else 1024**2
        size = int(memory[:-1])*multiplier
        info = dict(Id='c'*64, HostConfig=dict(Memory=size, MemorySwap=size, NanoCpus=10**9, NetworkMode='none'),
            State=dict(Running=True))
        with patch.object(R, 'docker_ids', return_value=['c'*64]) as owned, \
                patch.object(R, 'command', side_effect=[json.dumps([info]), '10%']):
            self.assertEqual(R.container_observation(name)['memory_swap_bytes'], size)
            owned.assert_called_with(name)
        info['HostConfig']['MemorySwap'] = size*2
        with patch.object(R, 'docker_ids', return_value=['c'*64]), \
                patch.object(R, 'command', return_value=json.dumps([info])):
            with self.assertRaisesRegex(ValueError, 'swap must be disabled'):
                R.container_observation(name)

    def test_sta_dispatch_and_receipt_are_guard_compatible(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            f = self.fixture(Path(tmp)); process = Mock(); process.wait.return_value=0; process.poll.return_value=0
            replacements = dict(checkpoint=(f['report'],f['roots'],'/work/run/actual.odb',f['odb']),
                constraints={}, pdk_identity={}, inspect_runtime=f['runtime'], dependency_closure={'files':[]},
                fresh_directory=f['out'])
            for name, value in replacements.items(): stack.enter_context(patch.object(STA,name,return_value=value))
            stack.enter_context(patch.object(STA,'stage_sources'))
            launch = stack.enter_context(patch.object(STA.subprocess,'Popen',return_value=process))
            stack.enter_context(patch.object(STA.subprocess,'check_output',side_effect=self.check_output))
            stack.enter_context(patch.object(sys,'argv',['sta','--physical-report',str(f['physical']),
                '--state',str(f['state']),'--tag','resource-sta']))
            self.assertEqual(STA.main(), 0)
            packet=STA.read(f['out']/'report.json')
            self.assertEqual(packet['argv'],launch.call_args.args[0])
            self.verify_resources(packet['argv'],packet,'pinwheel-sta-resource-sta','2g')

    def test_odb_export_dispatch_and_receipt_are_guard_compatible(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            f=self.fixture(Path(tmp)); process=Mock(); process.wait.return_value=0; process.poll.return_value=0
            for name,value in dict(checkpoint=(f['report'],f['roots'],'/work/run/actual.odb',f['odb']),
                    constraints={},pdk_identity={}).items():
                stack.enter_context(patch.object(EXPORT.checkpoint_host,name,return_value=value))
            for name,value in dict(inspect_runtime=f['runtime'],dependency_closure={'files':[]},
                    fresh_directory=f['out'],validate_native={}).items():
                stack.enter_context(patch.object(EXPORT,name,return_value=value))
            stack.enter_context(patch.object(EXPORT,'stage_sources'))
            launch=stack.enter_context(patch.object(EXPORT.subprocess,'Popen',return_value=process))
            stack.enter_context(patch.object(EXPORT.subprocess,'check_output',side_effect=self.check_output))
            stack.enter_context(patch.object(sys,'argv',['export','--physical-report',str(f['physical']),
                '--state',str(f['state']),'--tag','resource-export']))
            self.assertEqual(EXPORT.main(),0)
            packet=EXPORT.read(f['out']/'report.json')
            self.assertEqual(packet['argv'],launch.call_args.args[0])
            self.verify_resources(packet['argv'],packet,'pinwheel-export-resource-export','2g')

    def test_gds_dispatch_and_receipt_are_guard_compatible(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            f=self.fixture(Path(tmp)); process=Mock(); process.wait.return_value=0; process.poll.return_value=0
            (f['out']/'native-report.json').write_text('{}')
            api=SimpleNamespace(check_environment=lambda:None,validate_native=lambda *a,**k:{},
                owned_cleanup=lambda *a:dict(status='absent'))
            for name,value in dict(intake=(f['report'],f['roots'],'/work/run/actual.odb',f['odb'],{}),
                    export_api=api,checkpoint_api=SimpleNamespace(pdk_identity=lambda *a:{}),
                    dependency_closure={'files':[]},fresh_directory=f['out'],validate_native={}).items():
                stack.enter_context(patch.object(G,name,return_value=value))
            stack.enter_context(patch.object(G.P,'inspect_runtime',return_value=f['runtime']))
            stack.enter_context(patch.object(G,'stage_sources'))
            launch=stack.enter_context(patch.object(G.subprocess,'Popen',return_value=process))
            stack.enter_context(patch.object(G.subprocess,'check_output',side_effect=self.check_output))
            self.assertEqual(G.run(f['physical'],f['state'],'resource-gds',30),0)
            packet=G.read(f['out']/'report.json')
            self.assertEqual(packet['argv'],launch.call_args.args[0])
            self.verify_resources(packet['argv'],packet,'pinwheel-gds-resource-gds','1024m')

    def test_all_four_layout_dispatches_share_one_guarded_attempt_name(self):
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            f=self.fixture(Path(tmp)); top='tt_um_pinwheel_streaming_ready_d2'; captured=[]
            def stage(root,destination,files,committed):
                target=destination/'scripts/streaming_tt_layout.py'; target.parent.mkdir(parents=True)
                shutil.copyfile(ROOT/'scripts/streaming_tt_layout.py',target)
            def execute(argv,label,timeout,out,name):
                captured.append(argv); kind=name.split('-')[0]; extension='xml' if kind=='antenna' else 'lvsdb'
                if name.endswith('-interpret'):
                    L.write(out/(kind+'-result.json'),dict(schema='pinwheel.streaming-tt-layout-result.v1',
                        report_sha256=L.sha(out/(kind+'.'+extension)),
                        reader_sha256=L.sha(out/'producer/scripts/streaming_tt_layout.py'),top=top,result={'passed':True}))
                else: (out/(kind+'.'+extension)).write_bytes(b'mocked Native report')
                return dict(argv=argv,status='completed',exit_code=0,owned_container_absent=True)
            for name,value in dict(actual_inputs=(f['report'],f['roots'],top,f['gds'],f['cdl'],{}),
                    fresh_directory=f['out'],inspect_runtime=f['runtime'],
                    timing_host=SimpleNamespace(pdk_identity=lambda *a:{}),
                    dependency_closure={'files':['scripts/streaming_tt_layout.py']}).items():
                stack.enter_context(patch.object(L,name,return_value=value))
            stack.enter_context(patch.object(L,'stage_sources',side_effect=stage))
            stack.enter_context(patch.object(L,'run_command',side_effect=execute))
            stack.enter_context(patch.object(L.subprocess,'check_output',side_effect=self.check_output))
            path=L.run(f['physical'],f['state'],f['root']/'export.json','resource-layout',30)
            packet=L.read(path); self.assertEqual(len(captured),4)
            self.assertEqual([row['argv'] for row in packet['commands']],captured)
            self.assertEqual(packet['container_name'],'pinwheel-layout-resource-layout')
            for argv in captured:
                self.verify_resources(argv,packet,'pinwheel-layout-resource-layout','2g')


if __name__ == '__main__': unittest.main()
