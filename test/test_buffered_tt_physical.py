"""Fail-closed input and supply geometry controls for the bounded TT baseline."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import subprocess
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import buffered_tt_physical as physical

spec = importlib.util.spec_from_file_location('buffered_tt_runner', ROOT/'scripts/run-buffered-tt-physical.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

# Geometry helpers are pure Python; fake only the native CLI imports for these
# controls. Actual OpenDB creation/removal is checked by the retained replay.
power_spec = importlib.util.spec_from_file_location('buffered_tt_power', ROOT/'physical/buffered_tt/connect_sram_power.py')
power = importlib.util.module_from_spec(power_spec)
with patch.dict(sys.modules, {'odb': SimpleNamespace(),
                             'click': SimpleNamespace(command=lambda: (lambda f: f), ClickException=RuntimeError),
                             'reader': SimpleNamespace(click_odb=lambda f: f)}):
    power_spec.loader.exec_module(power)


class BufferedTTPhysicalTests(unittest.TestCase):
    def geometry(self):
        # Deliberately irregular support-logic column; VDDARRAY only exists in
        # the two arrays, while all columns of the same polarity share VPWR.
        return dict(size_um=[100,64.36],pins={
            'VDD!': [[4.26,0,7.07,38.825],[15.50,0,18.31,38.825],[39.41,0,42.22,64.36]],
            'VDDARRAY!': [[4.26,45.465,7.07,64.36],[15.50,45.465,18.31,64.36]],
            'VSS!': [[9.88,0,12.69,64.36],[21.12,0,23.93,64.36],[44.56,0,47.37,64.36]],
        })

    def test_irregular_columns_and_template_pin_clearance(self):
        plan = physical.column_plan(self.geometry(), [])
        self.assertEqual(plan['nets']['VPWR'][-1],[291.765,293.865])
        self.assertEqual(len(plan['nets']['VPWR']),3)
        # The independent tile pin prevents the central full-height stripe,
        # while both split VDD/VDDARRAY contacts remain available.
        plan = physical.column_plan(self.geometry(), [[292,292.3]])
        self.assertEqual(len(plan['nets']['VPWR']),2)
        self.assertEqual(len(plan['skipped']['VPWR']),1)

    def test_missing_supply_contacts_rejected(self):
        with self.assertRaisesRegex(ValueError,'Insufficient clear power columns'):
            physical.column_plan(self.geometry(), [[250,300]])
        geometry=self.geometry()
        geometry['pins']['VDDARRAY!'] = geometry['pins']['VDDARRAY!'][:1]
        with self.assertRaisesRegex(ValueError,'too few clear direct contacts'):
            physical.column_plan(geometry, [])

    def test_wrong_polarity_overlap_rejected(self):
        geometry=self.geometry()
        geometry['pins']['VSS!'][0]=[4.26,0,7.07,64.36]
        with self.assertRaisesRegex(ValueError,'Supply stripe collision'):
            physical.column_plan(geometry, [])

    def test_frozen_config_and_validation_mutations_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder)
            stage=root/'stage';stage.mkdir()
            (root/'source.py').write_text('x=1\n')
            (stage/'core.json').write_text('{}\n')
            validation=root/'validation.json'
            physical.write(validation,dict(status='passed'))
            inputs=dict(schema='pinwheel-buffered-tt-physical-input-v1',
                        files_sha256={'core.json':physical.sha(stage/'core.json')},
                        source_sha256={'source.py':physical.sha(root/'source.py')},
                        validation_receipt=str(validation),validation_receipt_sha256=physical.sha(validation))
            physical.write(stage/'inputs.json',inputs)
            with patch.object(physical,'ROOT',root):
                physical.verify_prepared(stage)
                (stage/'core.json').write_text('{"RUN_KLAYOUT_DRC":false}\n')
                with self.assertRaisesRegex(ValueError,'Changed staged input'):
                    physical.verify_prepared(stage)
                (stage/'core.json').write_text('{}\n')
                physical.write(validation,dict(status='failed'))
                with self.assertRaisesRegex(ValueError,'Changed or failed wrapper validation'):
                    physical.verify_prepared(stage)

    def test_runtime_identity_and_missing_backend(self):
        config={'Env':['fixed'], 'Cmd':['fixed']}
        digest=hashlib.sha256(json.dumps(config,sort_keys=True).encode()).hexdigest()
        lock=dict(container_tag='pinned',container_rootfs_diff_ids=['layer1'],container_runtime_config_sha256=digest)
        image=dict(Config=config,Architecture='arm64',Os='linux',RootFS={'Layers':['layer1']},Id='image1')
        class Result:
            returncode=0
            stdout=json.dumps([image])
        with patch.object(runner.subprocess,'run',return_value=Result()):
            self.assertEqual(runner.inspect_runtime(lock)['image_id'],'image1')
            lock['container_rootfs_diff_ids']=['wrong']
            with self.assertRaisesRegex(ValueError,'differs from pinned'):
                runner.inspect_runtime(lock)
        with patch.object(runner.subprocess,'run',side_effect=FileNotFoundError('docker unavailable')):
            with self.assertRaises(FileNotFoundError):
                runner.inspect_runtime(lock)

    def test_interruption_and_timeout_clean_up_only_owned_container(self):
        for error, status, code in [(KeyboardInterrupt('test signal'),'interrupted',130),
                                    (subprocess.TimeoutExpired(['docker'],1),'timed_out',124)]:
            with self.subTest(status=status), tempfile.TemporaryDirectory() as folder:
                root=Path(folder);stage=root/'build/physical/candidate';stage.mkdir(parents=True)
                (root/'tools').mkdir()
                physical.write(root/'tools/physical-toolchain.json',{})
                physical.write(stage/'inputs.json',{})
                physical.write(stage/'core.json',dict(PDN_MULTILAYER=False,PDN_CONNECT_MACROS_TO_GRID=True,RT_MAX_LAYER='Metal4',RUN_KLAYOUT_DRC=True,RUN_MAGIC_DRC=True,
                    meta={'flow':'Classic','substituting_steps':{'+OpenROAD.GeneratePDN':'Project.BufferedSramPower'}}))
                inputs=dict(status='ready',missing_macro_views=[],boundary='bounded fixture',disabled_checks=[])
                def launch_then_interrupt(*args,**kwargs):
                    self.assertTrue((stage/'runs/owned').is_dir(),'LibreLane run directory must exist before launch')
                    raise error
                with patch.object(runner,'ROOT',root), patch.object(sys,'argv',['runner','--design','candidate','--tag','owned','--timeout-seconds','1']), \
                     patch.object(runner,'verify_prepared',return_value=inputs), \
                     patch.object(runner,'inspect_runtime',return_value={'image_id':'pinned'}), \
                     patch.object(runner,'check_container_name'), \
                     patch.object(runner,'verify_pdk',return_value={}), \
                     patch.object(runner.subprocess,'run',side_effect=launch_then_interrupt), \
                     patch.object(runner,'cleanup_container',return_value={'status':'absent'}) as cleanup:
                    self.assertEqual(runner.main(),code)
                report=physical.read(root/'build/physical/owned-invocation.json')
                self.assertEqual(cleanup.call_args.args[0],report['ownership_label'])
                self.assertEqual(report['status'],status)
                self.assertEqual(report['container_termination']['status'],'absent')
                self.assertTrue(report['inputs_unchanged_after_run'])
                self.assertEqual(report['network'],'none')
                self.assertEqual(report['cpus'],4)
                self.assertEqual(report['memory'],'6g')

    def test_larger_walltime_is_rejected_before_launch(self):
        with patch.object(sys,'argv',['runner','--design','candidate','--tag','owned','--timeout-seconds','1801']), \
             patch.object(runner.subprocess,'run') as run:
            with self.assertRaises(SystemExit) as error:
                runner.main()
            self.assertEqual(error.exception.code,2)
            run.assert_not_called()

    def test_foreign_name_collision_is_not_stopped(self):
        class Result:
            returncode=0
            stdout='pinwheel-owned\n'
            stderr=''
        with patch.object(runner.subprocess,'run',return_value=Result()) as run:
            with self.assertRaisesRegex(ValueError,'preexisting container'):
                runner.check_container_name('pinwheel-owned')
            self.assertTrue(all('stop' not in call.args[0] for call in run.call_args_list))
        # In the race where another worktree wins the name after preflight,
        # cleanup sees no container bearing this attempt's random label.
        Result.stdout=''
        with patch.object(runner.subprocess,'run',return_value=Result()) as run:
            result=runner.cleanup_container('our-unique-owner',None)
            self.assertEqual(result['status'],'absent')
            self.assertTrue(all('stop' not in call.args[0] for call in run.call_args_list))

    def test_missing_declared_flow_cannot_start(self):
        config=dict(PDN_MULTILAYER=False,PDN_CONNECT_MACROS_TO_GRID=True,RT_MAX_LAYER='Metal4',RUN_KLAYOUT_DRC=True,RUN_MAGIC_DRC=True,
                    meta={'flow':'Classic','substituting_steps':{'+OpenROAD.GeneratePDN':'Project.BufferedSramPower'}})
        physical.validate_flow_config(config)
        del config['meta']['flow']
        with self.assertRaisesRegex(ValueError,'Explicit Classic flow'):
            physical.validate_flow_config(config)

    def test_false_macro_connection_flag_cannot_start(self):
        config=dict(PDN_MULTILAYER=False,PDN_CONNECT_MACROS_TO_GRID=False,RT_MAX_LAYER='Metal4',RUN_KLAYOUT_DRC=True,RUN_MAGIC_DRC=True,
                    meta={'flow':'Classic','substituting_steps':{'+OpenROAD.GeneratePDN':'Project.BufferedSramPower'}})
        with self.assertRaisesRegex(ValueError,'Explicit SRAM supply hooks require'):
            physical.validate_flow_config(config)

    def test_distinct_open_db_net_proxies_use_block_unique_name(self):
        class Net:
            def __init__(self, name): self.name=name
            def getName(self): return self.name
        left, right=Net('VPWR'), Net('VPWR')
        self.assertNotEqual(left, right)
        self.assertTrue(power.same_net(left, right))
        self.assertFalse(power.same_net(left, Net('VGND')))
        self.assertFalse(power.same_net(None, right))

    def test_via_stack_requires_enclosed_landings_and_intermediate_overlap(self):
        column=(100,0,2200,710640); rail=(0,9780,5000,10220)
        stack=[{'Metal1':[(185,9780,2115,10220)],'Metal2':[(230,9855,2070,10145)]},
               {'Metal2':[(230,9855,2070,10145)],'Metal3':[(185,9900,2115,10100)]},
               {'Metal3':[(185,9900,2115,10100)],'Metal4':[(100,9855,2200,10145)]}]
        self.assertTrue(power.stack_fits(stack,column,rail))
        # A center inside a rail is insufficient when the via landing extends
        # beyond its clipped end; this case must not create a floating stack.
        self.assertFalse(power.stack_fits(stack,column,(250,9780,5000,10220)))
        self.assertFalse(power.stack_fits(stack,(200,0,2100,710640),rail))
        stack[1]['Metal2']=[(230,10145,2070,10435)]
        self.assertFalse(power.stack_fits(stack,column,rail))

    def test_opposite_metal_clearance_accepts_exact_gap_rejects_intrusion(self):
        column=(100,0,2200,710640)
        self.assertFalse(power.overlaps(column,(2440,0,4540,710640),240))
        self.assertTrue(power.overlaps(column,(2439,0,4539,710640),240))


if __name__=='__main__':
    unittest.main()
