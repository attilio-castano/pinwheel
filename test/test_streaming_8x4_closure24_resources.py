"""HOST controls only: actual inherited guard, no real child or container."""
from datetime import timedelta
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_acceptance as OLD
import streaming_8x4_closure24_policy as P
import streaming_8x4_closure24_resources as W


class Process:
    pid=987654321
    returncode=0
    def __init__(self,running=False,tamper=None):self.running,self.tamper=running,tamper
    def poll(self):
        if self.tamper is not None:self.tamper.write_text('changed')
        return None if self.running else 0
    def wait(self,timeout):return 0


class Closure24(unittest.TestCase):
    def fixture(self,temp,kind='solver',timeout=1):
        root=Path(temp);(root/'scripts').mkdir()
        for name in P.HISTORICAL:(root/name).write_bytes((ROOT/name).read_bytes())
        seal=root/'input';seal.write_text('original')
        args=['--campaign-root',str(root),'--kind',kind,'--tag','control','--timeout-seconds',str(timeout),
            '--input',str(seal)]
        family=P.KINDS[kind][0]
        if family in P.FIXED:
            parent=root/'parent';parent.write_text('frozen parent');args+=['--validation-parent',str(parent)]
        if family in {'timing_eco_cad','qualified_timing'}:
            model=root/'model';model.write_text('typed worker must independently qualify this');args+=['--model-qualification',str(model)]
        if family=='timing_eco_cad':
            failure=root/'timing';failure.write_text('typed worker must independently admit failure');args+=['--timing-failure',str(failure)]
        if family in {'candidate_cad','timing_eco_cad','fixed_cad','qualified_timing','rc_experiment','rc_validation'}:
            args+=['--container-name','pinwheel-control']
        args+=['--','never-executed']
        return W.parser().parse_args(args),W.load_guard(root),seal

    def execute(self,args,guard,child):
        sample=dict(utc=P.SCHEDULE['start'],memory_available_percent=90,disk_free_bytes=64*1024**3)
        with patch.object(guard,'observation',return_value=sample),patch.object(guard,'process_table',return_value={}),\
             patch.object(guard.shutil,'which',return_value=None),patch.object(guard,'docker_ids',return_value=[]),\
             patch.object(guard,'container_observation',return_value=None),\
             patch.object(guard.subprocess,'Popen',return_value=child) as spawn,\
             patch.object(guard.time,'sleep'),patch.object(guard.time,'monotonic',side_effect=itertools.chain([0,.1,2],itertools.repeat(2.1))),\
             patch.object(guard.signal,'signal'),patch.object(guard.signal,'setitimer'):
            status=W.run(args,guard=guard,now=P.SCHEDULE['start'])
        row=json.loads((args.campaign_root/'build/streaming-tt-resources/control/report.json').read_text())
        return status,row,spawn

    def test_exact24_clock_and_original12_clock_stays_frozen(self):
        values=P.schedule_values(P.SCHEDULE)
        self.assertEqual(values['hard_deadline']-values['start'],timedelta(hours=24))
        self.assertIs(P.GATES,OLD.GATES);self.assertIs(P.MODEL_COVERAGE,OLD.MODEL_COVERAGE)
        self.assertIs(P.summarize,OLD.summarize);self.assertEqual(len(P.MODEL_COVERAGE),8)
        self.assertEqual(set(P.historical_sources(ROOT)),{str(ROOT/name) for name in P.HISTORICAL})
        old=dict(start=P.SCHEDULE['start'],candidate_cutoff=P.SCHEDULE['primary_route_cutoff'],
            rc_experiment_cutoff=P.SCHEDULE['model_cutoff'],heavy_cutoff=P.SCHEDULE['heavy_cutoff'],hard_deadline=P.SCHEDULE['hard_deadline'])
        with self.assertRaisesRegex(ValueError,'twelve-hour'):OLD.schedule_values(old)
        for key in P.SCHEDULE:
            changed=dict(P.SCHEDULE);changed[key]=(P.timestamp(changed[key])+timedelta(seconds=1)).isoformat()
            with self.assertRaises(ValueError):P.schedule_values(changed)

    def test_every_kind_stops_at_exact_cut_and_never_borrows_reserve(self):
        for kind,(family,_,cut) in P.KINDS.items():
            parent='a'*64 if family in P.FIXED else None
            end=P.timestamp(P.SCHEDULE[cut]);now=(end-timedelta(minutes=5)).isoformat()
            row=P.job_window(kind,P.SCHEDULE,now,14400,frozen_parent_sha256=parent)
            self.assertEqual(row['timeout_seconds'],280)
            for time in (end,end-timedelta(seconds=20)):
                with self.assertRaises(ValueError):P.job_window(kind,P.SCHEDULE,time.isoformat(),1,frozen_parent_sha256=parent)
        self.assertEqual(P.KINDS['timing-eco-cad'][2],'candidate_freeze')
        self.assertEqual(P.KINDS['qualified-timing'][2],'qualified_timing_cutoff')

    def test_four_hour_no_early_start_and_fixed_parent_are_strict(self):
        for timeout in (0,14401,True):
            with self.assertRaises(ValueError):P.job_window('solver',P.SCHEDULE,P.SCHEDULE['start'],timeout)
        with self.assertRaises(ValueError):P.job_window('solver',P.SCHEDULE,'2026-10-24T14:38:14Z',1)
        with self.assertRaises(ValueError):P.job_window('lean',P.SCHEDULE,P.SCHEDULE['start'],1)
        with self.assertRaises(ValueError):P.job_window('cad',P.SCHEDULE,P.SCHEDULE['start'],1,frozen_parent_sha256='a'*64)

    def test_real_guard_positive_uses_shared_root_and_all_source_seals(self):
        with tempfile.TemporaryDirectory() as temp:
            args,guard,_=self.fixture(temp);guard.BASE=Path('/wrong');guard.ROOT=Path('/wrong')
            status,row,spawn=self.execute(args,guard,Process())
            self.assertEqual(status,0);self.assertEqual(spawn.call_count,1)
            self.assertTrue(row['cleanup_confirmed']);self.assertFalse(row['acceptance_claim'])
            boundary=row['campaign_boundary'];self.assertEqual(boundary['schema'],'pinwheel.streaming-8x4-closure24-resource-boundary.v1')
            self.assertEqual(boundary['shared_lease'],P.shared_lease_paths(args.campaign_root))
            self.assertFalse(boundary['engineering_evidence_verified'])
            for path in [str(Path(W.__file__).resolve()),str(Path(P.__file__).resolve()),*P.historical_sources(args.campaign_root)]:
                self.assertEqual(row['input_sha256'][path],P.sha(path))

    def test_real_guard_timeout_and_input_tamper_remain_failures(self):
        for failure in ('timeout','tamper'):
            with tempfile.TemporaryDirectory() as temp:
                args,guard,seal=self.fixture(temp)
                status,row,_=self.execute(args,guard,Process(running=failure=='timeout',tamper=seal if failure=='tamper' else None))
                self.assertEqual(status,1);self.assertTrue(row['cleanup_confirmed'])
                self.assertEqual(row['status'],'stopped' if failure=='timeout' else 'invalidated')
                self.assertFalse(row['acceptance_claim'])

    def test_eco_requires_both_separate_evidences_and_preserves_hashes(self):
        with tempfile.TemporaryDirectory() as temp:
            args,guard,_=self.fixture(temp,'timing-eco-cad')
            failure=args.timing_failure;args.timing_failure=None
            with patch.object(guard,'main') as main,self.assertRaises(ValueError):W.run(args,guard=guard,now=P.SCHEDULE['start'])
            main.assert_not_called();args.timing_failure=failure
            status,row,_=self.execute(args,guard,Process())
            self.assertEqual(status,0);b=row['campaign_boundary']
            self.assertEqual(b['timing_failure_evidence']['sha256'],P.sha(failure))
            self.assertFalse(b['engineering_evidence_verified'])

    def test_container_cpu_memory_swap_and_network_caps_are_real_config_checks(self):
        for kind in ('cad','lean','solver','public-wire'):
            limits=P.resource_limits(kind)
            config=dict(Memory=limits['container_memory_bytes'],MemorySwap=limits['container_memory_bytes'],
                NanoCpus=limits['container_cpus']*10**9,NetworkMode='none')
            W.validate_container(dict(HostConfig=config),limits)
            for key,value in [('Memory',config['Memory']+1),('MemorySwap',config['Memory']+1),
                ('NanoCpus',config['NanoCpus']+1),('NetworkMode','bridge')]:
                with self.assertRaises(ValueError):W.validate_container(dict(HostConfig=dict(config,**{key:value})),limits)

    def test_deadline_override_wrong_historical_guard_and_late_launch_reject(self):
        with tempfile.TemporaryDirectory() as temp:
            args,guard,_=self.fixture(temp)
            with patch.object(guard,'main') as main,self.assertRaises(ValueError):W.run(args,guard=guard,now=P.SCHEDULE['model_cutoff'])
            main.assert_not_called();args.deadline=P.SCHEDULE['hard_deadline']
            with self.assertRaises(ValueError):W.run(args,guard=guard,now=P.SCHEDULE['start'])
            args.deadline=None;(args.campaign_root/'scripts/streaming_8x4_acceptance_resources.py').write_text('changed')
            with self.assertRaisesRegex(ValueError,'Historical'):W.run(args,guard=guard,now=P.SCHEDULE['start'])

    def test_actual_inspect_hook_rejects_proof_cpu_overcap_without_native(self):
        for cpus in (1,2):
            with tempfile.TemporaryDirectory() as temp:
                args,guard,_=self.fixture(temp,'lean')
                config=dict(HostConfig=dict(Memory=4*1024**3,MemorySwap=4*1024**3,NanoCpus=cpus*10**9,NetworkMode='none'))
                def main():guard.command(['docker','inspect','observed-id']);return 0
                with patch.object(guard,'command',return_value=json.dumps([config])),patch.object(guard,'main',side_effect=main):
                    if cpus==1:self.assertEqual(W.run(args,guard=guard,now=P.SCHEDULE['start']),0)
                    else:
                        with self.assertRaisesRegex(ValueError,'CPU cap'):W.run(args,guard=guard,now=P.SCHEDULE['start'])

    def test_evidence_change_between_admission_and_inherited_seal_rejects(self):
        with tempfile.TemporaryDirectory() as temp:
            args,guard,_=self.fixture(temp,'lean')
            def main():
                args.validation_parent.write_text('changed')
                guard.admission_window('lean',P.timestamp(P.SCHEDULE['heavy_cutoff']),P.timestamp(P.SCHEDULE['start']))
                return 0
            with patch.object(guard,'main',side_effect=main),self.assertRaisesRegex(ValueError,'Frozen admission'):
                W.run(args,guard=guard,now=P.SCHEDULE['start'])


if __name__=='__main__':unittest.main()
