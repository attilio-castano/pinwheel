"""Portable HOST controls: inherited supervisor exercised with no actual child/Docker."""
from datetime import timedelta
import itertools
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_acceptance as OLD
import streaming_8x4_closure24_policy as PREVIOUS
import streaming_8x4_closure48_policy as P
import streaming_8x4_closure48_resources as W


class Process:
    pid=987654321
    returncode=0
    def __init__(self,running=False,tamper=None):self.running,self.tamper=running,tamper
    def poll(self):
        if self.tamper is not None:self.tamper.write_text('changed')
        return None if self.running else 0
    def wait(self,timeout):return 0


class Closure48(unittest.TestCase):
    def fixture(self,temp,kind='reference-probe',timeout=1):
        root=Path(temp);(root/'scripts').mkdir()
        for name in P.HISTORICAL:(root/name).write_bytes((ROOT/name).read_bytes())
        seal=root/'input';seal.write_text('original')
        args=['--campaign-root',str(root),'--kind',kind,'--tag','control','--timeout-seconds',str(timeout),
            '--input',str(seal)]
        family=P.KINDS[kind][0]
        if family in P.FIXED:
            parent=root/'parent';parent.write_text('frozen parent');args+=['--validation-parent',str(parent)]
        if family not in {'proof','public_wire','host_closeout'}:args+=['--container-name','pinwheel-control']
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

    def test_exact48_schedule_original_mathematics_and_old_clocks_frozen(self):
        values=P.schedule_values(P.SCHEDULE)
        self.assertEqual(P.CAMPAIGN,'8x4-20261025-01')
        self.assertEqual([int((value-values['start']).total_seconds()/3600) for value in values.values()],
            [0,4,24,36,46,47,48])
        for name in ('GATES','MODEL_COVERAGE','CAPACITY','summarize','pass_gate','model_qualification'):
            self.assertIs(getattr(P,name),getattr(OLD,name))
        self.assertEqual(len(P.MODEL_COVERAGE),8)
        self.assertEqual(P.historical_sources(ROOT),{str(ROOT/name):pin for name,pin in P.HISTORICAL.items()})
        with self.assertRaises(ValueError):PREVIOUS.schedule_values(P.SCHEDULE)
        old=dict(start=P.SCHEDULE['start'],candidate_cutoff=P.SCHEDULE['reference_decision'],
            rc_experiment_cutoff=P.SCHEDULE['model_cutoff'],heavy_cutoff=P.SCHEDULE['heavy_cutoff'],hard_deadline=P.SCHEDULE['hard_deadline'])
        with self.assertRaisesRegex(ValueError,'twelve-hour'):OLD.schedule_values(old)
        for key in P.SCHEDULE:
            changed=dict(P.SCHEDULE);changed[key]=(P.timestamp(changed[key])+timedelta(seconds=1)).isoformat()
            with self.assertRaises(ValueError):P.schedule_values(changed)
        with self.assertRaises(ValueError):P.schedule_values(dict(P.SCHEDULE,extra=P.SCHEDULE['start']))

    def test_every_cut_exact_and_cleanup_hour_cannot_be_borrowed(self):
        for kind,(family,_,cut) in P.KINDS.items():
            parent='a'*64 if family in P.FIXED else None
            end=P.timestamp(P.SCHEDULE[cut]);now=(end-timedelta(minutes=5)).isoformat()
            row=P.job_window(kind,P.SCHEDULE,now,14400,frozen_parent_sha256=parent)
            self.assertEqual(row['timeout_seconds'],280)
            self.assertFalse(row['acceptance_claim'])
            for time in (end,end-timedelta(seconds=20)):
                with self.assertRaises(ValueError):P.job_window(kind,P.SCHEDULE,time.isoformat(),1,frozen_parent_sha256=parent)
        self.assertEqual(P.KINDS['reference-probe'][2],'reference_decision')
        self.assertEqual(P.KINDS['solver'][2],'model_cutoff')
        self.assertEqual(P.KINDS['timing-eco-cad'][2],'candidate_freeze')
        self.assertEqual(P.KINDS['qualified-timing'][2],'final_checks_cutoff')
        self.assertEqual(P.KINDS['lean'][2],'heavy_cutoff')

    def test_four_hour_maximum_early_start_and_exact_parent(self):
        for timeout in (0,14401,True):
            with self.assertRaises(ValueError):P.job_window('solver',P.SCHEDULE,P.SCHEDULE['start'],timeout)
        with self.assertRaises(ValueError):P.job_window('solver',P.SCHEDULE,'2026-10-25T22:38:16Z',1)
        for parent in (None,'a'*63,True):
            with self.assertRaises(ValueError):P.job_window('lean',P.SCHEDULE,P.SCHEDULE['start'],1,frozen_parent_sha256=parent)
        for parent in ('a'*64,'not a digest'):
            with self.assertRaises(ValueError):P.job_window('cad',P.SCHEDULE,P.SCHEDULE['start'],1,frozen_parent_sha256=parent)

    def test_real_guard_reference_probe_uses_one_shared_lease_and_source_seals(self):
        with tempfile.TemporaryDirectory() as temp:
            args,guard,_=self.fixture(temp);guard.BASE=Path('/wrong');guard.ROOT=Path('/wrong')
            status,row,spawn=self.execute(args,guard,Process())
            self.assertEqual(status,0);self.assertEqual(spawn.call_count,1)
            self.assertTrue(row['cleanup_confirmed']);self.assertFalse(row['acceptance_claim'])
            self.assertTrue(row['inputs_unchanged']);b=row['campaign_boundary']
            self.assertEqual(b['schema'],'pinwheel.streaming-8x4-closure48-resource-boundary.v1')
            self.assertEqual(b['shared_lease'],P.shared_lease_paths(args.campaign_root))
            self.assertEqual(b['campaign_id'],P.CAMPAIGN);self.assertFalse(b['engineering_evidence_verified'])
            self.assertEqual(b['campaign_kind'],'rc_reference_probe')
            for path in [str(Path(W.__file__).resolve()),str(Path(P.__file__).resolve()),*P.historical_sources(args.campaign_root)]:
                self.assertEqual(row['input_sha256'][path],P.sha(path))

    def test_real_fixed_cad_parent_and_lean_no_container_are_preserved(self):
        for kind in ('fixed-cad','lean'):
            with tempfile.TemporaryDirectory() as temp:
                args,guard,_=self.fixture(temp,kind)
                status,row,_=self.execute(args,guard,Process())
                self.assertEqual(status,0);parent=W.frozen(args.validation_parent)
                self.assertEqual(row['campaign_boundary']['frozen_parent'],parent)
                self.assertEqual(row['input_sha256'][parent['path']],parent['sha256'])
                self.assertEqual(row['validation_parent'],parent if kind=='fixed-cad' else None)
                self.assertEqual(row.get('containers_remaining'),[] if kind=='fixed-cad' else None)

    def test_real_guard_timeout_and_input_tamper_remain_failures(self):
        for failure in ('timeout','tamper'):
            with tempfile.TemporaryDirectory() as temp:
                args,guard,seal=self.fixture(temp)
                status,row,_=self.execute(args,guard,Process(running=failure=='timeout',tamper=seal if failure=='tamper' else None))
                self.assertEqual(status,1);self.assertTrue(row['cleanup_confirmed'])
                self.assertEqual(row['status'],'stopped' if failure=='timeout' else 'invalidated')
                self.assertFalse(row['acceptance_claim'])

    def test_timing_and_eco_file_presence_never_grants_admission(self):
        for kind in ('qualified-timing','timing-eco-cad'):
            with tempfile.TemporaryDirectory() as temp:
                args,guard,_=self.fixture(temp,kind)
                evidence=Path(temp)/'claimed-pass';evidence.write_text(json.dumps(dict(qualified=True,all_eight_rows=True)))
                args.model_qualification=evidence
                if kind=='timing-eco-cad':args.timing_failure=evidence
                with patch.object(guard,'main') as main,self.assertRaisesRegex(ValueError,'actual G2 reopener'):
                    W.run(args,guard=guard,now=P.SCHEDULE['start'])
                main.assert_not_called()
        with tempfile.TemporaryDirectory() as temp:
            args,guard,seal=self.fixture(temp);args.model_qualification=seal
            with patch.object(guard,'main') as main,self.assertRaisesRegex(ValueError,'file presence is insufficient'):
                W.run(args,guard=guard,now=P.SCHEDULE['start'])
            main.assert_not_called()

    def test_actual_docker_config_caps_no_swap_and_offline(self):
        for kind in P.KINDS:
            limits=P.resource_limits(kind)
            config=dict(Memory=limits['container_memory_bytes'],MemorySwap=limits['container_memory_bytes'],
                NanoCpus=limits['container_cpus']*10**9,NetworkMode='none')
            W.validate_container(dict(HostConfig=config),limits)
            for key,value in [('Memory',config['Memory']+1),('MemorySwap',config['Memory']+1),
                ('NanoCpus',config['NanoCpus']+1),('NetworkMode','bridge')]:
                with self.assertRaises(ValueError):W.validate_container(dict(HostConfig=dict(config,**{key:value})),limits)

    def test_reference_admission_is_sealed_data_without_qualification_authority(self):
        with tempfile.TemporaryDirectory() as temp:
            args,guard,seal=self.fixture(temp,'solver-validation');args.reference_admission=seal
            status,row,_=self.execute(args,guard,Process())
            self.assertEqual(status,0);b=row['campaign_boundary']
            self.assertEqual(b['reference_admission_evidence'],W.frozen(seal))
            self.assertFalse(b['reference_admission_verified']);self.assertFalse(b['engineering_evidence_verified'])
            self.assertFalse(b['acceptance_claim'])
        with tempfile.TemporaryDirectory() as temp:
            args,guard,seal=self.fixture(temp);args.reference_admission=seal
            with patch.object(guard,'main') as main,self.assertRaisesRegex(ValueError,'separate model-producer'):
                W.run(args,guard=guard,now=P.SCHEDULE['start'])
            main.assert_not_called()

    def test_inspect_hook_validates_actual_config_not_only_declared_limits(self):
        for cpus in (1,2):
            with tempfile.TemporaryDirectory() as temp:
                args,guard,_=self.fixture(temp,'reference-probe')
                config=dict(HostConfig=dict(Memory=6*1024**3,MemorySwap=6*1024**3,NanoCpus=cpus*10**9,NetworkMode='none'))
                def main():guard.command(['docker','inspect','observed-id']);return 0
                with patch.object(guard,'command',return_value=json.dumps([config])),patch.object(guard,'main',side_effect=main):
                    if cpus==1:self.assertEqual(W.run(args,guard=guard,now=P.SCHEDULE['start']),0)
                    else:
                        with self.assertRaisesRegex(ValueError,'CPU cap'):W.run(args,guard=guard,now=P.SCHEDULE['start'])

    def test_late_wrong_deadline_old_source_change_and_parent_tamper_reject(self):
        with tempfile.TemporaryDirectory() as temp:
            args,guard,_=self.fixture(temp)
            with patch.object(guard,'main') as main,self.assertRaises(ValueError):W.run(args,guard=guard,now=P.SCHEDULE['reference_decision'])
            main.assert_not_called();args.deadline=P.SCHEDULE['hard_deadline']
            with self.assertRaises(ValueError):W.run(args,guard=guard,now=P.SCHEDULE['start'])
            args.deadline=None;(args.campaign_root/'scripts/streaming_8x4_closure24_resources.py').write_text('changed')
            with self.assertRaisesRegex(ValueError,'Historical'):W.run(args,guard=guard,now=P.SCHEDULE['start'])
        with tempfile.TemporaryDirectory() as temp:
            args,guard,_=self.fixture(temp,'lean')
            def main():
                args.validation_parent.write_text('changed')
                guard.admission_window('lean',P.timestamp(P.SCHEDULE['heavy_cutoff']),P.timestamp(P.SCHEDULE['start']))
            with patch.object(guard,'main',side_effect=main),self.assertRaisesRegex(ValueError,'Frozen admission'):
                W.run(args,guard=guard,now=P.SCHEDULE['start'])

    def test_unchanged_lease_sentinel_and_resource_floors(self):
        for blocked in ('lease','sentinel'):
            with tempfile.TemporaryDirectory() as temp:
                args,guard,_=self.fixture(temp,'fixed-cad');base=args.campaign_root/'build/streaming-tt-resources'
                base.mkdir(parents=True)
                if blocked=='sentinel':(base/'cleanup-unconfirmed.json').write_text('{}')
                with patch.object(guard.subprocess,'Popen') as spawn,patch.object(guard.fcntl,'flock',side_effect=BlockingIOError),\
                     self.assertRaisesRegex(ValueError,'lease|cleanup'):
                    W.run(args,guard=guard,now=P.SCHEDULE['start'])
                spawn.assert_not_called()
        with tempfile.TemporaryDirectory() as temp:
            _,guard,_=self.fixture(temp)
            for admission,available in ((True,24),(False,14)):
                with self.assertRaises(ValueError):guard.gate(dict(memory_available_percent=available,disk_free_bytes=64*1024**3),admission=admission)
            for sample,rss in ((dict(memory_available_percent=90,disk_free_bytes=12*1024**3-1),0),
                (dict(memory_available_percent=90,disk_free_bytes=64*1024**3),4096*1024+1)):
                with self.assertRaises(ValueError):guard.gate(sample,admission=False,rss_kib=rss,rss_mib=4096)

    def test_missing_container_parent_or_excess_rss_rejects_before_guard(self):
        for change in ('container','parent','rss'):
            with tempfile.TemporaryDirectory() as temp:
                args,guard,_=self.fixture(temp,'solver-validation')
                if change=='container':args.container_name=None
                elif change=='parent':args.validation_parent=None
                else:args.rss_mib=4097
                with patch.object(guard,'main') as main,self.assertRaises(ValueError):W.run(args,guard=guard,now=P.SCHEDULE['start'])
                main.assert_not_called()


if __name__=='__main__':unittest.main()
