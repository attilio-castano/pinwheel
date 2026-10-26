"""HOST-only candidate ownership/overlay controls; never launches CAD."""
import copy
from datetime import datetime, timedelta, timezone
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_8x4_pg_flow24 as W


def put(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data) + '\n')


class FixedClock(datetime):
    @classmethod
    def now(cls, tz=None):
        return W.CLOCK.timestamp(W.CLOCK.SCHEDULE['start']) + timedelta(hours=1)


class PGFlow(unittest.TestCase):
    def tearDown(self):
        W.workspace_context(ROOT)

    def fixture(self, root):
        owner = root / 'owner'; flow = owner / 'flow'; flow.mkdir(parents=True)
        packet = dict(mode='full', variant=dict(ordinal=1, policy='A'), policy='A',
                      canonical_flow_steps=list(W.R.TAIL), original_preparation=dict(path='base', sha256='b'*64))
        prep = root / 'prepared/preparation.json'; put(prep, dict(frozen=True))
        rows = []
        odbs = {}
        for ordinal, name in ((1,'pinwheel-pgdiodebootstrap'), (2,'openroad-detailedrouting'), (3,'openroad-rcx')):
            stage = flow / ('%02d-' % ordinal + name); stage.mkdir()
            odb = stage / 'chip.odb' if ordinal < 3 else odbs[2]
            if ordinal < 3: odb.write_text('fresh stage ' + str(ordinal))
            odbs[ordinal] = odb
            container = '/work/run/' + str(odb.relative_to(flow))
            state = stage / 'state_out.json'; put(state, dict(odb=container, metrics={}))
            rows.append(dict(state=str(state), state_sha256=W.sha(state),step_directory=stage.name,
                             views=dict(odb=dict(path=str(odb),sha256=W.sha(odb),container=container))))
        order = dict(original_steps=list(W.R.TAIL), actual_steps=[W.BOOTSTRAP,*W.R.TAIL],
                     canonical_tail=list(W.R.TAIL),ordinary_tail_preserved=True,source_overlay=True,
                     disabled_is_not_executed=True,qualified=False)
        put(owner / 'metadata/flow-order.json',order)
        resolved = dict(observed=True,validated=True)
        report = dict(schema='pinwheel.closure24-pg-native-run.v1',mode='full',variant=packet['variant'],
            policy='A',source_ff_bits=6039,clock_period_ns=20,tiles='8x4',parent_is_not_final_target=True,
            status='failed',exit_code=1,inputs_pdk_runtime_unchanged=True,container_termination=dict(status='absent'),
            preparation=W.bound(prep),states=rows,resolved_contract=resolved)
        target=owner/'report.json'
        def seal():
            report['artifact_sha256']={str(p.relative_to(owner)):W.sha(p) for p in owner.rglob('*') if p.is_file() and p!=target}
            put(target,report)
        seal()
        return target,packet,report,resolved,seal

    def select(self, path, packet, resolved):
        with patch.object(W,'verify',return_value=packet),patch.object(W,'resolved_contract',return_value=resolved):
            return W.select_report(path,W.sha(path))

    def test_single_overlay_preserves_entire_canonical_body(self):
        text='canonical header\nread_current_odb\ncanonical body\nwrite_views\n'
        changed=W.insert_hook(text)
        self.assertEqual(changed.replace('source /work/closure/inputs/hook.tcl\n',''),text)
        for bad in ('no seam',text+text):
            with self.assertRaises(ValueError):W.insert_hook(bad)

    def test_full_selector_accepts_closed_later_failure_and_carried_fresh_drt_odb(self):
        with tempfile.TemporaryDirectory() as temp:
            path,packet,report,resolved,seal=self.fixture(Path(temp))
            result=self.select(path,packet,resolved)
            self.assertEqual(result['actual_odb']['path'],str(Path(report['states'][1]['views']['odb']['path']).resolve()))
            self.assertEqual(result['physical_exit_code'],1)
            self.assertFalse(result['physical_acceptance']);self.assertFalse(result['model_qualified'])

    def test_selector_rejects_timeout_internal_seed_and_missing_drt(self):
        for defect in ('timeout','seed','missing-drt','omitted-latest'):
            with self.subTest(defect=defect),tempfile.TemporaryDirectory() as temp:
                path,packet,report,resolved,seal=self.fixture(Path(temp))
                if defect=='timeout':report.update(status='timed_out',exit_code=124)
                elif defect=='seed':
                    seed=Path(temp)/'old.odb';seed.write_text('old seed')
                    row=report['states'][-1];row['views']['odb'].update(path=str(seed),sha256=W.sha(seed),container='/work/seed.odb')
                    put(Path(row['state']),dict(odb='/work/seed.odb'));row['state_sha256']=W.sha(row['state'])
                elif defect=='missing-drt':
                    report['states'][1]['step_directory']='02-internal-diagnostic'
                else:report['states'].pop()
                seal()
                with self.assertRaises(ValueError):self.select(path,packet,resolved)

    def test_selector_rejects_completed_state_artifact_tamper_and_omitted_tail(self):
        for defect in ('tamper','tail','contract'):
            with self.subTest(defect=defect),tempfile.TemporaryDirectory() as temp:
                path,packet,report,resolved,seal=self.fixture(Path(temp))
                if defect=='tamper':Path(report['states'][1]['views']['odb']['path']).write_text('changed')
                elif defect=='tail':
                    q=path.parent/'metadata/flow-order.json';order=json.loads(q.read_text());order['canonical_tail'].pop();put(q,order);seal()
                else:report['clock_period_ns']=21;seal()
                with self.assertRaises(ValueError):self.select(path,packet,resolved)

    def test_resolved_rules_only_allow_explicit_flow_metadata(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);before=root/'original.json';actual=root/'flow/resolved.json'
            value=dict(meta=dict(flow='old',version=1),CLOCK_PERIOD=20,PL_TARGET_DENSITY_PCT=85,
                DRT_OPT_ITERS=64,OPENROAD_THREADS=4,RUN_EQY=False,RUN_KLAYOUT_XOR=False,RUN_LINTER=False)
            put(before,value);packet=dict(original_resolved_config=W.bound(before))
            good=dict(value,meta=dict(value['meta'],flow=W.FLOW));put(actual,good)
            self.assertTrue(W.resolved_contract(packet,root)['validated'])
            for key,bad in [('CLOCK_PERIOD',21),('PL_TARGET_DENSITY_PCT',70),('DRT_OPT_ITERS',6),('RUN_EQY',True)]:
                put(actual,dict(good,**{key:bad}))
                with self.assertRaises(ValueError):W.resolved_contract(packet,root)

    def test_fixed_two_worker_delta_is_exact_and_never_changes_routing_rules(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);before=root/'original.json';actual=root/'flow/resolved.json'
            value=dict(meta=dict(flow='old',version=1),CLOCK_PERIOD=20,PL_TARGET_DENSITY_PCT=85,
                DRT_OPT_ITERS=64,OPENROAD_THREADS=4,RUN_EQY=False,RUN_KLAYOUT_XOR=False,RUN_LINTER=False)
            put(before,value);packet=dict(original_resolved_config=W.bound(before),resource_policy=copy.deepcopy(W.NATIVE_RESOURCES))
            good=dict(value,meta=dict(value['meta'],flow=W.FLOW),OPENROAD_THREADS=2);put(actual,good)
            result=W.resolved_contract(packet,root)
            self.assertEqual(result['delta']['OPENROAD_THREADS'],dict(before=4,after=2))
            self.assertLessEqual(W.NATIVE_RESOURCES['full_leaf_seconds_cap']+W.NATIVE_RESOURCES['minimum_outer_reserve_seconds'],14400)
            for bad in (dict(good,OPENROAD_THREADS=4),dict(good,DRT_OPT_ITERS=6),dict(good,CLOCK_PERIOD=21)):
                put(actual,bad)
                with self.assertRaises(ValueError):W.resolved_contract(packet,root)
            packet['resource_policy']['openroad_threads']=1
            with self.assertRaises(ValueError):W.thread_count(packet)

    def test_initial_adapter_uses_exact_step_membership_without_drt_fields_or_defaults(self):
        replay=dict(OPENROAD_THREADS=4,retained='unchanged')
        initial=dict(OPENROAD_THREADS=4,CLOCK_PERIOD=20,DESIGN_NAME=W.RR.TOP,
            PNR_SDC_FILE='/work/inputs/core.sdc',PL_OPTIMIZE_MIRRORING=False,
            PL_MAX_DISPLACEMENT_X=17,PL_MAX_DISPLACEMENT_Y=23,DPL_CELL_PADDING=0,
            exact_initial_only=['preserve','every','value'])
        packet=dict(mode='initial-smoke',resource_policy=copy.deepcopy(W.NATIVE_RESOURCES),diagnostic_config_version=2)
        with patch.object(W.RR,'validate_config') as validator:
            actual=W.diagnostic_config(packet,replay,initial)
            validator.assert_called_once_with(replay)
            self.assertEqual(actual,dict(initial,OPENROAD_THREADS=2));self.assertNotIn('retained',actual)
            self.assertNotIn('DRT_OPT_ITERS',actual)
            self.assertTrue(W.validate_diagnostic_config(actual,packet,replay,initial)['only_delta'])
            for bad in (dict(actual,DPL_CELL_PADDING=1),dict(actual,DPL_CELL_PADDING=False),
                        dict(actual,DRT_OPT_ITERS=64),{k:v for k,v in actual.items() if k!='DPL_CELL_PADDING'}):
                with self.assertRaises(ValueError):W.validate_diagnostic_config(bad,packet,replay,initial)
            with self.assertRaises(ValueError):W.diagnostic_config(packet,replay,dict(initial,OPENROAD_THREADS=2))
            with self.assertRaises(ValueError):W.diagnostic_config(dict(packet,mode='full'),replay,initial)
            legacy=dict(packet);legacy.pop('diagnostic_config_version')
            self.assertEqual(W.diagnostic_config(legacy,replay),dict(replay,OPENROAD_THREADS=2))
            self.assertEqual(W.diagnostic_config(dict(legacy,mode='full'),replay),dict(replay,OPENROAD_THREADS=2))

    def test_initial_config_authority_is_exact_executed_closed_parent_artifact(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);config=root/'parent'/W.INITIAL_CONFIG_RELATIVE
            put(config,dict(OPENROAD_THREADS=4,DPL_CELL_PADDING=0));expected=W.sha(config)
            parent=root/'parent/report.json';put(parent,dict(artifact_sha256={W.INITIAL_CONFIG_RELATIVE:expected}))
            repair=root/'repair/preparation.json';put(repair,dict(parent_report=W.bound(parent)))
            replay=dict(repair_preparation=W.bound(repair))
            with patch.object(W,'INITIAL_CONFIG_SHA256',expected):
                self.assertEqual(W.initial_config_authority(replay),W.bound(config))
                put(config,dict(OPENROAD_THREADS=4,DPL_CELL_PADDING=1))
                with self.assertRaises(ValueError):W.initial_config_authority(replay)
            put(repair,dict(parent_report=W.bound(parent),changed=True))
            with self.assertRaises(ValueError):W.initial_config_authority(replay)

    def test_b_requires_failed_a_authority_and_two_variants_never_reset(self):
        with tempfile.TemporaryDirectory() as temp,patch.object(W,'ROOT',Path(temp)),patch.object(W,'datetime',FixedClock):
            directory=Path(temp)/W.CAMPAIGN;directory.mkdir(parents=True)
            a=W.register_variant('A');self.assertEqual(W.register_variant('A'),a)
            definition=dict(search='test-finite-policy',rows=186)
            with self.assertRaises((ValueError,FileNotFoundError)):W.register_variant('B',definition)
            ledger=directory/'physical-variants';failure=directory/'A-failure.json';put(failure,dict(failed=True))
            put(ledger/'routing-fallback-B-admission.json',dict(schema='pinwheel.closure24-routing-fallback-admission.v1',
                policy='B',root_reviewed_A_failure=True,predecessor=W.bound(ledger/'variant-01.json'),failure_evidence=W.bound(failure)))
            b=W.register_variant('B',definition);self.assertEqual(b['ordinal'],2)
            self.assertEqual(b['policy_definition'],definition)
            W.verify_variant_authority(b)
            with self.assertRaises(ValueError):W.register_variant('B',dict(definition,rows=185))
            self.assertEqual(len(list(ledger.glob('variant-*.json'))),2)
            with self.assertRaises(ValueError):W.register_variant('C')
            put(failure,dict(failed=False))
            with self.assertRaises(ValueError):W.verify_variant_authority(b)
            with self.assertRaises(ValueError):W.register_variant('B',definition)

    def test_container_has_bounded_resources_readonly_seed_and_frozen_sources(self):
        packet=dict(original_preparation=dict(path='/tmp/base/preparation.json'),pdk_root='/tmp/pdk',
                    source_odb=dict(path='/tmp/seed.odb'),runtime=dict(image_id='sha256:'+'a'*64),mode='full')
        argv=W.container_command(Path('/tmp/prep'),Path('/tmp/out'),packet,'pinwheel-test','00000000-0000-0000-0000-000000000001')
        for key,value in [('--network','none'),('--cpus','4'),('--memory','6g'),('--memory-swap','6g'),('--pids-limit','256')]:
            self.assertEqual(argv[argv.index(key)+1],value)
        self.assertIn('type=bind,source=/tmp/seed.odb,target=/work/seed.odb,readonly',argv)
        packet['resource_policy']=copy.deepcopy(W.NATIVE_RESOURCES)
        two=W.container_command(Path('/tmp/prep'),Path('/tmp/out'),packet,'pinwheel-test','00000000-0000-0000-0000-000000000001')
        self.assertEqual(two[two.index('--cpus')+1],'2')
        with self.assertRaises(ValueError):W.container_command(Path('/tmp/p'),Path('/tmp/o'),packet,'unsafe/name','not-owner')


if __name__=='__main__':unittest.main()
