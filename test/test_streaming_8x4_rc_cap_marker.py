"""Focused HOST marker controls; no Native or field solve."""
import copy
from historical_evidence import historical_evidence
import streaming_8x4_consumer_fixtures as F
from decimal import Decimal as D
import hashlib
import inspect
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_rc_cap_marker as W
import streaming_8x4_rc_cap_marker_geometry as G
import streaming_8x4_rc_cap_marker_spef as Z
import streaming_8x4_rc_cap_marker_readback as R
B=ROOT/'build/campaigns/8x4-20261022-01'


def spef(job,k='0'):
    text='*SPEF "ieee 1481-1999"\n*DESIGN_FLOW "NAME_SCOPE LOCAL" "PIN_CAP NONE"\n*C_UNIT 1 FF\n'
    for row in job['rows']:
        n=row['net'];other=job['partners'][n];length=D(row['length_um']);ground=length/D(10);coupling=length*D(k)
        text+=f'*D_NET {n} {ground+coupling}\n*CONN\n*P {n}_A I\n*P {n}_B O\n*CAP\n1 {n}_A {ground}\n2 {n}_A {other}_A {coupling}\n*RES\n1 {n}_A {n}_B 1\n*END\n'
    return text


def values(k='.001'):
    rows=[]
    for name in W.JOBS:
        job=G.definition(name);names=[r['net'] for r in job['rows']]
        if name=='retained':v=dict(strict_physics_passed=False,strict_failure='ValueError: '+W.STRICT_ERROR,
            zero_inventory=Z.zero_inventory(spef(job),names,job['partners']))
        else:v=dict(strict_physics_passed=True,values=W.Q.parse(spef(job,k),names,job['partners']))
        rows.append(dict(job=name,values=v))
    return rows


class MarkerControls(unittest.TestCase):
    def test_one_exact_token_only_and_actual_hash(self):
        original=F.rules();changed=W.marker(original)
        anchor=b'Metal 1 DIAGUNDER 2\nDIST count 10 width 0.16\n0 0 0.000001 0\n'
        self.assertEqual(changed.replace(anchor,anchor.replace(b'0.000001',b'0')),original)
        self.assertEqual(hashlib.sha256(changed).hexdigest(),W.MARKER_HASH)
        for bad in (original+b'\n',original.replace(b'DIAGMODEL ON',b'DIAGMODEL TRUE')):
            with self.assertRaises(ValueError):W.marker(bad)

    def test_exact_six_net_twelve_port_centered_50_100_150_geometry(self):
        for name in W.JOBS:
            job=G.definition(name);got=G.validate(G.fixture(job),job)
            self.assertEqual((len(got['routes']),len(got['ports'])),(6,12))
            for length in (50,100,150):
                a,b=[r for r in job['rows'] if r['length_um']==length]
                self.assertEqual(a['start_DBU'],b['start_DBU']);self.assertEqual(a['end_DBU'],b['end_DBU'])
                self.assertEqual(a['end_DBU'][0]-a['start_DBU'][0],length*1000)
            text=G.fixture(job);self.assertTrue(G.validate(text.replace('+ ROUTED','+ USE SIGNAL + ROUTED'),job))
            for bad in (text.replace('MICRONS 1000','MICRONS 2000'),text.replace('NETS 6','NETS 5'),
                text.replace('+ ROUTED Metal1','+ ROUTED Metal2',1),text.replace('214000 1088000','214001 1088000'),
                text.replace('+ ROUTED Metal1','+ NONDEFAULTRULE bad + ROUTED Metal1',1)):
                with self.assertRaises(ValueError):G.validate(bad,job)

    def test_zero_baseline_keeps_frozen_strict_failure_and_no_matrix(self):
        job=G.definition('retained');names=[r['net'] for r in job['rows']];raw=spef(job)
        with self.assertRaisesRegex(ValueError,W.STRICT_ERROR):W.Q.parse(raw,names,job['partners'])
        got=Z.zero_inventory(raw,names,job['partners']);self.assertEqual(got['unique_coupling_segments'],3)
        self.assertFalse(got['valid_Maxwell_matrix_claimed']);self.assertNotIn('groups',got)
        for bad in (raw.replace('*C_UNIT 1 FF','*C_UNIT 1 XX'),raw.replace(' 0\n*RES',' 1\n*RES',1),
                    raw.replace('2 Metal1_Metal2_pair_L50_W1_A Metal1_Metal2_pair_L50_W2_A 0\n','',1)):
            with self.assertRaises(ValueError):Z.zero_inventory(bad,names,job['partners'])

    def test_zero_inventory_prefix_is_frozen_parser_derived(self):
        a=inspect.getsource(W.Q.parse).split('    matrices={}')[0] if '    matrices={}' in inspect.getsource(W.Q.parse) else inspect.getsource(W.Q.parse).split('    matrices = {}')[0]
        b=inspect.getsource(Z.zero_inventory).split('    required=')[0]
        a=a.replace('def parse(', 'def zero_inventory(')
        a=a.replace('(target is None or expected > 0)', '(target is not None and expected == 0)')
        a=a.replace("'Missing intended coupling or incident total differs'","'Marker retained baseline must preserve exact zero intended coupling'")
        self.assertEqual(a,b)

    def test_source_predicted_coupling_slopes_and_factor_two_failure(self):
        got=W.measurements(values());self.assertTrue(got['lookup_marker_diagnostic_passed'])
        self.assertEqual(list(map(D,got['coupling_slopes_F_per_m'])),[D('1e-12')]*2)
        self.assertFalse(got['coefficient_fitted']);self.assertFalse(got['model_qualified'])
        self.assertFalse(W.measurements(values('.002'))['lookup_marker_diagnostic_passed'])
        self.assertFalse(W.measurements(values('.0010011'))['lookup_marker_diagnostic_passed'])
        for bad in (values()[:-1],list(reversed(values()))):
            with self.assertRaises(ValueError):W.measurements(bad)
        bad=values();bad[1]['values']['values']['groups'].append(bad[1]['values']['values']['groups'][0])
        with self.assertRaises(ValueError):W.measurements(bad)

    def test_actual_leaf_zero_exit_bad_missing_coupling_warning_unit_and_version(self):
        log='PINWHEEL_CAP_INVENTORY insts=0 iterms=0 nets=6 bterms=12\nPINWHEEL_CAP_TECH dbu=1000 m1_width=160\n'
        log+=''.join(f'PINWHEEL_CAP_WIDTH layer={m} dbu_width={G.WIDTHS[m]}\n' for m in G.METALS)+'PINWHEEL_CAP_TERMINAL\n'
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp)
            for name in W.JOBS:
                job=G.definition(name);(base/'native.log').write_text(log)
                for n in ('before.def','after.def'):(base/n).write_text(G.fixture(job))
                (base/'result.spef').write_text(spef(job,'.001' if name=='marker' else '0'))
                self.assertEqual(W.parse_leaf(base,job)['strict_physics_passed'],name=='marker')
                (base/'native.log').write_text(log+'WARNING unexpected\n')
                with self.assertRaises(ValueError):W.parse_leaf(base,job)
                (base/'native.log').write_text(log)
                (base/'result.spef').write_text(spef(job,'0' if name=='marker' else '.001'))
                with self.assertRaises(ValueError):W.parse_leaf(base,job)
        self.assertIn('-version 1.0 -coupling_threshold 0',W.A.tcl());self.assertNotIn('-lef_res',W.A.tcl())
        self.assertEqual(W.protocol()['command_version'],'1.0')

    @historical_evidence
    def test_exact_source_intakes_and_physical_stack(self):
        for name,source in [('marker-source','rc-cap-marker-source-intake-01'),('model-source','rc-cap-causal-source-intake-01'),('dispatch-source','rc-consumer-source-intake-01')]:
            with tempfile.TemporaryDirectory() as temp:
                import shutil
                root=Path(temp);shutil.copytree(B/source,root/name)
                self.assertTrue(W.source_intake(root,name)['source_data_only'])
                first=next(p for p in (root/name).iterdir() if p.name!='manifest.json' and p.is_file());first.write_bytes(first.read_bytes()+b'\n')
                with self.assertRaises(ValueError):W.source_intake(root,name)
        case=W.physical(B/'rc-cap-marker-preparation-01') if (B/'rc-cap-marker-preparation-01').exists() else G.physical_cases(
            __import__('json').loads((B/'rc-cap-all-layers-preparation-01/reference32-inputs/plan.json').read_text()),{})
        self.assertEqual(len(case),1);self.assertEqual(case[0]['layers'],['Metal1','Metal2'])

    def test_work_overrun_is_failure_and_bad_terminal_flags_reject(self):
        self.assertTrue(R.work_budget(dict(actual_work_seconds=90,wall_seconds=90,work_budget_passed=True)))
        self.assertFalse(R.work_budget(dict(actual_work_seconds=90.001,wall_seconds=90.001,work_budget_passed=False)))
        for elapsed,flag in [(90.001,True),(float('nan'),False),(float('inf'),False),(-1,True)]:
            with self.assertRaises(ValueError):R.work_budget(dict(actual_work_seconds=elapsed,wall_seconds=elapsed,work_budget_passed=flag))
        self.assertIn("b['shared_lease'] ==",inspect.getsource(R.campaign_boundary))
        self.assertIn("r['timeout_seconds'] == 120",inspect.getsource(R.resource_join))


if __name__=='__main__':unittest.main()
