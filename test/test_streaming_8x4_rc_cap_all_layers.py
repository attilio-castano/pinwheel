"""Focused HOST tests for two fixed five-layer C calls; no Native/field solve."""
import copy
from decimal import Decimal as D
import inspect
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_rc_cap_all_layers as W
import streaming_8x4_rc_cap_all_layers_geometry as G
import streaming_8x4_rc_cap_all_layers_readback as R
B=ROOT/'build/campaigns/8x4-20261022-01'


def synthetic():
    rows=[];targets={}
    for job in G.JOBS:
        d=G.definition(job);groups=[]
        for case in G.CASES:
            matrix=[[D('8e-11')]] if len(case['layers'])==1 else [[D('2e-10'),D('-1e-10')],[D('-1e-10'),D('2e-10')]]
            targets[case['name']]=dict(matrix_F_per_m=[[str(x) for x in row] for row in matrix],ground_F_per_m=[str(sum(row)) for row in matrix])
            for length in (50,100,150):
                names=[r['net'] for r in d['rows'] if r['case']==case['name'] and r['length_um']==length]
                groups.append(dict(names=names,matrix_F=[[str(x*D(length)*D('1e-6')) for x in row] for row in matrix]))
        rows.append(dict(job=job,values=dict(groups=groups,nets={'example':dict(writer_rounding_bound_F='1e-20')})))
    return rows,targets


def full_spef(job):
    text='*SPEF "ieee 1481-1999"\n*DESIGN_FLOW "NAME_SCOPE LOCAL" "PIN_CAP NONE"\n*C_UNIT 1 FF\n'
    for row in job['rows']:
        name=row['net'];partner=job['partners'][name];ground=D(row['length_um'])/10
        coupling=D(0) if partner is None else ground;total=ground+coupling
        text+=f'*D_NET {name} {total}\n\n*CONN\n*P {name}_A I\n*P {name}_B O\n*CAP\n1 {name}_A {ground}\n'
        if partner:text+=f'2 {name}_A {partner}_A {coupling}\n'
        text+=f'*RES\n1 {name}_A {name}_B 1\n*END\n'
    return text


class AllLayerCControls(unittest.TestCase):
    def test_exact_two_call_39net_78port_default_five_widths_and_no_ndr(self):
        for name in G.JOBS:
            job=G.definition(name);actual=G.validate(G.fixture(job),job)
            self.assertEqual((len(actual['routes']),len(actual['ports'])),(39,78))
            self.assertEqual({r['width_DBU'] for r in job['rows']},{160,200,1640})
            self.assertEqual({r['layer'] for r in job['rows']},set(G.METALS))
            self.assertEqual({r['case'] for r in job['rows']},{c['name'] for c in G.CASES})
            self.assertTrue(actual['no_NDR'])
            for row in job['rows']:self.assertEqual(row['end_DBU'][0]-row['start_DBU'][0],row['length_um']*1000)

    def test_centered_adjacent_layers_and_exact_actual_writer_format(self):
        job=G.definition(G.JOBS[0]);text=G.fixture(job)
        # Native writer adds SIGNAL use, reverses connection order and repeats y as*.
        text=text.replace('+ ROUTED ','+ USE SIGNAL + ROUTED ')
        text=text.replace('( 82000 32000 ) ;','( 82000 * ) ;',1)
        self.assertTrue(G.validate(text,job))
        for case in G.CASES[5:]:
            for length in (50,100,150):
                a,b=[r for r in job['rows'] if r['case']==case['name'] and r['length_um']==length]
                self.assertEqual(a['start_DBU'],b['start_DBU']);self.assertEqual(a['end_DBU'],b['end_DBU'])
                self.assertNotEqual(a['layer'],b['layer'])

    def test_unknown_width_ndr_layer_port_outline_and_units_reject(self):
        job=G.definition(G.JOBS[0]);text=G.fixture(job)
        for bad in (text.replace('NETS 39','NETS 38'),text.replace('PINS 78','PINS 77'),
            text.replace('MICRONS 1000','MICRONS 2000'),text.replace('214000 13376000','214001 13376000'),
            text.replace('+ ROUTED Metal1','+ ROUTED Metal2',1),text.replace('( -820 -820 )','( -100 -100 )',1),
            text.replace('+ ROUTED Metal1','+ NONDEFAULTRULE foreign + ROUTED Metal1',1),
            text.replace('DIRECTION INPUT','DIRECTION OUTPUT',1),text+'VIAS 0 ;\nEND VIAS\n'):
            with self.assertRaises(ValueError):G.validate(bad,job)

    def test_exact_original_physical_cases_full_stack_and_reference32_pin(self):
        prep=B/'rc-reference-only-preparation-02';upper=W.F.verify(prep,W.REFERENCE32_HASH)
        lower=json.loads((prep/'reference/plan.json').read_text());cases=G.physical_cases(upper,lower)
        self.assertEqual(len(cases),9)
        approved=json.loads((B/'rc-cap-all-layers-proposal-01.json').read_text())
        self.assertEqual(cases,approved['cases']);self.assertIsNone(approved['supplementary_reference32_execution_plan_sha256'])
        wrong=copy.deepcopy(upper);wrong['cases'][-1]['rectangles'][1]['bounds_um'][0]='-.81'
        with self.assertRaises(ValueError):G.physical_cases(wrong,lower)

    def test_full39net_CAP_membership_and_all_nine_matrices(self):
        rows=[]
        for name in G.JOBS:
            job=G.definition(name);values=W.Q.parse(full_spef(job),[r['net'] for r in job['rows']],job['partners'])
            self.assertEqual(len(values['nets']),39);self.assertEqual(len(values['groups']),27)
            rows.append(dict(job=name,values=values))
            bad=full_spef(job).replace('Metal1_Metal2_pair_L50_W1_A Metal1_Metal2_pair_L50_W2_A',
                'Metal1_Metal2_pair_L50_W1_A Metal2_self_L50_W1_A',1)
            with self.assertRaises(ValueError):W.Q.parse(bad,[r['net'] for r in job['rows']],job['partners'])
        self.assertTrue(W.measurements(rows)['measurement_controls_passed'])

    def test_actual_leaf_inventory_warning_width_and_geometry_reject(self):
        job=G.definition(G.JOBS[0]);log='PINWHEEL_CAP_INVENTORY insts=0 iterms=0 nets=39 bterms=78\nPINWHEEL_CAP_TECH dbu=1000 m1_width=160\n'
        log+=''.join(f'PINWHEEL_CAP_WIDTH layer={m} dbu_width={G.WIDTHS[m]}\n' for m in G.METALS)+'PINWHEEL_CAP_TERMINAL\n'
        with tempfile.TemporaryDirectory() as temporary:
            base=Path(temporary);(base/'before.def').write_text(G.fixture(job));(base/'after.def').write_text(G.fixture(job))
            (base/'result.spef').write_text(full_spef(job));(base/'native.log').write_text(log)
            self.assertEqual(len(W.parse_leaf(base,job)['nets']),39)
            for bad in (log+'WARNING unexpected\n',log.replace('nets=39','nets=38'),log.replace('TopMetal1 dbu_width=1640','TopMetal1 dbu_width=1600')):
                (base/'native.log').write_text(bad)
                with self.assertRaises(ValueError):W.parse_leaf(base,job)
            (base/'native.log').write_text(log);(base/'after.def').write_text(G.fixture(job)+'\n')
            with self.assertRaises(ValueError):W.parse_leaf(base,job)

    def test_extraction_tcl_only_adds_exact_five_default_width_observation(self):
        extra='foreach layer {Metal1 Metal2 Metal3 Metal4 TopMetal1} {\nputs "PINWHEEL_CAP_WIDTH layer=$layer dbu_width=[[$tech findLayer $layer] getWidth]"\n}\n'
        self.assertEqual(W.tcl().replace(extra,''),W.C.tcl())
        self.assertIn('-version 1.0 -coupling_threshold 0',W.tcl())
        self.assertNotIn('-lef_res',W.tcl());self.assertEqual(W.protocol()['calls'],2)

    def test_complete_matrix_ground_slopes_isolation_and_no_prefix_pass(self):
        rows,_=synthetic();result=W.measurements(rows)
        self.assertTrue(result['measurement_controls_passed']);self.assertEqual(len(result['jobs']),18)
        self.assertEqual(len(result['spacing_isolation_controls']),9)
        for bad in (rows[:-1],list(reversed(rows))):
            with self.assertRaises(ValueError):W.measurements(bad)
        bad=copy.deepcopy(rows);bad[0]['values']['groups'][0]['names'][0]='foreign_L50_W1'
        with self.assertRaises(ValueError):W.measurements(bad)
        bad=copy.deepcopy(rows);bad[0]['values']['groups'].append(bad[0]['values']['groups'][0])
        with self.assertRaises(ValueError):W.measurements(bad)

    def test_length_and_isolation_failures_remain_failed(self):
        rows,_=synthetic();bad=copy.deepcopy(rows)
        for group in bad[1]['values']['groups']:group['matrix_F']=[[str(D(v)*D('1.03')) for v in row] for row in group['matrix_F']]
        self.assertFalse(W.measurements(bad)['measurement_controls_passed'])
        rows[0]['values']['groups'][2]['matrix_F'][0][0]=str(D(rows[0]['values']['groups'][2]['matrix_F'][0][0])*D('1.2'))
        self.assertFalse(W.measurements(rows)['measurement_controls_passed'])

    def test_missing_or_failed_reference_stays_unmeasured_or_blocked(self):
        got=R.provisional(None,None,None,None,None)
        self.assertEqual(got['status'],'unmeasured');self.assertFalse(got['reference_prerequisites_passed'])
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'failed.json';path.write_text('{"reference_only_complete_passed":false}')
            with patch.object(W.R,'closed_authority',side_effect=ValueError('Actual32 reference failed2percent mesh gate')):
                got=R.provisional(Path(temporary),{},None,[],path)
            self.assertEqual(got['status'],'blocked_by_reference_failure');self.assertFalse(got['provisional_numeric_comparison_passed'])
            self.assertIn('failed2percent',got['error']);self.assertEqual(got['reference32_authority']['sha256'],W.P.sha(path))
            self.assertEqual(got['full_accuracy_status'],'unmeasured');self.assertFalse(got['finite_BEM_passed'])

    def test_all_cell_provisional_comparison_never_promotes_full_accuracy(self):
        rows,targets=synthetic();analysis=W.measurements(rows)
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'authority.json';path.write_text('{}')
            with patch.object(R,'reference_targets',return_value=(targets,{})):
                result=R.provisional(None,dict(original_M1_FVM_control_authority={}),analysis,rows,path)
                self.assertTrue(result['provisional_numeric_comparison_passed']);self.assertEqual(result['full_accuracy_status'],'unmeasured')
                self.assertEqual(len(result['comparisons']),18);self.assertFalse(result['model_qualified'])
                bad=copy.deepcopy(analysis);bad['jobs'][-1]['slopes'][0]['matrix_F_per_m'][0][1]='-8e-11'
                result=R.provisional(None,dict(original_M1_FVM_control_authority={}),bad,rows,path)
                self.assertFalse(result['provisional_numeric_comparison_passed']);self.assertEqual(result['status'],'fail')
                bad=copy.deepcopy(targets);bad[G.CASES[-1]['name']]['ground_F_per_m']=[]
            with patch.object(R,'reference_targets',return_value=(bad,{})):
                with self.assertRaises(ValueError):R.provisional(None,dict(original_M1_FVM_control_authority={}),analysis,rows,path)

    def test_worker_is_baseline_body_with_only_declared_two_call_changes(self):
        source=inspect.getsource(W.C.run).replace('pinwheel.streaming-8x4-rc-consumer-cap-execution.v1','pinwheel.streaming-8x4-rc-cap-all-layers-execution.v1')
        source=source.replace('time.monotonic() - start < 115','time.monotonic() - start < 55').replace('len(jobs) == 4','len(jobs) == 2')
        source=source.replace('# Preserve numeric failures and finish the fixed four calls; no adaptive retry.','# Preserve numeric failures and finish both fixed calls; no adaptive retry.')
        self.assertEqual(inspect.getsource(W.run),source)
        self.assertIn("r['timeout_seconds'] == 120",inspect.getsource(R.resource_join))
        self.assertIn("b['shared_lease'] ==",inspect.getsource(R.campaign_boundary))


if __name__=='__main__':unittest.main()
