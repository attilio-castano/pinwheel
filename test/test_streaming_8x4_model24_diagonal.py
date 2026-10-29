"""Portable synthetic units/import/consumer controls; no build data or Native."""
from decimal import Decimal as D
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'));sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_diagonal_import as W
import streaming_8x4_model24_diagonal_readback as R
from test_streaming_8x4_rc_cap_marker import spef


def model(value='0'):
    return ('Extraction Rules for rcx\nVersion 1.2\nDIAGMODEL ON\nLayerCount 5\nCorners 1 : MODEL24_SYNTHETIC\nDensityModel 0\n'
        'Metal 1 DIAGUNDER\nWIDTH Table 1 entries: 0.16\nMetal 1 DIAGUNDER 2\nDIST count 2 width 0.16\n0 0 '+value+' 0\n0.18 0 0 0\nEND DIST\nEND DensityModel 0\n')


def raw_log():
    return ('MODEL24_DIAG_VERSION_BEGIN\nOpenROAD '+W.S.N.OPENROAD_COMMIT+'\nMODEL24_DIAG_VERSION_END\nMODEL24_DIAG_API_BEGIN\nMODEL24_DIAG_API_END\nMODEL24_DIAG_IMPORT_DONE\n'
        'PINWHEEL_CAP_INVENTORY insts=0 iterms=0 nets=6 bterms=12\nPINWHEEL_CAP_TECH dbu=1000 m1_width=160\n'
        +''.join('MODEL24_DIAG_WIDTH layer='+m+' width='+str(W.D.G.WIDTHS[m])+'\n' for m in W.D.G.METALS)
        +'PINWHEEL_CAP_TERMINAL\nMODEL24_DIAG_TERMINAL\n')

class DiagonalControls(unittest.TestCase):
    def test_synthetic_full_matrix_length_projection_and_import_half_units(self):
        r=W.D.synthetic_projection();self.assertEqual(D(r['pair_F_per_m']),D('2e-12'))
        self.assertEqual(D(r['total_pair_fF_at_20um']),D('.04'));self.assertEqual(D(r['expected_imported_fringe_fF_per_nm']),D('1e-6'))
        self.assertEqual(D(r['expected_consumer_pair_F_per_m']),D('2e-12'));self.assertFalse(r['model_qualified'])
    def test_exact_imported_zero_row_and_only_one_numeric_difference(self):
        self.assertTrue(W.D.compare_decks(model(),model('1e-6'))['exact_single_imported_numeric_delta'])
        for bad in (model('2e-6'),model('1e-6').replace('0.18 0 0 0','0.18 0 1e-6 0'),model('1e-6').replace('Corners 1 : MODEL24_SYNTHETIC','Corners 1 : TYP'),model('1e-6').replace('Version 1.2','Version 2.0')):
            with self.assertRaises(ValueError):W.D.compare_decks(model(),bad)
    def test_full_scaffold_census_required_and_one_explicit_nonopen_slot(self):
        patterns=[dict(path=W.D.TARGET if i==0 else f'1v2/MODEL24_TYP/Over1/M1oM0/W0.16_W0.16/S0.{i}_S0_L10/wires',text='synthetic grammar stub') for i in range(310)]
        def parsed(text,path):return dict(family='UnderDiag1' if path==W.D.TARGET else 'Over1',wires=[dict(name='M1_w1',index=1,voltage=1),dict(name='M2_w2',index=2,voltage=0)] if path==W.D.TARGET else [dict(name='M1_w1',index=1,voltage=1)],grounds=[dict(name='M0_w0')])
        with patch.object(W.D.N,'parse',side_effect=parsed):
            a=W.D.caps(patterns,W.D.MODES[0]);b=W.D.caps(patterns,W.D.MODES[1]);self.assertEqual(len(a.splitlines()),315)
            self.assertIn('CC 0.040 FR 0.06 TC 0.100',b);self.assertIn('UnderDiag3/M1duM2/W0.16_W0.2/S0_S0_L125/wire_2',b)
            self.assertIn('UnderDiag1/M1duM2/W0.16_W0.2/S0_S0_L125/wire_1',a)
            for bad in (patterns[:-1],patterns+[patterns[0]],patterns[:-1]+[patterns[0]]):
                with self.assertRaises(ValueError):W.D.caps(bad,W.D.MODES[1])
    def test_strict_baseline_failure_and_new_twice_per_lookup_prediction(self):
        job=W.D.G.definition('retained');base=W.D.read_cap(spef(job),W.D.MODES[0]);self.assertFalse(base['strict_physics_passed'])
        good=W.D.read_cap(spef(job,'.002'),W.D.MODES[1]);self.assertEqual(list(map(D,good['coupling_slopes_F_per_m'])),[D('2e-12')]*2)
        for bad in (spef(job,'.001'),spef(job,'.004'),spef(job,'.002').replace('*C_UNIT 1 FF','*C_UNIT 1 PF'),spef(job)):
            with self.assertRaises(ValueError):W.D.read_cap(bad,W.D.MODES[1])
        with self.assertRaises(ValueError):W.D.read_cap(spef(job,'.002'),W.D.MODES[0])
    def test_actual_full_leaf_grammar_geometry_and_source_model(self):
        with tempfile.TemporaryDirectory() as temp:
            owner=Path(temp);(owner/'native.log').write_text(raw_log())
            for n in ('before.def','after.def'):(owner/n).write_text(W.D.fixture())
            (owner/'imported.rules').write_text(model('1e-6'));(owner/'result.spef').write_text(spef(W.D.G.definition('retained'),'.002'))
            self.assertTrue(W.parse_leaf(owner,W.D.MODES[1])['consumer']['strict_physics_passed'])
            for raw in (raw_log()+'WARNING control\n',raw_log().replace('nets=6','nets=7'),raw_log().replace('width=200','width=201'),raw_log().replace('MODEL24_DIAG_API_BEGIN','MODEL24_DIAG_API_BEGIN\n'+'f'*41)):
                if 'f'*41 in raw:raw=raw.replace('MODEL24_DIAG_VERSION_END','f'*41+'\nMODEL24_DIAG_VERSION_END')
                (owner/'native.log').write_text(raw)
                with self.assertRaises(ValueError):W.parse_leaf(owner,W.D.MODES[1])
    def test_exact_fixture_units_ports_layers_and_unchanged_version_flags(self):
        text=W.D.fixture();self.assertEqual(len(W.D.G.validate(text,W.D.G.definition('retained'))['ports']),12)
        for bad in (text.replace('MICRONS 1000','MICRONS 2000'),text.replace('+ ROUTED Metal1','+ ROUTED Metal2',1)):
            with self.assertRaises(ValueError):W.D.G.validate(bad,W.D.G.definition('retained'))
        self.assertIn('init_rcx_model -corner_names {MODEL24_SYNTHETIC} -met_cnt 5',W.tcl())
        self.assertIn('read_rcx_tables -corner_name MODEL24_SYNTHETIC -file synthetic.caps',W.tcl());self.assertIn('-version 1.0 -coupling_threshold 0',W.tcl());self.assertNotIn('-lef_res',W.tcl())
    def test_prefix_and_measured_work_never_promote(self):
        rows=[dict(passed=True)]*2;delta=dict(exact_single_imported_numeric_delta=True)
        for seconds in (89.9,90.001):
            report=dict(actual_work_seconds=seconds,work_budget_passed=seconds<=90,measurement_packet_completed=True,deck_delta=delta,passed=seconds<=90)
            self.assertIs(R.packet_state(report,rows,delta)[1],seconds<=90)
            with self.assertRaises(ValueError):R.packet_state(report,rows[:-1],delta)
            if seconds>90:
                with self.assertRaises(ValueError):R.packet_state(dict(report,passed=True),rows,delta)

    def test_actual_frozen_producer_cgroup_schema_contract(self):
        kernel={'cpu.max':'100000 100000','memory.max':'2147483648','memory.swap.max':'0','pids.max':'128'}
        with patch('pathlib.Path.read_text',lambda p:kernel[p.name]):self.assertEqual(W.D.G.C.cgroups(),kernel)
        self.assertTrue(R.cgroup_contract(kernel))
        for bad in ({k.replace('.','_'):v for k,v in kernel.items()},dict(kernel,foreign='0'),dict(kernel,**{'memory.swap.max':'1'})):
            with self.assertRaises(ValueError):R.cgroup_contract(bad)

    def test_scope_no_fitting_no_physical_reference_or_model_promotion(self):
        p=W.D.policy();self.assertFalse(p['coefficient_fitted']);self.assertFalse(p['model_qualified']);self.assertEqual(p['calls'],2)
        self.assertTrue(p['supporting_rule_records_are_synthetic_scaffolding_not_physical_coefficients'])
        self.assertEqual(p['physical_model_accuracy'],'unmeasured')

if __name__=='__main__':unittest.main()
