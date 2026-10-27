"""HOST controls for real unit-correct fixture and separate DEF-local NDRs."""
import copy
from historical_evidence import historical_evidence
import streaming_8x4_consumer_fixtures as F
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_rc_consumer_ndr as N
import streaming_8x4_rc_consumer_ndr_readback as R

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'build/campaigns/8x4-20261022-01/rc-consumer-units-preparation-01/consumer-inputs'


class NDRControls(unittest.TestCase):
    def setUp(self):
        self.original=F.original_def();self.tech=F.tech()
        self.widths=F.widths()
        self.rows=N.C.fixtures({'explicit_vias':{name:{'cut_layer':layer} for name,layer in
            zip(N.C.VIA_FIXTURES,('Via1','Via1','Via2','Via3','TopVia1'))}})

    def test_compact_math_fixture_authentication_rejects_changed_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source = F.FIXTURES / 'math-plan.json'
            target = directory / source.name
            target.write_bytes(source.read_bytes())
            with patch.object(F, 'FIXTURES', directory):
                self.assertEqual(len(F.consumer_plan()['fixture_rows']), 17)
                target.write_bytes(target.read_bytes() + b'\n')
                with self.assertRaisesRegex(ValueError, 'fixture bytes changed'):
                    F.consumer_plan()

    @historical_evidence
    def test_actual_source_confirms_library_default_and_complete_block_rules(self):
        evidence=ROOT/'build/campaigns/8x4-20261022-01/rc-ndr-source-intake-01'
        self.assertEqual(len(N.source_evidence(evidence)),6)
        text=(evidence/'OpenRoad.tcl').read_text()
        self.assertIn('set make_tech [expr ![ord::db_has_tech]]',text)
        cpp=(evidence/'definNonDefaultRule.cpp').read_text()
        self.assertIn('dbTechNonDefaultRule::create(_block, name)',cpp)
        self.assertIn('getRoutingLayerCount()',cpp);self.assertIn('setWidth(dbdist(width))',cpp)
        with tempfile.TemporaryDirectory() as temporary:
            copied=Path(temporary)/'evidence';shutil.copytree(evidence,copied)
            (copied/'definNet.cpp').write_text('changed')
            with self.assertRaises(ValueError):N.source_evidence(copied)

    def test_actual_fixture_only_receives_two_declarations_and_all148_pairs_match(self):
        fixed,witness=N.add_ndr(self.original,self.tech,self.widths)
        block,rules=N.declarations(self.tech,self.widths)
        self.assertEqual(fixed.replace(block,'',1),self.original)
        self.assertEqual(N.U.PAIR.findall(fixed),N.U.PAIR.findall(self.original))
        self.assertEqual(witness['coordinate_pairs_unchanged'],148)
        self.assertEqual(len(rules),2)
        self.assertEqual(set(rules['WIDE_Metal1']),set(N.METALS))
        self.assertEqual(rules['WIDE_Metal1']['Metal1'],dict(width_dbu=320,spacing_dbu=210))
        self.assertEqual(rules['WIDE_Metal2']['Metal2'],dict(width_dbu=400,spacing_dbu=210))
        self.assertEqual(rules['WIDE_Metal1']['TopMetal1'],dict(width_dbu=1640,spacing_dbu=0))
        self.assertIn('+ NONDEFAULTRULE WIDE_Metal1',fixed)

    def test_native_reopener_checks_all_declared_rules_and17_net_bindings(self):
        fixed,witness=N.add_ndr(self.original,self.tech,self.widths)
        readback=R.native_ndr(fixed,witness,self.rows)
        self.assertEqual(len(readback['net_bindings']),17)
        self.assertEqual(readback['net_bindings']['Metal1_wide_L100'],'WIDE_Metal1')
        self.assertEqual(readback['net_bindings']['Metal2_wide_L100'],'WIDE_Metal2')
        self.assertIsNone(readback['net_bindings']['Metal3_L50'])
        self.assertFalse(readback['qualified'])

    def test_missing_layer_wrong_width_or_spacing_cannot_pass_native_readback(self):
        fixed,witness=N.add_ndr(self.original,self.tech,self.widths)
        for bad in [fixed.replace('  + LAYER Metal3 WIDTH 200\n','',1),
            fixed.replace('Metal1 WIDTH 320 SPACING 210','Metal1 WIDTH 160 SPACING 210',1),
            fixed.replace('Metal1 WIDTH 320 SPACING 210','Metal1 WIDTH 320 SPACING 180',1),
            fixed.replace('NONDEFAULTRULES 2 ;','NONDEFAULTRULES 1 ;',1)]:
            with self.assertRaises(ValueError):R.native_ndr(bad,witness,self.rows)

    def test_changed_net_assignment_and_unsupported_rule_attributes_reject(self):
        fixed,witness=N.add_ndr(self.original,self.tech,self.widths)
        for bad in [fixed.replace('+ NONDEFAULTRULE WIDE_Metal1','+ NONDEFAULTRULE WIDE_Metal2',1),
            fixed.replace('+ NONDEFAULTRULE WIDE_Metal1','',1),
            fixed.replace('- WIDE_Metal1\n','- WIDE_Metal1\n + HARDSPACING\n',1)]:
            with self.assertRaises(ValueError):R.native_ndr(bad,witness,self.rows)

    def test_wrong_units_double_declaration_and_changed_LEF_intent_reject(self):
        fixed,_=N.add_ndr(self.original,self.tech,self.widths)
        for original in [self.original.replace('MICRONS 1000','MICRONS 2000'),fixed]:
            with self.assertRaises(ValueError):N.add_ndr(original,self.tech,self.widths)
        with self.assertRaises(ValueError):N.add_ndr(self.original,self.tech,self.widths.replace('WIDTH .32','WIDTH .31'))
        with self.assertRaises(ValueError):N.default_widths(self.tech.replace('WIDTH\t\t0.20','WIDTH\t\t0.2005',1))

    def test_inner_numerical_policy_and_old_source_bytes_stay_unchanged(self):
        old=dict(files_sha256={'fixture.def':'old','run.tcl':'unchanged','MIN-retained_rules.txt':'unchanged'},
            protocol={'corners':['MIN','TYP','MAX'],'wire_relative_tolerance':'0.001'},fixture_rows=self.rows,
            producer_sha256={'original.py':'old'})
        before=copy.deepcopy(old);new=N.inner_plan(old,'only fixture bytes',{'new.py':'new'})
        self.assertEqual(old,before);self.assertEqual(new['protocol'],old['protocol'])
        self.assertEqual(new['fixture_rows'],old['fixture_rows']);self.assertEqual(new['files_sha256']['run.tcl'],'unchanged')
        self.assertEqual(new['files_sha256']['MIN-retained_rules.txt'],'unchanged')

    def test_no_incomplete_native_prefix_before_raw_reader(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);N.write(root/'report.json',dict(schema='pinwheel.streaming-8x4-rc-consumer-DEF-NDR-execution.v1',
                plan_sha256='seal',qualified=False,model_qualified=False,all_six_native_calls_closed=False))
            with patch.object(N,'verify',return_value={}),patch.object(R.R,'readback',side_effect=AssertionError('no prefix')):
                with self.assertRaises(ValueError):R.readback(root,'seal',root)


if __name__=='__main__':unittest.main()
