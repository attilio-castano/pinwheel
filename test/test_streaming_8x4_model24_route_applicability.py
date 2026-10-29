"""Portable HOST routing census controls; no Native or ignored campaign reads."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_model24_route_def as D
import streaming_8x4_model24_route_applicability as W

TECH='''LAYER Metal1
 TYPE ROUTING ;
 DIRECTION HORIZONTAL ;
 WIDTH 0.16 ;
END Metal1
LAYER Via1
 TYPE CUT ;
END Via1
LAYER Metal2
 TYPE ROUTING ;
 DIRECTION VERTICAL ;
 WIDTH 0.20 ;
END Metal2
VIA V DEFAULT
 LAYER Metal1 ;
 RECT -0.15 -0.15 0.15 0.15 ;
 LAYER Via1 ;
 RECT -0.095 -0.095 0.095 0.095 ;
 LAYER Via1 ;
 RECT 0.315 -0.095 0.505 0.095 ;
 LAYER Metal2 ;
 RECT -0.15 -0.15 0.56 0.15 ;
END V
VIARULE VR GENERATE
 LAYER Metal1 ;
 ENCLOSURE 0.05 0.125 ;
 LAYER Via1 ;
 RECT -0.095 -0.095 0.095 0.095 ;
 SPACING 0.41 BY 0.41 ;
 LAYER Metal2 ;
 ENCLOSURE 0.20 0.05 ;
END VR
'''
GV='''VIAS 1 ;
- G + VIARULE VR + CUTSIZE 190 190 + LAYERS Metal1 Via1 Metal2
 + CUTSPACING 220 220 + ENCLOSURE 50 125 200 50 + ROWCOL 2 3 + ORIGIN 10 -20 + OFFSET 1 2 3 4 ;
END VIAS
'''
NDR='''NONDEFAULTRULES 1 ;
- wide + HARDSPACING + LAYER Metal1 WIDTH 320 SPACING 300 + LAYER Metal2 WIDTH 400
 + VIA V + VIARULE VR + MINCUTS Via1 2 ;
END NONDEFAULTRULES
'''


def fixture(route='Metal1 ( 0 0 0 ) ( 1000 * 0 ) V FN ( * 2000 ) RECT ( -100 -100 100 100 )',extras='',net='n',attrs=''):
    return ('VERSION 5.8 ;\nDESIGN '+W.V.Q.TOP+' ;\nUNITS DISTANCE MICRONS 1000 ;\n'+extras+
        'NETS 1 ;\n- '+net+' ( a p ) ( b p ) '+attrs+' + ROUTED '+route+' + USE SIGNAL ;\nEND NETS\nEND DESIGN\n')


class RouteGrammarControls(unittest.TestCase):
    def test_complete_paths_vias_rects_lengths_and_scope(self):
        r=D.parse(fixture(),TECH)
        self.assertEqual(r['routing_sections']['NETS']['counts']['physical_shapes'],4)
        self.assertEqual(r['layer_usage']['Metal1']['centerline_length_um'],'1')
        self.assertEqual(r['layer_usage']['Metal2']['centerline_length_um'],'2')
        self.assertEqual(r['layer_usage']['Metal2']['widths_dbu'],{'200':1})
        self.assertEqual(r['via_usage']['V']['cut_occurrences'],2)
        self.assertEqual(r['via_usage']['V']['orientations'],{'FN':1})
        self.assertEqual(r['via_metal_layer_incidence']['Metal1'],{'NETS':1})
        self.assertEqual(r['cut_layer_occurrences']['Via1'],{'NETS':2})
        self.assertFalse(r['qualified_model_envelope']);self.assertFalse(r['physical_corner_applicability_complete'])

    def test_generated_cut_array_and_special_width_are_independent(self):
        text=fixture('Metal1 ( 0 0 ) ( 1000 0 )',GV)+'''SPECIALNETS 1 ;
- VDD ( * VDD ) + ROUTED Metal1 0 + SHAPE STRIPE ( 0 0 ) G
 NEW Metal2 1000 + SHAPE STRIPE ( 0 0 ) ( 0 3000 ) + USE POWER ;
END SPECIALNETS
'''
        r=D.parse(text,TECH)
        self.assertEqual(r['via_usage']['G']['cut_occurrences'],6)
        self.assertEqual(r['layer_usage']['Metal2']['widths_by_scope'],{'SPECIALNETS':{'1000':1}})
        self.assertEqual(r['cut_layer_occurrences']['Via1'],{'SPECIALNETS':6})

    def test_ndr_taper_taperrule_layer_switch_and_extension(self):
        route='Metal1 ( 0 0 ) ( 1000 0 ) V ( * 1000 ) NEW Metal1 TAPER ( 0 0 ) ( 1000 0 ) NEW Metal2 TAPERRULE wide ( 0 0 ) ( 0 1000 )'
        r=D.parse(fixture(route,NDR,attrs='+ NONDEFAULTRULE wide'),TECH)
        self.assertEqual(r['layer_usage']['Metal1']['widths_dbu'],{'320':1,'160':1})
        self.assertEqual(r['layer_usage']['Metal2']['widths_dbu'],{'400':2})
        self.assertEqual(r['used_NDRs'],['wide'])

    def test_escaped_identifiers_strings_comments_and_no_aliases(self):
        text=fixture(net=r'a\ b',attrs='+ PROPERTY x "hello; ROUTED"')
        r=D.parse(text,TECH);self.assertEqual(r['routing_sections']['NETS']['counts']['nets'],1)
        self.assertEqual(D.design_name('# DESIGN fake ;\n'+text),W.V.Q.TOP)
        duplicate=text.replace('NETS 1 ;','NETS 2 ;').replace('END NETS','- a\\ b + USE SIGNAL ;\nEND NETS')
        with self.assertRaisesRegex(ValueError,'Duplicate decoded'):D.parse(duplicate,TECH)
        with self.assertRaises(ValueError):list(D.lex('bad\\\nname'))

    def test_unknown_physical_grammar_is_never_skipped(self):
        for route in ('Metal1 STYLE 2 ( 0 0 ) ( 1 0 )','Metal1 ( * 0 ) ( 1 0 )','Metal1 ( 0 0 ) ( 1 1 )',
            'Metal1 ( 0 0 ) missingVia','Metal1 ( 0 0 ) MASK 1','Metal1 ( 0 0 ) RECT ( 0 0 0 1 )',
            'Metal1 ( 0 0 ) V DO 2 BY 2 STEP 10 10','Metal1 ( 0 0 -1 ) ( 1 0 )'):
            with self.subTest(route=route),self.assertRaises(ValueError):D.parse(fixture(route),TECH)
        for attr in ('+ SUBNET sub','+ VPIN p','+ NONDEFAULTRULE missing'):
            with self.subTest(attr=attr),self.assertRaises(ValueError):D.parse(fixture(attrs=attr),TECH)

    def test_declared_section_membership_boundaries_and_counts(self):
        text=fixture()
        for bad in (text.replace('NETS 1 ;','NETS 2 ;'),text.replace('END NETS',''),text+'NETS 0 ;\nEND NETS\n',
            text.replace(' + USE SIGNAL ;',' + USE SIGNAL ; junk'),text.replace('UNITS DISTANCE MICRONS 1000 ;','UNITS DISTANCE MICRONS 0 ;')):
            with self.assertRaises(ValueError):D.parse(bad,TECH)
        for bad in (text.replace('DESIGN '+W.V.Q.TOP+' ;','DESIGN a b ;'),text+'DESIGN other ;\n',text.replace('END DESIGN','')):
            with self.assertRaises(ValueError):D.design_name(bad)

    def test_indented_or_malformed_sections_are_not_silently_absent(self):
        text=fixture(extras=GV+NDR)+'''  SPECIALNETS 1 ; # header
- p + ROUTED Metal1 400 ( 0 0 ) ( 1000 0 ) ;
  END SPECIALNETS # end
'''
        r=D.parse(text,TECH);self.assertEqual(r['routing_sections']['SPECIALNETS']['counts']['nets'],1)
        indented='\n'.join('  '+line if line.startswith(('VIAS','END VIAS','NONDEFAULTRULES','END NONDEFAULTRULES','NETS','END NETS')) else line for line in text.splitlines())
        self.assertEqual(D.parse(indented,TECH),r)
        for bad in (text.replace('SPECIALNETS 1 ;','SPECIALNETS one ;'),text.replace('END SPECIALNETS # end','END SPECIALNETS extra')):
            with self.assertRaises(ValueError):D.parse(bad,TECH)

    def test_unresolved_via_cut_geometry_and_generated_patterns_reject(self):
        for extra in (GV.replace('+ ROWCOL 2 3','+ ROWCOL 0 3'),GV.replace('CUTSIZE 190 190','CUTSIZE 191 190'),
            GV.replace('+ ROWCOL 2 3','+ ROWCOL 2 3 + PATTERNNAME sparse'),GV.replace('LAYERS Metal1 Via1 Metal2','LAYERS Metal2 Via1 Metal1')):
            with self.assertRaises(ValueError):D.parse(fixture(extras=extra),TECH)
        with self.assertRaises(ValueError):D.parse(fixture(),TECH.replace(' RECT 0.315 -0.095 0.505 0.095 ;',' POLYGON 0 0 1 0 1 1 ;'))
        with self.assertRaises(ValueError):D.parse(fixture(),TECH.replace(' TYPE CUT ;',' TYPE IMPLANT ;'))

    def test_explicit_via_and_absolute_special_rect_are_complete(self):
        extra='''VIAS 1 ;
- E + RECT Metal1 ( -150 -150 ) ( 150 150 ) + RECT Via1 ( -95 -95 ) ( 95 95 ) + RECT Metal2 ( -150 -150 ) ( 150 150 ) ;
END VIAS
'''
        text=fixture('Metal1 ( 0 0 ) E',extra)+'''SPECIALNETS 1 ;
- VSS + RECT Metal1 MASK 1 ( -100 -100 ) ( 100 100 ) + USE GROUND ;
END SPECIALNETS
'''
        r=D.parse(text,TECH);self.assertEqual(r['via_usage']['E']['cut_occurrences'],1)
        self.assertEqual(r['layer_usage']['Metal1']['rect_patch_count'],1)

    def test_unparsed_conducting_sections_and_zero_width_reject(self):
        for kind in ('FILLS','SLOTS'):
            with self.assertRaises(ValueError):D.parse(fixture(extras=kind+' 1 ;\n- unknown ;\nEND '+kind+'\n'),TECH)
            with self.assertRaises(ValueError):D.parse(fixture(extras=kind+' 0 ;\n- hidden ;\nEND '+kind+'\n'),TECH)
        with self.assertRaises(ValueError):D.parse(fixture()+'''SPECIALNETS 1 ;
- p + ROUTED Metal1 0 ( 0 0 ) ( 1 0 ) ;
END SPECIALNETS
''',TECH)

    def test_units_convert_widths_integrally_and_do_not_relabel_lengths(self):
        r=D.parse(fixture('Metal1 ( 0 0 ) ( 1000 0 )').replace('MICRONS 1000','MICRONS 2000'),TECH)
        self.assertEqual(r['layer_usage']['Metal1']['widths_dbu'],{'320':1})
        self.assertEqual(r['layer_usage']['Metal1']['centerline_length_um'],'0.5')
        with self.assertRaises(ValueError):D.parse(fixture().replace('MICRONS 1000','MICRONS 1'),TECH)


class FinalAuthorityControls(unittest.TestCase):
    def test_coarse_obligations_never_promote_full_context(self):
        r=W.obligations(D.parse(fixture(),TECH))
        self.assertEqual(r['used_named_vias_outside_historical_five_fixture_names'],['V'])
        self.assertTrue(r['all_eight_model_coverage_fields_remain_unqualified'])
        self.assertFalse(r['model_qualified']);self.assertFalse(r['qualified_timing'])

    def test_certified_tech_actual_odb_and_selector_are_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);pdk=root/'pdk';tech=pdk/W.TECH_REL;tech.parent.mkdir(parents=True);tech.write_text(TECH)
            for name in ('report.json','preparation.json','design.def','native-geometry.json','actual-signal/inventory.json','base/preparation.json','final.odb','pdk-tree.json'):
                p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(fixture() if name=='design.def' else '{}')
            config={'TECH_LEFS':{'nom*':'/work/pdk/'+W.TECH_REL},'DEFAULT_CORNER':'nom_typ','PDK_ROOT':'/work/pdk'}
            (root/'resolved.json').write_text(json.dumps(config));pin=W.V.sha(tech)
            target={'actual_odb':{'path':str(root/'final.odb'),'sha256':W.V.sha(root/'final.odb')}}
            prep={'prepared':str(root/'base'),'pdk_root':str(pdk),'target':target,'source_flow':str(root)}
            base={'pdk_root':str(pdk),'pdk_identity':{'complete_files_sha256':{W.TECH_REL:pin}},'pdk_tree':{'path':str(root/'pdk-tree.json')}}
            (root/'native-report.json').write_text(json.dumps({'source_odb_sha256':target['actual_odb']['sha256'],'generated_files_sha256':{'design.def':W.V.sha(root/'design.def')}}))
            with patch.object(W.V,'closed_views',return_value=({'target':target},prep)),patch.object(W.V.P,'verify',return_value=base),patch.object(W,'TECH_SHA',pin):
                a=W.authority(root/'report.json');self.assertEqual(a[4]['technology_LEF']['sha256'],pin)
                for key in ('technology_LEF','selected_final_ODB','actual_cell_pin_inventory','pdk_git_tree'):self.assertIn(key,a[4])
                config['TECH_LEFS']={'nom*':'/other/tech.lef'};(root/'resolved.json').write_text(json.dumps(config))
                with self.assertRaises(ValueError):W.authority(root/'report.json')
                config['TECH_LEFS']={'nom*':'/work/pdk/'+W.TECH_REL};(root/'resolved.json').write_text(json.dumps(config));tech.write_text(TECH+'# changed\n')
                with self.assertRaises(ValueError):W.authority(root/'report.json')

    def test_build_rechecks_authority_and_missing_route_material(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);defpath=root/'design.def';lef=root/'tech.lef';defpath.write_text(fixture());lef.write_text(TECH)
            a=({'physical_candidate':{'target':'same'}},{},{},{'fresh_DEF':defpath,'technology_LEF':lef},{'selected_final_ODB':{'sha256':'a'*64}},'/work/pdk/tech.lef')
            with patch.object(W,'authority',return_value=a),patch.object(W,'source_identity',return_value={'owned':'frozen'}):
                r=W.build(root/'report.json');self.assertFalse(r['model_qualified']);self.assertTrue(r['exact_same_target_fresh_view_authority_closed'])
                defpath.write_text(fixture().replace('+ ROUTED Metal1 ( 0 0 0 ) ( 1000 * 0 ) V FN ( * 2000 ) RECT ( -100 -100 100 100 )',''))
                with self.assertRaisesRegex(ValueError,'Missing routed material'):W.build(root/'report.json')
            defpath.write_text(fixture());changed=deepcopy(a);changed[4]['selected_final_ODB']['sha256']='b'*64
            with patch.object(W,'authority',side_effect=[a,changed]),patch.object(W,'source_identity',return_value={'owned':'frozen'}):
                with self.assertRaisesRegex(ValueError,'changed during'):W.build(root/'report.json')


if __name__=='__main__':unittest.main()
