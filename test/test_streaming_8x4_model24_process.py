"""Portable source-defined process controls; no retained intake or Native."""
from decimal import Decimal as D
from pathlib import Path
import sys
import unittest
import tempfile
import json
import hashlib
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_process as W
from test_streaming_8x4_model24 import ITF_FIXTURE

class ProcessControls(unittest.TestCase):
    def test_fullstack_partition_resistance_and_gap_arithmetic(self):
        r=W.emit(ITF_FIXTURE,'ITF_TYP');m=r['conductors']
        self.assertEqual(len(m),5);self.assertEqual(m[1]['fields']['distance'],'0.540')
        self.assertEqual(D(m[1]['fields']['resistivity']),D('.088')*D('.49'))
        self.assertEqual(D(m[-1]['bottom_um']),D('5.4'));self.assertEqual(D(m[-1]['top_um']),D('7.4'))
        d=r['dielectrics'];self.assertEqual(len(d),14)
        self.assertEqual([(x['source_layer'],D(x['fields']['epsilon'])) for x in d[:3]], [('fox',D('3.95')),('nitride',D('6.5')),('dummyOx',D('4.1'))])
        self.assertTrue(W.verify_emission(r['process_text'],m,d,r['air']))
        self.assertFalse(r['model_qualified']);self.assertNotIn('width_delta',r['process_text'])

    def test_corner_label_does_not_invent_new_geometry_or_qualified_correlation(self):
        rows=[W.emit(ITF_FIXTURE,c) for c in W.CORNERS]
        self.assertEqual(rows[0]['fullstack'],rows[1]['fullstack'])
        self.assertTrue(rows[0]['policy']['source_arithmetic_does_not_establish_foundry_corner_qualification'])
        with self.assertRaises(ValueError):W.emit(ITF_FIXTURE,'MIN')

    def test_changed_er_is_explicit_source_policy_not_retained_typ_substitution(self):
        r=W.emit(ITF_FIXTURE.replace('ER=4.1','ER=4.0'),'ITF_MIN')
        self.assertTrue(all(D(x['fields']['epsilon'])==4 for x in r['dielectrics'] if x['source_layer'].startswith('ox')))
        self.assertEqual(D(r['conductors'][1]['fields']['min_width']),D('.2'))

    def test_any_emitted_numeric_mutation_is_rejected(self):
        r=W.emit(ITF_FIXTURE,'ITF_TYP')
        for text in [r['process_text'].replace('distance 0.540','distance 0.680'),r['process_text'].replace('epsilon 6.5','epsilon 4.1'),r['process_text']+'CONDUCTOR Foreign { thickness 1 }\n']:
            with self.assertRaises(ValueError):W.verify_emission(text,r['conductors'],r['dielectrics'],r['air'])

    def test_strict_owned_reopener_membership_and_source_identity(self):
        digest=hashlib.sha256(ITF_FIXTURE.encode()).hexdigest()
        with tempfile.TemporaryDirectory() as tmp,patch.object(W,'ITF_SHA',{c:digest for c in W.CORNERS}):
            root=Path(tmp);cases=[]
            for c in W.CORNERS:
                row=W.emit(ITF_FIXTURE,c);(root/(c+'.itf')).write_text(ITF_FIXTURE)
                (root/(c+'.process')).write_text(row.pop('process_text'));cases.append(row)
            manifest=W.expected_manifest(cases,W.INTAKE_MANIFEST);(root/'manifest.json').write_text(json.dumps(manifest))
            self.assertFalse(W.verify(root)['model_qualified'])
            unknown=root/'foreign';unknown.write_text('foreign')
            with self.assertRaises(ValueError):W.verify(root)
            unknown.unlink();p=root/'ITF_MIN.process';original=p.read_text();p.write_text(original.replace('0.540','0.680'))
            with self.assertRaises(ValueError):W.verify(root)
            p.write_text(original);bad=dict(manifest,producer_sha256={});(root/'manifest.json').write_text(json.dumps(bad))
            with self.assertRaises(ValueError):W.verify(root)

if __name__=='__main__':unittest.main()
