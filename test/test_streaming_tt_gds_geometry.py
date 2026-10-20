#!/usr/bin/env python3
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_tt_gds_geometry as G


class GeometryTests(unittest.TestCase):
    def test_parser_all43_pins_portable_inline_fixture(self):
        names=['clk',*[f'pin_{index}' for index in range(42)]]
        text='UNITS DISTANCE MICRONS 1000 ;\nPINS 43 ;\n'+''.join(
            f'- {name} + NET {name} + DIRECTION INPUT + USE SIGNAL\n+ PORT\n'
            '+ LAYER Metal4 ( -150 -500 ) ( 150 500 )\n+ PLACED ( 187200 710140 ) N ;\n'
            for name in names)+'END PINS\n'
        pins=G.template_pins(text)
        self.assertEqual(len(pins),43);self.assertEqual(pins['clk']['center'],[187.2,710.14])
        for changed in (text.replace('PINS 43 ;','PINS 42 ;'),text.replace('+ NET clk','+ NET unknown',1),
                text.replace('+ LAYER Metal4','+ LAYER Metal3',1),text.replace('710140 ) N ;','710140 ) S ;',1)):
            with self.assertRaises(ValueError):G.template_pins(changed)

    @unittest.skipUnless((G.P.ROOT/'build/streaming-tt-signoff/upstream/tt-support-d66cf17/tech/ihp-sg13cmos5l/def/tt_block_6x4_pgvdd.def').is_file(),
        'Optional actual official template integration fixture is absent; portable parser fixture still runs')
    def test_available_actual_official_template_is_pinned(self):
        path=G.P.ROOT/'build/streaming-tt-signoff/upstream/tt-support-d66cf17/tech/ihp-sg13cmos5l/def/tt_block_6x4_pgvdd.def'
        self.assertEqual(G.sha(path),G.TEMPLATE_SHA256);self.assertEqual(len(G.template_pins(path.read_text())),43)

    def test_geometry_tolerance_never_aliases_missing_coordinates(self):
        self.assertTrue(G.near([0.,710.64],[0.,710.640000000001]))
        self.assertFalse(G.near([0.,710.64],[0.,710.641]));self.assertFalse(G.near([0.],[0.,0.]))

    def test_exact_boundary_requires_four_actual_corner_vertices(self):
        vertices=[[0.,0.],[0.,710.64],[1289.28,710.64],[1289.28,0.]]
        polygon=SimpleNamespace(layer=189,datatype=4,bounding_box=lambda:((0.,0.),(1289.28,710.64)),
            area=lambda:1289.28*710.64,points=SimpleNamespace(tolist=lambda:vertices))
        self.assertTrue(G.measure(SimpleNamespace(labels=[]),[polygon],{})['exact_official_6x4_prBoundary_189_4'])
        vertices.append([0.,355.32])
        self.assertFalse(G.measure(SimpleNamespace(labels=[]),[polygon],{})['exact_official_6x4_prBoundary_189_4'])
        vertices[:]=[[0.,0.],[0.,710.64],[1289.28,355.32],[1289.28,0.]]
        self.assertFalse(G.measure(SimpleNamespace(labels=[]),[polygon],{})['exact_official_6x4_prBoundary_189_4'])


if __name__=='__main__':unittest.main()
