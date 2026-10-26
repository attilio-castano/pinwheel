import importlib.util
from decimal import Decimal
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('rc_process', Path(__file__).resolve().parents[1] / 'scripts/streaming_8x4_rc_process.py')
P = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(P)


def fixture():
    text = ''
    for name in P.METALS:
        text += f'LAYER {name}\n TYPE ROUTING ;\n RESISTANCE RPERSQ 0.1 ;\nEND {name}\n'
    for name in ('Via1', 'Via2', 'Via3', 'TopVia1'):
        text += f'LAYER {name}\n TYPE CUT ;\n RESISTANCE 20 ;\nEND {name}\n'
    text += 'VIA TwoCut\n RESISTANCE 20 ;\n LAYER Via1 ;\n RECT -0.2 -0.1 -0.1 0.1 ;\n LAYER Via1 ;\n RECT 0.1 -0.1 0.2 0.1 ;\nEND TwoCut\n'
    return text


class ProcessTests(unittest.TestCase):
    def test_repeated_regions_are_two_cuts_on_one_layer(self):
        via = P.lef_resistance_inventory(fixture())['explicit_vias']['TwoCut']
        self.assertEqual(via['cut_count'], 2)
        self.assertEqual(via['cut_layer'], 'Via1')
        self.assertEqual(via['cut_bbox_um'], (Decimal('-.2'), Decimal('-.1'), Decimal('.2'), Decimal('.1')))

    def test_two_distinct_cut_layers_rejected(self):
        with self.assertRaisesRegex(ValueError, 'exactly one cut layer'):
            P.lef_resistance_inventory(fixture().replace('LAYER Via1 ;\n RECT 0.1', 'LAYER Via2 ;\n RECT 0.1'))

    def test_bad_cut_geometry_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Nonpositive via cut'):
            P.lef_resistance_inventory(fixture().replace('RECT 0.1 -0.1 0.2', 'RECT 0.2 -0.1 0.1'))

    def test_duplicate_layer_or_resistance_rejected(self):
        for bad in (fixture() + 'LAYER Via1\n TYPE CUT ;\n RESISTANCE 20 ;\nEND Via1\n',
                    fixture().replace('RESISTANCE RPERSQ 0.1 ;', 'RESISTANCE RPERSQ 0.1 ; RESISTANCE RPERSQ 0.2 ;', 1)):
            with self.assertRaises(ValueError):
                P.lef_resistance_inventory(bad)


if __name__ == '__main__':
    unittest.main()
