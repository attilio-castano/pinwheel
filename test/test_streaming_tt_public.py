"""Public-output intake refusal controls; Lean checks remain a separate gate."""
from copy import deepcopy
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_tt_join import output_sources


def fixture():
    wire = lambda index: ('wire', index, False)
    frontend = dict(namespace='SyntheticFrontend', model=dict(outputs={
        'miso': tuple(wire(index) for index in range(2, 6)), 'ready': (wire(6),)}))
    core = dict(namespace='SyntheticCore', model=dict(outputs={
        'busy': (wire(7),), 'levels': tuple(wire(index) for index in range(8, 11)),
        'enabled': tuple(wire(index) for index in range(11, 14))}))
    image = tuple(wire(index) for index in range(14))
    embedding = lambda name: dict(embedding=dict(namespace=name), plan=dict(image=image))
    parent = dict(labels=tuple(('input', str(index), 0) for index in range(14)),
        nodes=[], outputs={})
    for port, sources in [('uio_oe', (11, 12, 13)), ('uio_out', (8, 9, 10)),
                          ('uo_out', (2, 3, 4, 5, 6, 7))]:
        outputs = []
        for source in sources:
            outputs.append(wire(14 + len(parent['nodes'])))
            parent['nodes'].append(dict(sources=(0, 1, source), expression=
                ('*', ('*', ('variable', 'p0'), ('variable', 'p1')), ('variable', 'p2'))))
        parent['outputs'][port] = tuple(outputs + [('constant', False)] * (8 - len(outputs)))
    return parent, frontend, core, embedding('SyntheticFEImage'), embedding('SyntheticCoreImage')


class PublicOutputIntake(unittest.TestCase):
    def test_all24_endpoints_and_opaque_helpers_are_emitted(self):
        parent, *rest = fixture()
        source = output_sources(parent, *rest)
        self.assertEqual(set(source), {'PhysicalGRTPublicLocal', 'PhysicalGRTPublicOutputs'})
        body = source['PhysicalGRTPublicOutputs']
        endpoints = re.findall(r'^theorem public_(uio_oe|uio_out|uo_out)_(\d+)_word ', body, re.M)
        self.assertEqual(set(endpoints), {(port, str(bit)) for port in parent['outputs'] for bit in range(8)})
        self.assertEqual(len(endpoints), 24)
        self.assertEqual(body.count('exact public_observe_mask '), 12)
        self.assertEqual(body.count('exact public_observe_constant '), 12)
        self.assertNotIn('Network.value_node', body)
        self.assertIn('theorem public_observe_mask', source['PhysicalGRTPublicLocal'])

    def test_omission_extra_endpoint_polarity_and_actual_mapping_refuse(self):
        for mutation in ('omit', 'extra', 'negative', 'unused', 'source', 'gate'):
            values = list(deepcopy(fixture()))
            parent = values[0]
            roots = list(parent['outputs']['uio_oe'])
            if mutation == 'omit': roots.pop()
            elif mutation == 'extra': roots.append(('constant', False))
            elif mutation == 'negative': roots[0] = ('wire', 14, True)
            elif mutation == 'unused': roots[7] = ('constant', True)
            elif mutation == 'source':
                image = list(values[4]['plan']['image'])
                image[11] = ('wire', 12, False)
                values[4]['plan']['image'] = tuple(image)
            elif mutation == 'gate': parent['nodes'][0]['sources'] = (0, 1, 12)
            parent['outputs']['uio_oe'] = tuple(roots)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                output_sources(*values)


if __name__ == '__main__':
    unittest.main()
