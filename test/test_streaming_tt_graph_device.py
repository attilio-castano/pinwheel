"""Complete physical endpoint domains and register-basis refusal controls."""
from copy import deepcopy
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_tt_graph import correspondence_sources, device_sources


def fixture():
    state = tuple('ff' + str(index) for index in range(6039))
    model = dict(labels=tuple(('input', 'p' + str(index), 0) for index in range(18)) +
        tuple(('state', name, 0) for name in state), nodes=(),
        next={name: ('wire', 18 + index, False) for index, name in enumerate(state)},
        outputs={port: (('constant', False),) * 8 for port in ('oe', 'uio', 'uo')})
    return model, dict(module='FixtureNetwork', namespace='Fixture.Network')


def complete_chunks(source, theorem, domain):
    blocks = re.findall(r'^private theorem ' + re.escape(theorem) +
        r'_bounded_chunk_\d+ : ∀ offset : Fin (\d+), ([^\n]+)', source, re.M)
    points = []
    for width, proposition in blocks:
        match = re.search(r'⟨(\d+) \+ offset.val, .*?⟩ : Fin (\d+)', proposition)
        if match is None or int(match[2]) != domain:
            raise AssertionError('Wrong endpoint domain')
        points.extend(range(int(match[1]), int(match[1]) + int(width)))
    if points != list(range(domain)):
        raise AssertionError('Omitted, duplicated or shifted endpoint range')


class DeviceProofDomains(unittest.TestCase):
    def test_all6039_D_and24_output_endpoints_remain_explicit(self):
        model, network = fixture()
        modules, actual = device_sources(model, network, prefix='FixtureActual', namespace='Fixture.Actual')
        source = modules['FixtureActualDevice']
        complete_chunks(source, 'nextBound', 6039)
        complete_chunks(source, 'outputBound', 24)
        reference = dict(actual, module='FixtureReferenceDevice', namespace='Fixture.Reference')
        proof = correspondence_sources(reference, actual,
            dict(module='FixtureTransportProof', namespace='Fixture.Transport'),
            module='FixtureProof', namespace='Fixture.Proof')['FixtureProof']
        complete_chunks(proof, 'next', 6039)
        complete_chunks(proof, 'output', 24)
        self.assertIn('theorem next : ∀ index : Fin 6039,', proof)
        self.assertIn('theorem output : ∀ index : Fin 24,', proof)
        self.assertEqual(actual['registers'], 6039)
        self.assertEqual(actual['inputs'], 18)
        self.assertEqual(len(actual['outputs']), 24)
        for name in ('next', 'output'):
            self.assertIn('device.' + name + ' index).rename Fixture.Transport.contraction.image', proof)

    def test_independent_coverage_check_rejects_omission_shift_and_duplication(self):
        model, network = fixture()
        source = device_sources(model, network, prefix='Fixture', namespace='Fixture')[0]['FixtureDevice']
        complete_chunks(source, 'nextBound', 6039)
        for mutated in (source.replace('Fin 128,', 'Fin 127,', 1),
                        source.replace('⟨128 + offset.val', '⟨129 + offset.val', 1),
                        source.replace('⟨128 + offset.val', '⟨0 + offset.val', 1)):
            with self.assertRaises(AssertionError):
                complete_chunks(mutated, 'nextBound', 6039)

    def test_missing_D_and_reordered_Q_basis_refuse(self):
        for mode in ('missing-D', 'reordered-Q'):
            model, network = deepcopy(fixture())
            if mode == 'missing-D':
                del model['next']['ff6038']
            else:
                labels = list(model['labels'])
                labels[-1], labels[-2] = labels[-2], labels[-1]
                model['labels'] = tuple(labels)
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                device_sources(model, network, prefix='Fixture', namespace='Fixture')


if __name__ == '__main__':
    unittest.main()
