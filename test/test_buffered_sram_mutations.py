"""Independent fixture and refusal checks for controller corruption controls."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import buffered_sram_readback as controller
import buffered_sram_mutations as mutations


class ControllerMutationBoundaries(unittest.TestCase):
    def setUp(self):
        self.rb = controller.backend()
        self.original = self.rb.Graph()
        self.original.next = {name: name for name in self.rb.REGISTERS}
        self.original.next['r_tx_data'] = 'tx_data'
        for name, (width, _) in self.rb.OUTPUTS.items():
            literal = 'fixture_' + name
            self.original.nodes[literal] = self.rb.Node(width, 'lit', value=0)
            self.original.outputs[name] = literal

    def test_baseline_certificate_graph_is_required(self):
        with self.assertRaisesRegex(ValueError, 'original certified graph'):
            mutations.mutation_sources(self.rb, self.original, 'next', 'r_tx_data')

    def test_unknown_operation_and_witness_are_refused(self):
        for operation, port in [('step', 'r_phase'), ('next', 'r_metadata0')]:
            with self.subTest(operation=operation, port=port), self.assertRaisesRegex(ValueError, 'witness'):
                mutations.mutation_sources(self.rb, self.original, operation, port, baseline=self.original)

    def test_unused_high_payload_bit_is_part_of_the_distinguishing_fixture(self):
        inputs, registers = mutations.FIXTURES['r_tx_data']
        self.assertEqual(inputs['tx_length'], 1)
        self.assertEqual(inputs['tx_data'], 0x80000001)
        self.assertEqual(mutations.graph_values(self.original, inputs, registers)['tx_data'], 0x80000001)
        candidate = copy.deepcopy(self.original)
        candidate.nodes['mask'] = self.rb.Node(32, 'lit', value=1)
        candidate.nodes['truncated'] = self.rb.Node(32, 'and', ('tx_data', 'mask'))
        candidate.next['r_tx_data'] = 'truncated'
        texts = mutations.mutation_sources(self.rb, candidate, 'next', 'r_tx_data', baseline=self.original)
        self.assertIn('= 1#32 := candidate_value_truncated', texts['SramReject'])
        self.assertIn('= 2147483649#32 := by rfl', texts['SramReject'])
        self.assertIn('(step_correct faultInputs faultState (.core .txData)).symm.trans original',
                      texts['SramReject'])

    def test_an_unknown_graph_operator_cannot_supply_a_reduction_hint(self):
        self.original.nodes['unknown'] = self.rb.Node(32, 'unknown')
        with self.assertRaisesRegex(ValueError, 'Unsupported candidate operation'):
            mutations.graph_values(self.original, {}, {})


if __name__ == '__main__':
    unittest.main()
