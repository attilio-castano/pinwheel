"""Refusal controls for the untrusted SRAM semantic-reference descriptions."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import buffered_reactive_reference as reactive
import buffered_sram_reference as reference
import buffered_sram_readback as sram


def fixture(rb):
    graph = rb.Graph()
    graph.next = {name: name for name in rb.REGISTERS}
    for name, (width, _) in rb.OUTPUTS.items():
        literal = 'fixture_' + name
        graph.nodes[literal] = rb.Node(width, 'lit', value=0)
        graph.outputs[name] = literal
    return graph


class SramReferenceBoundaries(unittest.TestCase):
    def setUp(self):
        self.environment_backend = reference.environment_backend()
        self.reactive_backend = reactive.backend()
        self.environment = fixture(self.environment_backend)
        self.reactive = fixture(self.reactive_backend)

    def test_omitted_environment_root_is_refused(self):
        for name in self.environment.outputs:
            changed = copy.deepcopy(self.environment)
            del changed.outputs[name]
            with self.subTest(root=name), self.assertRaisesRegex(ValueError, 'Incomplete SRAM'):
                reference.environment_sources(self.environment_backend, changed)

    def test_omitted_reactive_root_is_refused(self):
        for name in self.reactive.outputs:
            changed = copy.deepcopy(self.reactive)
            del changed.outputs[name]
            with self.subTest(root=name), self.assertRaisesRegex(ValueError, 'Incomplete named'):
                reactive.sources_source(self.reactive_backend, changed)

    def test_complete_interface_and_real_state_inventory_are_retained(self):
        graph, mapping, post = reference.complete_reference(self.environment, self.reactive)
        rb = sram.backend()
        sram.validate_graph(rb, graph)
        self.assertEqual(set(graph.next), set(rb.REGISTERS))
        self.assertEqual(set(graph.outputs), set(rb.OUTPUTS))
        self.assertEqual(sum(width for width, _ in rb.REGISTERS.values()), 3151)
        self.assertFalse(any(name.startswith('r_word') for name in graph.nodes))
        self.assertNotIn('mem_q0', self.reactive_backend.INPUTS)
        self.assertNotIn('mem_q1', self.reactive_backend.INPUTS)
        # The actual response ports remain separate leaves of the composed DAG.
        self.assertNotEqual(graph.nodes['mem_q0'].value, graph.nodes['mem_q1'].value)

    def test_word_environment_is_required_even_when_candidate_does_not_read_it(self):
        changed = copy.deepcopy(self.environment)
        del changed.outputs['register_word63']
        with self.assertRaisesRegex(ValueError, 'Missing environment substitution'):
            reference.compose_environment(changed, self.reactive)

    def test_composition_never_accepts_a_colliding_operator_name(self):
        changed = copy.deepcopy(self.environment)
        changed.nodes['p_fixture_helper_busy'] = self.environment_backend.Node(1, 'lit', value=0)
        with self.assertRaisesRegex(ValueError, 'Ambiguous composition node'):
            reference.compose_environment(changed, self.reactive)

    def test_malformed_composed_width_cannot_reach_proof_generation(self):
        graph, _, _ = reference.complete_reference(self.environment, self.reactive)
        rb = sram.backend()
        graph.nodes['read_address_false'] = rb.Node(7, 'slice',
            graph.nodes['read_address_false'].args, 0)
        with self.assertRaisesRegex(ValueError, 'Invalid graph mux width'):
            sram.validate_graph(rb, graph)


if __name__ == '__main__':
    unittest.main()
