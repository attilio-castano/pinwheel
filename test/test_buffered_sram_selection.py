"""Shape refusals and name hygiene for the untrusted selection proof hints."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import buffered_sram_readback as controller
import buffered_sram_selection as selection


def fixture(prefix):
    rb = controller.backend()
    graph = rb.Graph()
    counter = 0
    def node(width, op, args=(), value=None, name=None):
        nonlocal counter
        counter += 1
        name = name or prefix + str(counter)
        graph.nodes[name] = rb.Node(width, op, tuple(args), value)
        return name
    def tree(bits, words, address):
        if not bits:
            return words[0]
        low = node(1, 'slice', [address], 0)
        high = node(bits - 1, 'slice', [address], 1) if bits > 1 else None
        return node(graph.nodes[words[0]].width, 'mux',
                    [low, tree(bits-1, words[1::2], high), tree(bits-1, words[::2], high)])
    instruction = node(64, 'lit', value=0, name=prefix + 'instruction')
    zero = node(92, 'lit', value=0)
    rows, words = [], []
    for k in range(64):
        guard = node(1, 'lt', [node(7, 'lit', value=k), 'r_count'])
        payload = node(92, 'concat', ['r_metadata' + str(k), instruction])
        row = node(92, 'mux', [guard, payload, zero], name='v117' if k == 0 else None)
        rows.append(row)
        key = node(4, 'slice', [row], 88)
        dictionary = tree(4, ['r_branch' + str(j) for j in range(16)], key)
        words.append(node(144, 'concat', [dictionary, node(88, 'slice', [row], 0)]))
    address = node(6, 'slice', ['r_pc'], 0)
    source_root = tree(6, words, address)
    compact = tree(6, rows, address)
    key = node(4, 'slice', [compact], 88)
    dictionary = tree(4, ['r_branch' + str(j) for j in range(16)], key)
    target_root = node(144, 'concat', [dictionary, node(88, 'slice', [compact], 0)])
    return rb, graph, source_root, target_root, rows


class SelectionBoundaries(unittest.TestCase):
    def setUp(self):
        self.rb, self.source, self.sroot, _, self.srows = fixture('source')
        _, self.target, _, self.troot, self.trows = fixture('target')

    def generate(self, **options):
        return selection.selection_source(self.rb, self.source, self.target,
                                          self.sroot, self.troot, **options)

    def test_discovered_coordinates_and_template_name_hygiene(self):
        text, metadata = self.generate()
        self.assertEqual(metadata['source_instruction'], 'sourceinstruction')
        self.assertEqual(metadata['target_instruction'], 'targetinstruction')
        # v117 is a 92-bit row here, not the 64-bit instruction template marker.
        self.assertIn('Source.v117 i s', text)
        self.assertIn('Source.sourceinstruction i s = RTL.targetinstruction i s', text)
        self.assertNotIn('__SOURCE_', text)
        self.assertNotIn('__TARGET_', text)
        self.assertIn('theorem selection_entry', text)

    def test_incomplete_tree_is_refused(self):
        self.source.nodes[self.sroot] = self.rb.Node(144, 'lit', value=0)
        with self.assertRaisesRegex(ValueError, 'balanced selection tree'):
            self.generate()

    def test_wrong_metadata_coordinate_is_refused(self):
        row = self.source.nodes[self.srows[0]]
        payload = self.source.nodes[row.args[1]]
        self.source.nodes[row.args[1]] = self.rb.Node(92, 'concat', ['r_metadata1', payload.args[1]])
        with self.assertRaisesRegex(ValueError, 'metadata coordinate'):
            self.generate()

    def test_different_row_instruction_is_refused(self):
        row = self.target.nodes[self.trows[1]]
        payload = self.target.nodes[row.args[1]]
        self.target.nodes[row.args[1]] = self.rb.Node(92, 'concat', [payload.args[0], 'word'])
        with self.assertRaisesRegex(ValueError, 'one instruction'):
            self.generate()

    def test_changed_selected_row_slice_is_refused(self):
        root = self.target.nodes[self.troot]
        low = self.target.nodes[root.args[1]]
        self.target.nodes[root.args[1]] = self.rb.Node(88, 'slice', low.args, 1)
        with self.assertRaisesRegex(ValueError, 'selected row low slice'):
            self.generate()

    def test_non_lsb_selection_root_is_refused(self):
        root = self.source.nodes[self.sroot]
        guard = self.source.nodes[root.args[0]]
        self.source.nodes[root.args[0]] = self.rb.Node(1, 'slice', guard.args, 1)
        with self.assertRaisesRegex(ValueError, 'LSB guard'):
            self.generate()

    def test_untrusted_lean_names_cannot_inject_declarations(self):
        for key in ('namespace', 'hints_module', 'graphs_module'):
            with self.subTest(field=key), self.assertRaisesRegex(ValueError, 'Invalid Lean'):
                self.generate(**{key: 'Module\naxiom injected : False'})


if __name__ == '__main__':
    unittest.main()
