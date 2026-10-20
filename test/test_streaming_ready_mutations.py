"""Keep the retained-export negative control on the actual held-state arc."""
from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_ready_readback as adapter


class ReadyMutationTests(unittest.TestCase):
    def retained(self):
        return next(row for row in adapter.mutation_specs('frontend')
            if row[0] == 'retained-export')

    def test_inline_and_named_mux_change_only_retained_arc(self):
        cases = (
            "    r_export_bits <= initialize ? 7'h0 : take ? {1'h0, status_rx_bits} : r_export_bits;\n",
            "  wire [6:0] _GEN_835 = _GEN_674 ? _GEN_834 : r_export_bits;\n"
            "  wire [6:0] _GEN_836 = _GEN_800 ? 7'h0 : _GEN_835;\n"
            "  wire [6:0] _GEN_837 = _GEN_825 ? 7'h0 : _GEN_836;\n"
            "  wire [6:0] _GEN_838 = initialize ? 7'h0 : _GEN_837;\n"
            "  wire [6:0] _GEN_845 = r_work_bulk ? r_export_bits : 7'h0;\n"
            "    r_export_bits <= _GEN_838;\n",
        )
        _, pattern, replacement, operation = self.retained()
        self.assertEqual(operation, 'next')
        for source in cases:
            with self.subTest(source=source):
                value, count = re.subn(pattern, replacement, source)
                self.assertEqual(count, 1)
                self.assertEqual(value.count("(r_export_bits ^ 7'h1)"), 1)
                self.assertEqual(value.replace("(r_export_bits ^ 7'h1)", 'r_export_bits'), source)
        self.assertIn('r_work_bulk ? r_export_bits :', value)
        self.assertIn('r_export_bits <= _GEN_838;', value)

    def test_missing_or_ambiguous_retained_arc_cannot_look_unique(self):
        _, pattern, replacement, _ = self.retained()
        source = "  wire [6:0] _GEN_835 = take ? data : r_export_bits;\n"
        for text, expected in (
            ("  wire [6:0] _GEN_845 = r_work_bulk ? r_export_bits : 7'h0;\n", 0),
            (source.replace('[6:0]', '[5:0]'), 0),
            (source + source.replace('_GEN_835', '_GEN_836'), 2),
        ):
            with self.subTest(text=text):
                self.assertEqual(re.subn(pattern, replacement, text)[1], expected)

    def test_other_control_membership_and_replacements_are_unchanged(self):
        old = adapter.base.mutation_specs('frontend')
        new = adapter.mutation_specs('frontend')
        self.assertEqual([row[0] for row in old], [row[0] for row in new])
        self.assertEqual([row for row in old if row[0] != 'retained-export'],
            [row for row in new if row[0] != 'retained-export'])
        core = adapter.mutation_specs('core')
        self.assertEqual([row[0] for row in core[:-2]],
            [row[0] for row in adapter.base.mutation_specs('core')])
        self.assertEqual([row[2:] for row in core[:-2]],
            [row[2:] for row in adapter.base.mutation_specs('core')])
        self.assertEqual(core[0], adapter.base.mutation_specs('core')[0])
        self.assertEqual(core[2], adapter.base.mutation_specs('core')[2])
        self.assertEqual([row[0] for row in core[-2:]], ['sampler-stage', 'guard-bypass'])

    def test_core_inline_and_named_muxes_change_the_same_data_arc(self):
        cases = {
            'program-bank': (
                "    r_word0 <= initialize ? 64'h0 : take ? word : r_word0;\n",
                "  wire [63:0] _GEN_11 = _GEN_10 ? word : r_word0;\n",
                'word', "(word ^ 64'h1)"),
            'sampler-stage': (
                "    r_stage2 <= initialize ? 2'h0 : r_stage1;\n",
                "  wire [1:0] _GEN_1437 = _GEN_4 ? 2'h0 : r_stage1;\n",
                'r_stage1', 'raw_inputs'),
            'guard-bypass': (
                "    r_current_word <= initialize ? 64'h0 : take ? _GEN_1129 : r_current_word;\n",
                "  wire [63:0] _GEN_1229 = _GEN_1228 ? _GEN_1129 : r_current_word;\n",
                '_GEN_1129', "(_GEN_1129 & 64'hbfffffffffffffff)"),
        }
        specs = {row[0]:row for row in adapter.mutation_specs('core')}
        for name, (inline, named, original, changed) in cases.items():
            _, pattern, replacement, operation = specs[name]
            self.assertEqual(operation, 'next')
            for source in (inline, named):
                with self.subTest(name=name, source=source):
                    value, count = re.subn(pattern, replacement, source)
                    self.assertEqual(count, 1)
                    self.assertEqual(value.replace(changed, original), source)
                    self.assertEqual(value.count(changed), 1)

    def test_core_wrong_width_or_different_mux_arc_cannot_look_unique(self):
        specs = {row[0]:row for row in adapter.mutation_specs('core')}
        cases = {
            'program-bank': "  wire [62:0] _GEN_11 = take ? word : r_word0;\n",
            'sampler-stage': "  wire [1:0] _GEN_1437 = take ? r_stage1 : 2'h0;\n",
            'guard-bypass': "  wire [63:0] _GEN_1229 = take ? r_current_word : _GEN_1129;\n",
        }
        for name, source in cases.items():
            with self.subTest(name=name):
                self.assertEqual(re.subn(specs[name][1], specs[name][2], source)[1], 0)


if __name__ == '__main__':
    unittest.main()
