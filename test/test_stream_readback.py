"""Fail-closed stream state/interface intake, independent of installed CAD."""
import copy
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import paired_readback as pr
import stream_readback as sr
from test_paired_readback import fixture
from validation_run import sha

spec = importlib.util.spec_from_file_location('stream_readback_runner',
    Path(__file__).resolve().parents[1] / 'scripts/check-stream-readback.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class StreamReadback(unittest.TestCase):
    def read(self, rb, module):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'import.json'
            path.write_text(json.dumps({'modules': {rb.TOP: module}}))
            return rb.read_rtl(path)

    def test_exact_extra_state_without_changing_retained_interface(self):
        for kind, count in [('core', 82), ('chip', 111)]:
            rb = sr.backend(kind)
            retained = pr.backend(kind)
            self.assertEqual(len(rb.REGISTERS), count)
            self.assertNotIn('r_stream_enabled', retained.REGISTERS)
            self.assertEqual(rb.INPUTS, retained.INPUTS)
            self.assertEqual(rb.OUTPUTS, retained.OUTPUTS)
            self.assertEqual(len(self.read(rb, fixture(rb)).next), count)
            expected = '.extra .enabled' if kind == 'core' else '.inner (.inner (.inner (.inner (.extra .enabled))))'
            self.assertEqual(rb.REGISTERS['r_stream_enabled'], (1, expected))
        with self.assertRaises(ValueError):
            sr.backend('other')

    def test_missing_or_extra_state_and_every_port_rejected(self):
        for kind in ('core', 'chip'):
            rb = sr.backend(kind)
            for name in rb.REGISTERS:
                with self.subTest(kind=kind, missing_register=name):
                    module = fixture(rb)
                    del module['cells'][name]
                    with self.assertRaises(ValueError):
                        self.read(rb, module)
            module = fixture(rb)
            module['cells']['unmodeled'] = copy.deepcopy(module['cells']['r_stream_enabled'])
            with self.assertRaises(ValueError):
                self.read(rb, module)
            for name in [*rb.INPUTS, *rb.OUTPUTS]:
                with self.subTest(kind=kind, missing_port=name):
                    module = fixture(rb)
                    del module['ports'][name]
                    with self.assertRaises(ValueError):
                        self.read(rb, module)

    def test_new_register_cannot_hide_non_digital_semantics(self):
        for kind in ('core', 'chip'):
            rb = sr.backend(kind)
            module = fixture(rb)
            module['cells']['r_stream_enabled']['connections']['D'] = ['x']
            with self.assertRaises(ValueError):
                self.read(rb, module)
            module = fixture(rb)
            module['cells']['r_stream_enabled']['type'] = '$adff'
            with self.assertRaises(ValueError):
                self.read(rb, module)
            module = fixture(rb)
            module['netnames']['r_stream_enabled']['attributes']['init'] = '0'
            with self.assertRaises(ValueError):
                self.read(rb, module)

    def test_interface_requires_wrapper_state_and_exact_widths(self):
        for kind in ('core', 'chip'):
            rb = sr.backend(kind)
            interface = {name: [dict(name=n, width=w, reference=n) for n, (w, _) in table.items()]
                         for name, table in [('inputs', rb.INPUTS), ('registers', rb.REGISTERS), ('outputs', rb.OUTPUTS)]}
            sr.check_interface(rb, interface)
            stale = copy.deepcopy(interface)
            stale['registers'] = [e for e in stale['registers'] if e['name'] != 'r_stream_enabled']
            with self.assertRaises(ValueError):
                sr.check_interface(rb, stale)
            changed = copy.deepcopy(interface)
            next(e for e in changed['registers'] if e['name'] == 'r_stream_enabled')['width'] = 2
            with self.assertRaises(ValueError):
                sr.check_interface(rb, changed)


class StreamHelperGeneration(unittest.TestCase):
    def pair(self, left, right):
        return dict(left=left, right=right,
            variables=((64, 'input', 'data'), (9, 'reg', 'cursor')))

    def test_large_statement_uses_exact_typed_dag_despite_stale_size(self):
        left = right = (8, 'var', (), 0)
        for _ in range(13):
            left = (8, 'mux', ((1, 'var', (), 1), left, left), None)
            right = (8, 'mux', ((1, 'var', (), 2), right, right), None)
        pair = dict(left=left, right=right, size=1,
            variables=((8, 'input', 'byte'), (1, 'input', 'a'), (1, 'input', 'b')))
        rb = sr.backend('core')
        dag = sr._helper_dag(pair)
        with patch.object(sr, '_helper_dag_proof', return_value='  rfl') as proof:
            source = sr.helper_source(rb, [pair])
        proof.assert_called_once()
        self.assertIn(sr._helper_dag_proposition(rb, dag), source)
        self.assertIn('let d', source)
        self.assertEqual(source.count('let d'), len(dag[1]) - 3)
        self.assertNotIn('axiom ', source)
        self.assertNotIn('sorry', source)

    def test_wide_predicate_cut_drops_its_definition_without_a_premise(self):
        wide = (1, 'eq', ((64, 'var', (), 0), (64, 'lit', (), 1)), None)
        pair = self.pair((1, 'and', (wide, (1, 'lit', (), 1)), None), wide)
        _, nodes, roots = sr._helper_dag(pair)
        atom = next(j for j, node in enumerate(nodes) if node[1] == 'eq')
        literal = nodes[atom][2][1]
        facts = [(f'hd{j}', j) for j, node in enumerate(nodes) if node[1] != 'var']
        facts.append((f'hg{atom}', atom))
        text = '\n'.join(sr._helper_dag_context_proof(nodes, roots, 'hcut',
            f'd{roots[0]} = d{roots[1]}', facts))
        clear = next(line for line in text.splitlines() if 'clear ' in line)
        for hypothesis in (f'hd{atom}', f'hg{atom}', f'hd{literal}'):
            self.assertIn(hypothesis, clear.split())
        self.assertNotIn('intro ', text)
        self.assertNotIn('generalize', text)
        self.assertNotIn('axiom', text)

    def test_active_body_crosses_only_exact_padding_and_fixed_muxes(self):
        byte = (8, 'var', (), 0)
        guard = (1, 'var', (), 1)
        fixed = (8, 'mux', (guard, byte, (8, 'lit', (), 0)), None)
        padded = (8, 'slice', ((64, 'concat', ((56, 'lit', (), 0), fixed), None),), 0)
        pair = dict(left=padded, right=byte,
            variables=((8, 'input', 'byte'), (1, 'input', 'guard')))
        _, nodes, roots = sr._helper_dag(pair)
        guard_index = next(j for j, n in enumerate(nodes) if n[1] == 'var' and n[3] == 1)
        self.assertEqual(sr._helper_dag_active_body(nodes, roots[0], ((guard_index, True),)), roots[1])
        mux_index = next(j for j, n in enumerate(nodes) if n[1] == 'mux')
        self.assertEqual(sr._helper_dag_active_body(nodes, roots[0], ()), mux_index)
        shifted = dict(pair, left=(8, 'slice', (padded[2][0],), 1))
        _, shifted_nodes, shifted_roots = sr._helper_dag(shifted)
        self.assertEqual(sr._helper_dag_active_body(shifted_nodes, shifted_roots[0],
            ((guard_index, True),)), shifted_roots[0])

    def test_generic_plans_are_deterministic_untrusted_proposals(self):
        left = (20, 'var', (), 0)
        right = (20, 'var', (), 1)
        pair = dict(left=left, right=right,
            variables=((20, 'input', 'a'), (20, 'input', 'b')))
        _, nodes, roots = sr._helper_dag(pair)
        one = sr._helper_dag_plan(nodes, roots, (), count=32)
        two = sr._helper_dag_plan(nodes, roots, (), count=32)
        self.assertEqual(one, two)
        self.assertIn('untrusted', one['scope'])
        self.assertEqual(one['global_aliases'], [])
        self.assertEqual(one['data_cuts'], [])

    def test_original_statements_preserved_and_guards_are_arbitrary(self):
        wide = (1, 'eq', ((64, 'var', (), 0), (64, 'lit', (), 1)), None)
        cursor = (1, 'eq', ((9, 'var', (), 1), (9, 'lit', (), 290)), None)
        left = (1, 'and', (wide, cursor), None)
        right = (1, 'and', (cursor, wide), None)
        pair = self.pair(left, right)
        rb = sr.backend('core')
        retained = pr.helper_source(rb, [pair])
        generated = sr.helper_source(rb, [pair])
        statements = r'theorem local_\d+ .*? := by'
        self.assertEqual(re.findall(statements, generated, re.S),
                         re.findall(statements, retained, re.S))
        self.assertEqual(sr._helper_guards(pair), [wide])
        self.assertIn('generalize ' + rb.render_tree(wide) + ' = xstream_guard0', generated)
        self.assertNotIn('generalize ' + rb.render_tree(cursor), generated)
        self.assertNotRegex(generated, r'generalize\s+\w+\s*:')
        for forbidden in ('sorry', 'native_decide', 'bv_decide'):
            self.assertNotIn(forbidden, generated)
        self.assertIn('decide +kernel', generated)
        self.assertEqual(retained, pr.helper_source(rb, [pair]))

    def test_different_predicates_remain_distinct_and_one_sided_claim_is_preserved(self):
        one = (1, 'eq', ((64, 'var', (), 0), (64, 'lit', (), 1)), None)
        two = (1, 'eq', ((64, 'var', (), 0), (64, 'lit', (), 2)), None)
        for right in (two, (1, 'lit', (), 1)):
            pair = self.pair(one, right)
            self.assertEqual(len(sr._helper_guards(pair)), 2 if right == two else 1)
            source = sr.helper_source(sr.backend('core'), [pair])
            self.assertEqual(source.count('generalize '), 2 if right == two else 1)
            self.assertIn('    ' + sr.backend('core').render_tree(one) + ' = ' +
                          sr.backend('core').render_tree(right) + ' := by', source)

    def test_repeated_guard_generalized_once_with_stable_order(self):
        guard = (1, 'eq', ((64, 'var', (), 0), (64, 'lit', (), 1)), None)
        repeated = (1, 'and', (guard, guard), None)
        pair = self.pair(repeated, guard)
        generated = sr.helper_source(sr.backend('core'), [pair])
        self.assertEqual(generated.count('generalize '), 1)
        # JSON artifact trees and the importer's tuple trees suggest the same
        # proof atoms; neither form changes the proposition being checked.
        from_json = json.loads(json.dumps(pair))
        self.assertEqual(generated, sr.helper_source(sr.backend('core'), [from_json]))

    def test_exhaustive_proof_adapters_keep_top_level_declaration_scope(self):
        for kind in ('core', 'chip'):
            source = sr.proof_source(sr.backend(kind), kind)
            names = ('model_next', 'model_output', 'component_eq_reference', 'component_correct')
            self.assertEqual(re.findall(r'^theorem (\w+)', source, re.M), list(names))
            self.assertNotRegex(source, r'\n[ \t]+theorem ')
            self.assertIn('\n\ntheorem model_output ', source)
            self.assertIn('  cases o with\n', source)
            # The added constructor and every original output remain exhaustive.
            self.assertEqual(source.count('exact rtl_next_r_stream_enabled i s'), 1)
            for name in sr.backend(kind).OUTPUTS:
                self.assertIn('rtl_output_' + name + ' i s', source)

    def test_dag_shares_only_identical_typed_syntax_and_stays_json_stable(self):
        a, b = (1, 'var', (), 0), (1, 'var', (), 1)
        guard = (1, 'and', (a, b), None)
        pair = dict(variables=((1, 'input', 'a'), (1, 'input', 'b')),
            left=(1, 'and', (guard, guard), None), right=guard)
        dag = sr._helper_dag(pair)
        self.assertEqual(len(dag[1]), 4)
        self.assertEqual(dag, sr._helper_dag(json.loads(json.dumps(pair))))
        sr._helper_verify_dag(dag, pair)
        source = sr._helper_dag_proposition(sr.backend('chip'), dag)
        self.assertEqual(source.count('let '), 2)
        self.assertIn('let d2 : BitVec 1 := (x0) &&& (x1)', source)
        self.assertIn('let d3 : BitVec 1 := (d2) &&& (d2)', source)
        self.assertTrue(source.endswith('d3 = d2'))

    def test_valid_changed_dag_values_variables_and_operand_order_are_refused(self):
        a, b = (1, 'var', (), 0), (1, 'var', (), 1)
        pair = dict(variables=((1, 'input', 'a'), (1, 'input', 'b')),
            left=(1, 'and', (a, b), None), right=(1, 'lit', (), 0))
        variables, nodes, roots = sr._helper_dag(pair)
        for index, replacement in ((2, (1, 'and', (1, 0), None)),
                (3, (1, 'lit', (), 1))):
            changed = tuple(replacement if k == index else node for k, node in enumerate(nodes))
            with self.subTest(index=index), self.assertRaisesRegex(ValueError, 'expansion changed'):
                sr._helper_verify_dag((variables, changed, roots), pair)
        # This altered variable remains a well-typed, unique DAG node. Rejection
        # must come from matching the original AST, not malformed DAG intake.
        variable_pair = dict(pair, left=(1, 'not', (a,), None), right=a)
        variable_dag = sr._helper_dag(variable_pair)
        changed = ((1, 'var', (), 1), variable_dag[1][1])
        with self.assertRaisesRegex(ValueError, 'expansion changed'):
            sr._helper_verify_dag((variable_dag[0], changed, variable_dag[2]), variable_pair)
        swapped_parameters = tuple(reversed(variables))
        with self.assertRaisesRegex(ValueError, 'parameter table'):
            sr._helper_verify_dag((swapped_parameters, nodes, roots), pair)

    def test_dag_malformed_types_topology_and_original_cycles_are_refused(self):
        a = (1, 'var', (), 0)
        pair = dict(variables=((1, 'input', 'a'),), left=(1, 'not', (a,), None), right=a)
        variables, nodes, roots = sr._helper_dag(pair)
        for children in ((1,), (2,), (-1,), (True,)):
            changed = (nodes[0], (1, 'not', children, None))
            with self.subTest(children=children), self.assertRaises(ValueError):
                sr._helper_verify_dag((variables, changed, roots), pair)
        with self.assertRaisesRegex(ValueError, 'variables'):
            sr._helper_verify_dag((((True, 'input', 'a'),), nodes, roots), pair)
        with self.assertRaisesRegex(ValueError, 'AST'):
            sr._helper_verify_dag((variables, nodes, roots), dict(pair, left=(1, 'not', ([],), None)))
        for bad in ((True, 'lit', (), 0), (1, 'lit', (), True),
                (2, 'var', (), 0), (1, 'var', (), 1), (1, 'custom', (), None),
                (1, 'and', (a,), None), (1, 'not', (a,), 0),
                (1, 'mux', ((2, 'lit', (), 1), a, a), None),
                (2, 'eq', (a, a), None), (1, 'slice', (a,), -1)):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                sr._helper_dag(dict(pair, left=bad))
        cycle = [1, 'not', [], None]
        cycle[2].append(cycle)
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            sr._helper_dag(dict(pair, left=cycle))

    def test_data_mux_cut_hints_keep_branch_order_leaves_and_selector_obligations(self):
        var = lambda width, index: (width, 'var', (), index)
        leaves = [var(8, index + 2) for index in range(32)]
        def tree(guard, values):
            if len(values) == 1:
                return values[0]
            half = len(values) // 2
            return (8, 'mux', (guard, tree(guard, values[:half]), tree(guard, values[half:])), None)
        variables = ((1, 'input', 'a'), (1, 'input', 'b')) + tuple(
            (8, 'reg', f'word{index}') for index in range(32))
        left, right = tree(var(1, 0), leaves), tree(var(1, 1), leaves)
        dag = sr._helper_dag(dict(variables=variables, left=left, right=right))
        cuts = sr._helper_mux_cuts(dag)
        self.assertEqual(len(cuts), 1)
        self.assertEqual(cuts[0]['roots'], dag[2])
        self.assertEqual(len(cuts[0]['mux_pairs']), 31)
        self.assertEqual(len(cuts[0]['selectors']), 1)
        a, b = cuts[0]['selectors'][0]
        self.assertEqual((dag[1][a][3], dag[1][b][3]), (0, 1))
        # A valid but reversed data tree cannot be accepted as a shared shape.
        changed = sr._helper_dag(dict(variables=variables,
            left=left, right=tree(var(1, 1), list(reversed(leaves)))))
        self.assertEqual(sr._helper_mux_cuts(changed), [])


class StreamSmallHelperSelection(unittest.TestCase):
    def field_dag(self, *, other_word=False, mask=986880, reverse_fields=False):
        word = (20, 'var', (), 0)
        rhs_word = (20, 'var', (), 1 if other_word else 0)
        masked = (20, 'and', (word, (20, 'lit', (), mask)), None)
        fields = [(4, 'slice', (rhs_word,), offset) for offset in (16, 8)]
        if reverse_fields:
            fields.reverse()
        packed = (8, 'concat', tuple(fields), None)
        pair = dict(left=(1, 'eq', (masked, (20, 'lit', (), 0)), None),
            right=(1, 'eq', ((8, 'lit', (), 0), packed), None),
            variables=((20, 'input', 'word'), (20, 'input', 'other')))
        return sr._helper_dag(pair)

    def problem_dag(self, *, word_width=64, compound=False, competing=False,
                    other_word=False, second_literal=1, output_width=1, size=1000):
        variables = [(word_width, 'input', 'word')]
        nodes = [(word_width, 'var', (), 0), (word_width, 'lit', (), 0)]
        operand = 0
        if compound:
            nodes.append((word_width, 'and', (0, 1), None))
            operand = 2
        nodes.append((1, 'eq', (operand, 1), None))
        base = len(nodes) - 1
        base_size = 5 if compound else 3
        if competing:
            other = 0
            if other_word:
                other = len(nodes)
                nodes.append((word_width, 'var', (), 1))
                variables.append((word_width, 'input', 'other'))
            literal = len(nodes)
            nodes.append((word_width, 'lit', (), second_literal))
            flag = len(nodes)
            nodes.append((1, 'eq', (other, literal), None))
            nodes.append((1, 'and', (base, flag), None))
            base = len(nodes) - 1
            base_size += 4
        right = base
        right_size = base_size
        if output_width != 1:
            data = len(nodes)
            nodes.append((output_width, 'var', (), len(variables)))
            variables.append((output_width, 'input', 'data'))
            nodes.append((output_width, 'mux', (base, data, data), None))
            base = len(nodes) - 1
            base_size += 3
            right, right_size = data, 1
        left, left_size = base, base_size
        # Repeated children count twice in the imported tree, though the DAG
        # retains one node. Six levels leave room for an exact size boundary.
        for _ in range(6):
            nodes.append((output_width, 'and', (left, left), None))
            left, left_size = len(nodes) - 1, 1 + 2 * left_size
        for _ in range(size - left_size - right_size):
            nodes.append((output_width, 'not', (left,), None))
            left = len(nodes) - 1
        return tuple(variables), nodes, (left, right)

    def test_field_mask_matches_exact_slice_support_and_ignores_packing_order(self):
        for reverse in (False, True):
            with self.subTest(reverse_fields=reverse):
                _, nodes, roots = self.field_dag(reverse_fields=reverse)
                proposals = sr._helper_dag_field_zero_aliases(nodes, roots)
                self.assertEqual([tuple(item['roots']) for item in proposals], [roots])
                self.assertEqual(len(proposals[0]['support']), 8)
                self.assertEqual(sr._helper_dag_field_zero_aliases(
                    json.loads(json.dumps(nodes)), roots), proposals)

    def test_field_alias_rejects_different_word_and_extra_mask_bit(self):
        for arguments in ({'other_word': True}, {'mask': 986881}):
            with self.subTest(arguments=arguments):
                _, nodes, roots = self.field_dag(**arguments)
                self.assertEqual(sr._helper_dag_field_zero_aliases(nodes, roots), [])

    def test_small_boundaries_preserve_narrow_flag_correlations_and_order(self):
        nodes = [(3, 'var', (), 0), (3, 'lit', (), 0), (3, 'lit', (), 1),
            (1, 'eq', (0, 1), None), (1, 'eq', (0, 2), None),
            (64, 'var', (), 1), (64, 'lit', (), 0), (64, 'lit', (), 1),
            (1, 'eq', (5, 6), None), (1, 'eq', (5, 7), None),
            (1, 'not', (3,), None), (1, 'not', (4,), None)]
        pairs = [(8, 9), (3, 4), (10, 11), (5, 6)]
        self.assertEqual(sr._helper_dag_small_boundaries(nodes, pairs),
                         [(8, 9), (10, 11), (5, 6)])
        # A wide/narrow alias also retains the narrow endpoint definition.
        self.assertEqual(sr._helper_dag_small_boundaries(nodes, [(3, 8)]), [])

    def test_expanded_size_counts_shared_children_at_each_tree_occurrence(self):
        dag = (((8, 'input', 'data'), (1, 'input', 'guard')),
            [(8, 'var', (), 0), (1, 'var', (), 1),
             (8, 'mux', (1, 0, 0), None), (8, 'mux', (1, 2, 2), None)], (3, 0))
        self.assertEqual(sr._helper_dag_expanded_size(dag), 11)
        for size in (999, 1000):
            self.assertEqual(sr._helper_dag_expanded_size(
                self.problem_dag(compound=True, size=size)), size)

    def test_small_problem_requires_size_width_and_compound_wide_comparison(self):
        cases = [({'compound': True, 'size': 999}, False),
            ({'compound': True, 'size': 1000}, True),
            ({'compound': True, 'word_width': 15}, False),
            ({'compound': True, 'word_width': 16}, True),
            ({'compound': True, 'output_width': 8}, True),
            ({'compound': True, 'output_width': 9}, False),
            ({}, False)]
        for arguments, expected in cases:
            with self.subTest(arguments=arguments):
                self.assertEqual(sr._helper_dag_small_problem(
                    self.problem_dag(**arguments)), expected)

    def test_competing_scalar_predicates_require_one_bit_root_and_same_word(self):
        cases = [({'competing': True}, True),
            ({'competing': True, 'second_literal': 0}, False),
            ({'competing': True, 'other_word': True}, False),
            ({'competing': True, 'word_width': 15}, False),
            ({'competing': True, 'output_width': 8}, False),
            ({'competing': True, 'size': 999}, False)]
        for arguments, expected in cases:
            with self.subTest(arguments=arguments):
                self.assertEqual(sr._helper_dag_small_problem(
                    self.problem_dag(**arguments)), expected)


class StreamReadbackCustody(unittest.TestCase):
    """Mock CAD/proof execution; use real typed RTL intake and receipt closeout."""
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name in ('Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                     'tools/hardware-toolchain.json', 'test/ProofAudit.lean'):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Fixture ' + name)
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
        self.tool = self.root / 'build/tools/oss-cad-suite'
        self.circt = self.root / 'build/tools/firtool-1.159.0/bin/circt-opt'
        for path in (self.circt, self.tool / 'bin/yosys', self.tool / 'bin/z3',
                     self.tool / 'libexec/yosys', self.tool / 'libexec/z3'):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Fixture tool ' + path.name)
        self.on_event = lambda label: None
        self.sequence = 0

    def run_cli(self):
        self.sequence += 1
        tag = 'fixture-' + str(self.sequence)
        self.out = self.root / 'build/validation' / tag
        test, original_backend, original_json = self, sr.backend, sr.read_json

        class Commands:
            def __init__(self, root, out, records=None, **kwargs):
                self.out = Path(out)
                self.records = [] if records is None else records
                self.scope = kwargs.get('scope', '')

            def __call__(self, command, label, **kwargs):
                self.records.append(dict(label=self.scope + label, stubbed=True))
                if label == 'emit':
                    destination = Path(command[-1])
                    destination.mkdir()
                    interface = {}
                    for kind in ('core', 'chip'):
                        rb = original_backend(kind)
                        (destination / (kind + '.mlir')).write_text('Mock emitted ' + kind)
                        interface[kind] = {
                            group: [dict(name=n, width=w, reference=n) for n, (w, _) in table.items()]
                            for group, table in [('inputs', rb.INPUTS), ('registers', rb.REGISTERS),
                                                 ('outputs', rb.OUTPUTS)]}
                    (destination / 'assembly.json').write_text(json.dumps(interface))
                elif label == 'hint-labels':
                    destination = Path(command[-1])
                    destination.mkdir()
                    for kind in ('core', 'chip'):
                        (destination / (kind + '-cuts.json')).write_text('[]')
                elif label == 'import':
                    script = Path(command[-1]).read_text()
                    kind = 'chip' if '-top pinwheel_paired_controller' in script else 'core'
                    rb = original_backend(kind)
                    imported = Path(runner.re.search(r'write_json "([^"\n]+)"', script)[1])
                    imported.write_text(json.dumps({'modules': {rb.TOP: fixture(rb)}}))
                test.on_event('command:' + self.scope + label)
                return 'Lean (version 4.33.1, fixture, Release)' if label == 'lean-version' else ''

        class Closure:
            def __init__(self, *args):
                self.files = [test.circt]
            def closeout(self):
                test.on_event('closeout')
            def identity(self):
                return dict(mocked=True)

        def fresh_rtl(run, emitted, retain):
            for kind in ('core', 'chip'):
                text = ("r_cursor <= 9'h1;\nr_parameter_b1_w31 <= 20'h1;\n"
                        "assign mem_write = 1'b1;\nr_pin_second_init <= r_pin_first_init;\n"
                        "r_result_valid <= 1'b1;\nassign uo_out = 8'h1;\n"
                        "r_stream_enabled <= 1'b1;\n")
                (emitted / (kind + '.sv')).write_text(text)
            return {name: dict(path=str(path.relative_to(test.root)), sha256=sha(path))
                    for name in ('core.mlir', 'chip.mlir', 'core.sv', 'chip.sv', 'assembly.json')
                    for path in [retain(emitted / name)]}

        def backend(kind):
            rb = original_backend(kind)
            read = rb.read_rtl
            def interpreted(path):
                graph = read(path)
                test.on_event('interpreted:' + str(Path(path).relative_to(test.out)))
                return graph
            rb.read_rtl = interpreted
            rb.read_hints = lambda path: None
            rb.add_storage_views = lambda graph, source: None
            return rb

        def read_json(path):
            value = original_json(path)
            test.on_event('json:' + str(Path(path).relative_to(test.out)))
            return value

        def compile_lean(run, directory, name, paths=(), reject=None):
            # A rejected proof produces no reusable compiled artifact. Successful
            # outputs must exist so the real runner can bind later LEAN_PATH uses.
            if reject is None:
                (directory / (name + '.olean')).write_text('Mock compiled ' + name)
            test.on_event('compiled:' + str((directory / (name + '.lean')).relative_to(test.out)))
            return 'Pinwheel audit: 10 declarations, 3 theorems; standard axioms only.' if name == 'Audit' else ''

        with patch.object(runner, 'ROOT', self.root), patch.object(runner, 'CIRCT', self.circt), \
                patch.object(runner, 'YOSYS', self.tool / 'bin/yosys'), \
                patch.object(runner, 'SOLVER', self.tool / 'bin/z3'), \
                patch.object(runner, 'ProtocolToolClosure', Closure), \
                patch.object(runner.commands, 'ScopedCommands', Commands), \
                patch.object(runner.commands, 'fresh_rtl', side_effect=fresh_rtl), \
                patch.object(runner.commands, 'compile_lean', side_effect=compile_lean), \
                patch.object(runner.sr, 'backend', side_effect=backend), \
                patch.object(runner.sr, 'read_json', side_effect=read_json), \
                patch.object(runner.sr, 'check_cuts', return_value=None), \
                patch.object(runner.sr, 'partitions', return_value=[]), \
                patch.object(runner, 'generate', return_value={'Graphs': '-- mock graphs\n',
                    'Proof': 'import Graphs\n', 'Audit': 'import Proof\n#audit_pinwheel\n'}), \
                patch.object(sys, 'argv', ['check-stream-readback.py', '--tag', tag]), \
                contextlib.redirect_stdout(io.StringIO()):
            runner.main()
        return json.loads((self.out / 'report.json').read_text())

    def assert_failed_receipt(self):
        report = json.loads((self.out / 'report.json').read_text())
        self.assertEqual(report['status'], 'failed')
        self.assertNotIn('inputs_unchanged', report)

    def test_receipt_freezes_main_and_mutation_imports_and_proof_sources(self):
        report = self.run_cli()
        self.assertEqual(report['status'], 'passed')
        self.assertTrue(report['inputs_unchanged'])
        frozen = report['consumed_generated_sha256']
        for kind in ('core', 'chip'):
            paths = [kind + '/' + name for name in ('import.json', 'import.ys', 'Graphs.lean', 'Proof.lean',
                     'Graphs.olean', 'Proof.olean', 'Audit.olean')]
            paths += [kind + '/mutations/' + mutation + '/' + name
                      for mutation in report['modules'][kind]['mutation_controls']
                      for name in ('candidate.sv', 'import.json', 'import.ys', 'MutantGraphs.lean',
                                   'MutantModel.lean', 'Reject.lean', 'MutantGraphs.olean', 'MutantModel.olean')]
            paths.append(kind + '/mutations/unchanged/Reject.olean')
            for relative in paths:
                path = self.out / relative
                self.assertEqual(frozen[str(path.relative_to(self.root))], sha(path))
            rejected = [self.out / kind / 'RejectAxiom.olean'] + [
                self.out / kind / 'mutations' / mutation / 'Reject.olean'
                for mutation in report['modules'][kind]['mutation_controls'] if mutation != 'unchanged']
            for path in rejected:
                self.assertFalse(path.exists())
                self.assertNotIn(str(path.relative_to(self.root)), frozen)

    def test_json_change_immediately_after_interpretation_refuses_receipt(self):
        for relative in ('core/import.json', 'core/mutations/unchanged/import.json',
                         'core/mutations/parameter-bank/import.json'):
            def mutate(label, relative=relative):
                if label == 'interpreted:' + relative:
                    (self.out / relative).write_text('Changed after graph construction')
            self.on_event = mutate
            with self.subTest(path=relative), self.assertRaisesRegex(ValueError, 'Consumed generated input changed'):
                self.run_cli()
            self.assert_failed_receipt()

    def test_consumed_artifact_change_at_closeout_refuses_receipt(self):
        for relative in ('core/import.json', 'chip/import.json', 'core/import.ys',
                         'core/mutations/unchanged/candidate.sv', 'chip/mutations/stream-enabled/import.json',
                         'core/mutations/parameter-bank/import.ys', 'core/Graphs.lean', 'chip/Proof.lean',
                         'core/mutations/unchanged/MutantModel.lean', 'core/Graphs.olean',
                         'chip/Proof.olean', 'core/mutations/unchanged/MutantModel.olean'):
            def mutate(label, relative=relative):
                if label == 'closeout':
                    (self.out / relative).write_text('Changed consumed bytes')
            self.on_event = mutate
            with self.subTest(path=relative), self.assertRaisesRegex(ValueError, 'An input changed during validation'):
                self.run_cli()
            self.assert_failed_receipt()

    def test_compiled_dependency_change_before_import_refuses_receipt(self):
        for relative, trigger in (
                ('core/Proof.olean', 'command:core.mutations.unchanged.import'),
                ('chip/Graphs.olean', 'command:chip.mutations.unchanged.import')):
            def mutate(label, relative=relative, trigger=trigger):
                if label == trigger:
                    (self.out / relative).write_text('Changed compiled dependency before import')
            self.on_event = mutate
            with self.subTest(path=relative), self.assertRaisesRegex(ValueError, 'Consumed generated input changed'):
                self.run_cli()
            self.assert_failed_receipt()

    def test_compiled_dependency_change_during_import_refuses_receipt(self):
        for relative, trigger in (
                ('core/Graphs.olean', 'compiled:core/Proof.lean'),
                ('core/mutations/unchanged/MutantGraphs.olean',
                 'compiled:core/mutations/unchanged/MutantModel.lean')):
            def mutate(label, relative=relative, trigger=trigger):
                if label == trigger:
                    (self.out / relative).write_text('Changed compiled dependency during import')
            self.on_event = mutate
            with self.subTest(path=relative), self.assertRaisesRegex(ValueError, 'Consumed generated input changed'):
                self.run_cli()
            self.assert_failed_receipt()

    def test_cuts_change_during_read_refuses_receipt(self):
        def mutate(label):
            if label == 'json:hints/core-cuts.json':
                (self.out / 'hints/core-cuts.json').write_text('["Changed after read"]')
        self.on_event = mutate
        with self.assertRaisesRegex(ValueError, 'Consumed generated input changed'):
            self.run_cli()
        self.assert_failed_receipt()

    def test_import_script_change_during_command_refuses_receipt(self):
        def mutate(label):
            if label == 'command:core.import':
                (self.out / 'core/import.ys').write_text('Changed after importer consumed it')
        self.on_event = mutate
        with self.assertRaisesRegex(ValueError, 'Consumed generated input changed'):
            self.run_cli()
        self.assert_failed_receipt()


if __name__ == '__main__':
    unittest.main()
