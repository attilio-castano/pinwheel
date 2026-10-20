"""Restricted Liberty grammar and exact Boolean/sequential refusal controls."""
import itertools
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_liberty import (FF, PREFIX, SUPPORTED, eval_boolean, load_library,
    parse_boolean, parse_library)

INV = '''cell(sg13cmos5l_inv_1){
pin(A){direction:"input";}pin(Y){direction:"output";function:"!(A)";}}'''
AND = '''cell(sg13cmos5l_and2_1){
pin(A){direction:"input";}pin(B){direction:"input";}
pin(X){direction:"output";function:"(A*B)";}}'''
DFF = '''cell(sg13cmos5l_dfrbpq_1){
pin(Q){direction:"output";function:"IQ";}
pin(CLK){clock:true;direction:"input";}pin(D){direction:"input";}
pin(RESET_B){direction:"input";}
ff(IQ,IQN){clear:"!RESET_B";clocked_on:"CLK";next_state:"D";}}'''
LIBRARY = 'library(test){' + INV + AND + DFF + '}'
TYPES = {PREFIX + 'inv_1', PREFIX + 'and2_1', FF}


class LibertyTests(unittest.TestCase):
    def test_qualified_cell_scope_is_exactly_26_combinational_and_one_ff(self):
        self.assertEqual(len(SUPPORTED), 27)
        library = parse_library(LIBRARY, TYPES)
        self.assertFalse(library.pinned)
        self.assertEqual(sum(cell.sequential for cell in library.cells.values()), 1)
        ff = library.cells[FF]
        self.assertEqual(ff.state_names, ('IQ', 'IQN'))
        self.assertEqual(ff.directions, dict(Q='output', CLK='input', D='input', RESET_B='input'))

    def test_not_and_xor_or_precedence_and_constants(self):
        expression = parse_boolean('!A + B*C ^ 0', {'A', 'B', 'C'})
        for a, b, c in itertools.product((False, True), repeat=3):
            self.assertEqual(eval_boolean(expression, dict(A=a, B=b, C=c)), not a or b and c)

    def test_actual_mux4_function_uses_pin_names_and_low_select_bit(self):
        names = {'A0', 'A1', 'A2', 'A3', 'S0', 'S1'}
        expression = parse_boolean('(A0*(!S0*!S1))+(A1*(S0*!S1))+(A2*(!S0*S1))+(A3*(S0*S1))', names)
        for bits in itertools.product((False, True), repeat=6):
            values = dict(zip(('A0', 'A1', 'A2', 'A3', 'S0', 'S1'), bits))
            index = int(values['S0']) + 2 * int(values['S1'])
            self.assertEqual(eval_boolean(expression, values), values['A' + str(index)])

    def test_unknown_implicit_postfix_bus_python_and_trailing_syntax_refuse(self):
        for text in ('', 'A B', "A'", '~A', 'A& B', 'A[0]', 'A?B:0', 'A +', '(A', 'A)',
                'unknown', '__import__(A)', 'A 1', '2', 'A/1'):
            with self.subTest(text=text), self.assertRaises(ValueError): parse_boolean(text, {'A', 'B'})
        with self.assertRaises(ValueError): eval_boolean(parse_boolean('A', {'A'}), {'A': 1})

    def test_pin_unknown_duplicate_wrong_direction_and_unsupported_groups_refuse(self):
        changes = [LIBRARY.replace('function:"!(A)"', 'function:"IQ"'),
            LIBRARY.replace('pin(A){direction:"input";}', 'pin(A){direction:"inout";}'),
            LIBRARY.replace('function:"!(A)"', 'function:"!(A)";three_state:"A"'),
            LIBRARY.replace(INV, INV + INV),
            LIBRARY.replace('pin(A){direction:"input";}', 'pin(A){direction:"input";}pin(A){direction:"input";}'),
            LIBRARY.replace('pin(A){direction:"input";}', 'pin(A){direction:"input";ff(X,Y){next_state:"A";}}')]
        for changed in changes:
            with self.subTest(changed=changed), self.assertRaises(ValueError): parse_library(changed, TYPES)

    def test_negative_clock_wrong_next_state_preset_latch_and_qn_refuse(self):
        for before, after in [('clocked_on:"CLK"', 'clocked_on:"!CLK"'),
                ('next_state:"D"', 'next_state:"!D"'), ('function:"IQ"', 'function:"IQN"'),
                ('clear:"!RESET_B"', 'clear:"RESET_B"'),
                ('next_state:"D";', 'next_state:"D";preset:"D";'),
                ('ff(IQ,IQN)', 'latch(IQ,IQN)'), ('clock:true', 'clock:false')]:
            with self.subTest(after=after), self.assertRaises(ValueError):
                parse_library(LIBRARY.replace(before, after), TYPES)

    def test_comments_and_nonsemantic_tables_do_not_change_boolean_function(self):
        changed = LIBRARY.replace('library(test){', 'library(test){/* {} pin(fake) */\n// ignored\n')
        changed = changed.replace('function:"!(A)";', 'function:"!(A)";timing(){values("0.1,0.2");}')
        self.assertEqual(parse_library(changed, TYPES).cells[PREFIX + 'inv_1'].function,
            parse_library(LIBRARY, TYPES).cells[PREFIX + 'inv_1'].function)

    def test_unpinned_file_refuses_before_it_is_accepted_as_library(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'cells.lib'
            path.write_text(LIBRARY)
            with self.assertRaisesRegex(ValueError, 'unpinned'): load_library(path, TYPES)
        with self.assertRaises(ValueError): parse_library(LIBRARY, {PREFIX + 'unrecognized_1'})
        with self.assertRaises(ValueError): parse_library(LIBRARY + ' trailing', TYPES)


if __name__ == '__main__': unittest.main()
