from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
from streaming_tt_apply_fanout import checked_tcl


class TclStatusGuard(unittest.TestCase):
    def design(self, status, message):
        class Design:
            def evalTclString(self, command):
                return status if command.startswith('catch {') else message
        return Design()

    def test_requires_actual_exact_zero_status(self):
        journal = []
        self.assertEqual(checked_tcl(self.design('0', 'done'), 'native_command', journal), 'done')
        self.assertEqual(journal, [dict(command='native_command', tcl_catch_status='0', tcl_result='done')])

    def test_native_error_is_rejected_even_when_python_call_returns(self):
        journal = []
        with self.assertRaisesRegex(ValueError, 'Native Tcl command failed'):
            checked_tcl(self.design('1', 'DPL-0386'), 'check_placement -verbose', journal)
        self.assertEqual(journal[0]['tcl_catch_status'], '1')

    def test_none_boolean_or_numeric_status_is_never_success(self):
        for status in (None, False, True, 0, 1, '00', ''):
            with self.subTest(status=status), self.assertRaisesRegex(ValueError, 'unrecognized status'):
                checked_tcl(self.design(status, ''), 'native_command', [])


if __name__ == '__main__': unittest.main()
