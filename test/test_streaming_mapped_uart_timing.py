"""Additional first-terminal APIs must observe mapped public pads directly."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_uart_timing import THEOREMS, extra_qnames, generate, required_qnames


class MappedUARTTimingTests(unittest.TestCase):
    def test_both_depths_have_three_separate_extra_names_without_replacing44(self):
        self.assertEqual(required_qnames(), extra_qnames(1) + extra_qnames(2))
        self.assertEqual(len(set(required_qnames())), 6)
        for a, depth in ((1, 2), (2, 4)):
            modules = generate(a)
            self.assertEqual(set(modules), {'StreamingMappedUARTTimingD' + str(depth)})
            text = next(iter(modules.values()))
            self.assertIn('import StreamingMappedSessionD' + str(depth), text)
            self.assertIn('import Pinwheel.Hardware.StreamingMapped.UARTTiming', text)
            for theorem in THEOREMS:
                self.assertEqual(text.count('theorem ' + theorem + ' '), 1)

    def test_pad_transport_and_all_observation_values_are_in_the_conclusion(self):
        text = next(iter(generate(1).values()))
        self.assertIn('physicalObserve (physicalRun startup', text)
        self.assertIn('UARTTiming.padPin observation) .uo).getLsbD 5', text)
        self.assertIn('rw [uartBusyPad,physical_observe_correct,uart_actual_frame]', text)
        self.assertIn('∀ observation, uartBusyPad rate startup raw edges observation = false', text)
        self.assertIn('∀ earlier, earlier < edges → ∀ observation,', text)
        for theorem in THEOREMS:
            signature = text.split('theorem ' + theorem, 1)[1].split(':= by', 1)[0]
            self.assertNotRegex(signature, r'\((first|armed|result|related|agreement)\s*:')
            self.assertIn('(startup : Package.State 1)', signature)
        for target in ('good_first', 'bad_stop_first', 'false_start_first'):
            self.assertIn('UARTTiming.' + target, text)

    def test_unsupported_depth_and_bool_are_not_silent_profile_choices(self):
        for value in (True, False, 0, 3, 4, '1', None):
            for function in (generate, extra_qnames):
                with self.subTest(value=value, function=function.__name__), self.assertRaises(ValueError):
                    function(value)


if __name__ == '__main__': unittest.main()
