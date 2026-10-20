"""Refusal and binding checks for the Ready artifact proof factory.

The generated Lean modules must still compile and undergo the worker's full
axiom audit against actual component artifacts; these tests do not substitute
for that qualification.
"""
import importlib.util
from pathlib import Path
import re
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'scripts' / 'streaming_ready_composition.py'
spec = importlib.util.spec_from_file_location('ready_composition', SCRIPT)
factory = importlib.util.module_from_spec(spec)
spec.loader.exec_module(factory)

REQUIRED = {
    'components_correct', 'physical_step_correct', 'physical_observe_correct',
    'physical_run_correct', 'source_runtime_step_correct',
    'source_runtime_run_correct', 'source_runtime_observe_correct',
    'initialized_upload_correct', 'initialized_runtime_correct',
    'physical_warm_reset_correct', 'concrete_i2c_initialized',
    'concrete_i2c_runtime', 'concrete_i2c_custody', 'concrete_i2c_progress',
}


class ReadyCompositionTest(unittest.TestCase):
    def test_refuses_unqualified_depth_and_python_numeric_aliases(self):
        for value in (None, True, False, 0, 3, -1, 1.0, 2.0, '1', [], {}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                factory.generate(value)

    def test_each_depth_binds_new_components_and_all_required_claims(self):
        for address, depth in ((1, 2), (2, 4)):
            with self.subTest(depth=depth):
                modules = factory.generate(address)
                self.assertEqual(set(modules), {f'StreamingReadySessionD{depth}'})
                text = modules[f'StreamingReadySessionD{depth}']
                self.assertTrue(REQUIRED <= set(re.findall(r'^theorem (\w+)', text, re.M)))
                self.assertIn(f'import ReadyCoreD{depth}Proof\n', text)
                self.assertIn('import ReadyQuadFrontendProof\n', text)
                self.assertIn(f'import StreamingReadyWrappersD{depth}\n', text)
                self.assertIn('open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady\n', text)
                self.assertIn(f'(Package.Components.typed {address})', text)
                self.assertNotIn('open Pinwheel.Hardware.Streaming\n', text)
                self.assertNotIn('(.typed ', text)
                self.assertNotIn('Pinwheel.Hardware.Streaming.Package.Correct', text)
                self.assertNotIn('spiImage', text)
                self.assertNotIn('jtagImage', text)
                self.assertNotRegex(text, r'@[AD]@|\bsorry\b|\badmit\b|\bnative_decide\b')

    def test_concrete_progress_uses_reached_feedback_and_separate_fairness(self):
        text = factory.generate(1)['StreamingReadySessionD2']
        self.assertIn('SessionService.Runtime image.program false sourceStart sampled', text)
        self.assertIn('SessionService.Fair image.program false sourceStart sampled', text)
        self.assertIn('SessionService.Runtime.runtimeTrace', text)
        self.assertIn('SessionService.admitted_start', text)
        self.assertIn('final.core.phase.retained = true', text)
        self.assertIn('BootPins.coldPin :: BootPins.i2c', text)
        # The concrete image is derived by the actual physical boot theorem.
        self.assertIn('exact BootCorrespondence.i2c_initialized startup', text)


if __name__ == '__main__':
    unittest.main()
