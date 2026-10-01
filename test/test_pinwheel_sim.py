"""Simulator diagnostics and replies may arrive in one pipe read."""
from pathlib import Path
import select
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from pinwheel_host import Pins
from pinwheel_sim import Simulation


class SimulatorTransport(unittest.TestCase):
    def test_diagnostic_and_reply_in_one_write_do_not_hide_buffered_reply(self):
        with tempfile.TemporaryDirectory() as directory:
            peer = Path(directory) / 'peer.py'
            peer.write_text('import sys\nfor line in sys.stdin:\n'
                            ' sys.stdout.write("vendor diagnostic\\nPINWHEEL 2 20 28 23 255\\n")\n'
                            ' sys.stdout.flush()\n')
            poll = select.select
            # Fail a buffered-read regression promptly, without a 30-second wait.
            with patch('pinwheel_sim.select.select',
                       side_effect=lambda r, w, x, timeout: poll(r, w, x, min(timeout, 1))), \
                    Simulation(Path(sys.executable), peer) as simulation:
                self.assertEqual(simulation.advance(4, 2), Pins(2, 5, 7))
                self.assertEqual(simulation.advance(4, 3), Pins(2, 5, 7))
                self.assertEqual(simulation.cycle, 5)
                self.assertIn('vendor diagnostic', simulation.log)


if __name__ == '__main__':
    unittest.main()
