"""Checker fixtures and host observations; these tests do not execute RTL."""
from dataclasses import replace
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import host_demo
from pinwheel_host import Pins, Program, Result


def populate_peer(peer):
    if isinstance(peer, host_demo.UARTTransmit):
        peer.trace = [int(bit) for bit in '0110010101' for _ in range(4)]
    elif isinstance(peer, host_demo.SPI):
        peer.bits = [int(bit) for bit in '10100110']
        peer.rises = list(range(0, 64, 8))
    elif isinstance(peer, host_demo.I2C):
        peer.stopped, peer.starts = True, 2
        peer.clocks = [int(bit) for bit in '101001100101001100101001110100101101']
    elif peer.trigger and peer.value == 3:
        peer.pulse = list(range(8))


class PeerChecks(unittest.TestCase):
    def test_complete_traces_pass_and_empty_traces_fail(self):
        for cls, message in [(host_demo.UARTTransmit, 'UART pin waveform'),
                             (host_demo.SPI, 'SPI outgoing byte'),
                             (host_demo.I2C, 'I2C transaction framing')]:
            with self.subTest(peer=cls.__name__):
                peer = cls()
                with self.assertRaisesRegex(RuntimeError, message):
                    peer.check()
                populate_peer(peer)
                self.assertTrue(peer.check())

    def test_corrupted_waveforms_and_clock_spacing_fail(self):
        uart = host_demo.UARTTransmit(); populate_peer(uart); uart.trace[4] ^= 1
        spi = host_demo.SPI(); populate_peer(spi); spi.bits[0] ^= 1
        spacing = host_demo.SPI(); populate_peer(spacing); spacing.rises[-1] += 1
        i2c = host_demo.I2C(); populate_peer(i2c); i2c.clocks[-1] ^= 1
        for peer, message in [(uart, 'UART pin waveform'), (spi, 'SPI outgoing byte'),
                              (spacing, 'SPI clock spacing'), (i2c, 'I2C wire bytes/ACKs')]:
            with self.subTest(message=message), self.assertRaisesRegex(RuntimeError, message):
                peer.check()

    def test_invalid_pin_drives_fail(self):
        uart = host_demo.UARTTransmit(); uart.started = True
        for peer, pins, message in [(uart, Pins(0, 0, 0), 'UART released'),
                                    (host_demo.SPI(), Pins(0, 0, 4), 'SPI must drive'),
                                    (host_demo.I2C(), Pins(0, 1, 2), 'Unsafe I2C drive')]:
            with self.subTest(message=message), self.assertRaisesRegex(RuntimeError, message):
                peer(0, pins, 0)

    def test_i2c_framing_and_phase_intervals_fail(self):
        start = host_demo.I2C()
        repeated = host_demo.I2C(); repeated.starts = 1
        stop = host_demo.I2C(); stop.previous = [1, 0]
        low = host_demo.I2C(); low.previous = [0, 0]; low.starts = 1; low.fall_at = 3
        high = host_demo.I2C(); high.pending = 0; high.rise_at = 3
        for peer, cycle, enabled, message in [
                (start, 1, 2, 'START/STOP high interval'),
                (repeated, 5, 2, 'Unexpected I2C START'),
                (stop, 5, 0, 'STOP without START'),
                (low, 4, 0, 'clock low interval'),
                (high, 4, 1, 'clock high interval')]:
            with self.subTest(message=message), self.assertRaisesRegex(RuntimeError, message):
                peer(cycle, Pins(0, 0, enabled), 0)


class ScriptedHost:
    """Supply known observations to exercise the demo's acceptance boundary."""
    results = [(0, 5), (0x69, 5), (0x69, 5), (0x2a6, 5), (0x53, 5),
               (1, 5), (0, 5), (0, 6), (1, 5)]

    def __init__(self, sim, fault=None):
        self.sim, self.fault = sim, fault
        self.edges = self.frames = 0
        self.index = -1
        self.events = []
        self.reads = 0

    def reset(self):
        pass

    def upload(self, program):
        if program.words[0] == 1 << 63:
            if self.fault == 'malformed-accepted':
                return
            if self.fault == 'wrong-rejection':
                raise RuntimeError('Transport disconnected')
            raise RuntimeError('Chip rejected the staged image')
        self.index += 1
        self.reads = 0
        self.edges += 100

    def start(self):
        populate_peer(self.sim.device)
        if self.fault == 'pulse' and isinstance(self.sim.device, host_demo.Receive):
            self.sim.device.pulse = []

    def read_result(self, *, timeout_cycles, consume=True):
        self.events.append((self.index, 'read'))
        self.reads += 1
        result = Result(*self.results[self.index], False, False)
        if self.index == 0:
            if self.fault == 'samples' or (self.fault == 'retention' and self.reads == 2):
                result = replace(result, samples=1)
            if self.fault == 'outcome':
                result = replace(result, outcome=6)
            if self.fault in ('overrun', 'rejected'):
                result = replace(result, **{self.fault: True})
        if self.index == 8 and self.fault == 'recovery':
            result = replace(result, samples=0)
        return result

    def consume(self):
        self.events.append((self.index, 'consume'))

    def result_status(self):
        self.events.append((self.index, 'status'))
        return 1 if self.fault == 'consumption' else 0

    def page(self, number):
        self.events.append((self.index, 'page'))
        return 0 if self.fault == 'active-image' else 2

    def clear_flags(self):
        self.index = 8


class DemoChecks(unittest.TestCase):
    def demonstrate(self, fault=None):
        sim = SimpleNamespace(device=None)
        host = ScriptedHost(sim, fault)
        images = {name: Program((4,), 0) for name in ('uart', 'spi', 'i2c-read', 'uart-rx')}
        with tempfile.TemporaryDirectory() as directory, patch.object(host_demo, 'Host', return_value=host):
            report = host_demo.demonstrate(sim, images, Path(directory))
        return report, host

    def test_every_case_reads_twice_and_checks_consumption(self):
        report, host = self.demonstrate()
        self.assertEqual(len(report['cases']), 9)
        expected = [(i, action) for i in range(8) for action in ('read', 'read', 'consume', 'status')]
        self.assertEqual(host.events, [*expected, (7, 'page'), (8, 'read')])

    def test_incorrect_observations_cannot_complete_demo(self):
        for fault, message in [
                ('samples', 'expected samples'), ('outcome', 'expected samples'),
                ('overrun', 'unexpected result flags'), ('rejected', 'unexpected result flags'),
                ('retention', 'retained result changed'), ('consumption', 'consumption did not release'),
                ('pulse', 'Triggered pulse width/branch'),
                ('wrong-rejection', 'Unexpected malformed-upload failure'),
                ('malformed-accepted', 'Malformed program was accepted'),
                ('active-image', 'did not retain the active image'), ('recovery', 'Recovered program result')]:
            with self.subTest(fault=fault), self.assertRaisesRegex(RuntimeError, message):
                self.demonstrate(fault)


class OptimizationModes(unittest.TestCase):
    def test_acceptance_checks_survive_all_optimization_modes(self):
        for flags, environment in [(['-O'], {}), (['-OO'], {}), ([], {'PYTHONOPTIMIZE': '1'})]:
            env = dict(os.environ)
            env.pop('PYTHONOPTIMIZE', None)
            env.update(environment)
            with self.subTest(flags=flags, environment=environment):
                result = subprocess.run([sys.executable, '-B', *flags, str(Path(__file__).resolve()),
                                         'PeerChecks', 'DemoChecks'], env=env,
                                        capture_output=True, text=True, timeout=15)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
