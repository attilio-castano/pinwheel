"""Absolute external waveforms and distinguishing public-edge observations."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from pad_io import PadObservation
from streaming_uart_peers import AbsoluteUartPeer, FrameObservation, UartPlan


def record(plan, edge, terminal=None):
    return dict(cycle=edge, pins=dict(initialize=0, csn=1, sck=0, mosi=0),
        observation=dict(enabled=0, levels=0, edge_inputs=plan.raw_at(edge),
            busy=int(terminal is None or edge < terminal)))


def observe(plan, *, delta=0, change=None):
    first, last = plan.first_low_edge - 15, plan.first_low_edge + 40 * plan.quarter_cycles + 8
    observation = FrameObservation(plan, first, last)
    terminal = plan.expected_terminal_edge
    if terminal is not None: terminal += delta
    for edge in range(first, last + 1):
        item = record(plan, edge, terminal)
        if change: change(item)
        observation(item)
    return observation.result()


class UartPeerTests(unittest.TestCase):
    def test_external_transmitter_sends_start_lsb_first_and_stop_at_fixed_times(self):
        for q in (4, 12, 128):
            p = UartPlan(q, 0x96, 32)
            self.assertTrue(p.level_at(31))
            self.assertFalse(p.level_at(32))
            self.assertFalse(p.level_at(32 + p.bit_cycles - 1))
            self.assertEqual(tuple(p.level_at(edge) for edge in p.samples),
                (False, True, True, False, True, False, False, True))
            self.assertTrue(p.level_at(32 + 9 * p.bit_cycles))
            self.assertEqual(observe(p)['terminal_delta'], 0)

    def test_one_sample_false_start_bad_stop_and_never_start_have_distinct_results(self):
        for kind in ('false-start', 'bad-stop', 'held-high'):
            p = UartPlan(4, 0x69, 32, kind)
            observed = observe(p)
            self.assertEqual(observed['first_raw_low'], None if kind == 'held-high' else 32)
            self.assertEqual(p.expected_fault, kind != 'held-high')
            if kind == 'false-start':
                self.assertFalse(p.level_at(32))
                self.assertTrue(p.level_at(33))
                self.assertEqual(p.expected_bits, ())
            if kind == 'bad-stop': self.assertFalse(p.level_at(32 + 38 * 4))

    def test_single_edge_center_and_offcenter_pulses_are_explicit_non_uart_diagnostics(self):
        center = UartPlan(4, 0, 32, 'sampling-center')
        off = UartPlan(4, 0, 32, 'sampling-off-center')
        pulse = center.samples[3]
        self.assertEqual([center.level_at(edge) for edge in range(pulse - 1, pulse + 2)], [False, True, False])
        self.assertEqual([off.level_at(edge) for edge in range(pulse - 1, pulse + 3)], [False, False, True, False])
        self.assertFalse(center.uart_timing)
        self.assertFalse(off.uart_timing)
        self.assertEqual(sum(center.expected_bits), 1)
        self.assertEqual(sum(off.expected_bits), 0)

    def test_uniform_sampler_mutant_can_preserve_data_and_move_public_completion_one_edge(self):
        p = UartPlan(4, 0, 32, 'sampling-center')
        ordinary, mutant = observe(p), observe(p, delta=-1)
        self.assertEqual(ordinary['raw_center_bits'], mutant['raw_center_bits'])
        self.assertEqual(mutant['terminal_delta'], -1)
        self.assertEqual(mutant['public_terminal_edge'] + 1, ordinary['public_terminal_edge'])

    def test_host_io_wrong_raw_and_output_drive_fail_even_with_matching_payload(self):
        p = UartPlan(4, 0x55, 32)
        def io(item): item['pins']['csn'] = 0
        def raw(item): item['observation']['edge_inputs'] ^= 1
        def drive(item): item['observation']['enabled'] = 1
        for change in (io, raw, drive):
            with self.subTest(change=change.__name__), self.assertRaises(RuntimeError): observe(p, change=change)

    def test_peer_schedule_is_independent_of_status_and_supplies_next_edge(self):
        p = UartPlan(4, 0, 32)
        pads = PadObservation(0, 0, 0, 255, 255)
        peer = AbsoluteUartPeer(p)
        first = peer.drive(30, pads)
        self.assertEqual(first.levels, 1)
        second = peer.drive(31, PadObservation(1, 0, 0, 255, 255))
        self.assertEqual(second.levels, 0)
        self.assertEqual(second.enabled, 1)
        with self.assertRaises(RuntimeError): peer.drive(33, pads)

    def test_selected_second_raw_input_preserves_unused_high_line(self):
        p = UartPlan(4, 0, 32, rx_input=1)
        self.assertEqual(p.raw_at(31), 3)
        self.assertEqual(p.raw_at(32), 1)
        peer = AbsoluteUartPeer(p)
        drive = peer.drive(31, PadObservation(0, 0, 0, 255, 255))
        self.assertEqual((drive.enabled, drive.levels), (2, 0))

    def test_invalid_or_missing_callback_windows_refuse(self):
        with self.assertRaises(ValueError): UartPlan(4, 0, 32, false_low_edges=8)
        with self.assertRaises(ValueError): UartPlan(4, 1, 32, 'sampling-center')
        p = UartPlan(4, 0, 32)
        observation = FrameObservation(p, 17, 200)
        observation(record(p, 17, p.expected_terminal_edge))
        with self.assertRaises(RuntimeError): observation(record(p, 19, p.expected_terminal_edge))
        with self.assertRaises(RuntimeError): observation.result()


if __name__ == '__main__': unittest.main()
