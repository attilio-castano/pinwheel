"""Acceptance refusal controls for the fresh public-pin simulator producer."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('streaming_sim_gate', ROOT / 'scripts/check-streaming-rtl-sim.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def good_cases():
    cases = []
    for depth in (2, 4):
        for protocol, bits, fault in [('spi', 32768, None), ('jtag', 4097, None), ('spi', 0, None),
                ('spi', 8, 'request_close'), ('spi', 8, 'request_crc'),
                ('spi', 8, 'response_crc'), ('spi', 8, 'partial_read')]:
            peer = dict(bits=bits, high_phase_edges=[4] if bits else [], low_extra_edges=1,
                continuous_cs=True, clock_edges=bits * 2 if protocol == 'spi' else (bits + 11) * 2,
                clocks=bits + 11, capture_count=1, update_count=1, last_bit_exits_shift_dr=True,
                final_tap_state='run_test_idle')
            cases.append(dict(passed=True, depth=depth, protocol=protocol, bits=bits, fault=fault,
                start_count=1, owner_tag=65537, exchange_rx_max=32, physical_edges=100,
                trace=dict(edges=100), peer=peer, recoveries=1 if fault else 0,
                faults=[dict(kind=fault)] if fault else []))
        cases.append(dict(kind='custody', passed=True, depth=depth, trace=dict(edges=100),
            unacknowledged_release_rejected=True, rejected_request_custody_preserved=True,
            stale_owner_rejected=True, same_image_two_starts=True,
            stale_local_owner_no_io=True, stale_image_no_io=True))
    return cases


class GateControls(unittest.TestCase):
    def test_exact_two_depth_corpus_accepts(self):
        gate.check_results(good_cases())

    def test_missing_duplicate_wrong_depth_or_extra_case_refused(self):
        for mutation in ('missing', 'duplicate', 'depth', 'extra'):
            cases = good_cases()
            if mutation == 'missing': cases.pop()
            elif mutation == 'duplicate': cases[0] = deepcopy(cases[1])
            elif mutation == 'depth': cases[0]['depth'] = 8
            else: cases.append(deepcopy(cases[0]))
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeError): gate.check_results(cases)

    def test_protocol_owner_start_trace_timing_and_rx_mutations_refused(self):
        mutations = [('passed', False), ('start_count', 2), ('owner_tag', 65538),
            ('exchange_rx_max', 64), ('physical_edges', 99)]
        for field, value in mutations:
            cases = good_cases()
            cases[0][field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError): gate.check_results(cases)
        for field, value in [('bits', 32), ('high_phase_edges', [4, 5]), ('low_extra_edges', 0),
                ('continuous_cs', False), ('clock_edges', 65534)]:
            cases = good_cases()
            cases[0]['peer'][field] = value
            with self.subTest(peer=field), self.assertRaises(RuntimeError): gate.check_results(cases)

    def test_jtag_navigation_and_receive_boundary_mutations_refused(self):
        for field, value in [('clocks', 4107), ('capture_count', 0), ('update_count', 2),
                ('last_bit_exits_shift_dr', False), ('final_tap_state', 'shift_dr')]:
            cases = good_cases()
            cases[1]['peer'][field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError): gate.check_results(cases)

    def test_unexercised_fault_or_custody_control_refused(self):
        for field in ('recoveries', 'faults'):
            cases = good_cases()
            cases[3][field] = 0 if field == 'recoveries' else []
            with self.subTest(field=field), self.assertRaises(RuntimeError): gate.check_results(cases)
        for field in ('unacknowledged_release_rejected', 'rejected_request_custody_preserved',
                'stale_owner_rejected', 'same_image_two_starts', 'stale_local_owner_no_io', 'stale_image_no_io'):
            cases = good_cases()
            cases[7][field] = False
            with self.subTest(field=field), self.assertRaises(RuntimeError): gate.check_results(cases)

    def test_producer_and_required_membership_excludes_historical_receipts(self):
        self.assertIn('scripts/check-streaming-rtl-sim.py', gate.PRODUCER)
        self.assertIn('test/test_streaming_rtl_sim.py', gate.PRODUCER)
        self.assertIn('scripts/streaming_wire_cases.py', gate.REQUIRED)
        self.assertFalse(any('build/' in name or 'evidence/' in name for name in gate.PRODUCER + gate.REQUIRED))
        text = (ROOT / gate.DRIVER).read_text()
        for forbidden in ('h.worker(', 'h.main(', 'h.poison_bridge(', 'gate.wire_cases('):
            self.assertNotIn(forbidden, text)


if __name__ == '__main__': unittest.main()
