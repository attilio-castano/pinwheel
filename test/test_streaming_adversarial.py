"""Physical frame-length injection and additional receipt-contract controls."""
from copy import deepcopy
from pathlib import Path
from types import SimpleNamespace
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_adversarial import FrameFaultLink, check_adversarial, host_sequence_refusal


class Recorder:
    def __init__(self, ready=0):
        self.cycle, self.pins = 0, []
        self.snapshot = SimpleNamespace(ready=ready)

    def tick(self, **pins):
        self.cycle += 1
        self.pins.append(pins)
        return dict(miso=0, ready=self.snapshot.ready)

    def rises(self):
        previous = 0
        count = 0
        for pins in self.pins:
            count += int(not pins['csn'] and pins['sck'] and not previous)
            previous = pins['sck']
        return count


def good_result():
    names = ['overlong_response', 'partial_request', 'overlong_request',
        'changed_bytes_same_sequence', 'rejected_credit_fresh_sequence', 'retained_tx_ack']
    cases = []
    for index, name in enumerate(names):
        bits = 32 if index < 3 else 512 if index == 4 else 8
        case = dict(case=name, passed=True, owner_tag=65537, physical_edges=100,
            trace=dict(edges=100, bytes=2000, sha256='0' * 64),
            peer=dict(bits=bits, clock_edges=bits * 2, high_phase_edges=[4], continuous_cs=True, low_extra_edges=1))
        if index < 3:
            case.update(same_sequence_recovery=True, exact_tx_prefix_once=True,
                original_sequence=6, recovery_sequence=6, recoveries=1,
                faults=[dict(kind=name)], ready_retention_checked=index == 0)
        elif index == 3:
            case.update(changed_request_rejected=True, unacknowledged_release_still_rejected=True,
                rejected_cache_replayed_exactly=True)
        elif index == 4:
            case.update(cached_rejected_replay_exact=True, fresh_sequence_accepted=True,
                rx_backpressure_observed=True, rejected_sequence=8, fresh_sequence=10, probe=dict(flags=64))
        else:
            case.update(retained_tx_offer_rejected=True, rejected_ack_preserved_custody=True,
                explicit_zero_tx_ack_accepted=True, matching_release_accepted=True)
        cases.append(case)
    cases.append(host_sequence_refusal())
    return dict(schema='pinwheel.streaming-quad-adversarial.v1', depth=2,
        passed=True, physical_edges=600, cases=cases)


class AdversarialTests(unittest.TestCase):
    def test_request_faults_change_actual_sample_count(self):
        for kind, expected in [('partial_request', 43), ('overlong_request', 45)]:
            rtl = Recorder()
            link = FrameFaultLink(rtl)
            link.arm(kind)
            for _ in range(44):
                link.tick(csn=0, sck=0, mosi=3)
                link.tick(csn=0, sck=1, mosi=3)
            link.tick(csn=1, sck=0, mosi=0)
            self.assertEqual(rtl.rises(), expected)
            self.assertEqual([value['kind'] for value in link.triggered], [kind])
            self.assertIsNone(link.armed)

    def test_overlong_response_has_one_real_extra_clock(self):
        rtl = Recorder(ready=1)
        link = FrameFaultLink(rtl)
        link.arm('overlong_response')
        for _ in range(52):
            link.tick(csn=0, sck=0, mosi=0)
            link.tick(csn=0, sck=1, mosi=0)
        link.tick(csn=1, sck=0, mosi=0)
        self.assertEqual(rtl.rises(), 53)
        self.assertEqual(len(link.triggered), 1)

    def test_faults_do_not_silently_queue_or_accept_unknown_kinds(self):
        link = FrameFaultLink(Recorder())
        with self.assertRaises(ValueError): link.arm('unspecified_fault')
        link.arm('partial_request')
        with self.assertRaises(ValueError): link.arm('overlong_request')

    def test_maximum_sequence_refusal_is_explicitly_host_only(self):
        result = host_sequence_refusal()
        self.assertEqual(result['physical_edges'], 0)
        self.assertEqual(result['maximum_sequence'], 65535)
        self.assertTrue(result['refused_before_io'])

    def test_complete_contract_and_distinguishing_control_refusals(self):
        check_adversarial(good_result())
        for mutation in ('missing', 'duplicate', 'trace', 'recovery', 'custody', 'rx_stall', 'high_stall', 'host_io'):
            value = good_result()
            if mutation == 'missing': value['cases'].pop()
            elif mutation == 'duplicate': value['cases'][0] = deepcopy(value['cases'][1])
            elif mutation == 'trace': value['cases'][0]['trace']['edges'] = 99
            elif mutation == 'recovery': value['cases'][1]['recoveries'] = 0
            elif mutation == 'custody': value['cases'][5]['rejected_ack_preserved_custody'] = False
            elif mutation == 'rx_stall': value['cases'][4]['probe']['flags'] = 0
            elif mutation == 'high_stall': value['cases'][4]['peer']['high_phase_edges'] = [4, 5]
            else: value['cases'][6]['physical_edges'] = 1
            with self.subTest(mutation=mutation), self.assertRaises(ValueError): check_adversarial(value)


if __name__ == '__main__': unittest.main()
