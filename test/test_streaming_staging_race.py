"""Refusal and physical-edge alignment controls; no simulator receipt shortcut."""
from copy import deepcopy
from pathlib import Path
from types import SimpleNamespace
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from pad_io import PadObservation
from streaming_staging_race import (CloseOnFinalFall, HALF_CYCLES, ReceivePeer,
    VARIANTS, check_races, image_for, reply_for)
from streaming_compile import validate_image


def good_result():
    cases = []
    for bits, offered in VARIANTS:
        for terminal in ('halt', 'fault'):
            cases.append(dict(passed=True, depth=2, terminal=terminal, bit_count=bits,
                owner_tag=65537, old_export_start=bits - 33, old_export_bits=32,
                admitted_tx_bits=offered, staged_beats=offered // 32,
                tx_accepted_after_terminal=offered, terminal_retained=True,
                final_sample_preserved=True, simultaneous_rx_pop=True,
                old_export_ack_applied_once=True, release_blocks_unconsumed_tx=True, explicit_cancel=True,
                physical_edges=2000, trace=dict(edges=2000, bytes=40000, sha256='0' * 64),
                alignment=dict(request_nibbles=44, held_edges=1,
                    closing_cycle=1256, final_rise=1000, final_fall=1256),
                peer=dict(bits=bits, clock_edges=bits * 2,
                    high_phase_edges=[256], final_fall=1256),
                raced_reply=dict(code=0, tag=65537, tx_accepted=offered,
                    rx_start=bits - 1, rx_valid=1, data=1, tx_free=2 - offered // 32,
                    rx_queued=0, flags=13 if terminal == 'fault' else 5),
                held_reply=dict(code=5, tag=65537, tx_accepted=offered, flags=20),
                cancelled_reply=dict(code=0, tag=65537, flags=0, tx_accepted=0, rx_queued=0)))
    return dict(schema='pinwheel.streaming-terminal-staging.v1', passed=True,
        depth=2, cases=cases, physical_edges=8000)


class PublicClock:
    def __init__(self):
        self.cycle, self.calls = 88, []
        self.peer = SimpleNamespace(bit_count=33, rises=[1] * 32, falls=[])

    def tick(self, **pins):
        self.cycle += 1
        self.calls.append(pins)
        if self.cycle == 100: self.peer.rises.append(100)
        if self.cycle == 356: self.peer.falls.append(356)
        return dict(miso=0, ready=0)


def pads(clock):
    levels = 2 if clock else 0
    return PadObservation(1, levels << 2, 7 << 2, levels << 2, 255)


class RaceControls(unittest.TestCase):
    def test_images_are_generic_receive_only_and_preserve_terminal_distinction(self):
        for terminal in ('halt', 'fault'):
            image = image_for(terminal)
            validate_image(image)
            self.assertEqual(len(image.words), 2)
            self.assertFalse(image.source.instructions[0].cell.transmit)
            self.assertTrue(image.source.instructions[0].cell.receive)
            self.assertEqual(image.words[-1], 2 if terminal == 'halt' else 3)
        with self.assertRaises(ValueError): image_for('guessed-terminal')

    def test_reply_includes_nonbyte_final_sample(self):
        for bits, _ in VARIANTS:
            reply = reply_for(bits)
            self.assertEqual(len(reply), bits)
            self.assertTrue(reply[-1])
            self.assertTrue(any(reply[:-1]))
            self.assertFalse(all(reply[:-1]))
        with self.assertRaises(ValueError): reply_for(64)

    def test_alignment_uses_public_rise_and_closes_on_exact_final_fall(self):
        rtl = PublicClock()
        link = CloseOnFinalFall(rtl, rtl.peer)
        link.csn, link.sck, link.mosi, link.count = 0, 1, 6, 44
        link.arm()
        link.tick(csn=1, sck=0, mosi=0)
        self.assertEqual(rtl.cycle, 356)
        self.assertEqual(link.trigger['closing_cycle'], link.trigger['final_fall'])
        self.assertEqual(link.trigger['final_fall'] - link.trigger['final_rise'], HALF_CYCLES)
        self.assertTrue(all(call == dict(csn=0, sck=1, mosi=6) for call in rtl.calls[:-1]))
        self.assertEqual(rtl.calls[-1], dict(csn=1, sck=0, mosi=0))
        with self.assertRaises(RuntimeError): link.arm()

    def test_incomplete_request_or_late_alignment_cannot_claim_race(self):
        for count, cycle in ((43, 88), (44, 400)):
            rtl = PublicClock()
            rtl.cycle = cycle
            if cycle == 400: rtl.peer.rises.append(100)
            link = CloseOnFinalFall(rtl, rtl.peer)
            link.csn, link.sck, link.count = 0, 1, count
            link.arm()
            with self.assertRaises(RuntimeError): link.tick(csn=1, sck=0, mosi=0)

    def test_peer_rejects_high_stall_and_short_low_without_internal_state(self):
        peer = ReceivePeer(33)
        peer.drive(1, pads(0))
        peer.drive(257, pads(1))
        with self.assertRaisesRegex(RuntimeError, 'high phase'):
            peer.drive(514, pads(0))
        peer = ReceivePeer(33)
        peer.drive(1, pads(0))
        peer.drive(257, pads(1))
        peer.drive(513, pads(0))
        with self.assertRaisesRegex(RuntimeError, 'low phase'):
            peer.drive(768, pads(1))

    def test_peer_requires_exact_clock_count(self):
        with self.assertRaisesRegex(RuntimeError, 'exact number'):
            ReceivePeer(33).check()

    def test_contract_rejects_missing_variant_or_terminal_and_bad_alignment(self):
        check_races(good_result())
        for change in ('missing', 'duplicate', 'alignment', 'held', 'trace', 'rx_pop', 'beats'):
            value = good_result()
            if change == 'missing': value['cases'].pop()
            elif change == 'duplicate': value['cases'][-1]['terminal'] = 'halt'
            elif change == 'alignment': value['cases'][0]['alignment']['final_fall'] += 1
            elif change == 'held': value['cases'][0]['alignment']['held_edges'] = 0
            elif change == 'trace': value['cases'][0]['trace']['bytes'] -= 20
            elif change == 'rx_pop': value['cases'][0]['simultaneous_rx_pop'] = False
            else: value['cases'][2]['staged_beats'] = 1
            with self.subTest(change=change), self.assertRaises(RuntimeError): check_races(value)

    def test_contract_rejects_lost_second_beat_or_sample_and_early_release(self):
        for field, key, value in (('raced_reply', 'tx_accepted', 32),
                ('raced_reply', 'rx_valid', 0), ('held_reply', 'code', 0),
                ('cancelled_reply', 'tag', 131073)):
            report = deepcopy(good_result())
            report['cases'][2][field][key] = value
            with self.subTest(field=field, key=key), self.assertRaisesRegex(RuntimeError, 'receipts'):
                check_races(report)


if __name__ == '__main__': unittest.main()
