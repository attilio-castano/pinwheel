"""Independent UART sender, ownership and stream-gate refusal controls."""
from dataclasses import asdict, replace
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from pad_io import PadObservation
from capability_receipt import CapabilityEvidence
from pinwheel_host import Program
from uart_stream_peer import Frame, OneEntryOracle, UARTStreamPeer

spec = importlib.util.spec_from_file_location('uart_stream_gate', ROOT / 'scripts/check-uart-stream.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class UARTWireChecks(unittest.TestCase):
    def test_absolute_sender_covers_patterns_odd_periods_both_inputs_and_repeated_values(self):
        payload = [0, 255, 0x55, 0xaa, 0x53, 0xa6, 0, 0]
        for period in (8, 9, 16, 257):
            for pin in (0, 1):
                start = 1200
                peer = UARTStreamPeer([Frame(start + k * 10 * period * 100, byte, period * 100)
                                       for k, byte in enumerate(payload)], input_pin=pin)
                result = peer.completions(period, 0, peer.frames[-1].end // 100 + 4)
                with self.subTest(period=period, pin=pin):
                    self.assertEqual([r.byte for r in result], payload)
                    self.assertFalse(any(r.framing_error for r in result))
                    self.assertEqual([r.mailbox_edge - r.core_edge for r in result], [1] * len(payload))

    def test_bad_stop_held_low_and_false_start_then_valid_rearm(self):
        peer = UARTStreamPeer([Frame(1200, 0x53, 800, 0), Frame(11200, 0xa6, 800)])
        outcomes = peer.completions(8, 0, 200)
        self.assertEqual([(r.byte, r.framing_error) for r in outcomes], [(0x53, True), (0xa6, False)])
        peer = UARTStreamPeer([Frame(18000, 0xa6, 800)], initial_low_until=15000)
        # Drain the held-low pad into both sampler stages before arming.
        self.assertEqual([r.byte for r in peer.completions(8, 3, 270)], [0xa6])
        peer = UARTStreamPeer([Frame(3000, 0x53, 800)], low_pulses=[(1200, 1300)])
        self.assertEqual([r.byte for r in peer.completions(8, 0, 120)], [0x53])

    def test_unequal_transmitter_clock_phase_and_two_stage_history(self):
        for tx_tick in (97, 103):
            for phase in (0, 1, 99):
                peer = UARTStreamPeer([Frame(1201 + k * 160 * tx_tick, b, 16 * tx_tick)
                                       for k, b in enumerate([0x53, 0xa6, 0, 0])], rx_phase=phase)
                with self.subTest(tx_tick=tx_tick, phase=phase):
                    self.assertEqual([r.byte for r in peer.completions(16, 0, 680)], [0x53, 0xa6, 0, 0])
                    for edge in range(2, 680):
                        self.assertEqual(peer.consumed_line(edge), peer.line(peer.edge_time(edge - 2)))

    def test_single_frame_safe_rearm_failure_is_not_consumer_overrun(self):
        peer = UARTStreamPeer([Frame(300, 0, 770), Frame(8000, 0, 770)])
        result = peer.completions(8, 0, 170, mailbox_delay=1)
        # Exact callback/sampler alignment adds two edges to the old direct-input example.
        self.assertEqual([(r.core_edge, r.byte) for r in result], [(81, 0)])
        queue = OneEntryOracle()
        for event in result:
            queue.edge(asdict(event), take=True)
        self.assertFalse(queue.overrun)

    def test_sender_schedule_never_uses_dut_busy_or_result_values(self):
        peers = [UARTStreamPeer([Frame(300, 0x53, 800)]) for _ in range(2)]
        for cycle in range(120):
            drives = []
            for k, peer in enumerate(peers):
                previous = 1 if peer.last_applied is None else peer.last_applied
                pads = PadObservation(0 if k == 0 else 255, 0, 0, previous | 254, 255)
                drives.append(peer.drive(cycle, pads, 4 if k == 0 else 127))
            self.assertEqual(drives[0], drives[1])

    def test_resolved_wrong_pad_level_and_output_ownership_fail(self):
        peer = UARTStreamPeer([Frame(300, 0x53, 800)])
        peer.drive(0, PadObservation(0, 0, 0, 255, 255), 4)
        with self.assertRaisesRegex(RuntimeError, 'resolved input differs'):
            peer.drive(1, PadObservation(0, 0, 0, 254, 255), 4)
        with self.assertRaisesRegex(RuntimeError, 'release every output'):
            peer.drive(1, PadObservation(0, 4, 4, 255, 255), 4)

    def test_invalid_configuration_does_not_generate_a_waveform(self):
        for kwargs in (dict(input_pin=True), dict(input_pin=2), dict(rx_tick=0), dict(rx_phase=100),
                       dict(wire_delay=-1), dict(low_pulses=[(5, 5)])):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                UARTStreamPeer([Frame(300, 0x53, 800)], **kwargs)
        with self.assertRaises(ValueError):
            UARTStreamPeer([Frame(300, 0x53, 800), Frame(400, 0xa6, 800)])


class OwnershipOracleChecks(unittest.TestCase):
    def test_old_value_retained_drops_count_occurrences_even_when_bytes_match(self):
        queue = OneEntryOracle()
        queue.edge(('byte', 0x53))
        queue.edge(('byte', 0x53))
        queue.edge(('framing-error', 0x53))
        self.assertEqual(queue.pending, ('byte', 0x53))
        self.assertEqual(len(queue.dropped), 2)
        self.assertTrue(queue.overrun)

    def test_pop_then_push_no_empty_bypass_and_clear_cannot_hide_new_drop(self):
        queue = OneEntryOracle(('byte', 0x53), True)
        receipt = queue.edge(('framing-error', 0xa6), take=True, clear=True)
        self.assertEqual(receipt['delivered'], ('byte', 0x53))
        self.assertEqual(queue.pending, ('framing-error', 0xa6))
        self.assertFalse(queue.overrun)
        receipt = queue.edge(('byte', 0), clear=True)
        self.assertEqual(receipt['dropped'], ('byte', 0))
        self.assertTrue(queue.overrun)
        empty = OneEntryOracle()
        self.assertIsNone(empty.edge(('byte', 0x53), take=True)['delivered'])
        self.assertEqual(empty.pending, ('byte', 0x53))

    def test_reset_flushes_old_and_suppresses_simultaneous_arrival_and_take(self):
        queue = OneEntryOracle(('byte', 0x53), True)
        receipt = queue.edge(('byte', 0xa6), reset=True, take=True, clear=True)
        self.assertEqual(receipt, dict(accepted=None, delivered=None, dropped=None, flushed=('byte', 0x53)))
        self.assertIsNone(queue.pending)
        self.assertFalse(queue.overrun)


class UARTGateChecks(unittest.TestCase):
    def test_metadata_binds_image_capacity_and_requires_both_inputs_and_boundaries(self):
        entries = [dict(name=f'rx-b{b}-pin{p}', bit_cycles=b, input_pin=p,
                        populated_positions=1, canonical_records=1)
                   for b in (8,9,16,257,6656) for p in (0,1)]
        images = {x['name']:Program((4,),0) for x in entries}
        self.assertEqual(gate.metadata(json.dumps(entries),images), entries)
        for changed in [entries[:-1], [dict(entries[0], canonical_records=2),*entries[1:]],
                        [dict(entries[0], input_pin=True),*entries[1:]],
                        [dict(entries[0], unexpected=1),*entries[1:]]]:
            with self.subTest(changed=changed[0]), self.assertRaises(RuntimeError):
                gate.metadata(json.dumps(changed),images)

    def test_absolute_schedule_waits_for_serial_arm_and_keeps_held_low_until_after_arm(self):
        simulation=type('Simulation',(),dict(cycle=100))()
        item=dict(bit_cycles=16,input_pin=1)
        ordinary=gate.scheduled_peer(simulation,item,[0x53,0xa6])
        self.assertGreater(ordinary.frames[0].start, (simulation.cycle+310)*100)
        held=gate.scheduled_peer(simulation,item,[0x53],initial_low=True)
        self.assertLess(held.initial_low_until,held.frames[0].start)
        self.assertEqual(held.line((simulation.cycle+310)*100),0)
        self.assertEqual([e.byte for e in held.completions(16,410,800)],[0x53])

    def test_component_ownership_vectors_preserve_old_consume_then_arrive_and_clear_drop(self):
        vector=gate.result_component_vector(0x253,0x2a6,True,True,True)
        self.assertEqual(vector['expected']['next_result_samples'],0x2a6)
        self.assertEqual(vector['expected']['next_result_overrun'],0)
        self.assertEqual(vector['receipt']['delivered'],(0x253,5))
        dropped=gate.result_component_vector(0x253,0x2a6,True,False,True)
        self.assertEqual(dropped['expected']['next_result_samples'],0x253)
        self.assertEqual(dropped['expected']['next_result_overrun'],1)
        reset=gate.result_component_vector(0x253,0x2a6,True,True,True,reset=True)
        for name in ('valid','samples','outcome','overrun','rejected','was_active'):
            self.assertEqual(reset['expected']['next_result_'+name],0)
        self.assertEqual(len(gate.component_vectors()),148)
        self.assertIn('$fatal(1,"UART_BUFFER vector147',gate.component_testbench(gate.component_vectors()))

    def test_canonical_capture_mutation_preserves_start_branch_and_changes_data_and_stop(self):
        source=Program((2|(33<<35)|(2<<41)|(8<<43), 2|(29<<35), 2|(37<<35),4),3)
        mutated=gate.wrong_capture_slots(source)
        self.assertEqual(mutated.words[0],source.words[0])  # Start-validation slot8 survives.
        self.assertEqual((mutated.words[1]>>35)&63,1)
        self.assertEqual((mutated.words[2]>>35)&63,1)
        self.assertNotEqual(mutated.words,source.words)

    def test_timing_certificate_is_frozen_before_kernel_consumption(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);out=root/'out';out.mkdir()
            evidence=CapabilityEvidence(root,out,[],[],[])
            arguments=dict(bit_cycles=16,input_pin=0,tx_cycles=16,tx_tick=97,rx_tick=100,
                           phase=99,start=43001,payload=[0x53,0xa6])
            def run(command,label):
                path=Path(command[-1]);self.assertIn(path.name,evidence.generated_sha256)
                path.write_text(path.read_text()+'-- changed after kernel consumption\n')
                return 'UART stream timing certificate: kernel checked; standard axioms only.'
            with self.assertRaisesRegex(RuntimeError,'changed during kernel consumption'):
                gate.certify_timing(evidence,run,'timing',**arguments)

    def test_large_receiver_period_uses_separate_bounded_transmitter_config(self):
        text=gate.timing_certificate('Large',6656,1,1,665600,100,0,43001,[0x53])
        self.assertIn('tx := ⟨⟨0, by decide⟩⟩',text)
        self.assertIn('txTick := 665600',text)
        self.assertIn('rx := ⟨6656',text)
        self.assertIn('latency : Link.Latency := .fixed 200',text)
        self.assertIn('collectAxioms',text)

    def test_rtl_mutations_require_unambiguous_actual_assignment_and_distinct_rearm_reservation(self):
        text="wire _GEN_10 = ~(~_GEN_7 & ~(_GEN_3 & _GEN_8 & r_stream_enabled & r_valid & _GEN_5 & _GEN_9));\n" \
             "wire [2:0] _GEN_13 = r_stream_enabled & ~_GEN_8 ? 3'h6 : _GEN_2;\n" \
             "assign next_result_samples = state_result_samples;\n"
        self.assertIn('wire _GEN_10 = _GEN_7;',gate.supervisor_mutation(text,'no-rearm'))
        self.assertIn("1'h0 ? 3'h6 : _GEN_2",gate.supervisor_mutation(text,'no-reservation'))
        self.assertIn('next_result_samples = core_samples;',gate.replace_assignment(text,'next_result_samples','core_samples'))
        for mutated in ('',text+text):
            with self.subTest(text=mutated),self.assertRaises(RuntimeError):
                gate.supervisor_mutation(mutated,'no-rearm')
        with self.assertRaises(RuntimeError):
            gate.replace_assignment(text,'absent','0')

    def test_completion_reservation_includes_stopped_edge_command_delivery(self):
        class Simulation:
            cycle=0
            device=None
        simulation=Simulation()
        class Host:
            def arm_uart_stream(self):simulation.cycle+=298
            def command(self,*args):simulation.cycle+=292
            def stream_status(self):return 0x1c
            def page(self,*args):return 3
            def stop_uart_stream(self):simulation.cycle+=298
            def consume(self):pass
            def clear_flags(self):pass
        with patch.object(gate,'advance_to',side_effect=lambda host,edge:setattr(simulation,'cycle',edge)):
            receipt=gate.completion_edge_reservation(simulation,Host(),dict(bit_cycles=16,input_pin=0))
        leads={v['lead_cycles'] for v in receipt['observations']}
        self.assertTrue({288,289,290}<=leads)
        stopped=next(v for v in receipt['observations'] if v['lead_cycles']==289)
        self.assertEqual(stopped['command_delivery_edge'],stopped['core_completion_edge']+1)
        self.assertEqual(stopped['serial_frame_last_edge']-stopped['command_delivery_edge'],2)


if __name__ == '__main__':
    unittest.main()
