"""Pure UART corpus refusals; synthetic data is not native qualification."""
from copy import deepcopy
from dataclasses import asdict
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_transport import Code, Receipt
from streaming_uart_compile import QUARTERS, project, uart_image
from streaming_uart_peers import UartPlan
from streaming_uart_wire_cases import (MUTATION_OPERATION, SCHEMA, UART_CASES_PER_DEPTH,
    case_keys, check_uart_cases, run_uart_cases)


def fixture(depth=2):
    mutation = dict(changed_drivers=1, operation=MUTATION_OPERATION,
        candidate='/fixture/mutant/core.sv', candidate_sha256='b' * 64,
        executable='/fixture/mutant/chip.vvp', executable_sha256='c' * 64,
        source_sha256={'/fixture/' + name: 'a' * 64 for name in
            ('core.sv', 'frontend.sv', 'package.sv', 'tt.sv', 'bridge.sv')})
    images = [dict(quarter_cycles=q, words=list(uart_image(q).words),
        certificate=asdict(uart_image(q).certificate), rows=9, loads=1, generation=index + 1)
        for index, q in enumerate(QUARTERS)]
    cases = []
    for index, (kind, q, payload) in enumerate(case_keys()):
        mutant, held = kind == 'sampler-stage', kind == 'held-high'
        profile = 'sampling-center' if mutant else kind
        plan = UartPlan(q, payload, 1000 if mutant else 1000 + index * 6000, profile)
        generation = 1 if mutant else QUARTERS.index(q) + 1
        tag = generation * 65536 + (1 if mutant else index + 1)
        bits = plan.expected_bits
        start = Receipt(index * 4, Code.ACCEPTED, tag=tag, tx_free=depth, flags=3)
        rx = Receipt(index * 4 + 1, Code.ACCEPTED, tag=tag, tx_free=depth,
            flags=3 if held else 13 if plan.expected_fault else 5,
            data=sum(int(bit) << (len(bits) - 1 - bit_index) for bit_index, bit in enumerate(bits)), rx_valid=len(bits))
        final = Receipt(index * 4 + 3, Code.ACCEPTED, tag=tag, tx_free=depth, flags=0 if held else 1)
        terminal = plan.expected_terminal_edge
        observation = dict(first_edge=plan.first_low_edge - 15, last_edge=plan.first_low_edge + 40 * q + 8,
            edges=40 * q + 24, first_raw_low=None if held else plan.first_low_edge,
            idle_high_arm_edges=15, host_frames_during_reception=0, released_protocol_pins=True,
            expected_terminal_edge=terminal, public_terminal_edge=None if held else terminal - mutant,
            terminal_delta=None if held else -1 if mutant else 0, raw_sample_edges=list(plan.samples),
            raw_center_bits=[plan.level_at(edge) for edge in plan.samples])
        case = dict(passed=True, kind=kind, quarter_cycles=q, payload=payload, waveform=asdict(plan),
            image_generation=generation, owner_tag=tag, starts=1, tx_accepted=0,
            start_sequence=start.sequence, start_receipt=asdict(start), rx_receipt=asdict(rx), cleanup_receipt=asdict(final),
            captured_bits=len(bits), rx_bits=list(bits), cleanup='warm-cancel' if held else 'matching-release',
            requests=3 if held else 4, projection=asdict(project(bits, fault=plan.expected_fault, uart_timing=plan.uart_timing)),
            observation=observation, expected_terminal_delta=-1 if mutant else 0, source_timing_refuted=mutant)
        if mutant:
            case.update(name='sampler-stage', mutation=mutation, expected_rejection=True, oracle_rejected=True)
        cases.append(case)
    runs = []
    for mutant, edges in ((False, 5_000_000), (True, 2000)):
        runs.append(dict(name='sampler-stage' if mutant else 'unchanged',
            argv=['/fixture/vvp', mutation['executable'] if mutant else '/fixture/chip.vvp'],
            native_exit_code=0, physical_edges=edges, executable_sha256='c' * 64 if mutant else 'a' * 64,
            executable_unchanged=True, trace=dict(edges=edges, bytes=edges * 20, sha256='d' * 64),
            opcode_counts=dict(WRITE=9, COMMIT=1, START=1, EXCHANGE0=2, RELEASE=1) if mutant else
                dict(WRITE=27, COMMIT=3, START=779, RELEASE=776, WARM_RESET=3, EXCHANGE0=1555)))
    cases[-1]['native'] = runs[-1]
    return dict(schema=SCHEMA, passed=True, depth=depth, images=images, cases=cases, native_runs=runs,
        physical_edges=sum(run['physical_edges'] for run in runs),
        case_counts=dict(valid_frames=768, error_controls=9, sampling_diagnostics=2, mutant_controls=1, total=780))


class UartWireTests(unittest.TestCase):
    def test_exact_matrix_is_768_payloads_nine_controls_two_diagnostics_one_actual_mutant(self):
        self.assertEqual(len(case_keys()), UART_CASES_PER_DEPTH)
        for depth in (2, 4): check_uart_cases(fixture(depth))

    def test_missing_duplicate_or_reordered_payloads_and_false_total_refuse(self):
        for kind in ('missing', 'duplicate', 'reordered', 'count'):
            value = fixture()
            if kind == 'missing': value['cases'].pop(1)
            elif kind == 'duplicate': value['cases'][1] = deepcopy(value['cases'][0])
            elif kind == 'reordered': value['cases'][0], value['cases'][1] = value['cases'][1], value['cases'][0]
            else: value['case_counts']['total'] -= 1
            with self.subTest(kind=kind), self.assertRaises(RuntimeError): check_uart_cases(value)

    def test_rx_bit_order_packed_word_and_fault_projection_are_independent_requirements(self):
        for kind in ('bits', 'packed', 'projection', 'bad-stop-success'):
            value = fixture()
            row = value['cases'][0x96]
            if kind == 'bits': row['rx_bits'].reverse()
            elif kind == 'packed': row['rx_receipt']['data'] = 0x96
            elif kind == 'projection': row['projection']['value'] = 0x69
            else: value['cases'][257]['projection']['payload_valid'] = True
            with self.subTest(kind=kind), self.assertRaises(RuntimeError): check_uart_cases(value)

    def test_early_busy_edge_cannot_pass_as_unchanged_or_mutant_success_without_negative_label(self):
        for index, delta in ((0, -1), (-1, 0), (-1, -2)):
            value = fixture()
            row = value['cases'][index]
            row['observation']['terminal_delta'] = delta
            row['observation']['public_terminal_edge'] = row['observation']['expected_terminal_edge'] + delta
            with self.subTest(index=index, delta=delta), self.assertRaises(RuntimeError): check_uart_cases(value)

    def test_native_crash_unbound_mutant_executable_and_changed_source_refuse(self):
        for kind in ('exit', 'argv', 'hash', 'operation', 'same-source'):
            value = fixture()
            control = value['cases'][-1]
            if kind == 'exit': value['native_runs'][1]['native_exit_code'] = 1
            elif kind == 'argv': value['native_runs'][1]['argv'][1] = '/wrong/chip.vvp'
            elif kind == 'hash': value['native_runs'][1]['executable_sha256'] = 'a' * 64
            elif kind == 'operation': control['mutation']['operation'] = 'unrelated mutation'
            else: control['mutation']['candidate_sha256'] = 'a' * 64
            with self.subTest(kind=kind), self.assertRaises(RuntimeError): check_uart_cases(value)

    def test_reupload_per_byte_or_reused_owner_and_allocator_reset_refuse(self):
        for kind in ('write', 'owner', 'generation', 'loads'):
            value = fixture()
            if kind == 'write': value['native_runs'][0]['opcode_counts']['WRITE'] += 9
            elif kind == 'owner': value['cases'][1]['owner_tag'] = value['cases'][0]['owner_tag']
            elif kind == 'generation': value['images'][0]['generation'] += 1
            else: value['images'][0]['loads'] = 256
            with self.subTest(kind=kind), self.assertRaises(RuntimeError): check_uart_cases(value)

    def test_host_io_output_drive_or_overlapping_native_trace_window_refuse(self):
        for kind in ('host', 'pins', 'range', 'overlap'):
            value = fixture()
            obs = value['cases'][0]['observation']
            if kind == 'host': obs['host_frames_during_reception'] = 1
            elif kind == 'pins': obs['released_protocol_pins'] = False
            elif kind == 'range': value['native_runs'][0]['physical_edges'] = 1
            else: value['cases'][1]['waveform']['first_low_edge'] = value['cases'][0]['waveform']['first_low_edge']
            with self.subTest(kind=kind), self.assertRaises(RuntimeError): check_uart_cases(value)

    def test_missing_actual_mutant_refuses_before_creating_output(self):
        from tempfile import TemporaryDirectory
        with TemporaryDirectory() as temporary:
            out = Path(temporary) / 'not-created'
            with self.assertRaises(RuntimeError): run_uart_cases('unused', 'unused', out, depth=2)
            self.assertFalse(out.exists())

    def test_depth_boolean_and_float_aliases_refuse(self):
        for depth in (True, False, 2.0, 4.0):
            value = fixture()
            value['depth'] = depth
            with self.subTest(depth=depth), self.assertRaises(RuntimeError): check_uart_cases(value)
            with self.assertRaises(RuntimeError): run_uart_cases('unused', 'unused', 'not-created', depth=depth)


if __name__ == '__main__': unittest.main()
