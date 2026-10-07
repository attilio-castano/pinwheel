"""Negative controls for serial trace evidence and predecessor custody intake.

These tests check the acceptance checker itself with constructed wire records.
The separate emitted-package gate supplies actual controller/macro execution.
"""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
SPEC = importlib.util.spec_from_file_location('buffered_sram_serial_gate',
    ROOT / 'scripts/check-buffered-sram-serial.py')
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)

from buffered_sram_serial import STATUS_FIELDS, encode_request, encode_response
from buffered_sram_serial_reference import (FIELDS, WireSchedule, check_trace,
    expected_receipt)


GOLDEN_STATUS = dict(valid=1, busy=0, retained=1, pending=0, rejected=0, mode=2,
    pc=0x63, remaining=0x91, levels=5, enabled=3, tx_consumed=32, rx_length=32,
    rx_data=0xA596137B, read_valid=1, read_bit=1, generation=0x3769, transfer=0xC18D,
    exhausted=0, stage1=2, stage2=1, virtual_pc=0x155, env0=6, env1=5, phase=5,
    wait_left=0x53, scratch=0xC783)
GOLDEN_WORD = 0x5A1068AC063C1A9DB955660C69BB4F4B2C26F7040EC8B1C5
# Explicit published byte/bit positions, independently of either field table.
POSITIONS = (('valid', 0, 1), ('busy', 1, 1), ('retained', 2, 1),
    ('pending', 3, 1), ('rejected', 4, 1), ('mode', 5, 2), ('pc', 7, 8),
    ('remaining', 15, 8), ('levels', 23, 3), ('enabled', 26, 3),
    ('tx_consumed', 29, 6), ('rx_length', 35, 6), ('rx_data', 41, 32),
    ('read_valid', 73, 1), ('read_bit', 74, 1), ('generation', 75, 16),
    ('transfer', 91, 16), ('exhausted', 107, 1), ('stage1', 108, 2),
    ('stage2', 110, 2), ('virtual_pc', 112, 10), ('env0', 122, 3),
    ('env1', 125, 3), ('phase', 128, 3), ('wait_left', 131, 8), ('scratch', 139, 16))


def pin(csn=1, sck=0, mosi=0, initialize=0):
    return dict(initialize=initialize, csn=csn, sck=sck, mosi=mosi)


def request(packet, *, length=160, held=False, closing_edges=3):
    samples = [pin(csn=0)]
    for index in range(length):
        bit = (packet >> (159-index)) & 1 if index < 160 else 1
        samples.extend([pin(csn=0, mosi=bit)] * (2 if held else 1))
        samples.extend([pin(csn=0, sck=1, mosi=bit)] * (3 if held else 1))
    return samples + [pin()] * closing_edges


def response(length=192):
    samples = [pin(csn=0)]
    for _ in range(length):
        samples.extend((pin(csn=0), pin(csn=0, sck=1)))
    return samples + [pin()]


def trace(samples):
    """Make a consistent synthetic checker input from independently frozen data."""
    schedule, annotations, exported = WireSchedule(), [], []
    for index, pins in enumerate(samples):
        annotations.append(schedule.step(pins))
        # Controller state deliberately changes while receipts are held. The
        # expected serial packet must keep its capture-edge values nevertheless.
        state = dict(GOLDEN_STATUS, remaining=index & 255, scratch=(index * 73) & 65535)
        exported.append(dict(state=state))
    receipts = {a['captured']['receipt']: expected_receipt(a['captured'], exported)[0]
                for a in annotations if a['captured'] is not None}
    records = []
    for pins, annotation, vector in zip(samples, annotations, exported, strict=True):
        receipt, bit = annotation['miso_receipt'], annotation['miso_index']
        miso = 0 if receipt is None else (receipts[receipt] >> bit) & 1
        records.append(dict(pins=pins, observation=dict(miso=miso,
            ready=annotation['expected_ready'], **{name: vector['state'][name]
                for name in ('busy', 'levels', 'enabled')})))
    return records, annotations, exported


class SerialOracleTests(unittest.TestCase):
    def test_all_status_fields_match_independent_golden_positions(self):
        expected = tuple((name, width) for name, _, width in POSITIONS)
        self.assertEqual((FIELDS, STATUS_FIELDS), (expected, expected))
        self.assertEqual(sum(width for _, width in expected), 155)
        for name, offset, width in POSITIONS:
            self.assertEqual((GOLDEN_WORD >> offset) & ((1 << width) - 1), GOLDEN_STATUS[name])
        self.assertEqual(encode_response(0x68AC, 0, GOLDEN_STATUS), GOLDEN_WORD)
        event = dict(state_edge=0, delivery_edge=0, code=0, sequence=0x68AC)
        self.assertEqual(expected_receipt(event, [dict(state=GOLDEN_STATUS)]),
                         (GOLDEN_WORD, GOLDEN_STATUS, 0))

    def test_delivery_edge_rejection_does_not_use_later_quiet_status(self):
        before = dict(GOLDEN_STATUS, rejected=1)
        quiet = dict(GOLDEN_STATUS, rejected=0, generation=0x376A)
        event = dict(state_edge=1, delivery_edge=0, code=0, sequence=9)
        word, status, code = expected_receipt(event, [dict(state=before), dict(state=quiet)])
        self.assertEqual((word >> 176, code, status['rejected'], status['generation']),
                         (0x5A14, 4, 1, 0x376A))
        event['delivery_edge'] = None
        event['code'] = 2
        self.assertEqual(expected_receipt(event, [dict(state=before), dict(state=quiet)])[2], 2)

    def test_wrong_header_reserved_and_lengths_never_deliver(self):
        for packet, length, code in ((0xA720 << 144, 160, 2),
                ((0xA711 << 144) | (1 << 98), 160, 3), (0xA715 << 144, 160, 3),
                (encode_request(17, command=7), 159, 1),
                (encode_request(17, command=7), 193, 1)):
            with self.subTest(code=code, length=length):
                _, annotations, _ = trace([pin(initialize=1)] + request(packet, length=length))
                self.assertFalse(any(a['delivered'] for a in annotations))
                events = [a['captured'] for a in annotations if a['captured'] is not None]
                self.assertEqual(len(events), 1)
                self.assertEqual(events[0]['code'], code)
                if length != 160:
                    self.assertEqual(events[0]['sequence'], 0)
        with self.assertRaises(ValueError): WireSchedule().step(pin(mosi=True))

    def test_held_clock_delivers_one_command_on_the_next_edge(self):
        samples = [pin(initialize=1)] + request(encode_request(123, command=7), held=True)
        _, annotations, _ = trace(samples)
        delivered = [index for index, a in enumerate(annotations) if a['delivered']]
        self.assertEqual(len(delivered), 1)
        edge = delivered[0]
        self.assertEqual(annotations[edge]['command']['command'], 7)
        event = annotations[edge + 1]['captured']
        self.assertEqual((event['sequence'], event['state_edge'], event['delivery_edge']),
                         (123, edge, edge))

    def test_fresh_cs_required_after_por_and_high_clock_assertion(self):
        packet = encode_request(5, command=7)
        # POR at selected/high clock must not turn that level into a new frame.
        blocked = [pin(csn=0, sck=1, initialize=1)]
        blocked += [pin(csn=0), pin(csn=0, sck=1)] * 160
        blocked += [pin(), pin(csn=0, sck=1)]
        blocked += [pin(csn=0), pin(csn=0, sck=1)] * 160
        _, annotations, _ = trace(blocked)
        self.assertFalse(any(a['delivered'] or a['captured'] for a in annotations))
        _, annotations, _ = trace(blocked + [pin()] + request(packet))
        self.assertEqual(sum(a['delivered'] for a in annotations), 1)

    def test_read_backpressure_prevents_command_delivery_and_preserves_snapshot(self):
        samples = [pin(initialize=1)] + request(encode_request(19, command=0))
        samples += response(37) + request(encode_request(20, initialize=1))
        samples += response(193) + response()
        samples += request(encode_request(21, command=7)) + response()
        records, annotations, exported = trace(samples)
        events = [a['captured'] for a in annotations if a['captured'] is not None]
        self.assertEqual([e['sequence'] for e in events], [19, 21])
        self.assertEqual(sum(a['delivered'] for a in annotations), 2)
        checked = check_trace(records, annotations, exported)
        self.assertEqual((checked['frozen_receipts'], checked['complete_receipt_checks'],
            checked['frozen_status_field_checks']), (2, 2, 52))

    def test_por_cancels_pending_request_and_held_receipt(self):
        samples = [pin(initialize=1)] + request(encode_request(1, command=7), closing_edges=1)
        samples += [pin(initialize=1)]
        samples += request(encode_request(2, command=0)) + [pin(initialize=1)]
        samples += request(encode_request(3, command=7)) + response()
        records, annotations, exported = trace(samples)
        events = [a['captured'] for a in annotations if a['captured'] is not None]
        self.assertEqual([e['sequence'] for e in events], [2, 3])
        self.assertEqual(sum(a['delivered'] for a in annotations), 2)
        self.assertEqual(check_trace(records, annotations, exported)['frozen_status_field_checks'], 26)

    def test_partial_read_counts_only_observed_complete_status_fields(self):
        for length, fields in ((37, 0), (53, 1), (74, 5), (192, 26)):
            with self.subTest(length=length):
                samples = [pin(initialize=1)] + request(encode_request(7, command=0))
                samples += response(length) + [pin(initialize=1)]
                records, annotations, exported = trace(samples)
                checked = check_trace(records, annotations, exported)
                self.assertEqual(checked['frozen_status_field_checks'], fields)
                self.assertEqual(checked['complete_receipt_checks'], int(length == 192))

    def test_checker_rejects_each_public_wire_mutation_and_length_mismatch(self):
        records, annotations, exported = trace([pin(initialize=1)] +
            request(encode_request(13, command=0)) + response())
        self.assertEqual(check_trace(records, annotations, exported)['frozen_status_field_checks'], 26)
        edge = next(index for index, a in enumerate(annotations) if a['miso_receipt'] is not None)
        for name in ('ready', 'miso', 'busy', 'levels', 'enabled'):
            mutated = deepcopy(records)
            mutated[edge]['observation'][name] ^= 1
            with self.subTest(field=name), self.assertRaises(RuntimeError):
                check_trace(mutated, annotations, exported)
        with self.assertRaises(RuntimeError): check_trace(records[:-1], annotations, exported)
        mutated = deepcopy(exported)
        capture = next(a['captured'] for a in annotations if a['captured'] is not None)
        mutated[capture['state_edge']]['state']['scratch'] = True
        with self.assertRaises(RuntimeError): check_trace(records, annotations, mutated)


class SerialPredecessorIntakeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='pinwheel-serial-intake-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.critical = ['Pinwheel/Hardware/Buffered/Sram.lean',
            'Pinwheel/Hardware/Buffered/SramModel.lean', 'Pinwheel/Hardware/Buffered/SramProofs.lean',
            'Pinwheel/Hardware/Buffered/SramCandidates.lean', 'Pinwheel/Hardware/Buffered/Reactive.lean',
            'Pinwheel/Hardware/Buffered/SharedBranches.lean', 'Pinwheel/Hardware/Buffered/MemoBind.lean',
            'Pinwheel/Hardware/Buffered/MemoEval.lean', 'scripts/buffered_sram_hardware.py',
            'scripts/buffered_shared_branches.py', 'scripts/buffered_hardware.py',
            'scripts/buffered_reactive_hardware.py', 'test/BufferedSramExport.lean',
            'physical/buffered_sram_memory.sv', 'physical/buffered_sram_wrapper.sv']
        for name in self.critical:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('frozen predecessor ' + name + '\n')
        self.report = self.root / 'build/accepted/report.json'
        self.report.parent.mkdir(parents=True)
        self.report.write_text(json.dumps(dict(status='passed', smoke=False)))
        self.artifact = self.root / 'build/accepted/core.sv'
        self.artifact.write_text('frozen accepted core\n')
        self.manifest = dict(reports=dict(hardware=dict(path='build/accepted/report.json',
            sha256=gate.sha(self.report))), accepted_artifact_sha256={
            'build/accepted/core.sv': gate.sha(self.artifact)},
            frozen_source_sha256={name: gate.sha(self.root / name) for name in self.critical})
        self.manifest_path = self.root / 'physical/experiments/buffered-sram-results.json'
        self.manifest_path.parent.mkdir(parents=True)
        self.write_manifest()

    def write_manifest(self):
        self.manifest_path.write_text(json.dumps(self.manifest))

    def intake(self):
        with patch.object(gate, 'ROOT', self.root):
            return gate.predecessor()

    def test_valid_frozen_predecessor_is_accepted(self):
        directory, report = self.intake()
        self.assertEqual(directory, self.report.parent)
        self.assertEqual((report['critical_source_files'], report['accepted_artifact_files']), (15, 1))

    def test_changed_hardware_receipt_and_accepted_artifact_reject(self):
        self.report.write_text(json.dumps(dict(status='passed', smoke=False, changed=True)))
        with self.assertRaises(RuntimeError): self.intake()
        self.report.write_text(json.dumps(dict(status='passed', smoke=False)))
        self.artifact.write_text('corrupt imported Verilog bytes')
        with self.assertRaisesRegex(RuntimeError, 'predecessor artifact'): self.intake()

    def test_failed_and_smoke_receipts_reject_even_with_matching_hash(self):
        for report in (dict(status='failed', smoke=False), dict(status='passed', smoke=True)):
            self.report.write_text(json.dumps(report))
            self.manifest['reports']['hardware']['sha256'] = gate.sha(self.report)
            self.write_manifest()
            with self.subTest(report=report), self.assertRaises(RuntimeError): self.intake()

    def test_changed_execution_and_macro_source_pins_reject(self):
        for name in ('Pinwheel/Hardware/Buffered/Sram.lean', 'physical/buffered_sram_memory.sv'):
            path = self.root / name
            original = path.read_bytes()
            path.write_bytes(original + b'corruption\n')
            with self.subTest(source=name), self.assertRaisesRegex(RuntimeError, 'execution/admission source'):
                self.intake()
            path.write_bytes(original)


if __name__ == '__main__':
    unittest.main()
