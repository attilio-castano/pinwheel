"""Strict hardware lowering and public-port ownership/recovery helpers.

The port fixture supplies explicit completion observations; it does not execute
instructions. Emitted RTL, exact engine edges and independent peers are checked
by the separate hardware gate.
"""
from dataclasses import FrozenInstanceError, replace
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

from buffered_engine import (BufferedBlock, BufferedInstruction as I, BufferedProgram,
                             buffered_jtag, buffered_spi)
from buffered_hardware import (FORMAT, MAX_ID, BufferedHardwareHost,
    BufferedHardwareImage, BufferedHardwareTransportError, BufferedHardwareWaitTimeout,
    decode_instruction, encode_instruction, lower_buffered, pack_wire_bits)
from pinwheel_buffers import TransferError
from pinwheel_host import Host


def wire_bits(payload):
    return tuple(bool((byte >> bit) & 1) for byte in payload for bit in range(7, -1, -1))


class PublicPortFixture:
    """Command receipts and injected completions through public fields only."""
    def __init__(self):
        self.records = []
        self.state = self.fresh()
        self.words = {}
        self.idle = (0, 0)
        self.reject_command = None
        self.fail_command = None
        self.read_fault = None
        self.complete_after = None
        self.completion = None

    @staticmethod
    def fresh():
        return dict(valid=0, busy=0, retained=0, rejected=0, mode=0, pc=0,
            remaining=0, levels=0, enabled=0, tx_consumed=0, rx_length=0,
            rx_data=0, read_valid=0, read_bit=0, generation=0, transfer=0,
            exhausted=0, pending=0)

    def finish(self, bits, consumed, *, fault=False):
        self.state.update(busy=0, retained=1, mode=3 if fault else 2,
            tx_consumed=consumed, rx_length=len(bits),
            rx_data=sum(int(bit) << i for i, bit in enumerate(bits)),
            levels=self.idle[0], enabled=self.idle[1])

    def edge(self, **fields):
        self.records.append(dict(fields))
        command = fields.get('command', 0)
        if self.fail_command == command:
            self.fail_command = None
            raise OSError('Injected public transport failure')
        s = self.state
        s['rejected'] = 0
        if fields.get('initialize', 0):
            self.state = s = self.fresh()
            self.words.clear()
        elif command == self.reject_command:
            s['rejected'] = 1
        elif command == 7:
            generation, transfer = min(MAX_ID, s['generation'] + 1), s['transfer']
            self.state = s = self.fresh()
            s.update(generation=generation, transfer=transfer)
            self.words.clear()
        elif command == 1:
            if s['busy'] or s['retained']:
                s['rejected'] = 1
            else:
                if not s['pending']: self.words.clear()
                self.words[fields['address']] = fields['word']
                s.update(valid=0, pending=1)
        elif command == 2:
            count = fields['count']
            if (s['busy'] or s['retained'] or not s['pending'] or
                    not 1 <= count <= 128 or s['generation'] == MAX_ID or
                    any(index not in self.words for index in range(count))):
                s['rejected'] = 1
            else:
                self.idle = fields['idle_levels'], fields['idle_enabled']
                s.update(valid=1, pending=0, generation=s['generation'] + 1,
                         levels=self.idle[0], enabled=self.idle[1])
        elif command == 3:
            if (not s['valid'] or s['pending'] or s['busy'] or s['retained'] or
                    fields['expected_generation'] != s['generation'] or s['transfer'] == MAX_ID):
                s['rejected'] = 1
            else:
                s.update(busy=1, retained=0, mode=1, transfer=s['transfer'] + 1,
                         tx_consumed=0, rx_length=0, rx_data=0)
        elif command == 4:
            if (not s['retained'] or fields['expected_generation'] != s['generation'] or
                    fields['expected_transfer'] != s['transfer']):
                s['rejected'] = 1
            else:
                s.update(busy=0, retained=0, mode=0, tx_consumed=0, rx_length=0, rx_data=0)
        elif command == 0 and s['busy'] and self.complete_after is not None:
            self.complete_after -= 1
            if self.complete_after == 0:
                bits, consumed, fault = self.completion
                self.finish(bits, consumed, fault=fault)
        s['exhausted'] = int(s['generation'] == MAX_ID or s['transfer'] == MAX_ID)
        index = fields.get('read_index', 0)
        s['read_valid'] = int(bool(s['retained']) and index < s['rx_length'])
        s['read_bit'] = (s['rx_data'] >> index) & 1 if s['read_valid'] else 0
        if self.read_fault == index:
            s['read_valid'] = 0
        return dict(s)


class BufferedHardwareImageTests(unittest.TestCase):
    def test_spi_image_has_exact_canonical_word_fields_and_32_bit_demands(self):
        source = buffered_spi()
        image = lower_buffered(source)
        self.assertEqual((image.image_format, len(image.words), image.tx_bits,
                          image.rx_bits, image.execution_edges), (FORMAT, 66, 32, 32, 260))
        self.assertEqual(image.words[:2], (1 | 7 << 6 | 3 << 9,
                         2 | 2 << 3 | 7 << 6 | 3 << 9 | 1 << 17 | 1 << 22))
        self.assertEqual(image.words[-2:], (7 << 6 | 3 << 9, 3))
        self.assertEqual(tuple(decode_instruction(word) for word in image.words), source.instructions)
        self.assertEqual(image.program_key, source.key)
        self.assertEqual(BufferedHardwareImage.from_bytes(image.to_bytes()), image)
        with self.assertRaises(FrozenInstanceError): image.words = ()

    def test_jtag_and_nonbyte_wire_orders_pack_first_wire_bit_in_low_hardware_bit(self):
        spi = lower_buffered(buffered_spi(1))
        self.assertEqual(pack_wire_bits(spi.encode_tx(b'\x96')), 0x69)
        jtag = lower_buffered(buffered_jtag(13))
        self.assertEqual(pack_wire_bits(jtag.encode_tx(b'\x34\x12')), 0x1234)
        self.assertEqual(jtag.decode_rx(jtag.encode_tx(b'\x34\x12')), b'\x34\x12')
        with self.assertRaisesRegex(ValueError, 'padding'): jtag.encode_tx(b'\x34\x92')
        for value in range(256):
            payload = bytes((value,))
            bits = spi.encode_tx(payload)
            packed = pack_wire_bits(bits)
            self.assertEqual(tuple(bool(packed & (1 << i)) for i in range(8)), bits)
            self.assertEqual(spi.decode_rx(bits), payload)

    def test_shift_keep_and_entry_append_supported_at_duration_boundaries(self):
        for duration in (1, 256):
            for pin in range(3):
                for incoming in (None, 0, 1):
                    instruction = I('shift', duration, levels=5, enabled=3,
                                    shift_pin=pin, append_input=incoming)
                    self.assertEqual(decode_instruction(encode_instruction(instruction)), instruction)
            instruction = I('keep', duration, levels=3, enabled=2, preserve=5, append_input=1)
            self.assertEqual(decode_instruction(encode_instruction(instruction)), instruction)

    def test_reserved_and_noncanonical_words_are_rejected(self):
        for word in (1 << 24, 5, 6, 7, 3 | 1 << 3, 4 | 1 << 6,
                     3 << 22, 1 << 17, 1 << 20, 1 | 3 << 20, 2 | 1 << 20):
            with self.subTest(word=word), self.assertRaises(ValueError): decode_instruction(word)
        for word in (-1, 1 << 32, True, 1.0):
            with self.assertRaises(ValueError): decode_instruction(word)

    def test_unsupported_model_features_and_capacity_fail_before_hardware_io(self):
        port, host = PublicPortFixture(), None
        host = BufferedHardwareHost(port)
        variants = [I('shift', shift_pin=0, shift_enabled=True),
                    I('shift', shift_pin=0, shift_invert=True),
                    I('keep', preserve_enabled=1), I('drive', entry_capture=(0, 0)),
                    I('drive', 257), I('fault', outcome='timeout')]
        for instruction in variants:
            instructions = (instruction,) if instruction.kind == 'fault' else (instruction, I('halt'))
            source = BufferedProgram(instructions)
            with self.subTest(kind=instruction.kind), self.assertRaises(ValueError): host.load(source)
        reactive = BufferedProgram((), schedule=BufferedBlock((I('checked'), I('halt'))),
                                   declared_tx_bits=0, declared_rx_bits=0, max_rx_bits=0)
        for source in (reactive, buffered_spi(5), buffered_jtag(33),
                       BufferedProgram((I('drive'),) * 128 + (I('halt'),))):
            with self.assertRaises(ValueError): host.load(source)
        self.assertEqual(port.records, [])

    def test_captured_image_identity_and_declared_demands_cannot_be_replaced(self):
        image = lower_buffered(buffered_spi())
        for field, value in (('format', 'unknown'), ('program_key', '0' * 64),
                             ('image_key', '0' * 64), ('tx_bits', 31), ('rx_bits', True),
                             ('idle_levels', 0), ('wire_order', 'lsb-per-byte')):
            obj = json.loads(image.to_bytes())
            obj[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                BufferedHardwareImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['extra'] = 1
        with self.assertRaises(ValueError): BufferedHardwareImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['words'][0] ^= 1 << 3
        with self.assertRaises(ValueError): BufferedHardwareImage.from_bytes(json.dumps(obj).encode())

    def test_existing_serial_host_rejects_new_target_before_io(self):
        class NoIO:
            def advance(self, *args, **kwargs): raise AssertionError('Transport was touched')
        with self.assertRaisesRegex(ValueError, 'image format'):
            Host(NoIO()).upload(lower_buffered(buffered_spi()))


class BufferedHardwareHostTests(unittest.TestCase):
    def setUp(self):
        self.port = PublicPortFixture()
        self.host = BufferedHardwareHost(self.port)
        self.host.initialize()
        self.loaded = self.host.load(buffered_spi())

    def test_upload_writes_every_row_then_commits_versioned_exact_metadata(self):
        writes = [row for row in self.port.records if row.get('command') == 1]
        self.assertEqual([row['address'] for row in writes], list(range(66)))
        self.assertEqual(tuple(row['word'] for row in writes), self.loaded.image.words)
        self.assertEqual(self.port.records[-1], dict(command=2, count=66, idle_levels=4, idle_enabled=7))
        self.assertEqual(self.loaded.generation, 1)

    def test_start_copies_mutable_bytes_and_declares_exact_wire_data_and_reservation(self):
        payload = bytearray(b'\xa6\x53\x81\x00')
        pending = self.loaded.submit(tx=payload)
        command = self.port.records[-1]
        payload[:] = bytes(4)
        self.assertEqual(command, dict(command=3, tx_data=0x0081ca65, tx_length=32,
                                      rx_capacity=32, expected_generation=1))
        self.assertEqual((pending.identity.generation, pending.identity.transfer), (1, 1))
        count = len(self.port.records)
        with self.assertRaises(TransferError): self.loaded.submit(tx=bytes(4))
        with self.assertRaises(TransferError): self.host.load(buffered_spi())
        self.assertEqual(len(self.port.records), count)

    def test_invalid_payload_and_rx_reservation_do_not_issue_any_edge(self):
        before = len(self.port.records)
        for payload, limit in ((bytes(3), None), ('data', None), (bytes(4), 31),
                               (bytes(4), 33), (bytes(4), True)):
            with self.subTest(payload=payload, limit=limit), self.assertRaises(ValueError):
                self.loaded.submit(tx=payload, rx_limit=limit)
        self.assertEqual(len(self.port.records), before)

    def test_wait_budget_retains_pending_and_last_edge_completion_wins(self):
        pending = self.loaded.submit(tx=bytes(4))
        self.port.complete_after = 3
        self.port.completion = wire_bits(b'\x96\xa5\x55\x3c'), 32, False
        with self.assertRaises(BufferedHardwareWaitTimeout) as caught:
            pending.wait(timeout_cycles=2)
        self.assertIs(caught.exception.pending, pending)
        self.assertTrue(self.port.state['busy'])
        with self.assertRaises(TransferError): self.host.load(buffered_spi())
        pending.wait(timeout_cycles=1)
        result = pending.read()
        self.assertEqual(result.payload, b'\x96\xa5\x55\x3c')
        self.assertEqual(self.port.state['retained'], 1)
        self.assertEqual(pending.read(), result)
        indexes = [row['read_index'] for row in self.port.records if 'read_index' in row]
        self.assertEqual(indexes, list(range(32)) * 2)
        pending.release()
        self.assertEqual(self.port.records[-1], dict(command=4, expected_generation=1, expected_transfer=1))
        self.assertEqual(self.port.state['retained'], 0)
        self.assertEqual(result.payload, b'\x96\xa5\x55\x3c')

    def test_partial_fault_result_uses_indexed_prefix_without_normal_payload(self):
        pending = self.loaded.submit(tx=bytes(4))
        self.port.finish((True, False, True, True, False), 7, fault=True)
        result = pending.read()
        self.assertEqual((result.outcome, result.tx_consumed_bits, result.rx_valid_bits,
                          result.payload, result.raw_rx_bits),
                         ('fault', 7, 5, None, (True, False, True, True, False)))
        self.assertEqual(pending.read(), result)
        pending.release()

    def test_decode_failure_retains_exact_completion_until_release(self):
        pending = self.loaded.submit(tx=bytes(4))
        self.port.finish((True,) * 31, 32)
        with self.assertRaisesRegex(ValueError, 'complete program result'): pending.read()
        self.assertIs(self.host._pending, pending)
        self.assertEqual(self.port.state['retained'], 1)
        pending.release()
        pending = self.loaded.submit(tx=bytes(4))
        self.port.finish((True,) * 32, 31)
        with self.assertRaisesRegex(ValueError, 'declared TX'): pending.read()
        self.assertEqual(self.port.state['retained'], 1)
        pending.release()

    def test_invalid_indexed_window_fails_without_releasing_or_decoding(self):
        pending = self.loaded.submit(tx=bytes(4))
        self.port.finish((True,) * 32, 32)
        self.port.read_fault = 17
        with self.assertRaisesRegex(RuntimeError, 'bit window'): pending.read()
        self.assertEqual(self.port.state['retained'], 1)
        self.assertIs(self.host._pending, pending)
        self.port.read_fault = None
        pending.release()

    def test_warm_reset_and_cold_initialize_invalidate_old_handles_before_io(self):
        pending = self.loaded.submit(tx=bytes(4))
        old = pending.identity
        self.host.reset()
        self.assertEqual((self.port.state['generation'], self.port.state['transfer']), (2, 1))
        before = len(self.port.records)
        for action in (pending.read, pending.release, lambda: self.loaded.submit(tx=bytes(4))):
            with self.assertRaises(TransferError): action()
        self.assertEqual(len(self.port.records), before)
        self.host.initialize()
        new = self.host.load(buffered_spi()).submit(tx=bytes(4))
        self.assertEqual((new.identity.generation, new.identity.transfer), (old.generation, old.transfer))
        self.assertNotEqual(new.identity.epoch, old.epoch)
        with self.assertRaises(TransferError): pending.read()

    def test_wrong_host_or_transfer_handle_cannot_issue_release(self):
        pending = self.loaded.submit(tx=bytes(4))
        self.port.finish((False,) * 32, 32)
        before = len(self.port.records)
        mutant = replace(pending, identity=replace(pending.identity, transfer=2))
        with self.assertRaises(TransferError): mutant.release()
        other = replace(pending, host=BufferedHardwareHost(PublicPortFixture()))
        with self.assertRaises(TransferError): other.release()
        self.assertEqual(len(self.port.records), before)
        pending.release()

    def test_saturating_counters_require_new_cold_epoch_without_reuse(self):
        self.port.state['transfer'] = MAX_ID - 1
        pending = self.loaded.submit(tx=bytes(4))
        self.assertEqual(pending.identity.transfer, MAX_ID)
        self.port.finish((False,) * 32, 32)
        pending.release()
        before = len(self.port.records)
        with self.assertRaisesRegex(TransferError, 'identities are exhausted'):
            self.loaded.submit(tx=bytes(4))
        self.assertEqual(len(self.port.records), before + 1)  # status only
        self.port.state['generation'] = MAX_ID
        with self.assertRaisesRegex(TransferError, 'generation is exhausted'):
            self.host.load(buffered_spi())
        self.host.reset()
        self.assertEqual((self.port.state['generation'], self.port.state['transfer']), (MAX_ID, MAX_ID))
        self.host.initialize()
        fresh = self.host.load(buffered_spi()).submit(tx=bytes(4))
        self.assertEqual(fresh.identity.transfer, 1)
        self.assertGreater(fresh.identity.epoch, pending.identity.epoch)

    def test_failed_start_delivery_keeps_a_recoverable_pending_handle(self):
        self.port.fail_command = 3
        with self.assertRaises(BufferedHardwareTransportError) as caught:
            self.loaded.submit(tx=bytes(4))
        pending = caught.exception.pending
        self.assertIs(self.host._pending, pending)
        self.assertIsInstance(caught.exception.cause, OSError)
        with self.assertRaises(TransferError): pending.wait(timeout_cycles=0)
        self.host.reset()
        with self.assertRaises(TransferError): pending.read()

    def test_confirmed_start_rejection_leaves_no_owned_handle(self):
        self.port.reject_command = 3
        with self.assertRaisesRegex(TransferError, 'rejected the owned START'):
            self.loaded.submit(tx=bytes(4))
        self.assertIsNone(self.host._pending)
        self.assertEqual((self.port.state['busy'], self.port.state['retained']), (0, 0))


if __name__ == '__main__':
    unittest.main()
