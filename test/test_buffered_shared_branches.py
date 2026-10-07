"""Shared descriptor source binding and upload/ownership command receipts.

The port fixture acknowledges public loading and injects retained completions;
it does not execute instructions or establish hardware transition equivalence.
"""
from dataclasses import FrozenInstanceError
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'test'))

from buffered_engine import (BufferedBlock as Block, BufferedInstruction as I,
    BufferedRepeat as Repeat)
from buffered_hardware import (MAX_ID, BufferedHardwareWaitTimeout,
    LoadedBufferedHardware, PendingBufferedHardware)
from buffered_reactive_hardware import (BufferedReactiveHardwareResult, compact_i2c_read,
    compact_jtag, compact_spi, lower_reactive)
from buffered_shared_branches import (ALLOCATED_BANK_BITS, BRANCH_CAPACITY,
    BRANCH_INDEX_WIDTH, DECLARED_STATE_BITS, FORMAT, ROW_WIDTH,
    BufferedSharedBranchesHost, BufferedSharedBranchesImage, lower_shared_branches)
from pinwheel_buffers import TransferError
from test_buffered_reactive_hardware import ReactivePortFixture, source


class SharedBranchesPortFixture(ReactivePortFixture):
    """Receipt-only model of a joint row and dictionary upload epoch."""
    def __init__(self):
        self.dictionary = {}
        super().__init__()

    def edge(self, **fields):
        command = fields.get('command', 0)
        if fields.get('initialize') or command == 7:
            self.dictionary.clear()
        if command == 6:
            self.records.append(dict(fields))
            s = self.state
            s['rejected'] = 0
            if self.fail_command == command:
                self.fail_command = None
                raise OSError('Injected public transport failure')
            if (s['busy'] or s['retained'] or command == self.reject_command or
                    not 0 <= fields['address'] < BRANCH_CAPACITY):
                s['rejected'] = 1
            else:
                if not s['pending']:
                    self.words.clear()
                    self.controls.clear()
                    self.branches.clear()
                    self.dictionary.clear()
                self.dictionary[fields['address']] = fields['branch']
                s.update(valid=0, pending=1)
            return dict(s)
        if command == 2 and len(self.dictionary) != BRANCH_CAPACITY:
            self.records.append(dict(fields))
            self.state['rejected'] = 1
            return dict(self.state)
        return super().edge(**fields)


class SharedBranchesImageTests(unittest.TestCase):
    def test_i2c_dictionary_shares_entire_descriptors_and_uploads_fixed_bank(self):
        reactive = lower_reactive(compact_i2c_read())
        image = lower_shared_branches(compact_i2c_read())
        self.assertEqual((image.image_format, len(image.words), image.virtual_span,
            image.tx_bits, image.rx_bits, image.rx_reservation_bits), (FORMAT, 50, 270, 24, 32, 32))
        self.assertEqual((ROW_WIDTH, BRANCH_INDEX_WIDTH, BRANCH_CAPACITY,
            ALLOCATED_BANK_BITS, DECLARED_STATE_BITS), (92, 4, 16, 6784, 7183))
        self.assertEqual(image.words, reactive.words)
        self.assertEqual(image.controls, reactive.controls)
        self.assertEqual(image.branches, reactive.branches)
        self.assertEqual(image.program_key, reactive.program_key)
        self.assertNotEqual(image.key, reactive.key)
        self.assertEqual(image.branch_table, (0, next(b for b in reactive.branches if b)) + (0,) * 14)
        self.assertEqual(image.branch_indices.count(0), 48)
        self.assertEqual(image.branch_indices.count(1), 2)
        self.assertEqual((image.storage()['branch_table_bits'], image.storage()['branch_index_bits'],
            image.storage()['uploaded_bits'], image.distinct_branches), (896, 200, 5496, 2))
        self.assertEqual(BufferedSharedBranchesImage.from_bytes(image.to_bytes()), image)
        with self.assertRaises(FrozenInstanceError): image.branch_table = ()

    def test_spi_and_jtag_have_one_descriptor_but_pay_fixed_dictionary_upload(self):
        for code, rows, bits in ((compact_spi(4), 4, 1264), (compact_jtag(17), 20, 2736)):
            image = lower_shared_branches(code)
            self.assertEqual((len(image.words), image.distinct_branches,
                image.storage()['uploaded_bits']), (rows, 1, bits))
            self.assertEqual(image.branch_table, (0,) * 16)
            self.assertEqual(image.branch_indices, (0,) * rows)
            self.assertEqual(image.encode_tx(b'\x96\xa5\x3c\xc3' if rows == 4 else b'\x34\x12\x01'),
                lower_reactive(code).encode_tx(b'\x96\xa5\x3c\xc3' if rows == 4 else b'\x34\x12\x01'))

    def test_first_use_order_does_not_reserve_zero_at_index_zero(self):
        image = lower_shared_branches(source(Block((I('checked', finish=1), I('halt')))))
        self.assertNotEqual(image.branch_table[0], 0)
        self.assertEqual(image.branch_table[1:], (0,) * 15)
        self.assertEqual(image.branch_indices, (0, 1))
        self.assertEqual(image.branches, lower_reactive(image.source).branches)

    def test_sixteen_distinct_descriptors_fit_without_an_implicit_zero_slot(self):
        image = lower_shared_branches(source(Block(tuple(I('checked', finish=k) for k in range(16)))))
        self.assertEqual(image.distinct_branches, 16)
        self.assertEqual(image.branch_indices, tuple(range(16)))
        self.assertEqual(len(set(image.branch_table)), 16)
        self.assertNotIn(0, image.branch_table)
        self.assertEqual(BufferedSharedBranchesImage.from_bytes(image.to_bytes()), image)

    def test_dictionary_bound_is_additional_to_reactive_program_bounds(self):
        for count in (17, 64):
            leaves = tuple(I('checked', finish=(0, 2 * k, 2 * k + 1)) for k in range(count))
            code = Block(leaves) if count == 17 else Repeat(4, Repeat(4, Block(leaves)))
            program = source(code)
            reactive = lower_reactive(program)
            self.assertEqual(len(set(reactive.branches)), count)
            if count == 64:
                self.assertEqual((len(reactive.words), reactive.virtual_span, code.nodes), (64, 1024, 129))
            with self.assertRaisesRegex(ValueError, '16 distinct branch'):
                lower_shared_branches(program)

    def test_remapped_order_preserving_expanded_semantics_is_noncanonical(self):
        image = lower_shared_branches(compact_i2c_read())
        obj = json.loads(image.to_bytes())
        obj['branch_table'][0], obj['branch_table'][1] = obj['branch_table'][1], obj['branch_table'][0]
        obj['branch_indices'] = [1 - index for index in obj['branch_indices']]
        self.assertEqual(tuple(obj['branch_table'][index] for index in obj['branch_indices']), image.branches)
        with self.assertRaisesRegex(ValueError, 'canonical source lowering'):
            BufferedSharedBranchesImage.from_bytes(json.dumps(obj).encode())

    def test_ref_table_unused_padding_word_loop_and_source_mutations_reject(self):
        image = lower_shared_branches(compact_i2c_read())
        mutations = [('branch_indices', 0, 1), ('branch_indices', 0, 16),
            ('branch_indices', 0, True), ('branch_table', 1, 0),
            ('branch_table', 2, image.branch_table[1]), ('branch_table', 1, True),
            ('branch_table', 1, image.branch_table[1] | (1 << 54)),
            ('words', 0, image.words[0] ^ (1 << 3)),
            ('controls', 0, image.controls[0] ^ 4)]
        for field, index, value in mutations:
            obj = json.loads(image.to_bytes()); obj[field][index] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                BufferedSharedBranchesImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['source']['protocol'] = 'changed'
        with self.assertRaises(ValueError): BufferedSharedBranchesImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['words'][0] = True
        with self.assertRaises(ValueError): BufferedSharedBranchesImage.from_bytes(json.dumps(obj).encode())

    def test_metadata_lengths_and_schema_are_strict(self):
        image = lower_shared_branches(compact_spi())
        for key, value in [('format', 'wrong'), ('image_key', '0' * 64), ('program_key', '0' * 64),
            ('physical_count', True), ('virtual_span', 65), ('tx_bits', True),
            ('rx_bits', 31), ('rx_reservation_bits', 31), ('distinct_branches', True),
            ('branch_table', [0] * 15), ('branch_table', [0] * 17), ('branch_indices', []),
            ('words', []), ('controls', {})]:
            obj = json.loads(image.to_bytes()); obj[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                BufferedSharedBranchesImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['extra'] = 1
        with self.assertRaises(ValueError): BufferedSharedBranchesImage.from_bytes(json.dumps(obj).encode())
        with self.assertRaises(ValueError): BufferedSharedBranchesImage.from_bytes(image.to_bytes().decode())


class SharedBranchesHostTests(unittest.TestCase):
    def setUp(self):
        self.port = SharedBranchesPortFixture()
        self.host = BufferedSharedBranchesHost(self.port)
        self.host.initialize()
        self.loaded = self.host.load(source(Block((I('checked'), I('halt'))), tx=2, rx=1, maximum=4))

    def test_complete_dictionary_precedes_rows_and_same_commit_contract(self):
        self.assertIs(type(self.loaded), LoadedBufferedHardware)
        image = self.loaded.image
        writes = [record for record in self.port.records if record.get('command') in (1, 6)]
        expected = [dict(command=6, address=k, branch=b) for k, b in enumerate(image.branch_table)]
        expected += [dict(command=1, address=k, word=w, control=c, branch=i)
            for k, (w, c, i) in enumerate(zip(image.words, image.controls, image.branch_indices, strict=True))]
        self.assertEqual(writes, expected)
        self.assertEqual(self.port.records[-1], dict(command=2, count=2, virtual_span=2,
            idle_levels=0, idle_enabled=7))

    def test_invalid_source_or_tampered_image_fails_before_transport_io(self):
        count = len(self.port.records)
        program = source(Block(tuple(I('checked', finish=k) for k in range(17))))
        with self.assertRaises(ValueError): self.host.load(program)
        with self.assertRaises(ValueError): self.host.load(lower_reactive(compact_spi()))
        with self.assertRaises(ValueError): self.host.load(object())
        image = lower_shared_branches(compact_i2c_read())
        object.__setattr__(image, 'branch_indices', (1,) + image.branch_indices[1:])
        with self.assertRaises(ValueError): self.host.load(image)
        self.assertEqual(len(self.port.records), count)

    def test_mutable_payload_is_copied_and_maximum_reservation_is_used(self):
        count = len(self.port.records)
        for limit in (0, 1, 3, 33, True):
            with self.assertRaises(ValueError): self.loaded.submit(tx=b'\x03', rx_limit=limit)
        self.assertEqual(len(self.port.records), count)
        payload = bytearray(b'\x03')
        pending = self.loaded.submit(tx=payload); payload[0] = 0
        self.assertIs(type(pending), PendingBufferedHardware)
        self.assertEqual(self.port.records[-1], dict(command=3, tx_data=3, tx_length=2,
            rx_capacity=4, expected_generation=1))

    def test_wait_timeout_preserves_pending_and_repeated_retained_reads(self):
        pending = self.loaded.submit(tx=b'\x03')
        with self.assertRaises(BufferedHardwareWaitTimeout) as error:
            pending.wait(timeout_cycles=0)
        self.assertIs(error.exception.pending, pending)
        self.assertIs(self.host._pending, pending)
        self.port.finish((True,), 2, scratch=0x8001)
        pending.wait(timeout_cycles=1)
        result = pending.read()
        self.assertIs(type(result), BufferedReactiveHardwareResult)
        self.assertEqual((result.outcome, result.payload, result.scratch), ('complete', b'\x01', 0x8001))
        self.assertEqual(pending.read(), result)
        count = len(self.port.records)
        with self.assertRaises(TransferError): self.host.load(compact_spi())
        with self.assertRaises(TransferError): self.loaded.submit(tx=b'\x03')
        self.assertEqual(len(self.port.records), count)
        pending.release()
        self.assertIsNone(self.host._pending)
        self.assertEqual(result.scratch, 0x8001)

    def test_fault_and_timeout_return_prefix_without_payload(self):
        for outcome in ('fault', 'timeout'):
            pending = self.loaded.submit(tx=b'\x03')
            self.port.finish((True, False, True, False), 1, outcome=outcome, scratch=5)
            result = pending.read()
            self.assertEqual((result.outcome, result.payload, result.raw_rx_bits,
                result.tx_consumed_bits, result.rx_valid_bits, result.scratch),
                (outcome, None, (True, False, True, False), 1, 4, 5))
            pending.release()

    def test_loading_again_uploads_zero_padding_and_invalidates_old_handle(self):
        old = self.host.load(compact_i2c_read())
        self.assertNotEqual(self.port.dictionary[1], 0)
        loaded = self.host.load(compact_spi(1))
        self.assertEqual(self.port.dictionary, dict(enumerate((0,) * 16)))
        count = len(self.port.records)
        with self.assertRaises(TransferError): old.submit(tx=b'\x00\x00\x00')
        self.assertEqual(len(self.port.records), count)
        self.assertEqual(loaded.generation, 3)

    def test_dictionary_upload_rejection_and_exhaustion_do_not_create_handle(self):
        self.port.reject_command = 6
        with self.assertRaisesRegex(TransferError, 'dictionary upload'):
            self.host.load(compact_spi())
        self.assertIsNone(self.host._image)
        self.assertIsNone(self.host._generation)
        self.port.reject_command = None
        self.port.state['generation'] = MAX_ID
        count = len(self.port.records)
        with self.assertRaisesRegex(TransferError, 'generation is exhausted'):
            self.host.load(compact_spi())
        self.assertEqual(len(self.port.records), count + 1)
        self.assertEqual(self.port.records[-1], dict(command=0))


if __name__ == '__main__':
    unittest.main()
