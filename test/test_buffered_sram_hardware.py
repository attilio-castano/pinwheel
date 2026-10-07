"""SRAM image source binding and owned command receipts, not array execution."""
from dataclasses import FrozenInstanceError
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'test'))

from buffered_engine import BufferedBlock as Block, BufferedInstruction as I
from buffered_hardware import BufferedHardwareWaitTimeout
from buffered_reactive_hardware import compact_i2c_read, compact_jtag, compact_spi
from buffered_shared_branches import BufferedSharedBranchesImage, lower_shared_branches
from buffered_sram_hardware import (ALLOCATED_SRAM_BITS, DECLARED_CONTROLLER_STATE_BITS,
    FORMAT, BufferedSramHardwareHost, BufferedSramHardwareImage, lower_sram)
from pinwheel_buffers import TransferError
from test_buffered_reactive_hardware import source
from test_buffered_shared_branches import SharedBranchesPortFixture


class BufferedSramImageTests(unittest.TestCase):
    def test_same_source_and_commands_have_distinct_target_identity(self):
        for code in (compact_spi(4), compact_jtag(17), compact_i2c_read(4)):
            image, shared = lower_sram(code), lower_shared_branches(code)
            self.assertEqual((image.words, image.controls, image.branch_indices,
                image.branch_table, image.program_key), (shared.words, shared.controls,
                shared.branch_indices, shared.branch_table, shared.program_key))
            self.assertEqual(image.image_format, FORMAT)
            self.assertNotEqual(image.key, shared.key)
            self.assertEqual(image.storage()['uploaded_bits'], shared.storage()['uploaded_bits'])
            self.assertEqual(BufferedSramHardwareImage.from_bytes(image.to_bytes()), image)
            with self.assertRaises(ValueError): BufferedSramHardwareImage.from_bytes(shared.to_bytes())
            with self.assertRaises(ValueError): BufferedSharedBranchesImage.from_bytes(image.to_bytes())

    def test_controller_geometry_and_replication_are_explicit(self):
        image = lower_sram(compact_spi(1))
        self.assertEqual((ALLOCATED_SRAM_BITS, DECLARED_CONTROLLER_STATE_BITS), (8192, 3151))
        storage = image.storage()
        self.assertEqual((storage['declared_controller_state_bits'],
            storage['allocated_instruction_sram_bits'], storage['instruction_sram_copies'],
            storage['instruction_sram_words'], storage['instruction_sram_word_bits'],
            storage['allocated_row_metadata_register_bits'],
            storage['start_instruction_register_bits']), (3151, 8192, 2, 64, 64, 1792, 64))
        with self.assertRaises(FrozenInstanceError): image.words = ()

    def test_first_use_nonzero_descriptor_and_full_capacity_are_inherited(self):
        image = lower_sram(source(Block(tuple(I('checked', finish=k) for k in range(16)))))
        self.assertEqual(image.branch_indices, tuple(range(16)))
        self.assertNotIn(0, image.branch_table)
        with self.assertRaisesRegex(ValueError, '16 distinct branch'):
            lower_sram(source(Block(tuple(I('checked', finish=k) for k in range(17)))))

    def test_strict_reconstruction_rejects_schema_and_identity_mutations(self):
        image = lower_sram(compact_i2c_read())
        for field, value in (('format', 'wrong'), ('program_key', '0' * 64),
                ('image_key', '0' * 64), ('physical_count', True),
                ('distinct_branches', True), ('virtual_span', image.virtual_span + 1)):
            obj = json.loads(image.to_bytes()); obj[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                BufferedSramHardwareImage.from_bytes(json.dumps(obj).encode())
        for field, value in (('words', True), ('controls', True), ('branch_indices', True),
                ('branch_table', True)):
            obj = json.loads(image.to_bytes()); obj[field][0] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                BufferedSramHardwareImage.from_bytes(json.dumps(obj).encode())


class BufferedSramHostTests(unittest.TestCase):
    def setUp(self):
        self.port = SharedBranchesPortFixture()
        self.host = BufferedSramHardwareHost(self.port)
        self.host.initialize()

    def test_load_keeps_dictionary_first_public_upload_and_sram_receipt(self):
        image = lower_sram(compact_spi(1))
        loaded = self.host.load(image)
        self.assertEqual(loaded.image, image)
        writes = [v for v in self.port.records if v.get('command') in (1, 6)]
        expected = [dict(command=6, address=k, branch=b) for k, b in enumerate(image.branch_table)]
        expected += [dict(command=1, address=k, word=w, control=c, branch=i)
            for k, (w, c, i) in enumerate(zip(image.words, image.controls,
                image.branch_indices, strict=True))]
        self.assertEqual(writes, expected)

    def test_wrong_target_or_tampering_rejects_before_io(self):
        before = len(self.port.records)
        with self.assertRaises(ValueError): self.host.load(lower_shared_branches(compact_spi()))
        image = lower_sram(compact_i2c_read())
        object.__setattr__(image, 'words', (image.words[0] ^ 8,) + image.words[1:])
        with self.assertRaises(ValueError): self.host.load(image)
        self.assertEqual(len(self.port.records), before)

    def test_pending_timeout_and_retained_prefix_keep_owned_lifecycle(self):
        loaded = self.host.load(compact_spi(1))
        data = bytearray(b'\x96')
        pending = loaded.submit(tx=data); data[0] = 0
        expected = sum(int(bit) << k for k, bit in enumerate(loaded.image.encode_tx(b'\x96')))
        self.assertEqual(self.port.records[-1]['tx_data'], expected)
        with self.assertRaises(BufferedHardwareWaitTimeout) as timeout:
            pending.wait(timeout_cycles=0)
        self.assertIs(timeout.exception.pending, pending)
        self.port.finish((True, False), 3, outcome='fault', scratch=1)
        result = pending.read()
        self.assertEqual((result.outcome, result.payload, result.raw_rx_bits,
            result.tx_consumed_bits, result.scratch), ('fault', None, (True, False), 3, 1))
        with self.assertRaises(TransferError): self.host.load(compact_spi())
        pending.release()
        self.assertEqual(result.program_key, loaded.image.program_key)


if __name__ == '__main__':
    unittest.main()
