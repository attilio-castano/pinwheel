"""Reactive source binding, public host ownership and START sampler history.

The command fixture injects completions through public ports; it does not execute
the circuit. Actual phase/counter/datapath execution belongs to the separate
Lean/RTL gate. Sampler tests below exercise the existing buffered engine itself.
"""
from dataclasses import FrozenInstanceError, replace
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'test'))

from buffered_engine import (BufferedBlock as Block, BufferedEngine, BufferedInstruction as I,
    BufferedProgram, BufferedRepeat as Repeat, BufferedSequence as Sequence)
from buffered_hardware import (BufferedHardwareResult, BufferedHardwareWaitTimeout,
    LoadedBufferedHardware, PendingBufferedHardware)
from buffered_reactive_hardware import (BRANCH_WIDTH, CONTROL_WIDTH, FORMAT, ROW_WIDTH,
    BufferedReactiveHardwareHost, BufferedReactiveHardwareImage, BufferedReactiveHardwareResult,
    ReactiveBranch, ReactiveEndpoint, compact_i2c_read, compact_jtag, compact_spi,
    decode_branch, decode_control, decode_endpoint, decode_reactive_instruction,
    encode_branch, encode_endpoint, encode_reactive_instruction, lower_reactive, register_read_tx)
from pinwheel_buffers import TransferError, TransferSlot
from test_buffered_counted_hardware import CountedPortFixture


def source(code, tx=0, rx=0, maximum=None):
    return BufferedProgram((), schedule=code, declared_tx_bits=tx, declared_rx_bits=rx,
        max_rx_bits=rx if maximum is None else maximum)


class ReactivePortFixture(CountedPortFixture):
    """Command receipts and injected retained data, with no instruction oracle."""
    def __init__(self):
        self.branches = {}
        self.mutate_read = None
        super().__init__()

    @staticmethod
    def fresh():
        return dict(CountedPortFixture.fresh(), phase=0, wait_left=0, scratch=0)

    def finish(self, bits, consumed, *, outcome='complete', scratch=0, fault=False):
        super().finish(bits, consumed, fault=fault or outcome != 'complete')
        self.state.update(phase={'complete': 5, 'timeout': 6, 'fault': 7}[outcome], scratch=scratch)

    def edge(self, **fields):
        pending = self.state['pending']
        result = super().edge(**fields)
        command = fields.get('command', 0)
        if fields.get('initialize', 0) or command == 7:
            self.branches.clear()
        elif command == 1 and not result['rejected']:
            if not pending:
                self.branches.clear()
            self.branches[fields['address']] = fields['branch']
        elif command == 3 and not result['rejected']:
            self.state.update(phase=1, scratch=0)
        elif command == 4 and not result['rejected']:
            self.state.update(phase=0, scratch=0)
        result = dict(self.state)
        if self.mutate_read is not None and fields.get('read_index') == 1:
            self.mutate_read(result)
        return result


class ReactiveHardwareImageTests(unittest.TestCase):
    def test_i2c_footprint_includes_instruction_loop_and_branch_descriptors(self):
        image = lower_reactive(compact_i2c_read())
        self.assertEqual((image.image_format, len(image.words), image.virtual_span,
            image.tx_bits, image.rx_bits, image.rx_reservation_bits), (FORMAT, 50, 270, 24, 32, 32))
        self.assertEqual((ROW_WIDTH, CONTROL_WIDTH, BRANCH_WIDTH), (144, 24, 56))
        self.assertEqual((image.storage()['stored_nodes'], image.storage()['physical_rows'],
            image.storage()['instruction_bits'], image.storage()['control_bits'],
            image.storage()['branch_bits'], image.storage()['uploaded_bits']),
            (105, 50, 3200, 1200, 2800, 7200))
        self.assertEqual(BufferedReactiveHardwareImage.from_bytes(image.to_bytes()), image)
        self.assertEqual(len([word for word in image.branches if word]), 2)
        for word in image.branches:
            branch = decode_branch(word)
            if branch.finish:
                self.assertEqual(branch.finish, 2)
                self.assertEqual(branch.yes, ReactiveEndpoint(False, 265, 45, 0, 0))
                self.assertEqual(branch.no, ReactiveEndpoint(next=True))
        with self.assertRaises(FrozenInstanceError): image.branches = ()

    def test_exact_instruction_bit_fields_include_open_drain_and_scratch(self):
        shift = I('shift', 256, levels=5, enabled=3, shift_pin=2,
            append_input=1, shift_enabled=True, shift_invert=True, entry_capture=(1, 15))
        word = (1 | 5 << 3 | 3 << 6 | 255 << 9 | 2 << 20 | 2 << 22 |
                1 << 24 | 1 << 25 | 63 << 29)
        self.assertEqual(encode_reactive_instruction(shift), word)
        self.assertEqual(decode_reactive_instruction(word), shift)
        checked = I('checked', 256, enabled=2, preserve=5, preserve_enabled=6,
            entry_capture=(0, 4), terminal_capture=(1, 3), check_mask=3, check_value=1)
        self.assertEqual(decode_reactive_instruction(encode_reactive_instruction(checked)), checked)
        wait = I('wait', wait_input=1, wait_level=False, budget=256, preserve_enabled=2)
        qualify = I('qualify', 256, check_mask=3, check_value=2, budget=256, append_input=1)
        for instruction in (wait, qualify, I('halt'), I('fault'), I('fault', outcome='timeout')):
            self.assertEqual(decode_reactive_instruction(encode_reactive_instruction(instruction)), instruction)
        self.assertEqual(encode_reactive_instruction(I('fault', outcome='timeout')), 4 | 1 << 55)

    def test_reserved_and_inactive_instruction_fields_reject_before_model_construction(self):
        drive = encode_reactive_instruction(I('drive'))
        checked = encode_reactive_instruction(I('checked'))
        wait = encode_reactive_instruction(I('wait'))
        invalid = [1 << 56, 3 | 1 << 6, 3 | 1 << 55, 4 | 1 << 29,
            drive | 1 << 20, drive | 1 << 24, drive | 1 << 26,
            drive | 2 << 29, checked | 1 << 45, checked | 1 << 47,
            wait | 1 << 9, wait | 1 << 29, wait | 1 << 41,
            1 | 3 << 20, drive | 3 << 22]
        for word in invalid:
            with self.subTest(word=word), self.assertRaises(ValueError): decode_reactive_instruction(word)
        for word in (True, -1, 1 << 64):
            with self.assertRaises(ValueError): decode_reactive_instruction(word)

    def test_endpoint_and_branch_layout_are_canonical(self):
        endpoint = ReactiveEndpoint(False, 1023, 63, 7, 6)
        packed = 1023 << 1 | 63 << 11 | 7 << 18 | 6 << 21
        self.assertEqual(encode_endpoint(endpoint), packed)
        self.assertEqual(decode_endpoint(packed), endpoint)
        branch = ReactiveBranch(2, 15, endpoint, ReactiveEndpoint(next=True))
        self.assertEqual(encode_branch(branch), 2 | 15 << 2 | packed << 6 | 1 << 30)
        self.assertEqual(decode_branch(encode_branch(branch)), branch)
        for word in (3, 1 << 2, 1 << 6, 1 | 1 << 6, 1 | 1 << 30,
                     2 | (1 | 2) << 6, 2 | (65 << 11) << 6, 1 << 54):
            with self.subTest(word=word), self.assertRaises(ValueError): decode_branch(word)

    def test_nested_absolute_coordinates_and_dynamic_next_are_source_derived(self):
        loop = Repeat(3, Repeat(8, Block((I('drive'), I('checked', finish=(2, 37, None))))))
        image = lower_reactive(source(Sequence((Block((I('checked', finish=47),)), loop,
                                                Block((I('halt'),))))))
        branch = decode_branch(image.branches[0])
        # Virtual 47 is outer iteration2, inner iteration7, first body leaf.
        self.assertEqual(branch.yes, ReactiveEndpoint(False, 47, 1, 2, 7))
        repeated = decode_branch(image.branches[2])
        self.assertEqual(repeated.yes, ReactiveEndpoint(False, 37, 1, 2, 2))
        self.assertTrue(repeated.no.next)
        self.assertEqual((len(image.words), image.virtual_span), (4, 50))

    def test_terminal_inside_repeat_runaway_and_invalid_absolute_are_admitted(self):
        terminal = lower_reactive(source(Repeat(8, Block((I('fault', outcome='timeout'),)))))
        self.assertEqual((terminal.virtual_span, decode_control(terminal.controls[0]).depth), (8, 1))
        runaway = lower_reactive(source(Block((I('checked', append_input=0, finish=0),)), rx=0, maximum=32))
        self.assertEqual((runaway.rx_bits, runaway.rx_reservation_bits), (0, 32))
        invalid = lower_reactive(source(Block((I('checked', finish=1023),))))
        self.assertEqual(decode_branch(invalid.branches[0]).yes, ReactiveEndpoint(False, 1023, 64, 0, 0))

    def test_full_span_last_branch_keeps_eager_next_normalization_fixture(self):
        leaves = (I('checked', finish=1023),) + (I('drive'),) * 14 + (I('checked', finish=(0, 0, None)),)
        image = lower_reactive(source(Repeat(8, Repeat(8, Block(leaves)))))
        self.assertEqual((image.virtual_span, len(image.words)), (1024, 16))
        self.assertEqual(decode_branch(image.branches[0]).yes,
                         ReactiveEndpoint(False, 1023, 15, 7, 7))
        self.assertEqual(decode_branch(image.branches[-1]).no, ReactiveEndpoint(next=True))

    def test_source_binding_rejects_effect_loop_and_target_coordinate_mutation(self):
        image = lower_reactive(compact_i2c_read())
        branch_index = next(i for i, word in enumerate(image.branches) if word)
        mutations = [('words', 0, 1 << 3), ('controls', 3, 1 << 8),
                     ('branches', branch_index, 1 << (6 + 11)),
                     ('branches', branch_index, 1 << (6 + 18))]
        for key, index, mask in mutations:
            obj = json.loads(image.to_bytes()); obj[key][index] ^= mask
            with self.subTest(field=key), self.assertRaisesRegex(ValueError, 'canonical source lowering'):
                BufferedReactiveHardwareImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['source']['protocol'] = 'different'
        with self.assertRaisesRegex(ValueError, 'original source identity'):
            BufferedReactiveHardwareImage.from_bytes(json.dumps(obj).encode())
        stale = compact_i2c_read(); object.__setattr__(stale, '_key', '0' * 64)
        with self.assertRaisesRegex(ValueError, 'original source identity'): lower_reactive(stale)

    def test_capture_schema_demands_and_identity_metadata_are_strict(self):
        image = lower_reactive(compact_spi())
        for key, value in [('format', 'wrong'), ('image_key', '0' * 64),
                           ('physical_count', True), ('virtual_span', 65),
                           ('tx_bits', 31), ('rx_bits', True), ('rx_reservation_bits', 31)]:
            obj = json.loads(image.to_bytes()); obj[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                BufferedReactiveHardwareImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['branches'][0] = True
        with self.assertRaises(ValueError): BufferedReactiveHardwareImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['extra'] = 1
        with self.assertRaises(ValueError): BufferedReactiveHardwareImage.from_bytes(json.dumps(obj).encode())

    def test_capacity_and_unsupported_defaults_reject_without_transport_edges(self):
        port = ReactivePortFixture(); host = BufferedReactiveHardwareHost(port)
        invalid = [source(Block((I('drive'),) * 65)), source(Block((I('shift', shift_pin=0),)), tx=33),
                   source(Block((I('drive'),)), rx=33), source(Block((I('drive'),)), maximum=33),
                   source(Block((I('checked', budget=2),))),
                   source(Block((I('drive', wait_level=False),))),
                   source(Block((I('halt', outcome='timeout'),)))]
        for code in invalid:
            with self.assertRaises(ValueError): host.load(code)
        with self.assertRaises(ValueError): host.load(object())
        with self.assertRaises(ValueError): compact_i2c_read(5)
        self.assertEqual(port.records, [])

    def test_old_compact_frontends_keep_wire_order_and_nonbyte_padding(self):
        spi = lower_reactive(compact_spi(4)); jtag = lower_reactive(compact_jtag(17))
        self.assertEqual((len(spi.words), len(jtag.words)), (4, 20))
        for image, payload in ((spi, b'\x96\xa5\x3c\xc3'), (jtag, b'\x34\x12\x01')):
            self.assertEqual(image.decode_rx(image.encode_tx(payload)), payload)
        with self.assertRaisesRegex(ValueError, 'padding'): jtag.encode_tx(b'\x34\x12\x03')
        self.assertEqual(register_read_tx(127, 255), b'\xfe\xff\xff')


class ReactiveHardwareHostTests(unittest.TestCase):
    def setUp(self):
        self.port = ReactivePortFixture()
        self.host = BufferedReactiveHardwareHost(self.port)
        self.host.initialize()
        self.loaded = self.host.load(source(Block((I('checked'), I('halt'))), tx=2, rx=1, maximum=4))

    def test_shared_lifecycle_uploads_each_three_part_row_atomically(self):
        self.assertIs(type(self.loaded), LoadedBufferedHardware)
        image = self.loaded.image
        writes = [row for row in self.port.records if row.get('command') == 1]
        self.assertEqual(writes, [dict(command=1, address=i, word=image.words[i],
            control=image.controls[i], branch=image.branches[i]) for i in range(2)])
        self.assertEqual(self.port.records[-1], dict(command=2, count=2, virtual_span=2,
                                                   idle_levels=0, idle_enabled=7))

    def test_maximum_reservation_and_mutable_tx_snapshot_precede_start(self):
        count = len(self.port.records)
        for limit in (0, 1, 3, 33, True):
            with self.assertRaises(ValueError): self.loaded.submit(tx=b'\x03', rx_limit=limit)
        self.assertEqual(len(self.port.records), count)
        payload = bytearray(b'\x03')
        pending = self.loaded.submit(tx=payload); payload[0] = 0
        self.assertIs(type(pending), PendingBufferedHardware)
        self.assertEqual(self.port.records[-1], dict(command=3, tx_data=3, tx_length=2,
                                                   rx_capacity=4, expected_generation=1))

    def test_timeout_and_fault_retain_longer_prefix_and_immutable_scratch(self):
        for outcome in ('timeout', 'fault'):
            pending = self.loaded.submit(tx=b'\x03')
            raw = (True, False, True, False)
            self.port.finish(raw, 1, outcome=outcome, scratch=0x8001)
            result = pending.read()
            self.assertIs(type(result), BufferedReactiveHardwareResult)
            self.assertIsInstance(result, BufferedHardwareResult)
            self.assertEqual((result.outcome, result.payload, result.raw_rx_bits,
                result.tx_consumed_bits, result.rx_valid_bits, result.scratch),
                (outcome, None, raw, 1, 4, 0x8001))
            self.assertEqual(pending.read(), result)
            self.assertTrue(result.scratch_bits[0]); self.assertTrue(result.scratch_bits[15])
            with self.assertRaises(FrozenInstanceError): result.scratch_bits = ()
            with self.assertRaises(TransferError): self.loaded.submit(tx=b'\x03')
            pending.release()
            self.assertEqual(self.port.state['scratch'], 0)
            self.assertEqual(result.scratch, 0x8001)

    def test_success_requires_exact_tx_and_success_rx_and_keeps_owned_errors(self):
        pending = self.loaded.submit(tx=b'\x03')
        self.port.finish((True,), 1)
        with self.assertRaisesRegex(ValueError, 'declared TX demand'): pending.read()
        self.port.finish((True, False), 2)
        with self.assertRaisesRegex(ValueError, 'RX length'): pending.read()
        self.assertIs(self.host._pending, pending)
        self.port.finish((True,), 2, scratch=5)
        result = pending.read()
        self.assertEqual((result.outcome, result.payload, result.scratch), ('complete', b'\x01', 5))
        pending.release()

    def test_indexed_read_fingerprint_includes_phase_and_scratch(self):
        pending = self.loaded.submit(tx=b'\x03')
        self.port.finish((True, False), 1, outcome='fault', scratch=3)
        for mutation in (lambda status: status.update(scratch=2),
                         lambda status: status.update(phase=6)):
            self.port.mutate_read = mutation
            with self.assertRaisesRegex(RuntimeError, 'result changed'): pending.read()
            self.assertIs(self.host._pending, pending)
        self.port.mutate_read = None
        self.assertEqual(pending.read().scratch, 3)
        pending.release()

    def test_host_wait_timeout_is_distinct_from_hardware_timeout_and_reset_stales_handles(self):
        pending = self.loaded.submit(tx=b'\x03')
        with self.assertRaises(BufferedHardwareWaitTimeout) as caught:
            pending.wait(timeout_cycles=0)
        self.assertIs(caught.exception.pending, pending)
        self.port.finish((), 0, outcome='timeout')
        self.assertEqual(pending.wait(timeout_cycles=1)['phase'], 6)
        self.assertEqual(pending.read().outcome, 'timeout')
        old_epoch, old_generation = pending.identity.epoch, pending.identity.generation
        self.host.reset()
        with self.assertRaises(TransferError): pending.read()
        with self.assertRaises(TransferError): self.loaded.submit(tx=b'\x03')
        self.assertGreater(self.port.state['generation'], old_generation)
        self.host.initialize()
        self.assertGreater(self.host._epoch, old_epoch)


class BufferedInitialSamplerTests(unittest.TestCase):
    def test_first_entry_effects_use_pre_start_second_sample(self):
        code = source(Block((I('shift', 2, shift_pin=1, shift_enabled=True, shift_invert=True,
            entry_capture=(0, 4), append_input=1), I('halt'))), tx=1, rx=1)
        for first in range(4):
            for second in range(4):
                slot = TransferSlot(tx_capacity_bits=1, rx_capacity_bits=1)
                identity = slot.begin(code.key, (False,), 1)
                engine = BufferedEngine(slot, identity, code,
                    initial_first_sample=first, initial_second_sample=second)
                self.assertEqual((engine.samples[4], slot._rx),
                                 (bool(second & 1), (bool(second & 2),)))
                self.assertEqual((engine._first, engine._second), (first, second))
                engine.step(3)
                self.assertEqual((engine._first, engine._second), (3, first))
                self.assertEqual(slot._rx, (bool(second & 2),))

    def test_default_samples_stay_high_and_invalid_samples_have_no_entry_effects(self):
        code = source(Block((I('checked', entry_capture=(1, 15), append_input=0), I('halt'))), rx=1)
        for values in ({}, {'initial_first_sample': 4}, {'initial_second_sample': True},
                       {'initial_second_sample': -1}):
            slot = TransferSlot(tx_capacity_bits=0, rx_capacity_bits=1)
            identity = slot.begin(code.key, (), 1)
            if values:
                with self.assertRaises(ValueError): BufferedEngine(slot, identity, code, **values)
                self.assertEqual(slot._rx, ())
            else:
                engine = BufferedEngine(slot, identity, code)
                self.assertEqual((engine._first, engine._second, slot._rx, engine.samples[15]),
                                 (3, 3, (True,), True))


if __name__ == '__main__':
    unittest.main()
