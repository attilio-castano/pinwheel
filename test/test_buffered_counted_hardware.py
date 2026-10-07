"""Compact source/image admission and shared public-port ownership.

The command fixture acknowledges uploads and injects retained completions; it
does not execute counted rows. Actual counted dispatch is checked separately
through the Lean circuit, emitted RTL and resolved-pad peer gate.
"""
from dataclasses import FrozenInstanceError, replace
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'test'))

from buffered_counted_hardware import (CONTROL_WIDTH, FORMAT, ROW_WIDTH,
    BufferedCountedHardwareHost, BufferedCountedHardwareImage, CountedControl,
    compact_jtag, compact_spi, decode_control, encode_control, lower_counted)
from buffered_engine import (BufferedBlock as Block, BufferedInstruction as I,
    BufferedProgram, BufferedRepeat as Repeat, BufferedSequence as Sequence,
    buffered_jtag, buffered_spi)
from buffered_hardware import (MAX_ID, BufferedHardwareHost, BufferedHardwareWaitTimeout,
    LoadedBufferedHardware, PendingBufferedHardware, lower_buffered, pack_wire_bits)
from pinwheel_buffers import TransferError
from test_buffered_hardware import PublicPortFixture


def source(code, tx=0, rx=0, maximum=None):
    return BufferedProgram((), schedule=code, declared_tx_bits=tx, declared_rx_bits=rx,
                           max_rx_bits=rx if maximum is None else maximum)


class CountedPortFixture(PublicPortFixture):
    def __init__(self):
        self.controls = {}
        self.virtual_span = 0
        super().__init__()

    @staticmethod
    def fresh():
        return dict(PublicPortFixture.fresh(), virtual_pc=0, env0=0, env1=0)

    def edge(self, **fields):
        previous_pending = self.state['pending']
        result = super().edge(**fields)
        command = fields.get('command', 0)
        if fields.get('initialize', 0) or command == 7:
            self.controls.clear()
            self.virtual_span = 0
        elif command == 1 and not result['rejected']:
            if not previous_pending:
                self.controls.clear()
            self.controls[fields['address']] = fields['control']
        elif command == 2 and not result['rejected']:
            self.virtual_span = fields['virtual_span']
        return result


class CountedHardwareImageTests(unittest.TestCase):
    def test_spi_stores_four_56_bit_rows_and_distinguishes_syntax_nodes(self):
        image = lower_counted(compact_spi())
        self.assertEqual((image.image_format, len(image.words), image.virtual_span,
                          image.tx_bits, image.rx_bits, image.execution_edges),
                         (FORMAT, 4, 66, 32, 32, 260))
        self.assertEqual(image.words, (1 | 7 << 6 | 3 << 9,
            2 | 2 << 3 | 7 << 6 | 3 << 9 | 1 << 17 | 1 << 22,
            7 << 6 | 3 << 9, 3))
        common = 2 | 3 << 8 | 7 << 17
        self.assertEqual(image.controls, (common, common | 1 << 20 | 1 << 21, 0, 0))
        self.assertEqual((image.storage()['stored_nodes'], image.storage()['control_nodes'],
                          image.storage()['physical_rows'], image.storage()['uploaded_bits']),
                         (9, 5, 4, 224))
        self.assertEqual((ROW_WIDTH, CONTROL_WIDTH), (56, 24))
        self.assertEqual(BufferedCountedHardwareImage.from_bytes(image.to_bytes()), image)
        with self.assertRaises(FrozenInstanceError): image.controls = ()

    def test_metadata_bits_and_nested_boundary_are_explicit(self):
        descriptor = CountedControl(2, 5, 8, 9, 3, True, True)
        expected = 2 | 5 << 2 | 7 << 8 | 9 << 11 | 2 << 17 | 1 << 20 | 1 << 21
        self.assertEqual(encode_control(descriptor), expected)
        self.assertEqual(decode_control(expected), descriptor)
        code = Sequence((Repeat(1, Block((I('drive'),))),
                         Repeat(8, Repeat(1, Block((I('drive'),)))), Block((I('halt'),))))
        image = lower_counted(source(code))
        self.assertEqual(image.virtual_span, 10)
        self.assertEqual(tuple(decode_control(word) for word in image.controls),
            (CountedControl(1, 0, 1, outer_end=True),
             CountedControl(2, 1, 8, 1, 1, True, True), CountedControl()))

    def test_sequential_repeats_reuse_the_two_runtime_loop_levels(self):
        code = Sequence((Repeat(2, Block((I('drive'), I('drive')))),
            Repeat(3, Block((I('keep'),))), Repeat(4, Block((I('drive'),))),
            Block((I('halt'),))))
        image = lower_counted(source(code))
        self.assertEqual((len(image.words), image.virtual_span), (5, 12))
        self.assertEqual([decode_control(word).outer_start for word in image.controls],
                         [0, 0, 2, 3, 0])
        self.assertEqual([decode_control(word).outer_end for word in image.controls],
                         [False, True, True, True, False])

    def test_source_tree_grouping_remains_part_of_identity(self):
        original = compact_spi()
        regrouped = replace(original, schedule=Sequence((original.schedule,)))
        a, b = lower_counted(original), lower_counted(regrouped)
        self.assertEqual((a.words, a.controls), (b.words, b.controls))
        self.assertNotEqual(a.program_key, b.program_key)
        self.assertNotEqual(a.key, b.key)
        restored = BufferedCountedHardwareImage.from_bytes(b.to_bytes())
        self.assertEqual(restored.source, regrouped)
        self.assertEqual(restored.source.schedule.parts, (original.schedule,))
        stale = compact_spi(1)
        object.__setattr__(stale, '_key', '0' * 64)
        with self.assertRaisesRegex(ValueError, 'original source identity'):
            lower_counted(stale)

    def test_captured_rows_and_metadata_must_match_exact_source_lowering(self):
        image = lower_counted(compact_spi())
        mutations = [('controls', 0, image.controls[0] ^ 1 << 8),
                     ('controls', 1, image.controls[1] ^ 1 << 20),
                     ('words', 0, image.words[0] ^ 1 << 3)]
        for field, index, value in mutations:
            obj = json.loads(image.to_bytes())
            obj[field][index] = value
            with self.subTest(field=field, index=index), self.assertRaisesRegex(ValueError, 'canonical source lowering'):
                BufferedCountedHardwareImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes())
        obj['source']['schedule']['parts'][0]['count'] = 3
        obj['source']['declared_tx_bits'] = obj['source']['declared_rx_bits'] = obj['source']['max_rx_bits'] = 24
        with self.assertRaisesRegex(ValueError, 'original source identity'):
            BufferedCountedHardwareImage.from_bytes(json.dumps(obj).encode())

    def test_capture_schema_span_demand_and_version_are_strict(self):
        image = lower_counted(compact_spi())
        for field, value in [('format', 'pinwheel-buffered-linear32-v1'),
                ('program_key', '0' * 64), ('image_key', '0' * 64), ('physical_count', 3),
                ('virtual_span', 65), ('tx_bits', 31), ('rx_bits', True)]:
            obj = json.loads(image.to_bytes()); obj[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                BufferedCountedHardwareImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['source']['extra'] = 1
        with self.assertRaises(ValueError): BufferedCountedHardwareImage.from_bytes(json.dumps(obj).encode())
        obj = json.loads(image.to_bytes()); obj['controls'][0] = True
        with self.assertRaises(ValueError): BufferedCountedHardwareImage.from_bytes(json.dumps(obj).encode())

    def test_reserved_inactive_or_impossible_loop_metadata_is_rejected(self):
        for word in (3, 1 << 22, 1 << 23, 1 << 2, 1 << 8, 1 << 20,
                     1 | 1 << 11, 1 | 1 << 17, 1 | 1 << 21,
                     2 | 2 << 2 | 1 << 11, 2 | 1 << 20):
            with self.subTest(word=word), self.assertRaises(ValueError): decode_control(word)
        for word in (True, -1, 1 << 24, 1.0):
            with self.assertRaises(ValueError): decode_control(word)
        with self.assertRaises(ValueError): CountedControl(outer_end=1)

    def test_leaf_and_virtual_span_boundaries_require_no_unrolling(self):
        image = lower_counted(BufferedProgram((I('drive'),) * 63 + (I('halt'),)))
        self.assertEqual((len(image.words), image.virtual_span), (64, 64))
        with self.assertRaisesRegex(ValueError, '64 leaves'):
            lower_counted(BufferedProgram((I('drive'),) * 64 + (I('halt'),)))
        code = Sequence((Repeat(8, Repeat(8, Block((I('drive'),) * 15))),
                         Repeat(7, Repeat(8, Block((I('drive'),)))),
                         Repeat(7, Block((I('drive'),))), Block((I('halt'),))))
        image = lower_counted(source(code))
        self.assertEqual((len(image.words), image.virtual_span, image.execution_edges), (18, 1024, 1023))
        with self.assertRaisesRegex(ValueError, '1024 addresses'):
            source(Sequence((Repeat(8, Repeat(8, Block((I('drive'),) * 16))), Block((I('halt'),)))))
        with self.assertRaisesRegex(ValueError, 'two loops'):
            source(Sequence((Repeat(1, Repeat(1, Repeat(1, Block((I('drive'),))))), Block((I('halt'),)))))

    def test_terminal_must_be_unique_final_and_outside_repeat(self):
        for code in (Repeat(1, Block((I('halt'),))),
                     Sequence((Block((I('halt'),)), Block((I('drive'),)))),
                     Block((I('halt'), I('fault'))), Block((I('drive'),))):
            with self.assertRaisesRegex(ValueError, 'final terminal'): lower_counted(source(code))
        image = lower_counted(source(Block((I('fault'),))))
        self.assertEqual((image.words, image.controls, image.execution_edges), ((4,), (0,), 0))

    def test_derived_declarations_capacity_and_unsupported_effects_fail_before_io(self):
        port = CountedPortFixture(); host = BufferedCountedHardwareHost(port)
        p = compact_spi(1)
        invalid = [replace(p, declared_tx_bits=7), replace(p, declared_rx_bits=7),
                   replace(p, max_rx_bits=9),
                   source(Sequence((Repeat(5, Repeat(8, Block((I('shift', shift_pin=0),
                       I('keep', append_input=0))))), Block((I('halt'),)))), tx=40, rx=40)]
        for instruction in (I('wait'), I('checked'), I('qualify'),
                I('shift', shift_pin=0, shift_enabled=True), I('shift', shift_pin=0, shift_invert=True),
                I('keep', preserve_enabled=1), I('drive', entry_capture=(0, 0)),
                I('fault', outcome='timeout')):
            leaves = (instruction,) if instruction.kind == 'fault' else (instruction, I('halt'))
            invalid.append(source(Block(leaves), tx=int(instruction.kind == 'shift')))
        invalid.append(BufferedProgram((I('drive', 257), I('halt'))))
        for program in invalid:
            with self.subTest(program=program), self.assertRaises(ValueError): host.load(program)
        self.assertEqual(port.records, [])

    def test_factories_preserve_every_virtual_instruction_of_old_programs(self):
        for half in (3, 256):
            for length in (1, 2, 4):
                p = compact_spi(length, half)
                self.assertEqual(tuple(p.fetch(pc) for pc in range(p.span)), buffered_spi(length, half).instructions)
                self.assertEqual(lower_counted(p).execution_edges, (16 * length + 1) * half)
            for bits in range(1, 33):
                p = compact_jtag(bits, half)
                self.assertEqual(tuple(p.fetch(pc) for pc in range(p.span)), buffered_jtag(bits, half).instructions)
                self.assertEqual((lower_counted(p).tx_bits, lower_counted(p).rx_bits), (bits, bits))

    def test_jtag17_is_twenty_physical_rows_with_exact_nonbyte_order(self):
        image = lower_counted(compact_jtag())
        self.assertEqual((len(image.words), image.virtual_span, image.storage()['uploaded_bits']), (20, 58, 1120))
        payload = b'\x96\xa5\x01'
        self.assertEqual(pack_wire_bits(image.encode_tx(payload)), 0x1a596)
        self.assertEqual(image.decode_rx(image.encode_tx(payload)), payload)
        with self.assertRaisesRegex(ValueError, 'padding'): image.encode_tx(b'\x96\xa5\x03')


class CountedHardwareHostTests(unittest.TestCase):
    def setUp(self):
        self.port = CountedPortFixture()
        self.host = BufferedCountedHardwareHost(self.port)
        self.host.initialize()
        self.loaded = self.host.load(compact_spi())

    def test_counted_upload_is_atomic_per_row_and_commits_physical_and_virtual_counts(self):
        writes = [c for c in self.port.records if c.get('command') == 1]
        self.assertEqual(writes, [dict(command=1, address=i, word=word, control=control)
            for i, (word, control) in enumerate(zip(self.loaded.image.words, self.loaded.image.controls))])
        self.assertEqual(self.port.records[-1], dict(command=2, count=4, virtual_span=66,
                                                   idle_levels=4, idle_enabled=7))
        self.assertIsInstance(self.loaded, LoadedBufferedHardware)
        self.assertEqual(self.port.controls, dict(enumerate(self.loaded.image.controls)))

    def test_old_linear_load_transcript_remains_exact(self):
        port = PublicPortFixture(); host = BufferedHardwareHost(port)
        host.initialize(); image = lower_buffered(buffered_spi(1)); host.load(image)
        self.assertEqual(port.records, [dict(initialize=1), dict(command=0)] +
            [dict(command=1, address=i, word=word) for i, word in enumerate(image.words)] +
            [dict(command=2, count=18, idle_levels=4, idle_enabled=7)])

    def test_version_separation_and_revalidation_precede_io(self):
        before = len(self.port.records)
        with self.assertRaises(ValueError): self.host.load(lower_buffered(buffered_spi()))
        linear = PublicPortFixture()
        with self.assertRaises(ValueError): BufferedHardwareHost(linear).load(self.loaded.image)
        self.assertEqual(linear.records, [])
        corrupted = BufferedCountedHardwareImage.from_bytes(self.loaded.image.to_bytes())
        object.__setattr__(corrupted, 'controls', (corrupted.controls[0] ^ 1 << 8, *corrupted.controls[1:]))
        with self.assertRaises(ValueError): self.host.load(corrupted)
        self.assertEqual(len(self.port.records), before)

    def test_shared_wait_read_release_retains_owner_and_exact_payload(self):
        pending = self.loaded.submit(tx=b'\x96\xa5\x3c\xc3')
        self.assertIsInstance(pending, PendingBufferedHardware)
        with self.assertRaises(BufferedHardwareWaitTimeout) as caught: pending.wait(timeout_cycles=0)
        self.assertIs(caught.exception.pending, pending)
        before = len(self.port.records)
        with self.assertRaises(TransferError): self.host.load(compact_spi(1))
        with self.assertRaises(TransferError): self.loaded.submit(tx=bytes(4))
        self.assertEqual(len(self.port.records), before)
        bits = self.loaded.image.encode_tx(b'\xa6\x9b\x42\xe1')
        self.port.finish(bits, 32)
        result = pending.read()
        self.assertEqual(result.payload, b'\xa6\x9b\x42\xe1')
        self.assertEqual(pending.read(), result)
        self.assertEqual(self.port.state['retained'], 1)
        pending.release()
        self.assertEqual(self.port.records[-1], dict(command=4, expected_generation=1, expected_transfer=1))
        self.assertEqual(self.host.load(compact_spi(1)).generation, 2)

    def test_shared_partial_fault_and_decode_failure_keep_retained_result(self):
        pending = self.loaded.submit(tx=bytes(4))
        self.port.finish((True, False, True), 5, fault=True)
        result = pending.read()
        self.assertEqual((result.payload, result.raw_rx_bits, result.tx_consumed_bits),
                         (None, (True, False, True), 5))
        self.assertEqual(pending.read(), result)
        pending.release()
        pending = self.loaded.submit(tx=bytes(4))
        self.port.finish((False,) * 31, 32)
        with self.assertRaisesRegex(ValueError, 'complete program result'): pending.read()
        self.assertEqual(self.port.state['retained'], 1)
        pending.release()

    def test_shared_reset_epochs_and_counter_exhaustion_do_not_alias_handles(self):
        pending = self.loaded.submit(tx=bytes(4)); old = pending.identity
        self.host.reset()
        self.assertEqual((self.port.state['generation'], self.port.state['transfer']), (2, 1))
        before = len(self.port.records)
        with self.assertRaises(TransferError): pending.release()
        with self.assertRaises(TransferError): self.loaded.submit(tx=bytes(4))
        self.assertEqual(len(self.port.records), before)
        self.host.initialize(); loaded = self.host.load(compact_spi())
        fresh = loaded.submit(tx=bytes(4))
        self.assertEqual((old.generation, old.transfer), (fresh.identity.generation, fresh.identity.transfer))
        self.assertNotEqual(old.epoch, fresh.identity.epoch)
        self.port.finish((False,) * 32, 32); fresh.release()
        self.port.state['transfer'] = MAX_ID
        with self.assertRaisesRegex(TransferError, 'identities are exhausted'): loaded.submit(tx=bytes(4))

    def test_new_public_loop_fields_have_strict_integer_widths(self):
        for name, value in [('virtual_pc', 1024), ('env0', 8), ('env1', True)]:
            saved = self.port.state[name]; self.port.state[name] = value
            with self.subTest(name=name), self.assertRaises(RuntimeError): self.host.status()
            self.port.state[name] = saved


if __name__ == '__main__':
    unittest.main()
