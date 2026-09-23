"""Independent E64 and wire expectations for the bounded compact model study."""
from pathlib import Path
import runpy
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from compact_execution import (Machine, Op, Node, HOLD, SHIFT, CAPTURE, BRANCH,
                               WAIT, HALT, compile_graph, decode, linear,
                               lower_e64, uart_image, spi_image, branch_image,
                               resource_budget)

LEGACY = runpy.run_path(str(ROOT / 'scripts/reactive-core-vectors.py'))
pack, valid, fields = (LEGACY[n] for n in ('pack', 'valid', 'fields'))


def reference(words, idle, incoming=0):
    assert all(valid(w) for w in words)
    assert len(set(words + [4])) <= 32 and len(words) <= 256
    model = LEGACY['Machine'](False)
    model.load('compact-comparison', words, len(words)-1, idle)
    model.rows.clear()
    model.edge(start=1, incoming=incoming)
    return model


def observe_legacy(m):
    return m.s[0], m.s[4], m.s[5], m.s[6]


def uart_words(byte):
    return [pack(dict(levels=4 | bit, enabled=7, duration=3))
            for bit in [0] + [(byte >> k) & 1 for k in range(8)] + [1]] + [4]


def spi_words(byte):
    return [pack(dict(levels=((byte >> (7-k//2)) & 1 if k < 16 else 0) | (k % 2) << 1,
                      enabled=7, duration=3, entry=(1 + 4*(k//2)) if k % 2 else 0))
            for k in range(17)] + [4]


def spi_input(rx, edge):
    if edge >= 4 and (edge-4) % 8 == 0 and edge <= 60:
        return rx >> (7-(edge-4)//8) & 1
    return (edge * 3 + 1) % 4  # Decoy changes away from the rising capture edge.


def check_uart(case, m, byte, busy_commands=True):
    m.edge(command=5, data=byte)
    case.assertTrue(m.gates[2])
    ref = reference(uart_words(byte), (5, 7))
    for edge in range(41):
        expected = (5, 5, 7, 0) if edge == 40 else (
            1, 4 | ([0] + [(byte >> k) & 1 for k in range(8)] + [1])[edge//4], 7, 0)
        case.assertEqual(m.observe(), expected, ('uart', byte, edge))
        case.assertEqual(m.observe(), observe_legacy(ref))
        if edge < 40:
            m.edge(command=5 if busy_commands else 0, data=255-byte, incoming=edge % 4)
            ref.edge(incoming=edge % 4)
            if busy_commands:
                case.assertEqual(m.gates, (False, False, False, True))
    m.edge()  # Arrival is one edge after execution completes.
    case.assertEqual(m.result, (5, 0))
    m.edge(consume=True, clear=True)


def check_spi(case, m, tx, rx):
    m.edge(command=5, data=tx, incoming=spi_input(rx, 0))
    ref = reference(spi_words(tx), (4, 7), spi_input(rx, 0))
    for edge in range(69):
        expected_samples = sum((rx >> (7-k) & 1) << k for k in range(8) if 4 + 8*k <= edge)
        if edge == 68:
            expected = (5, 4, 7, expected_samples)
        else:
            phase = edge//4
            bit = tx >> (7-phase//2) & 1 if phase < 16 else 0
            expected = (1, bit | (phase % 2) << 1, 7, expected_samples)
        case.assertEqual(m.observe(), expected, ('spi', tx, rx, edge))
        case.assertEqual(m.observe(), observe_legacy(ref))
        if edge < 68:
            incoming = spi_input(rx, edge+1)
            m.edge(command=2, data=(1 << 64)-1, incoming=incoming)
            ref.edge(incoming=incoming)
    m.edge()
    case.assertEqual(m.result, (5, int(f'{rx:08b}'[::-1], 2)))
    m.edge(consume=True, clear=True)


class TraceTests(unittest.TestCase):
    def test_all_uart_payloads_on_one_resident_image(self):
        m = Machine()
        m.load(uart_image())
        original = m.memory.copy()
        for byte in range(256):
            check_uart(self, m, byte)
            self.assertEqual(m.memory, original)
        self.assertEqual(sum(a is not None and a[0] == 'write' for a in m.access), 32)

    def test_spi_changing_tx_rx_and_capture_phase(self):
        m = Machine()
        m.load(spi_image())
        original = m.memory.copy()
        for tx in range(256):
            check_spi(self, m, tx, (tx*73+19) % 256)
            self.assertEqual(m.memory, original)

    def test_consecutive_branch_entry_terminal_forwarding(self):
        words = [pack(dict(kind=2, levels=k+1, enabled=3, terminal=63,
                           entry=61, finish=2, sample=15, yes=1-k, no=k)) for k in range(2)]
        # Exhaust all histories of six two-bit samples, then a longer sequence.
        for history in range(4**6):
            m = Machine()
            m.load(branch_image())
            m.edge(command=5)
            ref = reference(words, (0, 0))
            pc = 0
            for edge in range(6):
                incoming = history >> (2*edge) & 3
                pc ^= incoming >> 1
                m.edge(incoming=incoming)
                ref.edge(incoming=incoming)
                self.assertEqual(m.observe(), (3, pc+1, 3, (incoming & 1) << 15))
                self.assertEqual(m.observe(), observe_legacy(ref))
                self.assertEqual(m.access[-1][0], 'read')
        m = Machine()
        m.load(lower_e64([fields(w) for w in words]))
        m.edge(command=5)
        pc = 0
        for edge in range(128):
            incoming = edge % 4
            pc ^= incoming >> 1
            m.edge(incoming=incoming)
            self.assertEqual(m.observe(), (3, pc+1, 3, (incoming & 1) << 15))

    def test_wait_release_and_exact_timeout(self):
        for pin in (0, 1):
            for budget in (0, 1, 7, 255):
                words = [pack(dict(kind=1, levels=1, enabled=3, duration=budget,
                                   check=pin | 2)), pack(dict(levels=2, enabled=3)), 4]
                image = lower_e64([fields(w) for w in words])
                for release in range(budget+2):
                    m = Machine()
                    m.load(image)
                    m.edge(command=5)
                    ref = reference(words, (0, 0))
                    for edge in range(budget+4):
                        incoming = int(edge >= release) << pin
                        m.edge(incoming=incoming)
                        ref.edge(incoming=incoming)
                        self.assertEqual(m.observe(), observe_legacy(ref))

    def test_existing_fixed_payload_programs_lower_without_extra_edges(self):
        for words, idle in [(uart_words(0xa6), (5, 7)), (spi_words(0x53), (4, 7))]:
            m = Machine()
            m.load(lower_e64([fields(w) for w in words], idle))
            m.edge(command=5)
            ref = reference(words, idle)
            for edge in range(70):
                self.assertEqual(m.observe(), observe_legacy(ref))
                m.edge(incoming=edge % 4)
                ref.edge(incoming=edge % 4)


class OwnershipTests(unittest.TestCase):
    def test_missing_start_and_incomplete_upload_preserve_program(self):
        for cut in (0, 1, 16, 31, 32, 33):
            for ending in ('abort', 'reset', 'restart'):
                m = Machine()
                m.load(uart_image())
                active = m.active
                original = m.memory[active*32:(active+1)*32]
                m.edge(command=1)
                for word in spi_image().upload()[:cut]:
                    m.edge(command=2, data=word)
                if cut < 33:
                    m.edge(command=3)
                    self.assertTrue(m.gates[3])
                if ending == 'reset':
                    m.edge(reset=True)
                else:
                    m.edge(command=4 if ending == 'abort' else 1)
                self.assertEqual(m.memory[active*32:(active+1)*32], original)
                self.assertEqual(m.active, active)
                for k in range(20):
                    m.edge(data=k)  # No delivered START; serial framing is outside this model.
                    self.assertFalse(m.busy)
                check_uart(self, m, 0xa6)

    def test_uninitialized_array_never_read_before_commit(self):
        m = Machine()
        for cmd in (5, 3, 4, 6, 1, 5):
            m.edge(command=cmd)
            self.assertFalse(m.busy)
            self.assertIsNone(m.access[-1])
        self.assertTrue(all(x is None for x in m.memory))

    def test_malformed_push_and_metadata_do_not_advance_or_commit(self):
        m = Machine()
        m.load(uart_image())
        m.edge(command=1)
        m.edge(command=2, data=7)
        self.assertEqual(m.cursor, 0)
        self.assertTrue(m.gates[3])
        for word in spi_image().rows:
            m.edge(command=2, data=word)
        m.edge(command=2, data=64)
        self.assertEqual(m.cursor, 32)
        m.edge(command=3)
        self.assertTrue(m.gates[3])
        m.edge(command=4)
        check_uart(self, m, 0x53)

    def test_immediate_and_delayed_start_after_commit_and_write(self):
        m = Machine()
        m.load(uart_image())
        check_uart(self, m, 0)
        m.load(spi_image())
        check_spi(self, m, 0xa6, 0x96)
        m.load(uart_image())
        m.edge(command=1)
        for word in spi_image().rows[:3]:
            m.edge(command=2, data=word)
        check_uart(self, m, 0xff)
        self.assertEqual(m.cursor, 3)

    def test_reset_during_every_uart_edge_and_fresh_start_payload(self):
        for cut in range(40):
            m = Machine()
            m.load(uart_image())
            m.edge(command=5, data=0xa6)
            for _ in range(cut):
                m.edge()
            m.edge(reset=True, command=5, data=255)
            self.assertEqual(m.observe(), (0, 5, 7, 0))
            self.assertEqual(m.payload, 0)
            check_uart(self, m, 0x53)
        m.edge(init=True)
        self.assertFalse(m.committed)
        self.assertIsNone(m.result)

    def test_oldest_result_overrun_and_consume_arrival(self):
        m = Machine()
        m.load(branch_image())
        m.edge(command=5)
        m.edge(incoming=1)
        # An explicit fault/complete graph provides distinguishable captures.
        m.edge(reset=True)
        image = linear([Op(kind=CAPTURE, arg=3)], (0, 0))
        m.load(image)
        m.edge(command=5, incoming=1)
        m.edge()
        self.assertIsNone(m.result)
        m.edge()
        self.assertEqual(m.result, (5, 8))
        m.edge(command=5, incoming=0)
        self.assertTrue(m.gates[2])  # No hardware unread-result start gate.
        m.edge()
        m.edge()
        self.assertTrue(m.overrun)
        self.assertEqual(m.result, (5, 8))
        m.edge(command=5, incoming=0)
        m.edge()
        m.edge(consume=True, clear=True)
        self.assertEqual(m.result, (5, 0))
        self.assertFalse(m.overrun)


class RejectionTests(unittest.TestCase):
    def test_entry_and_busy_payload_mutants_are_detected(self):
        for mutation in ('shift-on-hold', 'busy-payload'):
            m = Machine(mutation)
            m.load(uart_image())
            with self.assertRaises(AssertionError, msg=mutation):
                check_uart(self, m, 0xa6)

    def test_stale_read_address_requires_consecutive_dispatches(self):
        # Four-edge UART holds hide this bug: the correct read catches up.
        m = Machine('stale-row')
        m.load(branch_image())
        m.edge(command=5)
        m.edge(incoming=2)
        self.assertEqual(m.observe(), (3, 2, 3, 0))
        m.edge(incoming=0)
        self.assertNotEqual(m.observe(), (3, 2, 3, 0))

    def test_stale_terminal_capture_mutant_is_detected(self):
        m = Machine('stale-branch')
        m.load(branch_image())
        m.edge(command=5)
        m.edge(incoming=2)
        self.assertNotEqual(m.observe(), (3, 2, 3, 0))

    def test_currently_admitted_capacity_counterexample(self):
        words = [pack(dict(levels=1, enabled=1, duration=255))] * 32 + [4]
        ref = reference(words, (0, 0))
        for _ in range(8192):
            self.assertEqual(ref.s[0], 1)
            ref.edge()
        self.assertEqual(ref.s[0], 5)
        with self.assertRaisesRegex(ValueError, '33 successor rows exceed 32'):
            lower_e64([fields(w) for w in words])
        self.assertEqual(lower_e64([fields(w) for w in words[1:]]).used_rows, 32)

    def test_currently_admitted_rich_operations_rejected_explicitly(self):
        cases = [dict(kind=3, duration=4, budget=7, check=1),
                 dict(kind=2, check=1),
                 dict(kind=2, entry=1, terminal=7, finish=2, sample=2, yes=0, no=1)]
        for d in cases:
            word = pack(d)
            self.assertTrue(valid(word))
            with self.assertRaisesRegex(ValueError, 'capability:'):
                lower_e64([fields(word), fields(4)])

    def test_reserved_bits_and_bad_graphs_fail_closed(self):
        for word in (7, 1 << 32, -1, HALT | 8, SHIFT | 3 << 17, WAIT | 4 << 17):
            with self.assertRaises(ValueError):
                decode(word)
        with self.assertRaisesRegex(ValueError, 'missing successor'):
            compile_graph([Node(Op(), 9, 9)])
        with self.assertRaisesRegex(ValueError, 'only branches'):
            compile_graph([Node(Op(), 0, 1), Node(Op(kind=HALT))])

    def test_complete_declared_resource_accounting(self):
        r = resource_budget()
        self.assertEqual(r['declared_register_bits'], 250)
        self.assertEqual(sum(r['register_bits_by_owner'].values()), 250)
        self.assertEqual(r['macro_array_bits'], 4096)
        self.assertEqual(r['rows_per_bank'] * r['atomic_banks'] * 64, 4096)
        self.assertIn('hold repair', r['unmeasured'])


if __name__ == '__main__':
    unittest.main()
