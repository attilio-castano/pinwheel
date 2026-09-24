"""Completeness and deadline regressions for the revised paired-token model."""
from pathlib import Path
import random
import runpy
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
sys.path.insert(0, str(ROOT/'test'))
import test_compact_execution as old
from paired_execution import (Machine, compile_e64, unpack, valid_token, parameter,
                              fields, token, uart_image, spi_image, resource_budget)

pack, valid = old.pack, old.valid


def reference(words, idle=(0,0), last=None):
    assert all(valid(w) for w in words)
    assert len(set(list(words)+[4]*(256-len(words)))) <= 32
    m = old.LEGACY['Machine'](False)
    m.load('paired-completeness', list(words), len(words)-1 if last is None else last, idle)
    m.rows.clear()
    return m


def compare(case, words, inputs, idle=(0,0), last=None, candidate=None):
    m = candidate or Machine()
    m.load(compile_e64(words, idle, last))
    ref = reference(words, idle, last)
    m.edge(command=5, incoming=inputs[0])
    ref.edge(start=1, incoming=inputs[0])
    case.assertEqual(m.s, ref.s)
    for incoming in inputs[1:]:
        m.edge(incoming=incoming)
        ref.edge(incoming=incoming)
        case.assertEqual(m.s, ref.s)
    return m, ref


class EncodingTests(unittest.TestCase):
    def test_all_capture_descriptors_and_guard_fields_roundtrip(self):
        descriptors = [0] + [1+2*pin+4*slot for pin in range(2) for slot in range(16)]
        for entry in descriptors:
            for terminal in descriptors:
                for check in range(16):
                    d = fields(pack(dict(kind=2, duration=255, enabled=7, levels=7,
                                         entry=entry, terminal=terminal, check=check,
                                         finish=2, sample=(entry+terminal) % 16, yes=255, no=0)))
                    p = parameter(d)
                    t = token(2,7,7,255,31,255)
                    self.assertTrue(valid_token(t, [p]*32))
                    self.assertEqual((p&63,p>>6&63,p>>12&15,p>>16),
                                     (entry,terminal,check,d['sample']))
                    self.assertEqual(unpack(t)['row'],255)

    def test_all_qualifying_budgets_and_guards_fit(self):
        for budget in range(256):
            for check in range(16):
                d=fields(pack(dict(kind=3,duration=255,budget=budget,check=check)))
                p=parameter(d)
                self.assertEqual((p&255,p>>12&15),(budget,check))
                self.assertTrue(valid_token(token(3,duration=255),[p]*32))

    def test_full_dictionary_without_halt_uses_all_32_parameters(self):
        words=[pack(dict(entry=1+2*(k//16)+4*(k%16))) for k in range(32)]*8
        image=compile_e64(words)
        self.assertEqual(image.used_parameters,32)
        self.assertEqual(image.logical_positions,256)
        compare(self,words,[k%4 for k in range(258)])

    def test_reject_invalid_source_and_packed_forms(self):
        for words in ([], [1<<63], [pack(dict(duration=k)) for k in range(33)], [4]*257):
            with self.assertRaises(ValueError): compile_e64(words)
        for t,p in ((1<<30,0),(token(0),2),(token(2),2<<6),(token(3),1<<19),
                    (token(1),1), (token(4,levels=1),0)):
            self.assertFalse(valid_token(t,[p]*32))


class ExecutionTests(unittest.TestCase):
    def test_prior_capacity_counterexample_and_full_256_position_limit(self):
        for n in (32,255,256):
            words=[pack(dict(levels=1,enabled=1,duration=255))]*n
            if n<256: words.append(4)
            m=Machine();m.load(compile_e64(words));m.edge(command=5)
            ref=reference(words);ref.edge(start=1)
            for _ in range(n*256):
                self.assertTrue(m.busy)
                m.edge();ref.edge()
                self.assertEqual(m.s,ref.s)
            self.assertEqual(m.mode,5 if n<256 else 7)

    def test_irregular_full_capacity_without_repeat_compression(self):
        rng=random.Random(25632)
        dictionary=[pack(dict(levels=k%8,enabled=(k//8)+1,duration=k%4,entry=1+4*(k%16)))
                    for k in range(31)]+[4]
        words=[rng.choice(dictionary[:-1]) for _ in range(255)]+[4]
        m,ref=compare(self,words,[rng.randrange(4) for _ in range(1100)])
        self.assertEqual((m.mode,ref.s[0]),(5,5))
        self.assertEqual(compile_e64(words).logical_positions,256)

    def test_consecutive_branches_with_independent_entry_terminal_slots(self):
        words=[pack(dict(kind=2,levels=k+1,enabled=3,entry=1+4*3,
                         terminal=3+4*12,finish=2,sample=12,yes=1-k,no=k)) for k in range(2)]
        m=Machine();m.load(compile_e64(words));ref=reference(words)
        for history in range(4096):
            m.edge(reset=True,consume=True,clear=True);ref.edge(reset=1)
            m.edge(command=5);ref.edge(start=1)
            for edge in range(6):
                incoming=history>>(2*edge)&3
                m.edge(incoming=incoming);ref.edge(incoming=incoming)
                self.assertEqual(m.s,ref.s)
                self.assertEqual(m.parameter_access[-1],[(m.active,unpack(m.word)['param'])])

    def test_checked_guard_failure_and_terminal_capture_order(self):
        for check in range(16):
            for duration in (0,1,255):
                words=[pack(dict(kind=2,duration=duration,check=check,entry=1,
                                 terminal=7,finish=2,sample=1,yes=2,no=1)),4,4]
                for incoming in range(4):
                    compare(self,words,[incoming]*(duration+4))

    def test_qualifying_wait_renewal_timeout_and_all_short_input_histories(self):
        for duration in (0,1,2):
            for budget in (0,1,2):
                words=[pack(dict(kind=3,duration=duration,budget=budget,check=5)),4]
                m=Machine();m.load(compile_e64(words));ref=reference(words)
                for history in range(128):
                    m.edge(reset=True,consume=True,clear=True);ref.edge(reset=1)
                    m.edge(command=5);ref.edge(start=1)
                    for edge in range(7):
                        incoming=history>>edge&1
                        m.edge(incoming=incoming);ref.edge(incoming=incoming)
                        self.assertEqual(m.s,ref.s)
        compare(self,[pack(dict(kind=3,duration=255,budget=255,check=5)),4],
                [0]*256+[1]+[0]*255+[1]*257)

    def test_wait_both_pins_both_levels_and_last_address_fault(self):
        for pin in range(2):
            for level in range(2):
                words=[pack(dict(kind=1,duration=7,check=pin|level<<1)),4]
                for release in range(10):
                    inputs=[(1-level)<<pin]*release+[level<<pin]*12
                    compare(self,words,inputs)
        words=[pack(dict(kind=2,entry=1,terminal=7,finish=1,yes=255)),4]
        compare(self,words,[3,3,0],last=1)
        compare(self,words,[3,3,0],last=255)

    def test_random_mixed_images_against_existing_oracle(self):
        rng=random.Random(20260922)
        for _ in range(80):
            dictionary=[]
            for k in range(12):
                kind=rng.randrange(4)
                d=dict(kind=kind,levels=rng.randrange(8),enabled=rng.randrange(8),duration=rng.randrange(4))
                if kind in (0,2): d['entry']=rng.choice([0]+[1+2*rng.randrange(2)+4*rng.randrange(16)])
                if kind==1: d['check']=rng.randrange(4)
                if kind in (2,3): d['check']=rng.randrange(16)
                if kind==3: d['budget']=rng.randrange(4)
                if kind==2:
                    d.update(terminal=rng.choice([0,1+2*rng.randrange(2)+4*rng.randrange(16)]),finish=rng.randrange(3))
                    if d['finish']: d['yes']=rng.randrange(40)
                    if d['finish']==2: d.update(no=rng.randrange(40),sample=rng.randrange(16))
                dictionary.append(pack(d))
            words=[rng.choice(dictionary) for _ in range(31)]+[4]
            compare(self,words,[rng.randrange(4) for _ in range(128)],idle=(5,6))

    def test_resident_uart_and_spi_keep_one_image_for_all_payloads(self):
        m=Machine();m.load(uart_image());original=m.memory.copy()
        for byte in range(256): old.check_uart(self,m,byte)
        self.assertEqual(m.memory,original)
        m.load(spi_image());original=m.memory.copy()
        for tx in range(256): old.check_spi(self,m,tx,(tx*73+19)%256)
        self.assertEqual(m.memory,original)


class OwnershipTests(unittest.TestCase):
    def test_atomic_parameters_boot_and_rows_survive_partial_replacement(self):
        for cut in (0,1,31,32,33,160,287,288,289,290):
            for ending in ('abort','reset','restart'):
                m=Machine();m.load(uart_image());active=m.active
                previous=(m.memory[active*256:(active+1)*256],m.parameters[active].copy(),m.boot[active])
                m.edge(command=1)
                for word in spi_image().upload()[:cut]: m.edge(command=2,data=word)
                if cut<290:
                    m.edge(command=3);self.assertTrue(m.gates[3])
                m.edge(command=4 if ending=='abort' else 7 if ending=='reset' else 1)
                self.assertEqual((m.memory[active*256:(active+1)*256],m.parameters[active],m.boot[active]),previous)
                old.check_uart(self,m,0xa6)

    def test_upload_checks_both_parameter_indices_and_reserved_boot_bits(self):
        m=Machine();m.edge(command=1)
        m.edge(command=2,data=1<<20)
        self.assertEqual(m.cursor,0)
        for p in [0]*31+[2]:m.edge(command=2,data=p)
        bad=token(0,param=31)
        for row in (bad | 4<<32,4 | bad<<32):
            m.edge(command=2,data=row)
            self.assertEqual(m.cursor,32)
            self.assertEqual(len(m.parameter_access[-1]),2)
        for row in [4|4<<32]*256:m.edge(command=2,data=row)
        for boot in (1<<32,1<<30,bad):
            m.edge(command=2,data=boot);self.assertEqual(m.cursor,288)

    def test_busy_all_commands_reset_and_missing_payload(self):
        m=Machine();m.load(uart_image())
        for _ in range(8):m.edge(data=255);self.assertFalse(m.busy)
        m.edge(command=5,data=0xa6);original=m.memory.copy()
        for k in range(36):
            m.edge(command=1+k%6,data=255)
            self.assertEqual(m.gates,(False,False,False,True))
        self.assertEqual(m.memory,original)
        m.edge(command=7)
        self.assertEqual(m.observe(),(0,5,7,0))
        old.check_uart(self,m,0x53)
        m.edge(init=True);m.edge(command=5)
        self.assertFalse(m.committed)

    def test_completion_mailbox_oldest_result_and_consume_arrival(self):
        image=compile_e64([pack(dict(entry=13)),4])
        m=Machine();m.load(image)
        for incoming in (1,0):
            m.edge(command=5,incoming=incoming);m.edge();m.edge()
        self.assertEqual(m.result,(5,8));self.assertTrue(m.overrun)
        m.edge(command=5,incoming=0);m.edge();m.edge(consume=True,clear=True)
        self.assertEqual(m.result,(5,0));self.assertFalse(m.overrun)


class NegativeTests(unittest.TestCase):
    def test_old_and_new_timing_ownership_mutants_are_detected(self):
        for mutation in ('shift-on-hold','busy-payload'):
            m=Machine(mutation);m.load(uart_image())
            with self.assertRaises(AssertionError):old.check_uart(self,m,0xa6)
        words=[pack(dict(kind=2,levels=k+1,enabled=3,entry=61,terminal=63,
                         finish=2,sample=15,yes=1-k,no=k)) for k in range(2)]
        for mutation in ('stale-row','stale-branch'):
            with self.assertRaises(AssertionError):compare(self,words,[0,2,0,2,3,0],candidate=Machine(mutation))
        words=[pack(dict(kind=3,duration=2,budget=1,check=5)),4]
        with self.assertRaises(AssertionError):compare(self,words,[0,0,1,0,1,1,1],candidate=Machine('no-budget-renewal'))
        m=Machine('wrong-parameter-bank');m.load(spi_image());m.load(uart_image())
        with self.assertRaises(AssertionError):old.check_uart(self,m,0xa6)

    def test_resource_budget_charges_both_parameter_banks_and_ports(self):
        r=resource_budget()
        self.assertEqual(r['declared_register_bits'],1592)
        self.assertEqual(r['register_bits']['parameters'],1280)
        self.assertEqual(r['macro_array_bits'],32768)
        self.assertEqual(r['parameter_read_ports'],2)
        self.assertEqual(r['upload_words'],len(uart_image().upload()))


if __name__=='__main__':
    unittest.main()
