#!/usr/bin/env python3
"""Check exact cache writes on hold, branch, halt, fault and reset edges."""
from collections import Counter
import importlib.util
from pathlib import Path
import re
import runpy

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("bank_cases", ROOT / "scripts/check-bank-select-cases.py")
bank_cases = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bank_cases)


def vectors():
    oracle = runpy.run_path(str(ROOT / "scripts/loader-vectors.py"))
    fields = oracle["core"]["fields"]

    class CacheOracle(oracle["Atomic"]):
        def __init__(self):
            super().__init__()
            for image in self.images: image[32:64] = [4] * 32
            self.known_bank = [False, False]
            self.cache = None
            self.coverage = Counter()

        def edge(self, init=0, reset=0, command=0, data=0, incoming=0):
            mode, pc, _, _, _, _, samples = self.s
            running = 1 <= mode <= 4
            target = (pc + 1) % 256 if running else 0
            if running and mode == 3:
                d = fields(self.images[self.active][self.images[self.active][64 + pc]])
                if d['finish']:
                    slots = self.capture(samples, d['terminal'], incoming)
                    target = d['yes'] if d['finish'] == 1 or (slots >> d['sample']) & 1 else d['no']
            old_active, old_cursor = self.active, self.cursor
            fits = self.cursor < 32 or (data == 4 if self.cursor < 64 else data < 32 if self.cursor < 320 else True)
            super().edge(init, reset, 6 if command == 2 and not fits else command, data, incoming)
            self.rows[-1][2] = command
            if self.gates[0] and old_cursor == 321: self.known_bank[1 - old_active] = True
            if not running or self.s[1] != pc:
                image = self.images[self.read_bank]
                self.cache = image[image[64 + target]] if self.known_bank[self.read_bank] else None
            self.rows[-1] += [int(self.cache is not None), self.cache or 0]
            if self.cache is not None:
                self.coverage['exact_cache_edges'] += 1
                self.coverage['running_write' if running and self.s[1] != pc else
                              'running_hold' if running else 'idle_write'] += 1
                if running and (reset or init): self.coverage[f'reset_from_pc_{pc}'] += 1
                if running and self.s[0] in (5, 6, 7): self.coverage[f'stop_mode_{self.s[0]}_from_pc_{pc}'] += 1
                if running and self.pending and self.cursor == 322 and command == 3:
                    self.coverage['busy_commit_rejected_at_full_cursor'] += 1

    m = CacheOracle()
    pack, stream = oracle['pack'], oracle['stream']
    action = lambda duration=0: pack(dict(kind=0, levels=1, enabled=7, duration=duration))
    branch = lambda yes, check=0, duration=0: pack(dict(kind=2, levels=3, enabled=7,
                                                      yes=yes, finish=1, check=check, duration=duration))
    m.edge(init=1)
    # Hold, same-address branches, different-address branches, halt and range faults.
    for name, words, last, steps, end_mode in [
        ('halt-from-zero', [action(), 4], 1, 1, 5),
        ('halt-from-one', [action(), action(), 4], 2, 2, 5),
        ('range-fault-zero', [action()], 0, 1, 7),
        ('range-fault-one', [action(), action()], 1, 2, 7),
        ('hold-then-halt', [action(3), 4], 1, 4, 5),
        ('self-zero', [branch(0)], 0, 4, 3),
        ('self-one', [action(), branch(1)], 1, 5, 3),
        ('branch-back-zero', [action(), branch(0)], 1, 6, 1),
        ('guard-fault-zero', [branch(0, check=5)], 0, 1, 7),
        ('guard-fault-one', [action(), branch(1, check=5)], 1, 2, 7),
        ('wait-timeout-zero', [pack(dict(kind=1, check=2))], 0, 1, 6),
        ('wait-timeout-one', [action(), pack(dict(kind=1, check=2))], 1, 2, 6),
        ('qualify-timeout-zero', [pack(dict(kind=3, check=5))], 0, 1, 6),
        ('qualify-timeout-one', [action(), pack(dict(kind=3, check=5))], 1, 2, 6),
    ]:
        m.load(name, words, last)
        m.edge(command=5)
        for _ in range(steps): m.edge(command=3)
        assert m.s[0] == end_mode, (name, m.s)
    for pc in (0, 1):
        m.load(f'reset-running-{pc}', [action(3)] if pc == 0 else [action(), action(3)], pc)
        m.edge(command=5)
        if pc: m.edge()
        assert m.s[1] == pc
        m.edge(reset=1, command=3)
        assert m.s[0] == 0
    # An upload is complete but uncommitted throughout execution of the old bank.
    m.load('full-pending-upload', [action(3), 4], 1)
    m.edge(command=1)
    for word in stream([action(), 4], 1, (6, 7)): m.edge(command=2, data=word)
    m.edge(command=5)
    for _ in range(4):
        m.edge(command=3, data=(1 << 64) - 1)
        assert m.gates[3] and m.cursor == 322
    m.edge(command=3)
    assert m.gates[1]
    m.edge(command=5)
    assert m.s[0] == 1
    m.edge()
    assert m.s[0] == 5
    assert m.coverage['running_hold'] and m.coverage['running_write']
    for mode in (5, 6, 7):
        for pc in (0, 1): assert m.coverage[f'stop_mode_{mode}_from_pc_{pc}']
    return m.rows, {'edges': len(m.rows), 'cases': m.cases, 'coverage': dict(m.coverage)}


def transform_tb(text):
    def replace_once(old, new):
        nonlocal text
        if text.count(old) != 1: raise RuntimeError(f'Missing or ambiguous cache testbench anchor: {old}')
        text = text.replace(old, new, 1)
    replace_once('  reg e_push,', '  reg e_cache_known;\n  reg [63:0] e_cache;\n  reg e_push,')
    text, count = re.subn(r'(\$fscanf\(file, "[^"]+)(\\n")', r'\1 %d %d\2', text)
    if count != 1: raise RuntimeError('Missing vector scanner')
    replace_once('\n        e_mode, e_pc, e_remaining, e_wait, e_levels, e_enabled, e_samples);',
                 '\n        e_mode, e_pc, e_remaining, e_wait, e_levels, e_enabled, e_samples, e_cache_known, e_cache);')
    replace_once('status != 20', 'status != 22')
    replace_once('      if (busy && dut.r_cached_word',
        '      if (e_cache_known && dut.r_cached_word !== e_cache)\n'
        '        $fatal(1, "LOADER edge %0d exact cache actual=%h expected=%h", count, dut.r_cached_word, e_cache);\n'
        '      if (busy && dut.r_cached_word')
    return text


def mutations(rtl):
    match = re.search(r'\br_cached_word\s*<=\s*([^;]+);', rtl)
    if not match: raise RuntimeError('Missing cache update')
    # The emitted assignment is a conditional hold, possibly with nested conditions.
    expression = match[1]
    tail = re.search(r'\?\s*(\w+)\s*:\s*r_cached_word\s*$', expression)
    if not tail: raise RuntimeError('Missing final data/hold selector')
    word = tail[1]
    replacements = {'always-hold': 'r_cached_word', 'always-refresh': word,
                    'reset-holds-cache': f'reset ? r_cached_word : ({expression})'}
    return {name: rtl[:match.start(1)] + value + rtl[match.end(1):] for name, value in replacements.items()}


if __name__ == '__main__':
    bank_cases.main(vector_factory=vectors, mutate=mutations, transform_tb=transform_tb,
                    extra_sources=[Path(__file__).resolve()])
