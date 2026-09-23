"""Version-1 host transactions, independent of the engine and test oracle.

A transport supplies chip clock edges and reads physical output pins. The host
never inspects engine state. Real board transports must establish the documented
clock/sampling assumptions before using this interface.
"""
from dataclasses import dataclass
from enum import IntEnum
import json
from pathlib import Path
from typing import Protocol


class Command(IntEnum):
    BEGIN = 1
    PUSH = 2
    COMMIT = 3
    ABORT = 4
    START = 5
    RESET = 7


@dataclass(frozen=True)
class Pins:
    status: int
    levels: int
    enabled: int


class Transport(Protocol):
    def advance(self, ui: int, cycles: int, *, rst_n: int = 1) -> Pins: ...


@dataclass(frozen=True)
class Program:
    """Uncompressed E64 execution image; padding participates in capacity."""
    words: tuple[int, ...]
    last: int
    idle_levels: int = 0
    idle_enabled: int = 0

    def upload_words(self) -> tuple[int, ...]:
        if any(type(v) is not int for v in (self.last, self.idle_levels, self.idle_enabled)):
            raise ValueError('Program metadata must use integer fields')
        if not 1 <= len(self.words) <= 256 or not 0 <= self.last < len(self.words):
            raise ValueError('Program must contain 1..256 words and an in-range last address')
        if any(type(w) is not int or not 0 <= w < 1 << 64 for w in self.words):
            raise ValueError('Execution words must be unsigned 64-bit integers')
        if not (0 <= self.idle_levels < 8 and 0 <= self.idle_enabled < 8):
            raise ValueError('Idle levels/enables must fit three pins')
        words = (*self.words, *((4,) * (256 - len(self.words))))
        dictionary = tuple(dict.fromkeys(words))
        if len(dictionary) > 32:
            raise ValueError('Image exceeds 32 distinct records, including halt padding')
        indices = {word: k for k, word in enumerate(dictionary)}
        return (*dictionary, *((4,) * (64 - len(dictionary))),
                *(indices[word] for word in words),
                self.idle_levels | self.idle_enabled << 3, self.last)

    def write(self, path: Path):
        self.upload_words()
        path.write_text(json.dumps(dict(format='pinwheel-e64-v1', words=list(self.words),
            last=self.last, idle_levels=self.idle_levels, idle_enabled=self.idle_enabled), indent=2) + '\n')

    @classmethod
    def read(cls, path: Path):
        obj = json.loads(path.read_text())
        if not isinstance(obj, dict) or set(obj) != {'format', 'words', 'last', 'idle_levels', 'idle_enabled'} or obj['format'] != 'pinwheel-e64-v1':
            raise ValueError('Unsupported program image schema')
        if not isinstance(obj['words'], list) or any(type(obj[k]) is not int for k in ['last', 'idle_levels', 'idle_enabled']):
            raise ValueError('Malformed program image')
        program = cls(tuple(obj['words']), obj['last'], obj['idle_levels'], obj['idle_enabled'])
        program.upload_words()
        return program


@dataclass(frozen=True)
class Result:
    samples: int
    outcome: int
    overrun: bool
    rejected: bool

    @property
    def outcome_name(self):
        return {5: 'complete', 6: 'timeout', 7: 'fault'}[self.outcome]


class Host:
    def __init__(self, transport: Transport, phase_cycles: int = 2):
        if type(phase_cycles) is not int or phase_cycles < 2:
            raise ValueError('Serial phases require at least two chip edges')
        self.transport = transport
        self.phase_cycles = phase_cycles
        self.ui = 4  # serial select inactive, controls low, live status page
        self.edges = self.frames = 0

    def advance(self, cycles=1, *, rst_n=1):
        if cycles < 1:
            raise ValueError('An advance requires at least one edge')
        pins = self.transport.advance(self.ui, cycles, rst_n=rst_n)
        self.edges += cycles
        return pins

    def reset(self):
        self.ui = 4
        self.advance(8, rst_n=0)
        self.advance(4)

    def command(self, command: Command, data=0):
        if not 0 <= data < 1 << 64:
            raise ValueError('Command payload must fit 64 bits')
        # Each frame has an 8-bit command followed by a big-endian 64-bit word.
        for byte in bytes([command]) + data.to_bytes(8, 'big'):
            for shift in range(7, -1, -1):
                self.ui = (self.ui & ~7) | (((byte >> shift) & 1) << 1)
                self.advance(self.phase_cycles)
                self.ui |= 1
                self.advance(self.phase_cycles)
        self.ui = (self.ui & ~7) | 4
        self.advance(4)  # sampler, completed-frame pulse, loader delivery
        self.frames += 1

    def page(self, page: int):
        if page not in range(4):
            raise ValueError('Host page must be 0..3')
        self.ui = (self.ui & ~24) | page << 3
        return self.advance(3).status

    def _pulse(self, bit):
        self.ui &= ~(1 << bit)
        self.advance(3)
        self.ui |= 1 << bit
        self.advance(3)
        self.ui &= ~(1 << bit)
        self.advance(3)

    def consume(self):
        self._pulse(5)

    def clear_flags(self):
        self._pulse(6)

    def result_status(self):
        status = self.page(3)
        if status & 0x18 != 0x10:
            raise RuntimeError('Chip does not expose result interface version 1')
        return status

    def upload(self, program: Program):
        words = program.upload_words()  # reject capacity before touching the chip
        if self.page(0) & 1:
            raise RuntimeError('Cannot upload while the engine is busy')
        self.clear_flags()
        self.command(Command.BEGIN)
        for word in words:
            self.command(Command.PUSH, word)
        # A malformed record can leave the staging cursor behind. Do not issue
        # commit after a rejected push, and preserve the previous active image.
        if self.result_status() & 4:
            self.command(Command.ABORT)
            raise RuntimeError('Chip rejected the staged image; upload aborted')
        self.command(Command.COMMIT)
        live = self.page(0)
        if live & 7 != 2 or self.result_status() & 4:
            raise RuntimeError('Chip did not accept program commit')

    def start(self):
        if self.result_status() & 1:
            raise RuntimeError('Consume the previous result before starting')
        live = self.page(0)
        if live & 3 != 2:
            raise RuntimeError('Start requires a valid program and an idle engine')
        self.clear_flags()
        self.command(Command.START)
        if self.result_status() & 4:
            raise RuntimeError('Chip rejected start')

    def read_result(self, *, timeout_cycles=100_000, consume=True):
        if type(timeout_cycles) is not int or timeout_cycles < 0:
            raise ValueError('Timeout must be nonnegative')
        deadline = self.edges + timeout_cycles
        while True:
            status = self.result_status()
            if status & 1:
                break
            remaining = deadline - self.edges
            if remaining <= 0:
                raise TimeoutError('No result before host timeout; engine state is unchanged')
            self.advance(min(16, remaining))
        samples = self.page(1) | self.page(2) << 8
        # The retained slot cannot change without host consumption/reset.
        after = self.result_status()
        if not after & 1 or (after & 0xe1) != (status & 0xe1):
            raise RuntimeError('Result changed during readback')
        outcome = after >> 5
        if outcome not in (5, 6, 7):
            raise RuntimeError('Invalid completed result outcome')
        result = Result(samples, outcome, bool(after & 2), bool(after & 4))
        if consume:
            self.consume()
        return result
