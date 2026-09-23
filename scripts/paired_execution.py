"""Full E64-operation study: paired 32-bit tokens and banked 20-bit parameters.

One synchronous 512x64 macro holds two 256-row atomic images. The parameter
table is explicitly a two-bank, combinationally read FF array, NOT another
zero-latency SRAM. The original compact_execution.py experiment is unchanged.
No production emitter, E64 wire-format compatibility or physical fit is implied.
"""
from dataclasses import dataclass
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[1]
GRAMMAR = runpy.run_path(str(ROOT / 'scripts/execution-vectors.py'))
ROWS, PARAMETERS = 256, 32
HALT, SHIFT, KEEP, FAULT = 4, 5, 6, 7


def fields(word):
    result, offset = {}, 0
    for name, width in GRAMMAR['FIELDS']:
        result[name] = word >> offset & ((1 << width)-1)
        offset += width
    return result


def parameter(d):
    if d['kind'] == 3:
        return d['budget'] | d['check'] << 12
    return d['entry'] | d['terminal'] << 6 | d['check'] << 12 | d['sample'] << 16


def token(kind, levels=0, enabled=0, duration=0, param=0, row=0):
    values = (kind, levels, enabled, duration, param, row)
    widths = (3, 3, 3, 8, 5, 8)
    word, offset = 0, 0
    for v, width in zip(values, widths):
        if type(v) is not int or not 0 <= v < 1 << width:
            raise ValueError('token field width')
        word |= v << offset
        offset += width
    return word


def unpack(word):
    if type(word) is not int or not 0 <= word < 1 << 30:
        raise ValueError('reserved token bits or width')
    return dict(kind=word & 7, levels=word >> 3 & 7, enabled=word >> 6 & 7,
                duration=word >> 9 & 255, param=word >> 17 & 31, row=word >> 22 & 255)


def capture_valid(c):
    return bool(c & 1) or c == 0


def valid_token(word, params):
    try:
        d = unpack(word)
        if d['kind'] in (HALT, FAULT):
            return word == d['kind']
        p = params[d['param']]
        if type(p) is not int or not 0 <= p < 1 << 20:
            return False
        if d['kind'] == 0:
            return p < 64 and capture_valid(p)
        if d['kind'] == 1:
            return p & ~0x3000 == 0
        if d['kind'] == 2:
            return capture_valid(p & 63) and capture_valid(p >> 6 & 63)
        if d['kind'] == 3:
            return p & ~0xf0ff == 0
        if d['kind'] == SHIFT:
            return p < 8 and p % 4 < 3
        return p < 512 and capture_valid(p & 63)  # KEEP: capture + pin-preserve mask.
    except (ValueError, IndexError, TypeError):
        return False


@dataclass(frozen=True)
class Image:
    parameters: tuple
    rows: tuple
    boot: int
    idle: tuple
    used_parameters: int
    logical_positions: int

    def upload(self):
        return (*self.parameters, *self.rows, self.boot, self.idle[0] | self.idle[1] << 3)


def assemble(operations, successors, idle=(0, 0)):
    """Each (kind, levels, enables, duration, parameter) token owns row=PC.

    None successors become explicit faults. Boot lives in banked metadata,
    leaving every row available for an executable position. No loop recovery,
    branch restrictions, duration restriction or graph minimization is assumed.
    """
    if not 1 <= len(operations) <= ROWS or len(successors) != len(operations):
        raise ValueError('program capacity')
    if len(idle) != 2 or any(type(x) is not int or not 0 <= x < 8 for x in idle):
        raise ValueError('idle width')
    unique = list(dict.fromkeys(op[4] for op in operations if op[0] not in (HALT, FAULT)))
    if len(unique) > PARAMETERS:
        raise ValueError('parameter capacity')
    params = tuple(unique + [0]*(PARAMETERS-len(unique)))
    tokens = [op[0] if op[0] in (HALT, FAULT) else token(*op[:4], unique.index(op[4]), pc)
              for pc, op in enumerate(operations)]
    if not all(valid_token(t, params) for t in tokens):
        raise ValueError('invalid operation/parameter combination')

    def selected(pc):
        if pc is None:
            return FAULT
        if type(pc) is not int or not 0 <= pc < len(tokens):
            raise ValueError('unknown successor')
        return tokens[pc]

    rows = tuple(selected(a) | selected(b) << 32 for a, b in successors)
    return Image(params, rows + (HALT | HALT << 32,)*(ROWS-len(rows)),
                 tokens[0], tuple(idle), len(unique), len(tokens))


def compile_e64(words, idle=(0, 0), last=None):
    """Compile every canonical image admitted by the current 32-record limit.

    The full supplied/padded image participates in the admission count. As in
    E64, only addresses <= last may be entered; all other branches become faults.
    The parameter projection cannot have more distinct values than its records.
    """
    if not 1 <= len(words) <= 256 or not all(type(w) is int and GRAMMAR['decode'](w) for w in words):
        raise ValueError('E64 grammar or size')
    padded = list(words) + [4]*(256-len(words))
    if len(set(padded)) > 32:
        raise ValueError('E64 dictionary capacity')
    last = len(words)-1 if last is None else last
    if type(last) is not int or not 0 <= last < 256:
        raise ValueError('E64 last address')
    operations, successors = [], []
    for pc, word in enumerate(padded[:last+1]):
        d = fields(word)
        operations.append((d['kind'], d['levels'], d['enabled'], d['duration'], parameter(d)))
        no = yes = pc+1
        if d['kind'] == 2 and d['finish']:
            no = yes = d['yes']
        if d['kind'] == 2 and d['finish'] == 2:
            no = d['no']
        successors.append((no if no <= last else None, yes if yes <= last else None))
    return assemble(operations, successors, idle)


def linear(operations, idle):
    ops = [*operations, (HALT, 0, 0, 0, 0)]
    return assemble(ops, [(k+1, k+1) if k+1 < len(ops) else (None, None)
                          for k in range(len(ops))], idle)


def uart_image():
    return linear([(0,4,7,3,0)] + [(SHIFT,4,7,3,0)]*8 + [(0,5,7,3,0)], (5,7))


def spi_image():
    ops = []
    for slot in range(8):
        ops += [(SHIFT,0,7,3,4), (KEEP,2,7,3,(1+4*slot) | 1 << 6)]
    return linear(ops + [(0,0,7,3,0)], (4,7))


class Machine:
    def __init__(self, mutant=None):
        self.memory = [None]*512
        self.parameters = [[None]*32 for _ in range(2)]
        self.boot = [None, None]
        self.idle = [(0,0), (0,0)]
        self.active = self.committed = self.pending = self.cursor = 0
        self.q = None
        self.word, self.param = HALT, 0
        self.mode = self.remaining = self.wait_left = self.levels = self.enabled = self.samples = self.payload = 0
        self.result = None
        self.overrun = self.rejected = self.was_active = False
        self.gates = (False,)*4
        self.access, self.parameter_access = [], []  # Diagnostic, not stored hardware state.
        self.mutant = mutant

    @property
    def busy(self):
        return 1 <= self.mode <= 4

    @property
    def s(self):
        return [self.mode, unpack(self.word)['row'] if self.busy else 0,
                self.remaining, self.wait_left, self.levels, self.enabled, self.samples]

    def observe(self):
        return self.mode, self.levels, self.enabled, self.samples

    def stop(self, mode, samples=None):
        self.mode, self.remaining, self.wait_left = mode, 0, 0
        self.levels, self.enabled = self.idle[self.active] if self.committed else (0,0)
        if samples is not None:
            self.samples = samples

    def capture(self, descriptor, incoming):
        if descriptor & 1:
            slot = descriptor >> 2
            self.samples = (self.samples & ~(1 << slot)) | ((incoming >> (descriptor >> 1 & 1) & 1) << slot)

    def enter(self, word, incoming):
        d = unpack(word)
        self.word = word
        if d['kind'] in (HALT, FAULT):
            self.stop(5 if d['kind'] == HALT else 7)
            return
        bank = 1-self.active if self.mutant == 'wrong-parameter-bank' else self.active
        self.param = self.parameters[bank][d['param']]
        self.parameter_access[-1].append((bank, d['param']))
        if self.param is None:
            raise RuntimeError('uninitialized parameter read')
        previous = self.levels
        self.mode = d['kind']+1 if d['kind'] <= 3 else 1
        self.remaining = d['duration']
        self.wait_left = self.param & 255 if d['kind'] == 3 else 0
        self.levels, self.enabled = d['levels'], d['enabled']
        if d['kind'] in (0, 2, KEEP):
            self.capture(self.param & 63, incoming)
        if d['kind'] == KEEP:
            keep = self.param >> 6 & 7
            self.levels = self.levels & ~keep | previous & keep
        if d['kind'] == SHIFT:
            self.shift()

    def shift(self):
        pin, msb = self.param & 3, bool(self.param & 4)
        bit = self.payload >> (7 if msb else 0) & 1
        self.levels = self.levels & ~(1 << pin) | bit << pin
        self.payload = self.payload << 1 & 255 if msb else self.payload >> 1

    def advance(self, incoming):
        d = unpack(self.word)
        check = self.param >> 12 & 15
        guarded = (incoming & (check & 3)) == ((check >> 2) & (check & 3))
        if self.mode == 3 and not guarded:
            self.stop(7)
            return
        if self.mode == 4 and not guarded:
            if self.wait_left:
                self.remaining, self.wait_left = d['duration'], self.wait_left-1
            else:
                self.stop(6)
            return
        dispatch = self.remaining == 0
        if self.mode == 2:
            dispatch = (incoming >> (check & 1) & 1) == (check >> 1 & 1)
            if not dispatch and not self.remaining:
                self.stop(6)
                return
        if not dispatch:
            self.remaining -= 1
            if self.mode == 4 and self.mutant != 'no-budget-renewal':
                self.wait_left = self.param & 255
            if d['kind'] == SHIFT and self.mutant == 'shift-on-hold':
                self.shift()
            return
        choice = 0
        if self.mode == 3:
            slot = self.param >> 16
            stale = self.samples >> slot & 1
            self.capture(self.param >> 6 & 63, incoming)
            choice = stale if self.mutant == 'stale-branch' else self.samples >> slot & 1
        if self.q is None:
            raise RuntimeError('uninitialized SRAM response')
        self.enter(self.q >> (32*choice) & 0xffffffff, incoming)

    def edge(self, command=0, data=0, incoming=0, reset=False, init=False, consume=False, clear=False):
        if not (0 <= command < 8 and 0 <= data < 1 << 64 and 0 <= incoming < 4):
            raise ValueError('input width')
        reset = reset or command == 7
        busy, old_word = self.busy, self.word
        enabled = not (init or reset or busy)
        self.parameter_access.append([])
        inactive = 1-self.active
        good = False
        if enabled and command == 2 and self.pending:
            if self.cursor < 32:
                good = data < 1 << 20
            elif self.cursor < 288:
                indices = [data >> (32*k+17) & 31 for k in range(2)]
                self.parameter_access[-1].extend((inactive, k) for k in indices)
                good = all(valid_token(data >> (32*k) & 0xffffffff, self.parameters[inactive]) for k in range(2))
            elif self.cursor == 288:
                self.parameter_access[-1].append((inactive, data >> 17 & 31))
                good = data < 1 << 32 and valid_token(data, self.parameters[inactive])
            elif self.cursor == 289:
                good = data < 64
        push = enabled and command == 2 and self.pending and self.cursor < 290 and good
        commit = enabled and command == 3 and self.pending and self.cursor == 290
        start = enabled and command == 5 and self.committed
        accepted = enabled and (command in (0,1,4) or push or commit or start)
        rejected = not (init or reset) and command != 0 and not accepted
        self.gates = bool(push), bool(commit), bool(start), bool(rejected)
        arrival = self.was_active and self.mode in (5,6,7)
        if consume:
            self.result = None
        if clear:
            self.overrun = self.rejected = False
        if arrival:
            if self.result is None:
                self.result = self.mode, self.samples
            else:
                self.overrun = True
        self.rejected |= rejected
        self.was_active = busy or bool(start)
        if init:
            self.active = self.committed = self.pending = self.cursor = 0
            self.result = None
            self.overrun = self.rejected = self.was_active = False
            self.payload = 0
            self.stop(0, 0)
        elif reset:
            self.pending = self.cursor = 0
            self.payload = 0
            self.stop(0, 0)
        elif busy:
            if self.mutant == 'busy-payload' and command == 5:
                self.payload = data & 255
            self.advance(incoming)
        elif commit:
            self.active = inactive
            self.committed, self.pending, self.cursor = 1, 0, 0
            self.stop(0, 0)
        elif start:
            self.samples, self.payload = 0, data & 255
            self.enter(self.boot[self.active], incoming)
        elif command == 1:
            self.pending, self.cursor = 1, 0
        elif command == 4:
            self.pending = self.cursor = 0
        access = None
        if push:
            if self.cursor < 32:
                self.parameters[inactive][self.cursor] = data
            elif self.cursor < 288:
                address = inactive*256 + self.cursor-32
                self.memory[address] = data
                access = 'write', address
            elif self.cursor == 288:
                self.boot[inactive] = data
            else:
                self.idle[inactive] = data & 7, data >> 3
            self.cursor += 1
        elif self.busy:
            request = old_word if self.mutant == 'stale-row' and busy else self.word
            address = self.active*256 + unpack(request)['row']
            self.q = self.memory[address]
            if self.q is None:
                raise RuntimeError('uninitialized SRAM read')
            access = 'read', address
        self.access.append(access)
        if len(self.parameter_access[-1]) > 2:
            raise RuntimeError('unbudgeted parameter port')

    def load(self, image):
        self.edge(command=1)
        for word in image.upload():
            self.edge(command=2, data=word)
            if not self.gates[0]:
                raise ValueError('image push rejected')
        self.edge(command=3)
        if not self.gates[1]:
            raise ValueError('image commit rejected')


def resource_budget():
    state = dict(parameters=2*32*20, boot=2*32, current_token=32, current_parameter=20,
                 mode=3, remaining=8, wait_left=8, pins=6, captures=16, payload=8,
                 atomic_bank_valid_pending=3, upload_cursor=9, idle_metadata=12,
                 input_sampler=12, serial_receiver=76, result_observer=35)
    return dict(declared_register_bits=sum(state.values()), register_bits=state,
                macro='RM_IHPSG13_1P_512x64_c2_bm_bist', macro_count=1,
                macro_array_bits=512*64, rows_per_atomic_bank=256,
                parameter_read_ports=2, parameter_write_ports=1,
                parameter_reads_per_entry=1, parameter_reads_per_row_upload=2,
                synchronous_sram_reads_per_execution_edge=1, logical_successors_per_read=2,
                upload_words=290, index_map_bits=0,
                critical_paths=['SRAM Q -> half selection -> 8-bit row -> SRAM address',
                                'SRAM Q -> half selection -> parameter table -> entry capture/state',
                                'serial word -> two parameter reads -> validation -> upload admission'],
                unmeasured=['full emitted controller', 'parameter muxes and write decode',
                            'opcode/parameter validation', 'clock distribution', 'hold repair',
                            'wire and pin access', 'package integration and correspondence'])
