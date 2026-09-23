"""Experimental paired-successor execution model; no emitter or adopted ISA.

One 64x64 SRAM contains two atomic 32-row images. Each row holds the two
32-bit operations that may be entered next. An operation carries the row for
its own successors. Input-dependent choice and the next read address are both
computed before the edge; there is no extra branch cycle or combinational SRAM
read. The command interface below starts AFTER the existing serial sampler.
"""
from dataclasses import dataclass, replace


HOLD, SHIFT, CAPTURE, BRANCH, WAIT, HALT, FAULT = range(7)
WIDTHS = (('kind', 3), ('levels', 3), ('enabled', 3), ('duration', 8),
          ('arg', 5), ('row', 5), ('flags', 5))
ROWS = 32


@dataclass(frozen=True)
class Op:
    kind: int = HOLD
    levels: int = 0
    enabled: int = 0
    duration: int = 0
    arg: int = 0
    row: int = 0
    flags: int = 0

    def pack(self):
        value, offset = 0, 0
        for name, width in WIDTHS:
            field = getattr(self, name)
            if type(field) is not int or not 0 <= field < 1 << width:
                raise ValueError('field width: ' + name)
            value |= field << offset
            offset += width
        if not legal(self):
            raise ValueError('unsupported compact operation')
        return value


def decode(word):
    if type(word) is not int or not 0 <= word < 1 << 32:
        raise ValueError('compact word width')
    fields, offset = {}, 0
    for name, width in WIDTHS:
        fields[name] = (word >> offset) & ((1 << width) - 1)
        offset += width
    op = Op(**fields)
    if not legal(op):
        raise ValueError('unsupported compact operation')
    return op


def legal(op):
    if op.kind in (HALT, FAULT):
        return op == Op(kind=op.kind)
    if op.kind == HOLD:
        return op.arg == op.flags == 0
    if op.kind == SHIFT:
        # arg[1:0]: output pin; arg[2]: MSB-first (otherwise LSB-first).
        return op.arg < 8 and op.arg % 4 < 3 and op.flags == 0
    if op.kind == CAPTURE:
        # arg[3:0]: slot; arg[4]: input. flags[2:0]: keep prior output levels.
        return op.flags < 8
    if op.kind == BRANCH:
        # One slot for branch + optional entry/terminal captures. flags hold
        # entry-enable, terminal-enable, entry-input, terminal-input.
        return op.arg < 16 and op.flags < 16
    if op.kind == WAIT:
        return op.arg < 4 and op.flags == 0
    return False


@dataclass(frozen=True)
class Node:
    op: Op
    no: int = 0
    yes: int = 0


@dataclass(frozen=True)
class Image:
    rows: tuple
    idle: tuple
    used_rows: int

    def upload(self):
        return (*self.rows, self.idle[0] | self.idle[1] << 3)


def compile_graph(nodes, idle=(0, 0)):
    """Thread a finite graph without loops/counters added by the compiler.

    Row zero is the boot pair. Identical successor node pairs share a row;
    this is NOT a globally optimal graph minimizer. Capacity rejection refers
    to this concrete layout, not all possible compact-machine compilers.
    """
    if not nodes or len(idle) != 2 or any(type(x) is not int or not 0 <= x < 8 for x in idle):
        raise ValueError('invalid graph or idle pins')
    pairs = [(0, 0)]
    for node in nodes:
        if node.op.row:
            raise ValueError('compiler owns row addresses')
        node.op.pack()
        if node.op.kind in (HALT, FAULT):
            continue
        if not all(type(k) is int and 0 <= k < len(nodes) for k in (node.no, node.yes)):
            raise ValueError('missing successor')
        if node.op.kind != BRANCH and node.no != node.yes:
            raise ValueError('only branches have distinct successors')
        if (node.no, node.yes) not in pairs:
            pairs.append((node.no, node.yes))
    if len(pairs) > ROWS:
        raise ValueError(f'capacity: {len(pairs)} successor rows exceed {ROWS}')
    words = [replace(n.op, row=pairs.index((n.no, n.yes))).pack()
             if n.op.kind not in (HALT, FAULT) else n.op.pack() for n in nodes]
    rows = [words[a] | words[b] << 32 for a, b in pairs]
    padding = HALT | HALT << 32
    return Image(tuple(rows + [padding] * (ROWS - len(rows))), tuple(idle), len(rows))


def linear(ops, idle=(0, 0)):
    nodes = [Node(op, k + 1, k + 1) for k, op in enumerate(ops)]
    return compile_graph(nodes + [Node(Op(kind=HALT))], idle)


def uart_image():
    return linear([Op(levels=4, enabled=7, duration=3)] +
                  [Op(kind=SHIFT, levels=4, enabled=7, duration=3)] * 8 +
                  [Op(levels=5, enabled=7, duration=3)], (5, 7))


def spi_image():
    ops = []
    for slot in range(8):
        ops += [Op(kind=SHIFT, enabled=7, duration=3, arg=4),
                Op(kind=CAPTURE, levels=2, enabled=7, duration=3, arg=slot, flags=1)]
    return linear(ops + [Op(enabled=7, duration=3)], (4, 7))


def branch_image():
    # Same entry/terminal forwarding conflict as test/FetchChoice.lean.
    return compile_graph([Node(Op(kind=BRANCH, levels=k + 1, enabled=3,
                                 arg=15, flags=11), k, 1-k) for k in range(2)])


def lower_e64(fields, idle=(0, 0)):
    """Lower already-validated E64 field dictionaries in the supported subset.

    The existing independent E64 validator remains the admission oracle.
    Unsupported combinations fail explicitly instead of gaining extra cycles.
    """
    nodes = []
    for pc, d in enumerate(fields):
        kind, entry, terminal = d['kind'], d['entry'], d['terminal']
        op = Op(levels=d['levels'], enabled=d['enabled'], duration=d['duration'])
        no = yes = pc + 1
        if kind == 4:
            op = Op(kind=HALT)
        elif kind == 3:
            raise ValueError('capability: qualifying wait needs a second counter and guard')
        elif kind == 0:
            if entry:
                op = replace(op, kind=CAPTURE, arg=(entry >> 2) | ((entry >> 1 & 1) << 4))
        elif kind == 1:
            op = replace(op, kind=WAIT, arg=d['check'])
        elif kind == 2:
            if d['check']:
                raise ValueError('capability: checked guard has no compact encoding')
            slot = d['sample'] if d['finish'] == 2 else (terminal or entry) >> 2
            if any(c and c >> 2 != slot for c in (entry, terminal)):
                raise ValueError('capability: independent entry/terminal/branch slots')
            flags = bool(entry) | bool(terminal) << 1 | (entry >> 1 & 1) << 2 | (terminal >> 1 & 1) << 3
            op = replace(op, kind=BRANCH, arg=slot, flags=flags)
            if d['finish']:
                no = yes = d['yes']
            if d['finish'] == 2:
                no = d['no']
        else:
            raise ValueError('invalid E64 kind')
        # Out-of-range dispatch preserves the reference's fault observation.
        nodes.append(Node(op, no if no < len(fields) else len(fields),
                          yes if yes < len(fields) else len(fields)))
    return compile_graph(nodes + [Node(Op(kind=FAULT))], idle)


class Machine:
    """Clocked executable model with one macro access per edge.

    None SRAM/Q/start contents expose uninitialized reads. Reset never clears
    the arrays. `access` and `entries` are diagnostic history, not hardware
    state. Optional mutants deliberately break ownership/entry/branch timing.
    """
    def __init__(self, mutant=None):
        self.memory = [None] * 64
        self.meta = [(0, 0), (0, 0)]
        self.active = self.committed = self.pending = self.cursor = 0
        self.q = None
        self.start_word = None
        self.start_pending = False
        self.word = HALT
        self.mode = self.remaining = self.levels = self.enabled = self.samples = self.payload = 0
        self.result = None
        self.overrun = self.rejected = self.was_active = False
        self.access = []
        self.entries = 0
        self.mutant = mutant
        self.gates = (False,) * 4

    @property
    def busy(self):
        return self.mode in (1, 2, 3)

    def observe(self):
        return self.mode, self.levels, self.enabled, self.samples

    def stop(self, mode, samples=None):
        self.mode, self.remaining = mode, 0
        self.levels, self.enabled = self.meta[self.active] if self.committed else (0, 0)
        if samples is not None:
            self.samples = samples

    def capture(self, slot, pin, incoming):
        self.samples = (self.samples & ~(1 << slot)) | ((incoming >> pin & 1) << slot)

    def shift(self, op):
        pin, msb = op.arg % 4, bool(op.arg & 4)
        bit = self.payload >> (7 if msb else 0) & 1
        self.levels = (self.levels & ~(1 << pin)) | bit << pin
        self.payload = (self.payload << 1 & 255) if msb else self.payload >> 1

    def enter(self, word, incoming):
        op = decode(word)
        self.word = word
        self.entries += 1
        if op.kind in (HALT, FAULT):
            self.stop(5 if op.kind == HALT else 7)
            return
        previous = self.levels
        self.mode = 3 if op.kind == BRANCH else 2 if op.kind == WAIT else 1
        self.remaining, self.levels, self.enabled = op.duration, op.levels, op.enabled
        if op.kind == SHIFT:
            self.shift(op)
        elif op.kind == CAPTURE:
            self.levels = (self.levels & ~op.flags) | (previous & op.flags)
            self.capture(op.arg & 15, op.arg >> 4, incoming)
        elif op.kind == BRANCH and op.flags & 1:
            self.capture(op.arg, op.flags >> 2 & 1, incoming)

    def advance(self, incoming):
        op = decode(self.word)
        if op.kind == WAIT:
            dispatch = incoming >> (op.arg & 1) & 1 == op.arg >> 1
            if not dispatch and self.remaining == 0:
                self.stop(6)
                return
        else:
            dispatch = self.remaining == 0
        if not dispatch:
            self.remaining -= 1
            if self.mutant == 'shift-on-hold' and op.kind == SHIFT:
                self.shift(op)
            return
        choice = 0
        if op.kind == BRANCH:
            stale = self.samples >> op.arg & 1
            if op.flags & 2:
                self.capture(op.arg, op.flags >> 3 & 1, incoming)
            choice = stale if self.mutant == 'stale-branch' else self.samples >> op.arg & 1
        if self.q is None:
            raise RuntimeError('uninitialized successor response')
        self.enter(self.q >> (32 * choice) & 0xffffffff, incoming)

    def edge(self, command=0, data=0, incoming=0, reset=False, init=False,
             consume=False, clear=False):
        if not 0 <= incoming < 4 or not 0 <= command < 8 or not 0 <= data < 1 << 64:
            raise ValueError('input width')
        reset = reset or command == 7
        busy, old_word = self.busy, self.word
        enabled = not (init or reset or busy)
        good = False
        if self.cursor < 32:
            try:
                decode(data & 0xffffffff)
                decode(data >> 32)
                good = True
            except ValueError:
                pass
        elif self.cursor == 32:
            good = data < 64
        push = enabled and command == 2 and self.pending and self.cursor < 33 and good
        commit = enabled and command == 3 and self.pending and self.cursor == 33
        start = enabled and command == 5 and self.committed
        accepted = enabled and (command in (0, 1, 4) or push or commit or start)
        rejected = not (init or reset) and command != 0 and not accepted
        self.gates = bool(push), bool(commit), bool(start), bool(rejected)

        # Mailbox observes the state BEFORE this edge, matching arrival latency.
        arrival = self.was_active and self.mode in (5, 6, 7)
        if consume:
            self.result = None
        if clear:
            self.overrun = self.rejected = False
        if arrival:
            if self.result is None:
                self.result = (self.mode, self.samples)
            else:
                self.overrun = True
        self.rejected |= rejected
        self.was_active = busy or bool(start)

        # Save the response to the PREVIOUS commit. An immediate start uses
        # that same already-returned Q; an unrelated later write cannot lose it.
        if self.start_pending:
            if self.q is None:
                raise RuntimeError('uninitialized boot response')
            self.start_word = self.q & 0xffffffff
            self.start_pending = False
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
            self.active = 1 - self.active
            self.committed, self.pending, self.cursor = 1, 0, 0
            self.start_pending = True
            self.stop(0, 0)
        elif start:
            if self.start_word is None:
                raise RuntimeError('uninitialized start word')
            self.payload, self.samples = data & 255, 0
            self.enter(self.start_word, incoming)
        elif command == 1:
            self.pending, self.cursor = 1, 0
        elif command == 4:
            self.pending = self.cursor = 0

        # One synchronous macro transaction at this edge. Writes hold Q. The
        # new read address depends on selected OLD Q, never on this new Q.
        access = None
        if push:
            if self.cursor < 32:
                address = (1-self.active)*32 + self.cursor
                self.memory[address] = data
                access = ('write', address)
            else:
                self.meta[1-self.active] = (data & 7, data >> 3)
            self.cursor += 1
        elif commit or self.busy:
            request_word = old_word if self.mutant == 'stale-row' and busy else self.word
            address = self.active*32 + (0 if commit else decode(request_word).row)
            self.q = self.memory[address]
            if self.q is None:
                raise RuntimeError('uninitialized SRAM read')
            access = ('read', address)
        self.access.append(access)

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
    # All declared state, including the retained transport/observer contract.
    # These are logical widths, NOT synthesized cell counts or area estimates.
    state = dict(current_word=32, start_word=32, start_pending=1, mode=3,
                 remaining=8, pins=6, captures=16, payload=8,
                 atomic_bank_valid_pending=3, upload_cursor=6, idle_metadata=12,
                 input_sampler=12, serial_receiver=76, result_observer=35)
    return dict(declared_register_bits=sum(state.values()), register_bits_by_owner=state,
                macro_count=1, macro_array_bits=64*64, atomic_banks=2,
                rows_per_bank=32, word_bits=32, macro_data_bits=64,
                independent_reads_per_edge=1, candidate_words_per_read=2,
                image_upload_words=33, index_map_bits=0,
                unmeasured=['opcode/field validation', 'payload selection and shifts',
                            'successor-half selection and address path', 'loader decode',
                            'clock tree', 'hold repair', 'buffers and wires',
                            'routing and timing', 'serial/result wrapper composition'])
