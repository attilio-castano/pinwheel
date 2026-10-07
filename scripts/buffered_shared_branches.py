"""Opt-in reactive images with shared complete branch descriptors.

The engine's instruction, loop and endpoint meanings remain unchanged. This
representation has 64 allocated 92-bit rows and a separately uploaded bank of
16 full 56-bit branches. Its additional admission bound is 16 distinct branch
descriptors, including counted NEXT when present. Source binding reconstructs
the complete original reactive image before any transport I/O.
"""
from dataclasses import dataclass, field
import hashlib
import json

from buffered_counted_hardware import _definition, _read_program
from buffered_engine import BufferedProgram
from buffered_hardware import MAX_ID, LoadedBufferedHardware, _integer
from buffered_reactive_hardware import (BRANCH_WIDTH, CONTROL_WIDTH,
    INSTRUCTION_CAPACITY, INSTRUCTION_WIDTH, BufferedReactiveHardwareHost,
    BufferedReactiveHardwareImage, decode_branch, lower_reactive)
from pinwheel_buffers import TransferError


FORMAT = 'pinwheel-buffered-shared-branches32-v1'
BRANCH_CAPACITY = 16
BRANCH_INDEX_WIDTH = 4
ROW_WIDTH = INSTRUCTION_WIDTH + CONTROL_WIDTH + BRANCH_INDEX_WIDTH
ALLOCATED_BANK_BITS = INSTRUCTION_CAPACITY * ROW_WIDTH + BRANCH_CAPACITY * BRANCH_WIDTH
DECLARED_STATE_BITS = ALLOCATED_BANK_BITS + BRANCH_CAPACITY + 383


def _share(branches):
    """First appearance determines the index; unused bank entries are zero."""
    table, indices = [], []
    for branch in branches:
        if branch not in table:
            if len(table) == BRANCH_CAPACITY:
                raise ValueError('Shared branch image exceeds 16 distinct branch descriptors')
            table.append(branch)
        indices.append(table.index(branch))
    return tuple(indices), tuple(table + [0] * (BRANCH_CAPACITY - len(table)))


@dataclass(frozen=True)
class BufferedSharedBranchesImage:
    words: tuple[int, ...]
    controls: tuple[int, ...]
    branch_indices: tuple[int, ...]
    branch_table: tuple[int, ...]
    program_key: str
    source: BufferedProgram = field(repr=False)
    image_format: str = FORMAT
    _key: str = field(init=False, repr=False)
    _reactive: BufferedReactiveHardwareImage = field(init=False, repr=False, compare=False)

    def __post_init__(self):
        if self.image_format != FORMAT:
            raise ValueError('Wrong shared branch hardware image version')
        if (any(type(rows) is not tuple for rows in
                (self.words, self.controls, self.branch_indices, self.branch_table)) or
                not 1 <= len(self.words) <= INSTRUCTION_CAPACITY or
                not len(self.words) == len(self.controls) == len(self.branch_indices) or
                len(self.branch_table) != BRANCH_CAPACITY):
            raise ValueError('Shared image requires immutable 1..64 rows and exactly 16 branch entries')
        for index in self.branch_indices:
            _integer(index, 0, BRANCH_CAPACITY - 1, 'Shared branch index')
        for branch in self.branch_table:
            decode_branch(branch)
        reactive = lower_reactive(self.source)
        indices, table = _share(reactive.branches)
        if type(self.program_key) is not str or self.program_key != reactive.program_key:
            raise ValueError('Shared branch image differs from its original source identity')
        if (self.words, self.controls, self.branch_indices, self.branch_table) != (
                reactive.words, reactive.controls, indices, table):
            raise ValueError('Shared rows or dictionary differ from canonical source lowering')
        # Equality alone would admit Boolean substitutes for integer words.
        for word in self.words:
            _integer(word, 0, (1 << INSTRUCTION_WIDTH) - 1, 'Shared instruction word')
        for control in self.controls:
            _integer(control, 0, (1 << CONTROL_WIDTH) - 1, 'Shared loop descriptor')
        object.__setattr__(self, '_reactive', reactive)
        object.__setattr__(self, '_key', hashlib.sha256(json.dumps(self._canonical(),
            sort_keys=True, separators=(',', ':')).encode()).hexdigest())

    def _canonical(self):
        return dict(format=self.image_format, program_key=self.program_key,
            words=list(self.words), controls=list(self.controls),
            branch_indices=list(self.branch_indices), branch_table=list(self.branch_table),
            source=_definition(self.source), physical_count=len(self.words),
            virtual_span=self.virtual_span, tx_bits=self.tx_bits, rx_bits=self.rx_bits,
            rx_reservation_bits=self.rx_reservation_bits,
            distinct_branches=self.distinct_branches)

    @property
    def key(self): return self._key
    @property
    def branches(self): return tuple(self.branch_table[index] for index in self.branch_indices)
    @property
    def distinct_branches(self): return len(set(self.branch_indices))
    @property
    def virtual_span(self): return self._reactive.virtual_span
    @property
    def tx_bits(self): return self._reactive.tx_bits
    @property
    def rx_bits(self): return self._reactive.rx_bits
    @property
    def rx_reservation_bits(self): return self._reactive.rx_reservation_bits
    @property
    def idle_levels(self): return self._reactive.idle_levels
    @property
    def idle_enabled(self): return self._reactive.idle_enabled
    @property
    def wire_order(self): return self._reactive.wire_order
    @property
    def protocol(self): return self._reactive.protocol

    def storage(self):
        rows = len(self.words)
        return dict(self.source.storage(), physical_rows=rows,
            instruction_bits=INSTRUCTION_WIDTH * rows, control_bits=CONTROL_WIDTH * rows,
            branch_index_bits=BRANCH_INDEX_WIDTH * rows,
            branch_table_bits=BRANCH_CAPACITY * BRANCH_WIDTH,
            distinct_branches=self.distinct_branches, uploaded_bits=ROW_WIDTH * rows +
                BRANCH_CAPACITY * BRANCH_WIDTH,
            allocated_program_bits=ALLOCATED_BANK_BITS,
            declared_state_bits=DECLARED_STATE_BITS, image_format=FORMAT)

    def encode_tx(self, payload): return self._reactive.encode_tx(payload)
    def decode_rx(self, bits): return self._reactive.decode_rx(bits)

    def to_bytes(self):
        return (json.dumps(dict(self._canonical(), image_key=self.key),
                           sort_keys=True, indent=2) + '\n').encode()

    @classmethod
    def from_bytes(cls, data):
        if type(data) is not bytes:
            raise ValueError('Captured shared branch image must be bytes')
        obj = json.loads(data)
        required = {'format', 'program_key', 'image_key', 'words', 'controls',
            'branch_indices', 'branch_table', 'source', 'physical_count', 'virtual_span',
            'tx_bits', 'rx_bits', 'rx_reservation_bits', 'distinct_branches'}
        if (type(obj) is not dict or set(obj) != required or
                any(type(obj[k]) is not list for k in
                    ('words', 'controls', 'branch_indices', 'branch_table'))):
            raise ValueError('Unsupported shared branch hardware image schema')
        image = cls(tuple(obj['words']), tuple(obj['controls']), tuple(obj['branch_indices']),
            tuple(obj['branch_table']), obj['program_key'], _read_program(obj['source']), obj['format'])
        expected = dict(physical_count=len(image.words), virtual_span=image.virtual_span,
            tx_bits=image.tx_bits, rx_bits=image.rx_bits, rx_reservation_bits=image.rx_reservation_bits,
            distinct_branches=image.distinct_branches)
        if (any(type(obj[k]) is not int or obj[k] != v for k, v in expected.items()) or
                obj['image_key'] != image.key):
            raise ValueError('Shared image demand, span, dictionary or identity metadata differs')
        return image


def lower_shared_branches(program):
    reactive = lower_reactive(program)
    indices, table = _share(reactive.branches)
    return BufferedSharedBranchesImage(reactive.words, reactive.controls, indices,
        table, reactive.program_key, program)


class BufferedSharedBranchesHost(BufferedReactiveHardwareHost):
    """The reactive owned lifecycle with a complete dictionary upload first."""
    def _prepare_image(self, source):
        image = lower_shared_branches(source) if type(source) is BufferedProgram else source
        if type(image) is not BufferedSharedBranchesImage:
            raise ValueError('Shared branch load requires its versioned image')
        return BufferedSharedBranchesImage.from_bytes(image.to_bytes())

    def _write_fields(self, image, address):
        return dict(command=1, address=address, word=image.words[address],
                    control=image.controls[address], branch=image.branch_indices[address])

    def load(self, source):
        image = self._prepare_image(source)
        if self._pending is not None:
            raise TransferError('Release or reset the owned transfer before loading an image')
        before = self._edge(command=0)
        if before['busy'] or before['retained']:
            raise TransferError('Hardware transfer remains owned')
        if before['generation'] == MAX_ID:
            raise TransferError('Hardware generation is exhausted; cold initialize a new epoch')
        self._image = self._generation = None
        for address, branch in enumerate(image.branch_table):
            written = self._edge(command=6, address=address, branch=branch)
            if written['rejected'] or written['busy'] or written['retained'] or not written['pending']:
                raise TransferError('Hardware rejected shared branch dictionary upload')
        for address in range(len(image.words)):
            written = self._edge(**self._write_fields(image, address))
            if written['rejected'] or written['busy'] or written['retained'] or not written['pending']:
                raise TransferError('Hardware rejected buffered instruction upload')
        committed = self._edge(**self._commit_fields(image))
        if (committed['rejected'] or not committed['valid'] or committed['pending'] or
                committed['busy'] or committed['retained'] or
                committed['generation'] != before['generation'] + 1 or
                committed['transfer'] != before['transfer']):
            raise TransferError('Hardware did not accept the exact shared branch image commit')
        self._image, self._generation = image, committed['generation']
        return LoadedBufferedHardware(self, image, self._epoch, self._generation)
