"""Single-transfer buffer ownership and a host for the buffered reference model.

This is a software/model interface, not a transport for the retained paired chip.
TX is copied in wire order; RX has a separate reserved capacity. Identity counters
are mathematical nonwrapping integers, not a proposed physical register encoding.
"""
from dataclasses import dataclass
from uuid import uuid4


def _natural(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f'{name} must be a nonnegative integer')
    return value


class TransferError(RuntimeError):
    """The operation does not own the current transfer or its current phase."""


class BufferFault(TransferError):
    """A running program attempted to exceed its admitted data bounds."""


@dataclass(frozen=True)
class TransferId:
    epoch: int
    sequence: int
    owner: str = ''

    def __post_init__(self):
        _natural(self.epoch, 'Identity epoch')
        _natural(self.sequence, 'Identity sequence')
        if type(self.owner) is not str:
            raise ValueError('Identity owner must be a slot namespace string')


@dataclass(frozen=True)
class Descriptor:
    identity: TransferId
    program_key: str
    program_generation: int
    tx_bit_count: int
    rx_limit: int


@dataclass(frozen=True)
class Completion:
    identity: TransferId
    program_key: str
    program_generation: int
    outcome: str
    tx_consumed_bits: int
    rx_bits: tuple[bool, ...]

    @property
    def id(self):
        return self.identity


class TransferSlot:
    """One slot: free -> preparing -> running -> completed -> free.

    Rejection never mutates the slot. Reads do not consume a completion. Data
    access is gated here, rather than relying only on a friendly host caller.
    """
    def __init__(self, *, tx_capacity_bits=32, rx_capacity_bits=32):
        self._tx_capacity = _natural(tx_capacity_bits, 'TX capacity')
        self._rx_capacity = _natural(rx_capacity_bits, 'RX capacity')
        self._owner = uuid4().hex
        self._epoch, self._next_sequence = 0, 1
        self._clear()

    def _clear(self):
        self._state = 'free'
        self._descriptor = None
        self._tx = ()
        self._tx_consumed = 0
        self._rx = ()
        self._completion = None

    @property
    def state(self):
        return self._state

    @property
    def descriptor(self):
        return self._descriptor

    @property
    def tx_capacity_bits(self):
        return self._tx_capacity

    @property
    def rx_capacity_bits(self):
        return self._rx_capacity

    @property
    def tx_length(self):
        return 0 if self._descriptor is None else self._descriptor.tx_bit_count

    @property
    def rx_limit(self):
        return 0 if self._descriptor is None else self._descriptor.rx_limit

    def _require(self, identity, phase):
        if (type(identity) is not TransferId or self._descriptor is None or
                identity != self._descriptor.identity):
            raise TransferError('Stale or unowned transfer identity')
        if self._state != phase:
            raise TransferError(f'Transfer requires {phase}; currently {self._state}')

    def prepare(self, program_key, tx_bits, rx_limit, *, program_generation=0):
        if self._state != 'free':
            raise TransferError('Release the current transfer before preparing another')
        if type(program_key) is not str or not program_key:
            raise ValueError('Program key must be a nonempty string')
        _natural(program_generation, 'Program generation')
        _natural(rx_limit, 'RX limit')
        if rx_limit > self._rx_capacity:
            raise ValueError('RX reservation exceeds buffer capacity')
        # Bound materialization, including iterators, before accepting ownership.
        bits = []
        for bit in tx_bits:
            if type(bit) is not bool:
                raise ValueError('TX wire bits must be Booleans')
            if len(bits) == self._tx_capacity:
                raise ValueError('TX data exceeds buffer capacity')
            bits.append(bit)
        identity = TransferId(self._epoch, self._next_sequence, self._owner)
        descriptor = Descriptor(identity, program_key, program_generation,
                                len(bits), rx_limit)
        self._descriptor, self._tx = descriptor, tuple(bits)
        self._next_sequence += 1
        self._state = 'preparing'
        return identity

    def start(self, identity, *, program_generation=None):
        self._require(identity, 'preparing')
        if program_generation is not None:
            _natural(program_generation, 'Program generation')
            if program_generation != self._descriptor.program_generation:
                raise TransferError('Prepared transfer belongs to a different program generation')
        self._state = 'running'

    def begin(self, program_key, tx_bits, rx_limit, *, program_generation=0):
        """Validate, copy, and accept START without an intervening caller edge."""
        identity = self.prepare(program_key, tx_bits, rx_limit,
                                program_generation=program_generation)
        self.start(identity, program_generation=program_generation)
        return identity

    def take_tx(self, identity):
        self._require(identity, 'running')
        if self._tx_consumed == len(self._tx):
            raise BufferFault('TX buffer underflow')
        bit = self._tx[self._tx_consumed]
        self._tx_consumed += 1
        return bit

    def append_rx(self, identity, bit):
        self._require(identity, 'running')
        if type(bit) is not bool:
            raise ValueError('RX wire bit must be a Boolean')
        if len(self._rx) == self._descriptor.rx_limit:
            raise BufferFault('RX buffer overflow')
        self._rx += (bit,)

    def complete(self, identity, outcome='complete'):
        self._require(identity, 'running')
        if type(outcome) is not str or outcome not in ('complete', 'timeout', 'fault'):
            raise ValueError('Unknown terminal transfer outcome')
        self._completion = Completion(identity, self._descriptor.program_key,
            self._descriptor.program_generation, outcome, self._tx_consumed, self._rx)
        self._state = 'completed'

    def peek(self, identity):
        self._require(identity, 'completed')
        return self._completion

    def release(self, identity):
        self._require(identity, 'completed')
        self._clear()

    def reset(self):
        """Flush ownership and invalidate all prior handles, including unread ones."""
        self._epoch += 1
        self._next_sequence = 1
        self._clear()

    def inspect(self):
        return dict(target='buffered-reference-v1', state=self.state,
                    tx_capacity_bits=self._tx_capacity, rx_capacity_bits=self._rx_capacity,
                    data_storage_bits=self._tx_capacity + self._rx_capacity,
                    capacity_is_physical_qualification=False,
                    identity_counters='nonwrapping model integers')


@dataclass(frozen=True)
class BufferedResult:
    identity: TransferId
    program_key: str
    program_generation: int
    protocol: str
    outcome: str
    tx_consumed_bits: int
    rx_valid_bits: int
    payload: bytes | None
    raw_rx_bits: tuple[bool, ...]


class HostWaitTimeout(TimeoutError):
    def __init__(self, pending):
        super().__init__('Host wait expired; transfer ownership and execution are unchanged')
        self.pending = pending


class BufferedExecutionError(TransferError):
    """A local model/peer failure with its accepted transfer still recoverable."""
    def __init__(self, pending, cause):
        super().__init__(f'Buffered execution failed; retained transfer is available: {cause}')
        self.pending, self.cause = pending, cause


class _ZeroPeer:
    def drive(self, cycle, pads, ui):
        from pad_io import PadDrive
        return PadDrive(0, 3)


class BufferedModelHost:
    """Execute buffered programs locally; no existing chip commands are sent."""
    def __init__(self, *, tx_capacity_bits=32, rx_capacity_bits=32):
        self.slot = TransferSlot(tx_capacity_bits=tx_capacity_bits,
                                 rx_capacity_bits=rx_capacity_bits)
        self._program, self._program_key = None, None
        self._generation = 0
        self._simulation = None
        self.edges = 0

    def load(self, program):
        from buffered_engine import BufferedProgram
        if self.slot.state != 'free':
            raise TransferError('Release the current transfer before replacing its program')
        if type(program) is not BufferedProgram or program.target != 'buffered-reference-v1':
            raise ValueError('BufferedModelHost requires a buffered reference program')
        if (program.tx_bits > self.slot.tx_capacity_bits or
                program.rx_reservation_bits > self.slot.rx_capacity_bits):
            raise ValueError('Program data requirements exceed model buffer capacities')
        program.validate_transfer((False,) * program.tx_bits, program.rx_reservation_bits)
        self._program, self._program_key = program, program.key
        self._generation += 1
        return LoadedBufferedTransaction(self, program, program.key, self._generation)

    def _submit(self, loaded, tx, rx_limit, peer):
        from buffered_engine import BufferedEngine, BufferedWireSimulation
        if (loaded.generation != self._generation or loaded.program is not self._program or
                loaded.program_key != self._program_key or loaded.program.key != loaded.program_key):
            raise TransferError('Buffered session lost its loaded program; load it again')
        if self.slot.state != 'free':
            raise TransferError('Release the current transfer before submitting another')
        if type(tx) not in (bytes, bytearray, memoryview):
            raise ValueError('TX payload must be bytes or a byte buffer')
        bits = loaded.program.encode_tx(bytes(tx))
        if rx_limit is None:
            rx_limit = loaded.program.rx_reservation_bits
        _natural(rx_limit, 'RX limit')
        loaded.program.validate_transfer(bits, rx_limit)
        if peer is not None and not callable(getattr(peer, 'drive', None)):
            raise ValueError('A peer must expose a wire drive callback')
        identity = self.slot.begin(loaded.program_key, bits, rx_limit,
                                   program_generation=loaded.generation)
        pending = PendingTransfer(self, loaded.program, identity)
        self._simulation = None
        engine = None
        try:
            engine = BufferedEngine(self.slot, identity, loaded.program)
            self._simulation = BufferedWireSimulation(engine, peer if peer is not None else _ZeroPeer())
        except Exception as error:
            self._retain_failure(pending, error, engine)
        return pending

    def _retain_failure(self, pending, error, engine):
        if self.slot.state == 'running':
            if engine is None:
                self.slot.complete(pending.identity, 'fault')
            else:
                engine.fail()
        raise BufferedExecutionError(pending, error) from error

    def advance(self, cycles=1):
        _natural(cycles, 'Advance cycles')
        if cycles == 0:
            raise ValueError('Advance requires at least one edge')
        if self._simulation is None:
            raise TransferError('No buffered execution to advance')
        for _ in range(cycles):
            if self.slot.state != 'running':
                break
            previous = self._simulation.engine.cycle
            try:
                self._simulation.step()
            except Exception as error:
                self.edges += self._simulation.engine.cycle - previous
                pending = PendingTransfer(self, self._program,
                                          self.slot.descriptor.identity)
                self._retain_failure(pending, error, self._simulation.engine)
            self.edges += self._simulation.engine.cycle - previous

    def reset(self):
        self.slot.reset()
        self._generation += 1
        self._program, self._program_key, self._simulation = None, None, None


@dataclass(frozen=True)
class LoadedBufferedTransaction:
    host: BufferedModelHost
    program: object
    program_key: str
    generation: int

    def submit(self, *, tx, rx_limit=None, peer=None):
        return self.host._submit(self, tx, rx_limit, peer)

    def run(self, *, tx, rx_limit=None, peer=None, timeout_cycles=100_000):
        _natural(timeout_cycles, 'Timeout cycles')
        pending = self.submit(tx=tx, rx_limit=rx_limit, peer=peer)
        pending.wait(timeout_cycles=timeout_cycles)
        result = pending.read()  # decode failure preserves the unread transfer
        pending.release()
        return result


@dataclass(frozen=True)
class PendingTransfer:
    host: BufferedModelHost
    program: object
    identity: TransferId

    def wait(self, *, timeout_cycles=100_000):
        _natural(timeout_cycles, 'Timeout cycles')
        descriptor = self.host.slot.descriptor
        if descriptor is None or descriptor.identity != self.identity:
            raise TransferError('Stale or unowned transfer identity')
        deadline = self.host.edges + timeout_cycles
        while self.host.slot.state == 'running':
            remaining = deadline - self.host.edges
            if remaining <= 0:
                raise HostWaitTimeout(self)
            self.host.advance(min(16, remaining))
        return self.host.slot.peek(self.identity)

    def read(self):
        raw = self.host.slot.peek(self.identity)
        if self.program.key != raw.program_key:
            raise TransferError('Result interpretation differs from its accepted program')
        if raw.outcome == 'complete' and raw.tx_consumed_bits != self.program.tx_bits:
            raise ValueError('Completed transfer did not consume the declared TX data')
        payload = self.program.decode_rx(raw.rx_bits) if raw.outcome == 'complete' else None
        return BufferedResult(raw.identity, raw.program_key, raw.program_generation,
            self.program.protocol, raw.outcome, raw.tx_consumed_bits,
            len(raw.rx_bits), payload, raw.rx_bits)

    def release(self):
        self.host.slot.release(self.identity)
