"""One request/compile/load/run/decode workflow for the existing paired engine.

Protocols keep independent Lean specifications. This layer binds their compiled
image to pin requirements, START payload capacity and result interpretation.
Timing is in chip edges; board electrical and sampling assumptions are separate.
"""
from dataclasses import dataclass, asdict
import json
from pathlib import Path
import subprocess
import sys

from pinwheel_host import Host, Program, Result, PAIRED_FORMAT
from pinwheel_program import resident_uart, resident_spi, resource_report
from protocol_results import i2c_read_result

ROOT = Path(__file__).resolve().parents[1]
REQUEST_SCHEMA = 'pinwheel-protocol-request-v1'
ARTIFACT_SCHEMA = 'pinwheel-transaction-v1'


class CapabilityError(ValueError):
    """A request exceeds the declared engine or implemented frontend capability."""


def _integer(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer in {low}..{high}')
    return value


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON field: ' + key)
        result[key] = value
    return result


def _loads(data):
    return json.loads(data, object_pairs_hook=_object)


def _validate_request(request):
    if not isinstance(request, dict) or request.get('schema') != REQUEST_SCHEMA:
        raise ValueError('Unsupported protocol request schema')
    protocol = request.get('protocol')
    keys = {'schema', 'protocol'}
    if protocol == 'uart-tx':
        keys |= {'bit_cycles'}
    elif protocol == 'spi-resident':
        keys |= {'half_cycles'}
    elif protocol == 'spi-transaction':
        keys |= {'mode', 'payload', 'half_cycles'}
    elif protocol == 'i2c-register-read':
        keys |= {'address', 'register', 'byte_count', 'phase_cycles', 'wait_cycles'}
    elif protocol == 'jtag-scan':
        keys |= {'outgoing_bits', 'captured_bits', 'half_cycles'}
    else:
        raise ValueError('Unsupported transaction protocol')
    if set(request) != keys:
        raise ValueError('Unexpected or missing protocol request fields')
    for field in ('bit_cycles', 'half_cycles', 'phase_cycles', 'wait_cycles'):
        if field in request:
            _integer(request[field], 1, 256, field)
    if protocol == 'spi-transaction':
        _integer(request['mode'], 0, 3, 'SPI mode')
        values = request['payload']
        if not isinstance(values, list) or not 1 <= len(values) <= 2:
            raise CapabilityError('Fixed SPI transactions support one or two bytes')
        for value in values:
            _integer(value, 0, 255, 'SPI payload byte')
    if protocol == 'i2c-register-read':
        _integer(request['address'], 0, 127, 'I2C address')
        _integer(request['register'], 0, 255, 'I2C register')
        count = request['byte_count']
        if type(count) is not int or count not in (1, 2):
            raise CapabilityError('I2C reads support one or two bytes in the 16-bit result')
    if protocol == 'jtag-scan':
        outgoing = _integer(request['outgoing_bits'], 1, 65536, 'Outgoing bits')
        captured = _integer(request['captured_bits'], 1, 65536, 'Captured bits')
        if outgoing > 8 or captured > 16:
            raise CapabilityError('JTAG request exceeds the 8-bit START operand or 16 capture slots')
        if outgoing != 8 or captured != 8:
            raise CapabilityError('This JTAG frontend implements an eight-bit transmit/receive scan')
    return request


@dataclass(frozen=True)
class TransactionSpec:
    """Immutable protocol intent; constructing it performs no chip or compiler I/O."""
    request_json: str

    def __post_init__(self):
        _validate_request(_loads(self.request_json))

    @property
    def request(self):
        return _loads(self.request_json)

    @classmethod
    def from_request(cls, request):
        _validate_request(request)
        return cls(json.dumps(request, sort_keys=True, separators=(',', ':')))


def _spec(protocol, **values):
    return TransactionSpec.from_request(dict(schema=REQUEST_SCHEMA, protocol=protocol, **values))


def uart_tx(*, bit_cycles=4):
    return _spec('uart-tx', bit_cycles=bit_cycles)


def spi_transfer(payload=None, *, mode=0, half_cycles=4):
    """Resident mode-0 byte when payload is omitted; fixed one/two-byte modes 0..3 otherwise."""
    _integer(mode, 0, 3, 'SPI mode')
    if payload is None:
        if mode != 0:
            raise CapabilityError('Resident SPI currently supports mode 0; supply fixed bytes for modes 1..3')
        return _spec('spi-resident', half_cycles=half_cycles)
    if not isinstance(payload, (tuple, list, bytes)):
        raise ValueError('Fixed SPI payload must be a byte sequence')
    return _spec('spi-transaction', mode=mode, payload=list(payload), half_cycles=half_cycles)


def i2c_register_read(address, register, *, byte_count=1, phase_cycles=4, wait_cycles=32):
    return _spec('i2c-register-read', address=address, register=register,
                 byte_count=byte_count, phase_cycles=phase_cycles, wait_cycles=wait_cycles)


def jtag_scan(*, half_cycles=4, outgoing_bits=8, captured_bits=8):
    return _spec('jtag-scan', half_cycles=half_cycles,
                 outgoing_bits=outgoing_bits, captured_bits=captured_bits)


def export_lean(request):
    """Invoke a static production frontend; requests are data, never generated Lean source."""
    completed = subprocess.run([sys.executable, str(ROOT/'scripts/export-program.py')],
        input=json.dumps(request), text=True, capture_output=True, cwd=ROOT, timeout=120)
    if completed.returncode:
        raise ValueError('Lean protocol compilation failed: ' + completed.stderr.strip())
    return _loads(completed.stdout)


@dataclass(frozen=True)
class PinRequirements:
    outputs: tuple[tuple[str, int], ...]
    inputs: tuple[tuple[str, int], ...]
    joined_output_inputs: tuple[tuple[int, int], ...] = ()
    open_drain: bool = False


@dataclass(frozen=True)
class TransactionResult:
    protocol: str
    outcome: str
    payload: tuple[int, ...] | None
    overrun: bool
    rejected: bool


@dataclass(frozen=True)
class Transaction:
    spec: TransactionSpec
    program: Program

    @property
    def protocol(self):
        return self.spec.request['protocol']

    @property
    def payload_bits(self):
        return 8 if self.protocol in ('uart-tx', 'spi-resident', 'jtag-scan') else 0

    @property
    def result_bits(self):
        request = self.spec.request
        if self.protocol == 'uart-tx':
            return 0
        if self.protocol == 'i2c-register-read':
            return 8 * request['byte_count']
        if self.protocol == 'spi-transaction':
            return 8 * len(request['payload'])
        return 8

    @property
    def pins(self):
        if self.protocol == 'uart-tx':
            return PinRequirements((('tx', 0), ('aux', 1), ('cs_n', 2)), ())
        if self.protocol.startswith('spi-'):
            return PinRequirements((('mosi', 0), ('sclk', 1), ('cs_n', 2)), (('miso', 0),))
        if self.protocol == 'jtag-scan':
            return PinRequirements((('tdi', 0), ('tck', 1), ('tms', 2)), (('tdo', 0),))
        return PinRequirements((('scl', 0), ('sda', 1)), (('scl', 0), ('sda', 1)), ((0, 0), (1, 1)), True)

    def validate_payload(self, payload):
        _integer(payload, 0, 255, 'START payload')
        if not self.payload_bits and payload:
            raise CapabilityError('This transaction has fixed compiled data; START payload must be zero')

    def inspect(self):
        return dict(protocol=self.protocol, pins=asdict(self.pins),
            payload_bits=self.payload_bits, result_bits=self.result_bits,
            result_layout=dict(byte_count=self.result_bits // 8,
                bit_order='msb_first_wire_slots' if self.protocol.startswith('spi-') or self.protocol == 'i2c-register-read'
                    else 'lsb_first_wire_slots' if self.protocol == 'jtag-scan' else 'none',
                failure_policy='discard_captures; aggregate_nack_or_bus_fault' if self.protocol == 'i2c-register-read'
                    else 'discard_captures; terminal_timeout_or_fault'),
            resources=resource_report(self.program), timing=dict(unit='chip_edges',
                input_sampler_edges=2, board_frequency_qualified=False,
                **{k: v for k, v in self.spec.request.items() if k.endswith('_cycles')}))

    def decode(self, raw: Result):
        _integer(raw.samples, 0, 65535, 'Result captures')
        _integer(raw.outcome, 5, 7, 'Terminal outcome')
        if self.protocol == 'i2c-register-read':
            decoded = i2c_read_result(raw, byte_count=self.spec.request['byte_count'])
            return TransactionResult(self.protocol, decoded.outcome, decoded.payload,
                                     decoded.overrun, decoded.rejected)
        if raw.outcome != 5:
            return TransactionResult(self.protocol, 'timeout' if raw.outcome == 6 else 'fault',
                                     None, raw.overrun, raw.rejected)
        if raw.samples >> self.result_bits:
            raise ValueError('Completed transaction contains captures outside its declared result layout')
        if self.protocol.startswith('spi-'):
            payload = tuple(sum(((raw.samples >> (8*n + bit)) & 1) << (7-bit)
                                for bit in range(8)) for n in range(self.result_bits // 8))
        elif self.protocol == 'jtag-scan':
            payload = (raw.samples,)
        else:
            payload = ()
        return TransactionResult(self.protocol, 'success', payload, raw.overrun, raw.rejected)

    def load(self, host: Host):
        if host.image_format != PAIRED_FORMAT:
            raise CapabilityError('Transaction workflow requires a paired engine')
        host.upload(self.program)
        return LoadedTransaction(self, host, host.program_generation)

    def artifact(self):
        program = dict(format=self.program.image_format, words=list(self.program.words),
            last=self.program.last, idle_levels=self.program.idle_levels, idle_enabled=self.program.idle_enabled)
        # JSON-normalize tuples so a parsed artifact has the same exact shape.
        return json.loads(json.dumps(dict(schema=ARTIFACT_SCHEMA, request=self.spec.request,
            program=program, description=self.inspect())))

    def write(self, path):
        Path(path).write_text(json.dumps(self.artifact(), indent=2) + '\n')

    @classmethod
    def from_bytes(cls, data, *, exporter=None):
        saved = _loads(data)
        if not isinstance(saved, dict) or set(saved) != {'schema', 'request', 'program', 'description'} or saved['schema'] != ARTIFACT_SCHEMA:
            raise ValueError('Unsupported transaction artifact schema')
        spec = TransactionSpec.from_request(saved['request'])
        Program.from_bytes(json.dumps(saved['program']).encode())
        expected = compile_transaction(spec, exporter=exporter)
        if json.dumps(saved, sort_keys=True) != json.dumps(expected.artifact(), sort_keys=True):
            raise ValueError('Transaction program or metadata differs from its compiled request')
        return expected


@dataclass(frozen=True)
class LoadedTransaction:
    transaction: Transaction
    host: Host
    generation: int

    def run(self, *, payload=0, timeout_cycles=100_000):
        self.transaction.validate_payload(payload)
        _integer(timeout_cycles, 0, sys.maxsize, 'Timeout cycles')
        if self.host.program_generation != self.generation or self.host.committed_program != self.transaction.program:
            raise RuntimeError('Transaction session lost its committed program; load it again')
        self.host.start(payload=payload)
        deadline = self.host.edges + timeout_cycles
        while self.host.page(0) & 1:
            remaining = deadline - self.host.edges
            if remaining <= 0:
                raise TimeoutError('Transaction exceeded host timeout; engine state is unchanged')
            self.host.advance(min(16, remaining))
        decoded = self.transaction.decode(self.host.read_result(
            timeout_cycles=max(0, deadline - self.host.edges), consume=False))
        self.host.consume()
        return decoded


def compile_transaction(spec: TransactionSpec, *, exporter=None):
    request = spec.request
    protocol = request['protocol']
    if protocol == 'uart-tx':
        program = resident_uart(request['bit_cycles'])
    elif protocol == 'spi-resident':
        program = resident_spi(request['half_cycles'])
    elif protocol == 'jtag-scan':
        from pinwheel_jtag import resident_jtag_scan
        program = resident_jtag_scan(request['half_cycles'])
    else:
        response = (export_lean if exporter is None else exporter)(request)
        if not isinstance(response, dict) or set(response) != {'schema', 'request', 'program'} or response['schema'] != 'pinwheel-compiled-program-v1' or response['request'] != request:
            raise ValueError('Lean frontend response differs from the requested transaction')
        _validate_request(response['request'])
        program = Program.from_bytes(json.dumps(response['program']).encode())
        if program.image_format != PAIRED_FORMAT:
            raise ValueError('Lean frontend returned a different target format')
    program.upload_words()
    return Transaction(spec, program)
