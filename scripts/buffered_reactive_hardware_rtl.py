"""Public parallel-command transport for the reactive counted RTL slice.

The transport has no engine or protocol model. An optional peer receives only
resolved package pads and integer edge counts, using the existing callback and
two-register sampler timing contract. Tests own their independent expectations.
"""
from collections import deque
from dataclasses import asdict, dataclass
import os
from pathlib import Path
import select
import subprocess
import time

from pad_io import PadDrive, PadObservation


COMMAND_FIELDS = dict(initialize=1, command=3, address=6, word=64, control=24, branch=56, count=7, virtual_span=11, idle_levels=3,
    idle_enabled=3, tx_data=32, tx_length=6, rx_capacity=6,
    expected_generation=16, expected_transfer=16, read_index=5)
STATE_WIDTHS = dict(valid=1, busy=1, retained=1, rejected=1, mode=2, pc=8,
    remaining=8, levels=3, enabled=3, tx_consumed=6, rx_length=6, rx_data=32,
    read_valid=1, read_bit=1, generation=16, transfer=16, exhausted=1,
    pending=1, stage1=2, stage2=2, virtual_pc=10, env0=3, env1=3, phase=3, wait_left=8, scratch=16)


@dataclass(frozen=True)
class RTLSnapshot:
    valid: int
    busy: int
    retained: int
    rejected: int
    mode: int
    pc: int
    remaining: int
    levels: int
    enabled: int
    tx_consumed: int
    rx_length: int
    rx_data: int
    read_valid: int
    read_bit: int
    generation: int
    transfer: int
    exhausted: int
    pending: int
    stage1: int
    stage2: int
    virtual_pc: int
    env0: int
    env1: int
    phase: int
    wait_left: int
    scratch: int
    wires: int
    known: int
    edge_inputs: int

    def __post_init__(self):
        for name, width in {**STATE_WIDTHS, 'wires': 8, 'known': 8, 'edge_inputs': 2}.items():
            value = getattr(self, name)
            if type(value) is not int or not 0 <= value < (1 << width):
                raise ValueError('Reactive buffered RTL observation exceeds its port width: ' + name)

    @property
    def observation(self):
        return PadObservation(self.busy, self.levels << 2, self.enabled << 2,
                              self.wires, self.known)

    @property
    def rx_bits(self):
        return tuple(bool(self.rx_data & (1 << index)) for index in range(self.rx_length))


class BufferedReactiveRTL:
    """Issue one edge at a time; retain every command and observed public state."""
    def __init__(self, vvp: Path, executable: Path):
        self.process = subprocess.Popen([str(vvp), str(executable)], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0)
        self.buffer = bytearray()
        self.log = deque(maxlen=100)
        self.cycle = 0
        self.snapshot = None
        self.observation = PadObservation(0, 0, 0, 255, 255)
        self.records = []
        self._device = None
        self._drive = PadDrive()

    @property
    def device(self):
        return self._device

    @device.setter
    def device(self, value):
        self._device = value
        self._drive = PadDrive() if value is None else self._peer_drive()

    def _peer_drive(self):
        drive = self._device.drive(self.cycle, self.observation, 0)
        if type(drive) is not PadDrive:
            raise TypeError('Reactive buffered RTL peer must return PadDrive')
        self.observation.validate_drive(drive)
        return drive

    def edge(self, *, drive=None, **fields):
        unknown = set(fields) - set(COMMAND_FIELDS)
        if unknown:
            raise ValueError('Unknown reactive buffered hardware fields: ' + repr(sorted(unknown)))
        command = {name: fields.get(name, 0) for name in COMMAND_FIELDS}
        for name, width in COMMAND_FIELDS.items():
            value = command[name]
            if type(value) is not int or not 0 <= value < (1 << width):
                raise ValueError('Reactive buffered hardware ' + name + ' exceeds its port width')
        if drive is None:
            drive = self._drive
        if type(drive) is not PadDrive:
            raise TypeError('Reactive buffered RTL external drive must be PadDrive')
        # A command can release an output at this edge. Validate its current
        # ownership before sending, as well as the resolved post-edge profile.
        if self.observation.enabled & drive.enabled:
            raise RuntimeError('External peer drives a DUT-owned package pad')
        connected = (5 if drive.links & 1 else 0) | (10 if drive.links & 2 else 0)
        if connected & ((self.observation.levels & self.observation.enabled) |
                        (drive.levels & drive.enabled)):
            raise RuntimeError('Declared I2C board links require open-drain low/release drivers')
        tokens = [format(value, 'x') if name in ('word', 'branch') else str(value)
                  for name, value in command.items()]
        tokens += list(map(str, (drive.levels, drive.enabled, drive.links, drive.pullups)))
        self.process.stdin.write((' '.join(tokens) + '\n').encode())
        deadline = time.monotonic() + 30
        while True:
            while b'\n' not in self.buffer:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                    raise TimeoutError('Reactive buffered RTL did not answer the command')
                data = os.read(self.process.stdout.fileno(), 65536)
                if not data:
                    raise RuntimeError('Reactive buffered RTL exited: ' + '\n'.join(self.log))
                self.buffer.extend(data)
            raw, _, self.buffer = self.buffer.partition(b'\n')
            line = raw.decode(errors='replace')
            self.log.append(line)
            if line.startswith('REACTIVE '):
                try:
                    self.snapshot = RTLSnapshot(*map(int, line.split()[1:]))
                    self.observation = self.snapshot.observation
                    self.observation.validate_drive(drive)
                except (ValueError, TypeError) as error:
                    raise RuntimeError('Malformed buffered RTL observation: ' + line) from error
                self.cycle += 1
                self.records.append(dict(cycle=self.cycle, command=command,
                    drive=asdict(drive), state=asdict(self.snapshot)))
                if self._device is not None:
                    self._drive = self._peer_drive()
                return self.snapshot

    def close(self):
        self.process.stdin.close()
        try:
            self.process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait(timeout=5)
        self.process.stdout.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()


def compare_public_state(actual, expected):
    """Exact comparison of independently supplied fields, excluding only bridge observations."""
    if type(actual) is not RTLSnapshot or type(expected) is not dict or not expected:
        raise ValueError('State comparison requires a snapshot and nonempty expected mapping')
    fields = set(asdict(actual)) - {'wires', 'known', 'edge_inputs'}
    if set(expected) != fields:
        raise ValueError('Expected buffered hardware state must cover every public state field')
    for name, width in STATE_WIDTHS.items():
        value = expected[name]
        if type(value) is not int or not 0 <= value < (1 << width):
            raise ValueError('Expected buffered hardware state exceeds its port width: ' + name)
    differences = {key: [getattr(actual, key), expected[key]] for key in expected
                   if getattr(actual, key) != expected[key]}
    if differences:
        raise RuntimeError('Reactive buffered RTL public state mismatch: ' + repr(differences))


def replay_vectors(simulation, vectors):
    """Replay saved independent command/state vectors without accepting extras."""
    if type(vectors) is not list or not vectors:
        raise ValueError('Reactive buffered RTL vectors must be a nonempty list')
    for vector in vectors:
        if type(vector) is not dict or set(vector) != {'command', 'raw_inputs', 'state'}:
            raise ValueError('Unsupported buffered RTL vector schema')
        if type(vector['command']) is not dict:
            raise ValueError('Reactive buffered RTL vector command must be a field mapping')
        raw = vector['raw_inputs']
        if type(raw) is not int or not 0 <= raw < 4:
            raise ValueError('Reactive buffered RTL raw input exceeds two input pads')
        actual = simulation.edge(drive=PadDrive(raw, 3), **vector['command'])
        compare_public_state(actual, vector['state'])
    return dict(edges=len(vectors), public_state_fields=len(vectors[0]['state']))
