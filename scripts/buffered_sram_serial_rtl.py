"""Physical serial-pin backend for the buffered latency-one SRAM package.

Every tick advances the free-running core clock once. It samples serial MISO
before that edge and returns ready plus public protocol pad observations after
it. Framing and response decoding belong to the separate serial transport;
this backend has no engine commands, protocol model or private DUT observations.
"""
from collections import deque
from dataclasses import asdict, dataclass
import math
import os
from pathlib import Path
import select
import subprocess
import time

from pad_io import PadDrive, PadObservation


PIN_WIDTHS = dict(initialize=1, csn=1, sck=1, mosi=1)
OBSERVATION_WIDTHS = dict(miso=1, ready=1, busy=1, levels=3, enabled=3,
                          wires=8, known=8, edge_inputs=2)


@dataclass(frozen=True)
class SerialPinSnapshot:
    miso: int
    ready: int
    busy: int
    levels: int
    enabled: int
    wires: int
    known: int
    edge_inputs: int

    def __post_init__(self):
        for name, width in OBSERVATION_WIDTHS.items():
            value = getattr(self, name)
            if type(value) is not int or not 0 <= value < (1 << width):
                raise ValueError('Buffered SRAM serial observation exceeds its pin width: ' + name)

    @property
    def observation(self):
        return PadObservation(self.busy, self.levels << 2, self.enabled << 2,
                              self.wires, self.known)


class BufferedSramSerialRTL:
    """Advance physical pins, with a bounded recent log and optional full sink."""
    def __init__(self, vvp: Path, executable: Path, *, timeout_seconds=30,
                 record_limit=4096, record_sink=None):
        if (type(timeout_seconds) not in (int, float) or
                not math.isfinite(timeout_seconds) or timeout_seconds <= 0):
            raise ValueError('Buffered SRAM serial timeout must be finite and positive')
        if record_limit is not None and (type(record_limit) is not int or record_limit < 0):
            raise ValueError('Buffered SRAM serial record limit must be nonnegative or None')
        if record_sink is not None and not callable(record_sink):
            raise TypeError('Buffered SRAM serial record sink must be callable')
        self.process = subprocess.Popen([str(vvp), str(executable)], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0)
        self.timeout_seconds = timeout_seconds
        self.buffer = bytearray()
        self.log = deque(maxlen=100)
        self.cycle = 0
        self.snapshot = None
        self.observation = PadObservation(0, 0, 0, 255, 255)
        self.records = [] if record_limit is None else deque(maxlen=record_limit)
        self.record_sink = record_sink
        self._device = None
        self._drive = PadDrive()
        self._closed = False

    @property
    def device(self):
        return self._device

    @device.setter
    def device(self, value):
        if value is not None and not callable(getattr(value, 'drive', None)):
            raise TypeError('Buffered SRAM serial peer must provide drive')
        self._device = value
        self._drive = PadDrive() if value is None else self._peer_drive()

    def _peer_drive(self):
        drive = self._device.drive(self.cycle, self.observation, 0)
        if type(drive) is not PadDrive:
            raise TypeError('Buffered SRAM serial peer must return PadDrive')
        self._validate_pre_drive(drive)
        return drive

    def _validate_pre_drive(self, drive):
        if self.observation.enabled & drive.enabled:
            raise RuntimeError('External peer drives a DUT-owned package pad')
        connected = (5 if drive.links & 1 else 0) | (10 if drive.links & 2 else 0)
        if connected & ((self.observation.levels & self.observation.enabled) |
                        (drive.levels & drive.enabled)):
            raise RuntimeError('Declared I2C board links require open-drain low/release drivers')

    def tick(self, *, csn, sck, mosi, initialize=0, drive=None):
        pins = dict(initialize=initialize, csn=csn, sck=sck, mosi=mosi)
        for name, width in PIN_WIDTHS.items():
            value = pins[name]
            if type(value) is not int or not 0 <= value < (1 << width):
                raise ValueError('Buffered SRAM serial ' + name + ' exceeds its pin width')
        if self._closed:
            raise RuntimeError('Buffered SRAM serial RTL backend is closed')
        if drive is None:
            drive = self._drive
        if type(drive) is not PadDrive:
            raise TypeError('Buffered SRAM serial external drive must be PadDrive')
        # Check the current ownership, including an edge that releases an output.
        self._validate_pre_drive(drive)
        tokens = [*pins.values(), drive.levels, drive.enabled, drive.links, drive.pullups]
        try:
            self.process.stdin.write((' '.join(map(str, tokens)) + '\n').encode())
            self.process.stdin.flush()
            deadline = time.monotonic() + self.timeout_seconds
            while True:
                while b'\n' not in self.buffer:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                        raise TimeoutError('Buffered SRAM serial RTL did not answer the pin edge')
                    data = os.read(self.process.stdout.fileno(), 65536)
                    if not data:
                        raise RuntimeError('Buffered SRAM serial RTL exited: ' + '\n'.join(self.log))
                    self.buffer.extend(data)
                raw, _, self.buffer = self.buffer.partition(b'\n')
                line = raw.decode(errors='replace')
                self.log.append(line)
                if line.startswith('SRAM_SERIAL '):
                    try:
                        snapshot = SerialPinSnapshot(*map(int, line.split()[1:]))
                        observation = snapshot.observation
                        observation.validate_drive(drive)
                    except (ValueError, TypeError, RuntimeError) as error:
                        raise RuntimeError('Malformed buffered SRAM serial observation: ' + line) from error
                    self.snapshot, self.observation = snapshot, observation
                    self.cycle += 1
                    record = dict(cycle=self.cycle, pins=pins,
                        drive=asdict(drive), observation=asdict(snapshot))
                    self.records.append(record)
                    if self.record_sink is not None:
                        self.record_sink(record)
                    if self._device is not None:
                        self._drive = self._peer_drive()
                    return asdict(snapshot)
                if time.monotonic() >= deadline:
                    raise TimeoutError('Buffered SRAM serial RTL did not answer the pin edge')
        except Exception:
            # A sent edge has uncertain completion after any I/O/parser failure.
            # Closing prevents another request from consuming a stale response.
            self.close()
            raise

    def cold_reset(self):
        """Explicit POR at CS high/SCK low; SRAM contents and Q are untouched."""
        self.tick(csn=1, sck=0, mosi=0, initialize=1)
        return self.tick(csn=1, sck=0, mosi=0, initialize=0)

    def close(self):
        if self._closed:
            return
        self._closed = True
        try:
            self.process.stdin.close()
        except (BrokenPipeError, OSError):
            pass
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
