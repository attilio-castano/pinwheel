"""Public quad host pins and resolved protocol pads through an Icarus pipe."""
from collections import deque
from dataclasses import asdict, dataclass
import math
import os
from pathlib import Path
import select
import subprocess
import time

from pad_io import PadDrive, PadObservation
from streaming_transport import uint


@dataclass(frozen=True)
class Snapshot:
    miso: int
    ready: int
    busy: int
    levels: int
    enabled: int
    wires: int
    known: int
    edge_inputs: int

    def __post_init__(self):
        for name, bits in (('miso', 4), ('ready', 1), ('busy', 1), ('levels', 3),
                ('enabled', 3), ('wires', 8), ('known', 8), ('edge_inputs', 2)):
            uint(getattr(self, name), bits, name)

    @property
    def observation(self):
        return PadObservation(self.busy, self.levels << 2, self.enabled << 2, self.wires, self.known)


class QuadRTL:
    def __init__(self, vvp, executable, *, timeout_seconds=30, record_limit=4096, record_sink=None):
        if (type(timeout_seconds) not in (int, float) or
                not math.isfinite(timeout_seconds) or timeout_seconds <= 0):
            raise ValueError('Pin response timeout must be finite and positive')
        if type(record_limit) is not int or record_limit < 0:
            raise ValueError('Recent record limit must be nonnegative')
        if record_sink is not None and not callable(record_sink):
            raise ValueError('Record sink must be callable')
        self.process = subprocess.Popen([str(vvp), str(executable)], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0)
        self.timeout_seconds = timeout_seconds
        self.cycle, self.snapshot, self.closed = 0, None, False
        self.observation = PadObservation(0, 0, 0, 255, 255)
        self.records, self.log = deque(maxlen=record_limit), deque(maxlen=100)
        self.buffer, self.record_sink = bytearray(), record_sink
        self._device, self._drive = None, PadDrive()

    @property
    def device(self): return self._device

    @device.setter
    def device(self, value):
        if value is not None and not callable(getattr(value, 'drive', None)):
            raise ValueError('Peer must supply an edge-driven drive callback')
        self._device = value
        self._drive = PadDrive() if value is None else self._peer_drive()

    def _peer_drive(self):
        drive = self._device.drive(self.cycle, self.observation, 0)
        if type(drive) is not PadDrive:
            raise TypeError('Peer must return PadDrive')
        self.observation.validate_drive(drive)
        return drive

    def tick(self, *, csn, sck, mosi, initialize=0, drive=None):
        pins = dict(initialize=uint(initialize, 1, 'initialize'), csn=uint(csn, 1, 'csn'),
            sck=uint(sck, 1, 'sck'), mosi=uint(mosi, 4, 'mosi'))
        if self.closed:
            raise RuntimeError('Quad RTL backend is closed')
        drive = self._drive if drive is None else drive
        if type(drive) is not PadDrive:
            raise TypeError('External drive must be PadDrive')
        self.observation.validate_drive(drive)
        values = [*pins.values(), drive.levels, drive.enabled, drive.links, drive.pullups]
        try:
            self.process.stdin.write((' '.join(map(str, values)) + '\n').encode())
            self.process.stdin.flush()
            deadline = time.monotonic() + self.timeout_seconds
            while True:
                while b'\n' not in self.buffer:
                    remaining = deadline - time.monotonic()
                    if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                        raise TimeoutError('Streaming RTL did not answer the physical edge')
                    data = os.read(self.process.stdout.fileno(), 65536)
                    if not data:
                        raise RuntimeError('Streaming RTL exited: ' + '\n'.join(self.log))
                    self.buffer.extend(data)
                raw, _, self.buffer = self.buffer.partition(b'\n')
                line = raw.decode(errors='replace')
                self.log.append(line)
                if line.startswith('STREAM_QUAD '):
                    snapshot = Snapshot(*map(int, line.split()[1:]))
                    observation = snapshot.observation
                    observation.validate_drive(drive)
                    self.cycle += 1
                    self.snapshot, self.observation = snapshot, observation
                    record = dict(cycle=self.cycle, pins=pins, drive=asdict(drive), observation=asdict(snapshot))
                    self.records.append(record)
                    if self.record_sink is not None:
                        self.record_sink(record)
                    if self._device is not None:
                        self._drive = self._peer_drive()
                    return asdict(snapshot)
                if time.monotonic() >= deadline:
                    raise TimeoutError('Streaming RTL emitted no physical-edge response')
        except Exception as error:
            try:
                self.close(check_returncode=False)
            except Exception as cleanup:
                error.add_note('Streaming RTL cleanup also failed: ' + repr(cleanup))
            raise

    def cold_reset(self):
        self.tick(initialize=1, csn=1, sck=0, mosi=0)
        self.tick(initialize=0, csn=1, sck=0, mosi=0)

    def close(self, *, check_returncode=True):
        if self.closed:
            return
        self.closed = True
        try:
            self.process.stdin.close()
        except OSError:
            pass
        try:
            self.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.process.terminate()
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=2)
        finally:
            self.process.stdout.close()
        if check_returncode and self.process.returncode != 0:
            raise RuntimeError('Streaming RTL exited with status ' + str(self.process.returncode) +
                ': ' + '\n'.join(self.log))

    def __enter__(self): return self
    def __exit__(self, kind, error, traceback):
        if error is None:
            self.close()
        else:
            try:
                self.close(check_returncode=False)
            except Exception as cleanup:
                error.add_note('Streaming RTL cleanup also failed: ' + repr(cleanup))
