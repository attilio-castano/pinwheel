"""Interactive pin transport to Icarus; no model of Pinwheel execution."""
from pathlib import Path
from collections import deque
import os
import select
import subprocess
import time

from pinwheel_host import Pins
from pad_io import PadDrive, PadObservation


class Simulation:
    def __init__(self, vvp: Path, executable: Path):
        self.process = subprocess.Popen([str(vvp), str(executable)], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0)
        self.buffer = bytearray()
        self.pins = Pins(0, 0, 0)
        self.observation = PadObservation(0, 0, 0, 255, 255)
        self.cycle = 0
        self.incoming = 3
        # Optional external device. It sees only package pins and chip-edge
        # count; it supplies external drivers, never independent uio_in values.
        self.device = None
        self.log = deque(maxlen=100)

    def _advance(self, ui, drive, cycles, rst_n):
        self.process.stdin.write(f'{rst_n} {ui} {drive.levels} {drive.enabled} '
                                f'{drive.links} {drive.pullups} {cycles}\n'.encode())
        deadline = time.monotonic() + 30
        while True:
            # TextIOWrapper.readline may read ahead. select would then wait on
            # an empty OS pipe even though a complete reply is already buffered.
            while b'\n' not in self.buffer:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                    raise TimeoutError('RTL simulation did not answer the host')
                data = os.read(self.process.stdout.fileno(), 65536)
                if not data:
                    raise RuntimeError('RTL simulation exited: ' + '\n'.join(self.log))
                self.buffer.extend(data)
            raw, _, rest = self.buffer.partition(b'\n')
            self.buffer = rest
            line = raw.decode(errors='replace')
            self.log.append(line.strip())
            if line.startswith('PINWHEEL '):
                try:
                    self.observation = PadObservation(*map(int, line.split()[1:]))
                    self.observation.validate_drive(drive)
                    self.pins = self.observation.logical
                except ValueError as error:
                    raise RuntimeError('Unknown RTL pins after a host operation: ' + line) from error
                self.cycle += cycles
                return self.pins

    def advance(self, ui, cycles, *, rst_n=1):
        if self.device is None:
            return self._advance(ui, PadDrive(self.incoming, 3), cycles, rst_n)
        for _ in range(cycles):
            drive = self.device.drive(self.cycle, self.observation, ui)
            if not isinstance(drive, PadDrive):
                raise TypeError('Resolved-pad peer must return PadDrive')
            self._advance(ui, drive, 1, rst_n)
        return self.pins

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
