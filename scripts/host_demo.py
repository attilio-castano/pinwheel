"""Pin-only protocol peers and monitors for the reusable host demonstration."""
from dataclasses import asdict

from pinwheel_host import Host, Program


def _require(condition, message):
    """Acceptance checks must execute even when Python assertions are disabled."""
    if not condition:
        raise RuntimeError(message)


def compiler_images(path):
    images = {}
    for line in path.read_text().splitlines():
        name, *values = line.split()
        last, levels, enabled, *words = map(int, values)
        images[name] = Program(tuple(words), last, levels, enabled)
    return images


class UARTTransmit:
    def __init__(self, byte=0x53, period=4):
        self.byte, self.period = byte, period
        self.trace = []
        self.started = False

    def __call__(self, cycle, pins, ui):
        if pins.enabled & 1 and not pins.levels & 1:
            self.started = True
        if self.started and len(self.trace) < 10 * self.period:
            _require(pins.enabled & 1, 'UART released TX within a frame')
            self.trace.append(pins.levels & 1)
        return 3

    def check(self):
        symbols = [0, *[(self.byte >> k) & 1 for k in range(8)], 1]
        _require(self.trace == [bit for bit in symbols for _ in range(self.period)], 'UART pin waveform')
        return dict(byte=self.byte, bit_cycles=self.period, frame_cycles=len(self.trace))


class SPI:
    def __init__(self, receive=0x96):
        self.receive = receive
        self.bits = []
        self.previous_clock = 0
        self.miso = (receive >> 7) & 1
        self.rises = []

    def __call__(self, cycle, pins, ui):
        if pins.enabled & 4 and not pins.levels & 4:
            _require(pins.enabled == 7, 'SPI must drive MOSI/SCLK/CS')
            clock = (pins.levels >> 1) & 1
            if clock and not self.previous_clock:
                self.bits.append(pins.levels & 1)
                self.rises.append(cycle)
            if not clock:
                self.miso = (self.receive >> (7 - min(len(self.bits), 7))) & 1
            self.previous_clock = clock
        else:
            self.previous_clock = 0
        return self.miso

    def check(self):
        _require(self.bits == [(0xa6 >> k) & 1 for k in range(7, -1, -1)], 'SPI outgoing byte')
        _require([b - a for a, b in zip(self.rises, self.rises[1:])] == [8] * 7, 'SPI clock spacing')
        return dict(transmitted=0xa6, received=self.receive, clock_cycles=8, rising_edges=len(self.bits))


class Receive:
    def __init__(self, byte=0xa6, stop=1, trigger=False, value=3):
        self.byte, self.stop, self.trigger, self.value = byte, stop, trigger, value
        self.started = None
        self.pulse = []

    def __call__(self, cycle, pins, ui):
        if self.started is None and (ui >> 3) & 3 == 0 and pins.status & 1:
            self.started = cycle
        if self.trigger and pins.enabled & 1 and pins.levels & 1:
            self.pulse.append(cycle)
        if self.started is None:
            return 0 if self.trigger else 1
        t = cycle - self.started
        if self.trigger:
            return self.value if t >= 8 else 0
        symbol = (t - 8) // 16
        return 1 if t < 8 else 0 if symbol == 0 else ((self.byte >> (symbol - 1)) & 1) if 1 <= symbol <= 8 else self.stop if symbol == 9 else 1


class I2C:
    """Open-drain register-read peer, with independently checked wire bytes."""
    def __init__(self, byte=0x96):
        self.byte = byte
        self.previous = [1, 1]
        self.previous_command = [0, 0]
        self.target_sda = self.stretch_left = self.releases = self.starts = 0
        self.stopped = False
        self.clocks = []
        self.pending = None
        self.rise_at = self.fall_at = 0

    def __call__(self, cycle, pins, ui):
        _require(pins.levels == 0 and pins.enabled < 4, 'Unsafe I2C drive')
        command = [pins.enabled & 1, (pins.enabled >> 1) & 1]
        if self.previous_command[0] and not command[0]:
            self.stretch_left = self.releases % 4
            self.releases += 1
        bus = [int(not (command[0] or self.stretch_left)), int(not (command[1] or self.target_sda))]
        if self.previous[0] and bus[0] and self.previous[1] != bus[1]:
            _require(cycle - self.rise_at >= 4, 'I2C START/STOP high interval')
            if self.previous[1]:
                self.starts += 1
                _require(self.starts == 1 or (self.starts == 2 and len(self.clocks) == 18),
                         'Unexpected I2C START')
            else:
                _require(self.starts > 0, 'I2C STOP without START')
                self.stopped = True
            self.pending = None
        if not self.previous[0] and bus[0] and self.starts and not self.stopped:
            _require(cycle - self.fall_at >= 4, 'I2C clock low interval')
            self.rise_at, self.pending = cycle, bus[1]
        if self.previous[0] and not bus[0]:
            self.fall_at = cycle
            if self.pending is not None:
                _require(cycle - self.rise_at >= 4, 'I2C clock high interval')
                self.clocks.append(self.pending)
                self.pending = None
        if not bus[0]:
            k = len(self.clocks)
            self.target_sda = int(k in (8, 17, 26))
            if 27 <= k < 35:
                self.target_sda = 1 - ((self.byte >> (34 - k)) & 1)
        bus[1] = int(not (command[1] or self.target_sda))
        self.previous, self.previous_command = bus, command
        self.stretch_left = max(0, self.stretch_left - 1)
        return bus[0] | bus[1] << 1

    def check(self):
        _require(self.stopped and self.starts == 2 and len(self.clocks) == 36, 'I2C transaction framing')
        outgoing = [0xa6, 0xa6, 0xa7, self.byte]
        expected = [((0 if k < 27 else 1) if k % 9 == 8 else
                     (outgoing[k // 9] >> (7 - k % 9)) & 1) for k in range(36)]
        _require(self.clocks == expected, 'I2C wire bytes/ACKs')
        return dict(address=0x53, register=0xa6, received=self.byte, clocks=36,
                    starts=self.starts, stretching_cycles='0..3 per SCL release')


def trigger_program():
    # A custom program authored in the public E64 format, independent of the
    # UART/SPI/I2C compilers. Capture pin 1, then branch on the captured bit.
    wait = 1 | (1 << 6) | (31 << 9) | (2 << 25)
    branch = 2 | (1 << 6) | (3 << 35) | (2 << 41) | (2 << 47) | (3 << 55)
    pulse = (1 << 3) | (1 << 6) | (7 << 9)
    return Program((wait, branch, pulse, 4), 3)


def demonstrate(sim, images, directory):
    host = Host(sim)
    host.reset()
    cases = []

    def run(name, program, device, samples, outcome=5, check=None):
        sim.device = None
        program.write(directory / (name + '.json'))
        before = host.edges
        host.upload(program)
        upload_cycles = host.edges - before
        sim.device = device
        host.start()
        result = host.read_result(timeout_cycles=4000, consume=False)
        _require(result.samples == samples and result.outcome == outcome,
                 f'{name}: expected samples={samples:#x}, outcome={outcome}; got {result}')
        _require(not result.overrun and not result.rejected, f'{name}: unexpected result flags: {result}')
        # A second read is nondestructive and observes the same retained slot.
        retained = host.read_result(timeout_cycles=0, consume=False)
        _require(retained == result, f'{name}: retained result changed: {result} -> {retained}')
        details = check() if check else {}
        host.consume()
        status = host.result_status()
        _require(not status & 1, f'{name}: consumption did not release result')
        cases.append(dict(name=name, result=asdict(result), upload_cycles=upload_cycles,
                          **details))
        sim.device = None

    uart = UARTTransmit()
    run('uart-tx', images['uart'], uart, 0, check=uart.check)
    spi = SPI()
    run('spi-mode0', images['spi'], spi, 0x69, check=spi.check)
    i2c = I2C()
    run('i2c-stretched-read', images['i2c-read'], i2c, 0x69, check=i2c.check)
    for name, byte, stop in [('uart-rx', 0xa6, 1), ('uart-rx-bad-stop', 0x53, 0)]:
        peer = Receive(byte=byte, stop=stop)
        run(name, images['uart-rx'], peer, byte | (stop << 9))
    program = trigger_program()
    for name, value, samples, outcome in [('trigger-captured-high', 3, 1, 5),
                                          ('trigger-captured-low', 1, 0, 5),
                                          ('trigger-timeout', 0, 0, 6)]:
        peer = Receive(trigger=True, value=value)
        def check(peer=peer, value=value):
            _require(len(peer.pulse) == (8 if value == 3 else 0), 'Triggered pulse width/branch')
            return dict(pulse_cycles=len(peer.pulse), external_value=value)
        run(name, program, peer, samples, outcome, check)
    # The client must fail closed on a chip-rejected record, retain the old
    # committed program, and expose the error through the actual host pins.
    try:
        host.upload(Program((1 << 63, 4), 1))
    except RuntimeError as error:
        _require('rejected the staged image' in str(error), f'Unexpected malformed-upload failure: {error}')
    else:
        raise RuntimeError('Malformed program was accepted')
    live = host.page(0)
    _require(live & 7 == 2, 'Malformed upload did not retain the active image')
    cases.append(dict(name='malformed-upload-retains-active-image'))
    host.clear_flags()
    sim.device = Receive(trigger=True, value=3)
    host.start()
    result = host.read_result(timeout_cycles=4000)
    _require(result.samples == 1 and result.outcome == 5, f'Recovered program result: {result}')
    sim.device = None
    return dict(cases=cases, edges=host.edges, frames=host.frames,
                transport='Actual RTL pins over an interactive Icarus pipe; no internal state access',
                clock_assumption_ns=20,
                upload_time_ms_at_assumed_clock=cases[0]['upload_cycles'] * 20 / 1_000_000)
