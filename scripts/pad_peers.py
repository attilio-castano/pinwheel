"""Protocol peers driven only by resolved package wires and edge counts."""
from pad_io import OUTPUT_MASK, PadDrive


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def spi_result_bytes(samples, byte_count):
    """Slot zero holds the first MSB-first wire bit, independent of byte order."""
    if type(byte_count) is not int or not 1 <= byte_count <= 2:
        raise ValueError('SPI result requires one or two bytes')
    if type(samples) is not int or not 0 <= samples < 1 << (8 * byte_count):
        raise ValueError('SPI samples exceed the declared capture slots')
    return tuple(sum(((samples >> (8 * byte + bit)) & 1) << (7 - bit)
                     for bit in range(8)) for byte in range(byte_count))


class SPIPeer:
    """CPHA0 samples leading/shifts trailing; CPHA1 shifts leading/samples trailing.

    CPOL selects the idle level. The peer preloads the first reply bit, updates
    subsequent bits only on the mode's shift edge, and observes MOSI only on its
    sample edge. It does not inspect program words, PC or capture-slot state.
    """
    def __init__(self, mode=0, transmit=(0xa6,), receive=(0x96,), half_cycles=4, tco=0):
        if type(mode) is not int or mode not in range(4):
            raise ValueError('SPI mode must be 0..3')
        if len(transmit) != len(receive) or len(transmit) not in (1, 2):
            raise ValueError('SPI peer requires matching one/two-byte payloads')
        if any(type(byte) is not int or not 0 <= byte <= 255 for byte in (*transmit, *receive)):
            raise ValueError('SPI peer payload bytes must fit eight bits')
        if type(half_cycles) is not int or half_cycles < 1 or type(tco) is not int or tco < 0:
            raise ValueError('SPI half period and peer delay must be nonnegative')
        self.mode, self.cpol, self.cpha = mode, mode >> 1, mode & 1
        self.transmit, self.receive = tuple(transmit), tuple(receive)
        self.half_cycles, self.tco = half_cycles, tco
        self.reply = [(byte >> bit) & 1 for byte in receive for bit in range(7, -1, -1)]
        self.miso = self.reply[0]
        self.previous_clock = self.cpol
        self.selected = self.finished = False
        self.bits, self.sample_edges, self.clock_edges = [], [], []
        self.selected_at = self.released_at = None
        self.pending = None

    def drive(self, cycle, pads, ui):
        logical = pads.logical
        cs = pads.bit(4)
        clock = pads.bit(3)
        if not cs:
            require(pads.enabled == OUTPUT_MASK, 'SPI must drive physical MOSI2/SCLK3/CS4')
            if not self.selected:
                require(not self.finished, 'SPI CS asserted twice within one transaction')
                require(clock == self.cpol, 'SPI CS assertion must start at CPOL idle')
                self.selected, self.selected_at = True, cycle
                self.previous_clock = clock
            if clock != self.previous_clock:
                leading = clock != self.cpol
                self.clock_edges.append((cycle, leading))
                sample_edge = leading != bool(self.cpha)
                if sample_edge:
                    self.bits.append(pads.bit(2))
                    self.sample_edges.append(cycle)
                else:
                    index = min(len(self.bits), len(self.reply) - 1)
                    self.pending = (cycle + self.tco, self.reply[index])
                self.previous_clock = clock
        elif self.selected:
            require(clock == self.cpol, 'SPI release must restore CPOL idle')
            self.selected, self.finished, self.released_at = False, True, cycle
        if self.pending is not None and cycle >= self.pending[0]:
            self.miso = self.pending[1]
            self.pending = None
        # MISO is a separate physical input, never a driven MOSI pad.
        return PadDrive(self.miso, 1)

    def check(self):
        expected = [(byte >> bit) & 1 for byte in self.transmit for bit in range(7, -1, -1)]
        require(self.bits == expected, 'SPI outgoing byte/wire order')
        require(self.finished, 'SPI transaction did not release CS')
        require(len(self.clock_edges) == 2 * len(expected), 'SPI clock edge count')
        require([leading for _, leading in self.clock_edges] == [True, False] * len(expected),
                'SPI leading/trailing edge order')
        cycles = [at for at, _ in self.clock_edges]
        require([b - a for a, b in zip(cycles, cycles[1:])] == [self.half_cycles] * (len(cycles) - 1),
                'SPI clock spacing')
        require(cycles[0] - self.selected_at == self.half_cycles and
                self.released_at - cycles[-1] == self.half_cycles, 'SPI CS setup/hold interval')
        require([b - a for a, b in zip(self.sample_edges, self.sample_edges[1:])] ==
                [2 * self.half_cycles] * (len(expected) - 1), 'SPI sample edge spacing')
        return dict(mode=self.mode, cpol=self.cpol, cpha=self.cpha,
                    transmitted=list(self.transmit), received=list(self.receive),
                    half_cycles=self.half_cycles, peer_tco_cycles=self.tco,
                    callback_delay_cycles=1, sampler_delay_cycles=2,
                    required_half_cycles=self.tco + 3,
                    within_receive_timing_contract=self.half_cycles >= self.tco + 3,
                    sampled_bits=len(self.bits), clock_edges=len(self.clock_edges))


class I2CPeer:
    """Real shared open-drain wires, including declared board sense connections."""
    def __init__(self, byte=0x96):
        self.byte = byte
        self.previous, self.previous_command = [1, 1], [0, 0]
        self.target_sda = self.stretch_left = self.releases = self.starts = 0
        self.clock_sink = False
        self.stopped = False
        self.clocks = []
        self.pending = None
        self.rise_at = self.fall_at = 0

    def drive(self, cycle, pads, ui):
        pins = pads.logical
        require(pins.levels == 0 and pins.enabled < 4, 'Unsafe I2C drive')
        command = [pins.enabled & 1, (pins.enabled >> 1) & 1]
        bus = [pads.bit(0), pads.bit(1)]
        if self.previous[0] and bus[0] and self.previous[1] != bus[1]:
            require(cycle - self.rise_at >= 4, 'I2C START/STOP high interval')
            if self.previous[1]:
                self.starts += 1
                require(self.starts == 1 or (self.starts == 2 and len(self.clocks) == 18),
                        'Unexpected I2C START')
            else:
                require(self.starts > 0, 'I2C STOP without START')
                self.stopped = True
            self.pending = None
        if not self.previous[0] and bus[0] and self.starts and not self.stopped:
            require(cycle - self.fall_at >= 4, 'I2C clock low interval')
            self.rise_at, self.pending = cycle, bus[1]
        if self.previous[0] and not bus[0]:
            self.fall_at = cycle
            if self.pending is not None:
                require(cycle - self.rise_at >= 4, 'I2C clock high interval')
                self.clocks.append(self.pending)
                self.pending = None
        if not bus[0]:
            k = len(self.clocks)
            self.target_sda = int(k in (8, 17, 26))
            if 27 <= k < 35:
                self.target_sda = 1 - ((self.byte >> (34 - k)) & 1)
        # Pre-arm clock sinking while the controller holds SCL low. Waiting to
        # react after SCL rises would create a real extra clock edge on the wire.
        if command[0]:
            self.clock_sink = True
        elif self.previous_command[0]:
            self.stretch_left = self.releases % 4
            self.releases += 1
            self.clock_sink = self.stretch_left > 0
        elif self.stretch_left == 0:
            self.clock_sink = False
        self.previous, self.previous_command = bus, command
        self.stretch_left = max(0, self.stretch_left - 1)
        return PadDrive(0, int(self.clock_sink) | self.target_sda << 1, links=3)

    def check(self):
        require(self.stopped and self.starts == 2 and len(self.clocks) == 36, 'I2C transaction framing')
        outgoing = [0xa6, 0xa6, 0xa7, self.byte]
        expected = [((0 if k < 27 else 1) if k % 9 == 8 else
                     (outgoing[k // 9] >> (7 - k % 9)) & 1) for k in range(36)]
        require(self.clocks == expected, 'I2C wire bytes/ACKs')
        return dict(address=0x53, register=0xa6, received=self.byte, clocks=36,
                    starts=self.starts, stretching_cycles='0..3 per SCL release',
                    board_links=[[0, 2], [1, 3]])
