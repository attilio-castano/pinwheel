"""Independent one/two-byte register targets on resolved open-drain wires."""
from pad_io import PadDrive


class I2CReadWireError(RuntimeError):
    """A wire-oracle violation, which may occur before the terminal result."""
    def __init__(self, message, category='wire-order'):
        self.category = category
        super().__init__(message)


def require(condition, message, category='wire-order'):
    if not condition:
        raise I2CReadWireError(message, category)


class I2CReadPeer:
    def __init__(self, address, register, payload_bytes, ack_bits=(0, 0, 0), *,
                 phase_cycles=4, stretch_cycles=0, scl_stuck=False,
                 fault_after_rises=None, fault_delay_cycles=2):
        if type(address) is not int or not 0 <= address < 128:
            raise ValueError('I2C read address must fit seven bits')
        if type(register) is not int or not 0 <= register < 256:
            raise ValueError('I2C read register must fit a byte')
        if len(payload_bytes) not in (1, 2) or any(type(v) is not int or not 0 <= v < 256 for v in payload_bytes):
            raise ValueError('I2C read requires one/two reply bytes')
        if len(ack_bits) != 3 or any(type(v) is not int or v not in (0, 1) for v in ack_bits):
            raise ValueError('I2C read requires three independent ACK bits')
        if type(phase_cycles) is not int or phase_cycles < 1 or type(stretch_cycles) is not int or stretch_cycles < 0:
            raise ValueError('I2C read phase/stretch configuration')
        if type(scl_stuck) is not bool or type(fault_delay_cycles) is not int or fault_delay_cycles < 0:
            raise ValueError('I2C read clock fault configuration')
        if fault_after_rises is not None and (type(fault_after_rises) is not int or fault_after_rises < 1):
            raise ValueError('I2C read clock fault must follow a positive rise count')
        self.address, self.register = address, register
        self.payload_bytes, self.ack_bits = tuple(payload_bytes), tuple(ack_bits)
        self.phase_cycles, self.stretch_cycles, self.scl_stuck = phase_cycles, stretch_cycles, scl_stuck
        self.nack_stage = next((i for i, value in enumerate(ack_bits) if value), None)
        self.stop_after = 9 * (self.nack_stage + 1) if self.nack_stage is not None else 27 + 9 * len(payload_bytes)
        self.previous = (1, 1)
        self.previous_clock_command = self.clock_sink = self.sda_sink = False
        self.release_at = self.rise_at = self.fall_at = self.start_at = self.stop_rise_at = None
        self.both_high_since = None
        self.pending_start_fall = False
        self.starts = 0
        self.stopped = False
        self.bits, self.rising_cycles = [], []
        self.stretch_events = 0
        self.fault_after_rises, self.fault_delay_cycles = fault_after_rises, fault_delay_cycles
        self.fault_at, self.faulted = None, False

    def expected(self):
        prefix = (self.address << 1, self.register, (self.address << 1) | 1)
        values = []
        for index, byte in enumerate(prefix):
            values.extend((byte >> bit) & 1 for bit in range(7, -1, -1))
            values.append(self.ack_bits[index])
            if self.ack_bits[index]:
                return values
        for index, byte in enumerate(self.payload_bytes):
            values.extend((byte >> bit) & 1 for bit in range(7, -1, -1))
            values.append(int(index == len(self.payload_bytes) - 1))
        return values

    def drive(self, cycle, pads, ui):
        pins = pads.logical
        require(pins.levels == 0 and not pins.enabled & ~3,
                'I2C read must use only low/release SCL/SDA', 'open-drain')
        bus = (pads.bit(0), pads.bit(1))
        clock_command = bool(pins.enabled & 1)
        if self.previous[0] and bus[0] and self.previous[1] != bus[1]:
            if not bus[1]:
                require(self.both_high_since is not None and
                        cycle - self.both_high_since >= self.phase_cycles,
                        'I2C read START setup interval')
                require(not self.stopped and (self.starts == 0 or
                    self.starts == 1 and len(self.bits) == 18 and self.nack_stage not in (0, 1)),
                    'Unexpected I2C read START/repeated START')
                self.starts += 1
                self.start_at = cycle
                self.pending_start_fall = True
            else:
                require(self.starts > 0 and len(self.bits) == self.stop_after,
                        'I2C read STOP before requested prefix/data finished')
                require(self.stop_rise_at is not None and cycle - self.stop_rise_at >= self.phase_cycles,
                        'I2C read STOP high interval')
                self.stopped = True
        if self.starts and not self.stopped and not self.previous[0] and bus[0]:
            if self.fall_at is not None:
                require(cycle - self.fall_at >= self.phase_cycles, 'I2C read clock low interval')
            self.rise_at = cycle
            if len(self.bits) == self.stop_after:
                require(self.stop_rise_at is None and pins.enabled & 2, 'I2C read lacks STOP preparation')
                self.stop_rise_at = cycle
            elif len(self.bits) == 18 and self.starts == 1:
                require(not pins.enabled & 2 and bus[1] == 1, 'I2C repeated START setup must release SDA')
            else:
                slot = len(self.bits)
                if slot < 27 and slot % 9 == 8 or slot >= 27 and (slot - 27) % 9 < 8:
                    require(not pins.enabled & 2, 'Controller drives SDA during target-owned ACK/data')
                else:
                    require(not self.sda_sink, 'Target drives SDA during controller-owned data/ACK')
                self.bits.append(bus[1])
                self.rising_cycles.append(cycle)
                if len(self.bits) == self.fault_after_rises:
                    self.fault_at = cycle + self.fault_delay_cycles
        if self.previous[0] and not bus[0] and self.starts and not self.stopped:
            require(self.stop_rise_at is None, 'Extra I2C read clock after terminal prefix/data')
            if self.pending_start_fall:
                require(cycle - self.start_at >= self.phase_cycles, 'I2C read START hold interval')
                self.pending_start_fall = False
            if self.rise_at is not None and not self.faulted:
                require(cycle - self.rise_at >= self.phase_cycles, 'I2C read clock high interval')
            self.fall_at = cycle
        if not bus[0]:
            slot = len(self.bits)
            if slot >= self.stop_after:
                self.sda_sink = False
            elif slot < 27:
                self.sda_sink = slot % 9 == 8 and self.ack_bits[slot // 9] == 0
            else:
                relative = slot - 27
                self.sda_sink = relative % 9 < 8 and not bool(
                    self.payload_bytes[relative // 9] & (1 << (7 - relative % 9)))
        if clock_command:
            self.clock_sink = self.stretch_cycles > 0
            self.release_at = None
        elif self.previous_clock_command:
            self.release_at = cycle + max(0, self.stretch_cycles - 1)
            self.stretch_events += int(self.stretch_cycles > 0)
        if self.release_at is not None and cycle >= self.release_at:
            self.clock_sink = False
        if self.fault_at is not None and cycle >= self.fault_at:
            self.faulted = True
        if bus == (1, 1):
            if self.both_high_since is None:
                self.both_high_since = cycle
        else:
            self.both_high_since = None
        self.previous, self.previous_clock_command = bus, clock_command
        return PadDrive(0, int(self.clock_sink or self.scl_stuck or self.faulted) |
                        int(self.sda_sink) << 1, links=3)

    def check(self, *, timeout=False, fault=False):
        if timeout:
            require(self.scl_stuck and self.starts == 0 and not self.bits and not self.stopped,
                    'I2C initial stuck-clock timeout transferred data')
        elif fault:
            require(self.faulted and self.starts > 0 and not self.stopped and
                    len(self.bits) == self.fault_after_rises, 'I2C guard fault did not interrupt the declared data prefix')
        else:
            require(self.stopped and self.bits == self.expected(), 'I2C read wire bytes/ACK order or STOP differs')
            expected_starts = 1 if self.nack_stage in (0, 1) else 2
            require(self.starts == expected_starts, 'I2C read repeated START count')
        return dict(address=self.address, register=self.register, payload_bytes=list(self.payload_bytes),
                    ack_bits=list(self.ack_bits), clock_count=len(self.bits), starts=self.starts,
                    stopped=self.stopped, observed_bits=self.bits, phase_cycles=self.phase_cycles,
                    stretch_cycles=self.stretch_cycles, stretch_events=self.stretch_events,
                    scl_stuck=self.scl_stuck, guard_clock_lost=self.faulted,
                    board_links=[[0, 2], [1, 3]])
