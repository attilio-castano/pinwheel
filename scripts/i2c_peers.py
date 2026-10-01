"""Bounded I2C peers that observe resolved package wires, not engine state."""
from pad_io import PadDrive
from pad_peers import require


class I2CWritePeer:
    """Decode address/data/ACK edges and stop at the first independent NACK.

    ``stretch_cycles`` is a digital callback configuration: a positive value
    pre-arms SCL low and releases it that many chip edges after the controller's
    release is observed. No electrical timing bound follows from this fixture.
    """
    def __init__(self, address, payload_bytes, ack_bits, *, phase_cycles=4,
                 stretch_cycles=0, scl_stuck=False, fault_after_rises=None, fault_delay_cycles=2):
        if type(address) is not int or not 0 <= address < 128:
            raise ValueError('I2C address must fit seven bits')
        if len(payload_bytes) not in (1, 2) or any(type(v) is not int or not 0 <= v < 256 for v in payload_bytes):
            raise ValueError('I2C write requires one/two payload bytes')
        if len(ack_bits) != len(payload_bytes) + 1 or any(type(v) is not int or v not in (0, 1) for v in ack_bits):
            raise ValueError('I2C ACK bits must cover address and payloads')
        if type(phase_cycles) is not int or phase_cycles < 1 or type(stretch_cycles) is not int or stretch_cycles < 0:
            raise ValueError('I2C phase/stretch configuration out of range')
        if type(scl_stuck) is not bool:
            raise ValueError('I2C stuck-clock configuration must be boolean')
        if fault_after_rises is not None and (type(fault_after_rises) is not int or fault_after_rises < 1):
            raise ValueError('I2C guarded-clock fault must follow a positive rise count')
        if type(fault_delay_cycles) is not int or fault_delay_cycles < 0:
            raise ValueError('Guarded-clock fault delay must be nonnegative')
        self.address, self.payload_bytes, self.ack_bits = address, tuple(payload_bytes), tuple(ack_bits)
        self.phase_cycles, self.stretch_cycles, self.scl_stuck = phase_cycles, stretch_cycles, scl_stuck
        self.expected_bytes = (address << 1, *payload_bytes)
        self.completed_bytes = next((index + 1 for index, bit in enumerate(ack_bits) if bit), len(ack_bits))
        self.previous = (1, 1)
        self.previous_clock_command = False
        self.started = self.stopped = False
        self.start_cycle = self.stop_cycle = self.rise_cycle = self.fall_cycle = None
        self.stop_rise_cycle = None
        self.bits, self.rising_cycles, self.falling_cycles = [], [], []
        self.sda_sink = self.clock_sink = False
        self.release_at = None
        self.stretch_events = 0
        self.fault_after_rises, self.faulted = fault_after_rises, False
        self.fault_delay_cycles, self.fault_at = fault_delay_cycles, None

    @property
    def exchange_complete(self):
        return len(self.bits) == 9 * self.completed_bytes

    def drive(self, cycle, pads, ui):
        pins = pads.logical
        require(pins.levels == 0 and not pins.enabled & ~3, 'I2C writes require only low/release SCL/SDA drivers')
        bus = (pads.bit(0), pads.bit(1))
        clock_command = bool(pins.enabled & 1)
        if self.previous[0] and bus[0] and self.previous[1] != bus[1]:
            if not bus[1]:
                require(not self.started and not self.stopped, 'Unexpected repeated I2C START')
                self.started, self.start_cycle = True, cycle
            else:
                require(self.started and self.exchange_complete, 'I2C STOP before complete byte/ACK prefix')
                require(self.stop_rise_cycle is not None, 'I2C STOP lacks its SCL-high preparation')
                require(cycle - self.stop_rise_cycle >= self.phase_cycles, 'I2C STOP high interval')
                self.stopped, self.stop_cycle = True, cycle
        if self.started and not self.stopped and not self.previous[0] and bus[0]:
            if self.fall_cycle is not None:
                require(cycle - self.fall_cycle >= self.phase_cycles, 'I2C clock low interval')
            self.rise_cycle = cycle
            if self.exchange_complete:
                require(self.stop_rise_cycle is None and bool(pins.enabled & 2), 'I2C must prepare STOP after first NACK/final ACK')
                self.stop_rise_cycle = cycle
            else:
                slot = len(self.bits)
                if slot % 9 == 8:
                    require(not pins.enabled & 2, 'Controller drives SDA during peer ACK')
                    require(bus[1] == self.ack_bits[slot // 9], 'I2C ACK wire differs from independent reply')
                else:
                    require(not self.sda_sink, 'I2C peer must release data-bit SDA')
                self.bits.append(bus[1])
                self.rising_cycles.append(cycle)
                if len(self.bits) == self.fault_after_rises:
                    self.fault_at = cycle + self.fault_delay_cycles
        if self.previous[0] and not bus[0] and self.started and not self.stopped:
            require(self.stop_rise_cycle is None, 'Extra I2C clock after first NACK/final ACK')
            if self.rise_cycle is not None and not self.faulted:
                require(cycle - self.rise_cycle >= self.phase_cycles, 'I2C clock high interval')
            elif self.rise_cycle is None:
                require(cycle - self.start_cycle >= self.phase_cycles, 'I2C START hold interval')
            self.fall_cycle = cycle
            self.falling_cycles.append(cycle)
        if not bus[0]:
            slot = len(self.bits)
            self.sda_sink = (not self.exchange_complete and slot % 9 == 8 and self.ack_bits[slot // 9] == 0)
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
        self.previous, self.previous_clock_command = bus, clock_command
        return PadDrive(0, int(self.clock_sink or self.scl_stuck or self.faulted) | int(self.sda_sink) << 1, links=3)

    def check(self, *, timeout=False, fault=False):
        if fault:
            require(self.faulted and self.started and not self.stopped and len(self.bits) == self.fault_after_rises,
                    'Guard loss must interrupt the declared partial I2C write')
        elif timeout:
            require(self.scl_stuck and not self.started and not self.bits and not self.stopped,
                    'Initial stuck-SCL timeout must not issue START or transfer bytes')
        else:
            expected = [bit for index, byte in enumerate(self.expected_bytes[:self.completed_bytes])
                        for bit in (*[(byte >> shift) & 1 for shift in range(7, -1, -1)], self.ack_bits[index])]
            require(self.started and self.stopped, 'I2C write lacks START/STOP framing')
            require(self.bits == expected, 'I2C outgoing byte/ACK order differs from independent peer')
            require(self.exchange_complete, 'I2C continued past first NACK or omitted a byte')
        observed_bytes = [sum(self.bits[9 * index + bit] << (7 - bit) for bit in range(8))
                          for index in range(len(self.bits) // 9)]
        observed_acks = self.bits[8::9]
        return dict(address=self.address, payload_bytes=list(self.payload_bytes),
                    transmitted_bytes=observed_bytes, observed_ack_bits=observed_acks,
                    clock_count=len(self.bits), started=self.started, stopped=self.stopped,
                    phase_cycles=self.phase_cycles, stretch_cycles=self.stretch_cycles,
                    stretch_events=self.stretch_events, scl_stuck=self.scl_stuck,
                    fault_after_rises=self.fault_after_rises, guard_clock_lost=self.faulted,
                    fault_delay_cycles=self.fault_delay_cycles,
                    board_links=[[0, 2], [1, 3]])


class I2CBusClearPeer:
    """Hold SDA until a configured recovery pulse, with no invented tenth rise."""
    def __init__(self, release_after_pulses, *, phase_cycles=4, stretch_cycles=0,
                 scl_stuck=False, fault_after_rises=None, fault_delay_cycles=2):
        if release_after_pulses is not None and (type(release_after_pulses) is not int or not 1 <= release_after_pulses <= 9):
            raise ValueError('Bus-clear SDA release must occur on pulse1..9 or remain stuck')
        if type(phase_cycles) is not int or phase_cycles < 1 or type(stretch_cycles) is not int or stretch_cycles < 0:
            raise ValueError('Bus-clear phase/stretch configuration out of range')
        if type(scl_stuck) is not bool or (fault_after_rises is not None and
                (type(fault_after_rises) is not int or not 1 <= fault_after_rises <= 9)):
            raise ValueError('Bus-clear clock scenario invalid')
        if type(fault_delay_cycles) is not int or fault_delay_cycles < 0:
            raise ValueError('Bus-clear guarded-clock fault delay must be nonnegative')
        self.release_after_pulses, self.phase_cycles = release_after_pulses, phase_cycles
        self.stretch_cycles, self.scl_stuck = stretch_cycles, scl_stuck
        self.fault_after_rises, self.faulted = fault_after_rises, False
        self.fault_delay_cycles, self.fault_at = fault_delay_cycles, None
        self.previous = (1, 1)
        self.previous_clock_command = self.clock_sink = False
        self.sda_sink = True
        self.release_at = self.rise_cycle = self.fall_cycle = None
        self.rising_cycles, self.falling_cycles = [], []
        self.sda_released_at = None
        self.natural_stop = False

    def drive(self, cycle, pads, ui):
        pins = pads.logical
        require(pins.levels == 0 and not pins.enabled & ~1, 'Bus clear must always release SDA and only sink/release SCL')
        bus = (pads.bit(0), pads.bit(1))
        command = bool(pins.enabled & 1)
        if not self.previous[0] and bus[0]:
            require(self.fall_cycle is not None, 'Bus-clear rise lacks a controller low pulse')
            require(cycle - self.fall_cycle >= self.phase_cycles, 'Bus-clear low interval')
            self.rise_cycle = cycle
            self.rising_cycles.append(cycle)
            require(len(self.rising_cycles) <= 9, 'Bus clear emitted more than nine recovery rises')
            if len(self.rising_cycles) == self.fault_after_rises:
                self.fault_at = cycle + self.fault_delay_cycles
            # There is no tenth low phase: release at the ninth observed rise.
            if self.release_after_pulses == 9 and len(self.rising_cycles) == 9:
                self.sda_sink, self.sda_released_at = False, cycle
        if self.previous[0] and not bus[0]:
            if self.rise_cycle is not None and not self.faulted:
                require(cycle - self.rise_cycle >= self.phase_cycles, 'Bus-clear high interval')
            self.fall_cycle = cycle
            self.falling_cycles.append(cycle)
            if self.release_after_pulses is not None and self.release_after_pulses < 9 and len(self.rising_cycles) >= self.release_after_pulses:
                self.sda_sink, self.sda_released_at = False, cycle
        if self.previous[0] and bus[0] and not self.previous[1] and bus[1]:
            self.natural_stop = True
        if command:
            self.clock_sink = self.stretch_cycles > 0
            self.release_at = None
        elif self.previous_clock_command:
            self.release_at = cycle + max(0, self.stretch_cycles - 1)
        if self.release_at is not None and cycle >= self.release_at:
            self.clock_sink = False
        if self.fault_at is not None and cycle >= self.fault_at:
            self.faulted = True
        self.previous, self.previous_clock_command = bus, command
        return PadDrive(0, int(self.clock_sink or self.scl_stuck or self.faulted) | int(self.sda_sink) << 1, links=3)

    def check(self, *, timeout=False, fault=False):
        count = len(self.rising_cycles)
        if fault:
            require(self.faulted and count == self.fault_after_rises, 'Bus-clear guard loss did not interrupt expected pulse')
        elif timeout:
            require(self.scl_stuck and count == 0, 'Stuck-SCL bus clear must time out before any rising pulse')
        else:
            require(count == 9, 'Bus clear must finish exactly nine recovery rises in this finite peer')
            require((self.sda_released_at is not None) == (self.release_after_pulses is not None), 'Bus-clear peer SDA release scenario mismatch')
        return dict(recovery_policy='nine_rises_release_only', pulse_rises=count,
                    release_after_pulses=self.release_after_pulses,
                    sda_released_at=self.sda_released_at, natural_stop=self.natural_stop,
                    controller_stop_claimed=False, stretch_cycles=self.stretch_cycles,
                    callback_delay_cycles=1, sampler_delay_cycles=2,
                    scl_stuck=self.scl_stuck, fault_after_rises=self.fault_after_rises,
                    fault_delay_cycles=self.fault_delay_cycles,
                    guard_clock_lost=self.faulted, board_links=[[0, 2], [1, 3]])
