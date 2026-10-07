"""Independent resolved-wire target for the buffered register-read witness.

The target observes package pads and edge numbers only. It neither receives nor
inspects a program, engine, descriptor, or buffer cursor. This is a digital
fixture, with one callback edge and the model's two sampler registers; its
cycle limits do not establish a physical I2C speed grade.
"""
from pad_io import PadDrive


class BufferedI2CWireError(RuntimeError):
    """The independent wire oracle rejected a waveform."""


def require(condition, message):
    if not condition:
        raise BufferedI2CWireError(message)


def _natural(value, name, low=0):
    if type(value) is not int or value < low:
        raise ValueError(name + ' must be an integer >= ' + str(low))


class BufferedI2CReadPeer:
    """Register target with three control-byte ACKs and a bounded reply.

    ``stretch_cycles`` holds SCL for this many callback cycles at every release.
    ``never_after_bits`` holds the next low phase forever after exactly this
    many wire clocks. ``stop_sda_stuck`` prevents bus-free qualification after
    a complete exchange. None of these injected failures fabricates a STOP.
    """
    def __init__(self, address, register, reply, ack_bits=(0, 0, 0), *,
                 phase_cycles=4, stretch_cycles=0, initially_stuck=False,
                 never_after_bits=None, stop_sda_stuck=False):
        if type(address) is not int or not 0 <= address < 128:
            raise ValueError('I2C address must fit seven bits')
        if type(register) is not int or not 0 <= register < 256:
            raise ValueError('I2C register must fit a byte')
        if type(reply) is not bytes or not 1 <= len(reply) <= 8:
            raise ValueError('I2C reply must contain one through eight bytes')
        if type(ack_bits) is not tuple or len(ack_bits) != 3 or any(
                type(bit) is not int or bit not in (0, 1) for bit in ack_bits):
            raise ValueError('I2C requires three independent ACK bits')
        _natural(phase_cycles, 'I2C phase', 3)
        _natural(stretch_cycles, 'Clock stretching')
        if any(type(flag) is not bool for flag in (initially_stuck, stop_sda_stuck)):
            raise ValueError('I2C fault flags must be Boolean')
        if never_after_bits is not None:
            _natural(never_after_bits, 'Stuck-clock position')
        self.address, self.register, self.reply = address, register, reply
        self.ack_bits = ack_bits
        self.phase_cycles, self.stretch_cycles = phase_cycles, stretch_cycles
        self.initially_stuck, self.never_after_bits = initially_stuck, never_after_bits
        self.stop_sda_stuck = stop_sda_stuck
        self.nack_stage = next((i for i, bit in enumerate(ack_bits) if bit), None)
        self.stop_after = (9 * (self.nack_stage + 1) if self.nack_stage is not None
                           else 27 + 9 * len(reply))
        self.previous = (1, 1)
        self.previous_clock_command = False
        self.clock_sink = self.sda_sink = False
        self.release_at = self.rise_at = self.fall_at = self.start_at = None
        self.stop_rise_at = self.stopped_at = self.sda_changed_at = None
        self.both_high_since = 0
        self.pending_start_fall = False
        self.starts = self.stretch_events = self.release_count = 0
        self.stuck_armed = False
        self.bits, self.rising_cycles = [], []
        self.final_pads = None
        self.final_cycle = None

    def expected(self):
        result = []
        for index, byte in enumerate((self.address << 1, self.register,
                                       (self.address << 1) | 1)):
            result.extend((byte >> bit) & 1 for bit in range(7, -1, -1))
            result.append(self.ack_bits[index])
            if self.ack_bits[index]:
                return result
        for index, byte in enumerate(self.reply):
            result.extend((byte >> bit) & 1 for bit in range(7, -1, -1))
            result.append(int(index == len(self.reply) - 1))
        return result

    def drive(self, cycle, pads, ui):
        pins = pads.logical
        require(pins.levels == 0 and not pins.enabled & ~3,
                'I2C requires only open-drain SCL/SDA low or release')
        bus = pads.bit(0), pads.bit(1)
        require(bus == (pads.bit(2), pads.bit(3)), 'I2C sense/drive board links differ')
        clock_command = bool(pins.enabled & 1)
        if self.previous[0] and bus[0] and self.previous[1] != bus[1]:
            if not bus[1]:
                require(self.both_high_since is not None and
                        cycle - self.both_high_since >= self.phase_cycles,
                        'I2C START setup interval')
                require(self.stopped_at is None and (self.starts == 0 or
                        self.starts == 1 and len(self.bits) == 18 and
                        self.nack_stage not in (0, 1)),
                        'Unexpected I2C START or repeated START')
                self.starts += 1
                self.start_at = cycle
                self.pending_start_fall = True
            else:
                require(self.starts > 0 and len(self.bits) == self.stop_after,
                        'I2C STOP before requested control/data clocks finished')
                require(self.stop_rise_at is not None and
                        cycle - self.stop_rise_at >= self.phase_cycles,
                        'I2C STOP high setup interval')
                require(self.stopped_at is None, 'I2C duplicate STOP')
                self.stopped_at = cycle
        if self.starts and self.stopped_at is None and not self.previous[0] and bus[0]:
            require(bus[1] == self.previous[1], 'I2C SDA changed on SCL rising edge')
            if self.fall_at is not None:
                require(cycle - self.fall_at >= self.phase_cycles, 'I2C clock low interval')
            self.rise_at = cycle
            if len(self.bits) == self.stop_after:
                require(self.stop_rise_at is None and pins.enabled & 2,
                        'I2C lacks SDA-low STOP preparation')
                self.stop_rise_at = cycle
            elif len(self.bits) == 18 and self.starts == 1:
                require(not pins.enabled & 2 and bus[1] == 1,
                        'I2C repeated START setup must release SDA')
            else:
                slot = len(self.bits)
                target_owned = ((slot < 27 and slot % 9 == 8) or
                                (slot >= 27 and (slot - 27) % 9 < 8))
                if target_owned:
                    require(not pins.enabled & 2,
                            'Controller drives SDA during target-owned ACK/data')
                else:
                    require(not self.sda_sink,
                            'Target drives SDA during controller-owned data/ACK')
                if self.sda_changed_at is not None:
                    require(cycle - self.sda_changed_at >= self.phase_cycles,
                            'I2C SDA setup interval')
                expected = self.expected()
                require(slot < len(expected) and bus[1] == expected[slot],
                        'I2C wire bytes or ACK/NACK order differs')
                self.bits.append(bus[1])
                self.rising_cycles.append(cycle)
        if self.previous[0] and not bus[0] and self.starts and self.stopped_at is None:
            require(self.stop_rise_at is None, 'I2C extra clock after terminal exchange')
            if self.pending_start_fall:
                require(cycle - self.start_at >= self.phase_cycles, 'I2C START hold interval')
                self.pending_start_fall = False
            if self.rise_at is not None:
                require(cycle - self.rise_at >= self.phase_cycles, 'I2C clock high interval')
            self.fall_at = cycle
        if self.previous[1] != bus[1] and not bus[0]:
            self.sda_changed_at = cycle
        if self.stopped_at is not None:
            require(bus == (1, 1) and pins.enabled == 0, 'I2C activity after STOP')
        if not bus[0]:
            slot = len(self.bits)
            if slot >= self.stop_after:
                self.sda_sink = self.stop_sda_stuck
            elif slot < 27:
                self.sda_sink = slot % 9 == 8 and self.ack_bits[slot // 9] == 0
            else:
                relative = slot - 27
                self.sda_sink = relative % 9 < 8 and not bool(
                    self.reply[relative // 9] & (1 << (7 - relative % 9)))
        if clock_command:
            if self.never_after_bits is not None and len(self.bits) >= self.never_after_bits:
                self.stuck_armed = True
            self.clock_sink = self.stretch_cycles > 0 or self.stuck_armed
            self.release_at = None
        elif self.previous_clock_command:
            self.release_count += 1
            self.release_at = cycle + max(0, self.stretch_cycles - 1)
            self.stretch_events += int(self.stretch_cycles > 0)
        if self.release_at is not None and cycle >= self.release_at and not self.stuck_armed:
            self.clock_sink = False
        if bus == (1, 1):
            if self.both_high_since is None:
                self.both_high_since = cycle
        else:
            self.both_high_since = None
        self.previous, self.previous_clock_command = bus, clock_command
        self.final_pads = pads
        self.final_cycle = cycle
        return PadDrive(0, int(self.clock_sink or self.initially_stuck) |
                        (int(self.sda_sink) << 1), links=3)

    def check(self, rx_bits=None, *, timeout=False):
        if timeout:
            require(self.initially_stuck or self.stuck_armed or self.stop_sda_stuck or
                    self.stretch_cycles > 0,
                    'I2C timeout lacks an independently injected bus fault')
            require(self.stopped_at is None, 'I2C timeout fabricated a recovered STOP')
            require(self.bits == self.expected()[:len(self.bits)],
                    'I2C timeout wire prefix differs')
            require(self.final_pads.logical.enabled == 0,
                    'Timed-out I2C controller did not release the bus')
        else:
            require(self.stopped_at is not None and self.bits == self.expected(),
                    'I2C lacks complete wire bytes, ACK/NACK clocks, or lawful STOP')
            expected_starts = 1 if self.nack_stage in (0, 1) else 2
            require(self.starts == expected_starts, 'I2C repeated START count')
            require(self.final_pads.logical.enabled == 0 and self.previous == (1, 1),
                    'I2C did not finish on a released, high bus')
            require(self.final_cycle - self.stopped_at >= self.phase_cycles,
                    'I2C STOP bus-free interval')
        if rx_bits is not None:
            expected_rx = tuple(bool(bit) for index, bit in enumerate(self.bits[27:])
                                if index % 9 < 8)
            require(type(rx_bits) is tuple and all(type(bit) is bool for bit in rx_bits)
                    and rx_bits == expected_rx, 'I2C appended RX differs from target wire prefix')
        return dict(protocol='i2c-register-read', address=self.address, register=self.register,
                    reply=self.reply.hex(), ack_bits=list(self.ack_bits), starts=self.starts,
                    sampled_bits=len(self.bits), receive_bits=max(0, len(self.bits) - 27) -
                    max(0, len(self.bits) - 27) // 9, stopped=self.stopped_at is not None,
                    stretch_cycles=self.stretch_cycles, stretch_events=self.stretch_events,
                    phase_cycles=self.phase_cycles, callback_delay_cycles=1,
                    sampler_delay_cycles=2, board_links=[[0, 2], [1, 3]],
                    clock_timeout=bool(self.initially_stuck or self.stuck_armed or
                                       timeout and self.stretch_cycles > 0),
                    bus_free_timeout=bool(self.stop_sda_stuck),
                    final_resolved_bus=list(self.previous),
                    bus_still_held=self.previous != (1, 1),
                    controller_released=self.final_pads.logical.enabled == 0,
                    observed_wire_bits=list(self.bits))
