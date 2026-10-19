"""Independent edge-driven SPI and JTAG targets for the streaming continuation.

Peers see resolved package pins and the physical edge count only. They do not
inspect programs, queue credits, controller state, source traces or counters.
The contract permits low-clock stretching, requires exact high phases, and
retains the callback-plus-two-register sampler assumptions explicitly.
"""
from jtag_peers import TAP
from pad_io import OUTPUT_MASK, PadDrive


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def timing(half_cycles, tco):
    if (type(half_cycles) is not int or type(tco) is not int or
            tco < 0 or half_cycles < tco + 3):
        raise ValueError('Receive timing requires half_cycles >= peer_tco + 3')


class StreamingSPIPeer:
    def __init__(self, transmit, receive, *, half_cycles=4, tco=1):
        if type(transmit) is not bytes or type(receive) is not bytes or len(transmit) != len(receive):
            raise ValueError('SPI target needs matching captured TX and reply bytes')
        timing(half_cycles, tco)
        self.expected = tuple(bool((byte >> bit) & 1) for byte in transmit for bit in range(7, -1, -1))
        self.reply = tuple(bool((byte >> bit) & 1) for byte in receive for bit in range(7, -1, -1))
        self.half_cycles, self.tco = half_cycles, tco
        self.selected = self.finished = False
        self.selected_at = self.released_at = None
        self.previous_clock = self.previous_mosi = 0
        self.control_since = None
        self.clock_edges, self.bits = [], []
        self.low_durations, self.high_durations = [], []
        self.miso = self.reply[0] if self.reply else False
        self.pending = None
        self.decoy_edges = 0

    def drive(self, cycle, pads, ui=0):
        pads.logical
        clock, mosi, cs = pads.bit(3), pads.bit(2), pads.bit(4)
        if not cs:
            require(pads.enabled == OUTPUT_MASK, 'SPI must drive MOSI/SCLK/CS')
            if not self.selected:
                require(not self.finished and not clock, 'SPI must assert CS once with idle clock')
                self.selected, self.selected_at = True, cycle
                self.previous_clock, self.previous_mosi = 0, mosi
                self.control_since = cycle
            if mosi != self.previous_mosi:
                require(not clock, 'SPI MOSI changed during a high phase')
                self.control_since = cycle
            if clock != self.previous_clock:
                if self.clock_edges:
                    duration = cycle - self.clock_edges[-1][0]
                    if clock:
                        require(duration >= self.half_cycles, 'SPI low phase shorter than declared minimum')
                        self.low_durations.append(duration)
                    else:
                        require(duration == self.half_cycles, 'SPI high phase stalled or changed duration')
                        self.high_durations.append(duration)
                else:
                    require(cycle - self.selected_at >= self.half_cycles, 'SPI CS setup interval too short')
                self.clock_edges.append((cycle, bool(clock)))
                if clock:
                    require(cycle - self.control_since >= self.half_cycles, 'SPI MOSI setup interval too short')
                    require(len(self.bits) < len(self.expected), 'SPI extra data clock')
                    self.bits.append(bool(mosi))
                elif self.reply:
                    self.pending = (cycle + self.tco, self.reply[min(len(self.bits), len(self.reply) - 1)])
        elif self.selected:
            require(not clock, 'SPI CS release must restore idle clock')
            if self.clock_edges:
                require(cycle - self.clock_edges[-1][0] >= self.half_cycles, 'SPI CS hold interval too short')
            self.selected, self.finished, self.released_at = False, True, cycle
        if self.pending is not None and cycle >= self.pending[0]:
            self.miso, self.pending = self.pending[1], None
        self.previous_clock, self.previous_mosi = clock, mosi
        if self.selected and clock:
            self.decoy_edges += 1
            return PadDrive(int(not self.miso), 1)
        return PadDrive(int(self.miso), 1)

    def check(self, rx_bits, *, require_stall=False):
        require(self.finished, 'SPI did not finish its single continuous-CS transfer')
        require(tuple(self.bits) == self.expected, 'SPI transmitted data differs from independent target expectation')
        require(tuple(rx_bits) == self.reply, 'SPI received data differs from independent target reply')
        require([level for _, level in self.clock_edges] == [True, False] * len(self.expected),
                'SPI rising/falling clock count or order differs')
        # The current engine has one boundary edge between ordinary cells.
        # Longer low intervals are observed evidence, never inferred from FIFO state.
        extra = sum(max(0, duration - self.half_cycles - 1) for duration in self.low_durations)
        require(not require_stall or extra > 0, 'SPI fixture did not exercise a long low interval')
        return dict(protocol='spi-mode0', bits=len(self.bits), clock_edges=len(self.clock_edges),
            continuous_cs=True, half_cycles=self.half_cycles, high_phase_edges=sorted(set(self.high_durations)),
            low_min_edges=min(self.low_durations, default=0), low_max_edges=max(self.low_durations, default=0),
            low_extra_edges=extra, setup_edges=(self.clock_edges[0][0] - self.selected_at if self.clock_edges else 0),
            total_selected_edges=self.released_at - self.selected_at,
            high_phase_decoy_edges=self.decoy_edges, peer_tco_cycles=self.tco,
            callback_delay_cycles=1, sampler_delay_cycles=2)


class StreamingJTAGPeer:
    def __init__(self, transmit, receive, bit_count, *, half_cycles=4, tco=1, initial_state='pause_ir'):
        if type(bit_count) is not int or not 1 <= bit_count <= 65535:
            raise ValueError('JTAG scan length must be in 1..65535; zero is not a scan')
        if any(type(value) is not int or not 0 <= value < (1 << bit_count) for value in (transmit, receive)):
            raise ValueError('JTAG target data must fit the exact non-byte scan width')
        timing(half_cycles, tco)
        if initial_state not in TAP:
            raise ValueError('Unknown TAP state')
        self.transmit, self.receive, self.bit_count = transmit, receive, bit_count
        self.half_cycles, self.tco = half_cycles, tco
        self.initial_state = self.state = initial_state
        self.previous_clock = self.previous_tms = self.previous_tdi = 0
        self.started_at = self.finished_at = self.last_edge_at = self.control_since = None
        self.clock_edges, self.tms_bits, self.bits, self.states = [], [], [], []
        self.low_durations, self.high_durations = [], []
        self.capture_count = self.update_count = 0
        self.register, self.updated = 0, None
        self.tdo, self.pending, self.final_fall_at = 0, None, None

    def drive(self, cycle, pads, ui=0):
        pads.logical
        clock, tms, tdi = pads.bit(3), pads.bit(4), pads.bit(2)
        if self.finished_at is not None:
            require(not clock, 'JTAG extra clock after the final idle hold')
        if self.started_at is None:
            # A deselected/tri-stated chip is not a driven JTAG reset attempt.
            if pads.enabled == OUTPUT_MASK and tms and not clock:
                self.started_at = self.last_edge_at = self.control_since = cycle
                self.previous_clock = 0
                self.previous_tms, self.previous_tdi = tms, tdi
        if self.started_at is not None and self.finished_at is None:
            require(pads.enabled == OUTPUT_MASK, 'JTAG must drive TDI/TCK/TMS')
            if (tms, tdi) != (self.previous_tms, self.previous_tdi):
                require(not clock, 'JTAG TMS/TDI changed during high phase')
                self.control_since = cycle
            if clock != self.previous_clock:
                duration = cycle - self.last_edge_at
                if clock:
                    require(duration >= self.half_cycles, 'JTAG low phase shorter than declared minimum')
                    require(cycle - self.control_since >= self.half_cycles, 'JTAG TMS/TDI setup interval too short')
                    self.low_durations.append(duration)
                else:
                    require(duration == self.half_cycles, 'JTAG high phase stalled or changed duration')
                    self.high_durations.append(duration)
                self.clock_edges.append((cycle, bool(clock)))
                self.last_edge_at = cycle
                if clock:
                    self._rise(tms, tdi, pads)
                elif self.state == 'shift_dr':
                    self.pending = (cycle + self.tco, self.register & 1)
                elif self.state == 'update_dr' and len(self.tms_bits) > 5:
                    self.updated, self.update_count = self.register, self.update_count + 1
                if not clock and len(self.tms_bits) == self.bit_count + 11:
                    self.final_fall_at = cycle
            if self.final_fall_at is not None and cycle - self.final_fall_at >= self.half_cycles:
                require(not clock and not tms and not tdi, 'JTAG final idle pins differ')
                self.finished_at = cycle
        if self.pending is not None and cycle >= self.pending[0]:
            self.tdo, self.pending = self.pending[1], None
        self.previous_clock, self.previous_tms, self.previous_tdi = clock, tms, tdi
        drive = PadDrive(self.tdo, int(self.state == 'shift_dr'))
        pads.validate_drive(drive)
        return drive

    def _rise(self, tms, tdi, pads):
        index = len(self.tms_bits)
        expected = (1 if index < 5 else (0, 1, 0, 0)[index - 5] if index < 9 else
                    int(index == self.bit_count + 8) if index < self.bit_count + 9 else
                    (1, 0)[index - self.bit_count - 9] if index < self.bit_count + 11 else None)
        require(expected is not None and tms == expected,
                'JTAG reset/navigation/last-bit TMS sequence differs')
        self.tms_bits.append(tms)
        previous = self.state
        if index < 5:
            require(tdi == 0, 'JTAG nonzero TDI during reset')
        elif previous == 'capture_dr':
            self.register, self.capture_count = self.receive, self.capture_count + 1
        elif previous == 'shift_dr':
            slot = len(self.bits)
            require(slot < self.bit_count, 'JTAG scan exceeds its declared width')
            self.bits.append(bool(tdi))
            require(pads.bit(0) == ((self.receive >> slot) & 1), 'JTAG resolved TDO differs from target reply')
            self.register = (self.register >> 1) | (tdi << (self.bit_count - 1))
        else:
            require(tdi == 0, 'JTAG nonzero TDI outside DR scan')
        self.state = TAP[previous][tms]
        self.states.append(self.state)

    def check(self, rx_bits, *, require_stall=False):
        require(self.finished_at is not None, 'JTAG final idle hold missing')
        expected_tx = tuple(bool((self.transmit >> bit) & 1) for bit in range(self.bit_count))
        expected_rx = tuple(bool((self.receive >> bit) & 1) for bit in range(self.bit_count))
        require(tuple(self.bits) == expected_tx, 'JTAG transmitted scan data differs')
        require(tuple(rx_bits) == expected_rx, 'JTAG received scan data differs')
        require(self.capture_count == self.update_count == 1, 'JTAG capture/update count differs')
        require(self.updated == self.transmit and self.state == 'run_test_idle', 'JTAG updated register or final TAP state differs')
        require([level for _, level in self.clock_edges] == [True, False] * (self.bit_count + 11),
                'JTAG clock count/order differs')
        extra = sum(max(0, duration - self.half_cycles - 2) for duration in self.low_durations)
        require(not require_stall or extra > 0, 'JTAG fixture did not exercise a long low interval')
        return dict(protocol='jtag-dr', bits=self.bit_count, clocks=self.bit_count + 11,
            clock_edges=len(self.clock_edges), last_bit_exits_shift_dr=True,
            capture_count=self.capture_count, update_count=self.update_count,
            half_cycles=self.half_cycles, high_phase_edges=sorted(set(self.high_durations)),
            low_min_edges=min(self.low_durations, default=0), low_max_edges=max(self.low_durations, default=0),
            low_extra_edges=extra, initial_tap_state=self.initial_state, final_tap_state=self.state,
            peer_tco_cycles=self.tco, callback_delay_cycles=1, sampler_delay_cycles=2)
