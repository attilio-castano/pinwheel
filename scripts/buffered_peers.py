"""Independent targets for longer buffered-model transfers.

Targets consume resolved package wires and integer edge counts. They do not
read programs, engine state, buffer descriptors, or completion counters. These
are bounded digital fixtures, with the same one-edge callback and two-edge
sampler contract as the existing SPI/JTAG package peers; no physical timing
qualification, JTAG instruction register, or scan chain is implied.
"""
from jtag_peers import TAP
from pad_io import OUTPUT_MASK, PadDrive
from pad_peers import require


def _timing(half_cycles, tco):
    if type(half_cycles) is not int or type(tco) is not int or tco < 0 or half_cycles < tco + 3:
        raise ValueError('Receive timing requires half_cycles >= tco + 3')


class BufferedSPIPeer:
    """Mode-0 target retaining CS across every byte of one transfer.

    Delayed reply changes are followed by high-phase complements. Capturing
    late in a high phase therefore does not accidentally produce a valid reply.
    """
    def __init__(self, transmit, receive, half_cycles=4, tco=1):
        if type(transmit) is not bytes or type(receive) is not bytes or not transmit or len(transmit) != len(receive):
            raise ValueError('SPI peer needs matching nonempty byte strings')
        _timing(half_cycles, tco)
        self.transmit, self.receive = transmit, receive
        self.half_cycles, self.tco = half_cycles, tco
        self.reply = tuple(bool((byte >> bit) & 1) for byte in receive for bit in range(7, -1, -1))
        self.miso = self.reply[0]
        self.selected = self.finished = False
        self.previous_clock = self.previous_mosi = 0
        self.selected_at = self.released_at = None
        self.clock_edges, self.bits, self.sample_edges = [], [], []
        self.pending = None
        self.decoy_edges = 0

    def drive(self, cycle, pads, ui):
        pads.logical
        clock, mosi, cs = pads.bit(3), pads.bit(2), pads.bit(4)
        if not cs:
            require(pads.enabled == OUTPUT_MASK, 'SPI must drive MOSI2/SCLK3/CS4')
            if not self.selected:
                require(not self.finished, 'SPI CS asserted twice')
                require(not clock, 'SPI CS assertion must start with idle clock')
                self.selected, self.selected_at = True, cycle
            if clock and self.previous_clock:
                require(mosi == self.previous_mosi, 'SPI MOSI changed inside high phase')
            if clock != self.previous_clock:
                if self.clock_edges:
                    require(cycle - self.clock_edges[-1][0] == self.half_cycles,
                            'SPI clock half-period spacing')
                else:
                    require(cycle - self.selected_at == self.half_cycles,
                            'SPI CS setup interval')
                self.clock_edges.append((cycle, bool(clock)))
                if clock:
                    require(len(self.bits) < len(self.reply), 'SPI extra data clock')
                    self.bits.append(bool(mosi))
                    self.sample_edges.append(cycle)
                else:
                    self.pending = (cycle + self.tco, self.reply[min(len(self.bits), len(self.reply) - 1)])
        elif self.selected:
            require(not clock, 'SPI release must restore idle clock')
            require(self.clock_edges and cycle - self.clock_edges[-1][0] == self.half_cycles,
                    'SPI CS hold interval')
            self.selected, self.finished, self.released_at = False, True, cycle
        if self.pending is not None and cycle >= self.pending[0]:
            self.miso = self.pending[1]
            self.pending = None
        self.previous_clock, self.previous_mosi = clock, mosi
        if self.selected and clock:
            self.decoy_edges += 1
            return PadDrive(int(not self.miso), 1)
        return PadDrive(int(self.miso), 1)

    def check(self, rx_bits=None):
        expected = [bool((byte >> bit) & 1) for byte in self.transmit for bit in range(7, -1, -1)]
        require(self.finished, 'SPI did not release CS')
        require(self.bits == expected, 'SPI outgoing bytes/MSB-first wire order')
        require([level for _, level in self.clock_edges] == [True, False] * len(expected),
                'SPI complete rising/falling clock sequence')
        require(self.released_at - self.selected_at == (2 * len(expected) + 1) * self.half_cycles,
                'SPI exact continuous-CS duration')
        require(self.decoy_edges == len(expected) * self.half_cycles,
                'SPI high-phase decoy coverage')
        if rx_bits is not None:
            require(type(rx_bits) is tuple and all(type(bit) is bool for bit in rx_bits) and rx_bits == self.reply,
                    'SPI appended RX differs from target wire reply')
        return dict(protocol='spi-mode0', transmitted=self.transmit.hex(), received=self.receive.hex(),
                    sampled_bits=len(expected), clock_edges=len(self.clock_edges),
                    execution_edges=(2 * len(expected) + 1) * self.half_cycles,
                    half_cycles=self.half_cycles, peer_tco_cycles=self.tco,
                    callback_delay_cycles=1, sampler_delay_cycles=2,
                    required_half_cycles=self.tco + 3, continuous_cs=True,
                    high_phase_decoy_edges=self.decoy_edges)


class BufferedJTAGPeer:
    """Arbitrary-width reset-selected DR, including non-byte scan lengths."""
    def __init__(self, transmit, receive, bit_count=32, half_cycles=4, tco=1,
                 initial_state='pause_ir'):
        if type(bit_count) is not int or bit_count < 1:
            raise ValueError('JTAG peer bit count must be positive')
        if any(type(value) is not int or not 0 <= value < 1 << bit_count for value in (transmit, receive)):
            raise ValueError('JTAG values must fit declared bit count')
        _timing(half_cycles, tco)
        if initial_state not in TAP:
            raise ValueError('Unknown initial TAP state')
        self.transmit, self.receive, self.bit_count = transmit, receive, bit_count
        self.half_cycles, self.tco = half_cycles, tco
        self.initial_state = self.state = initial_state
        self.previous_clock = self.previous_tms = self.previous_tdi = 0
        self.started_at = self.finished_at = self.last_edge_at = self.control_since = None
        self.clock_edges, self.tms_bits, self.bits, self.tdo_bits, self.states = [], [], [], [], []
        self.capture_count = self.update_count = 0
        self.register, self.updated = 0, None
        self.tdo, self.pending, self.final_fall_at = 0, None, None

    def drive(self, cycle, pads, ui):
        pads.logical
        clock, tms, tdi = pads.bit(3), pads.bit(4), pads.bit(2)
        if self.finished_at is not None:
            require(not clock, 'JTAG extra clock after final hold')
        if self.started_at is None:
            if tms:
                require(pads.enabled == OUTPUT_MASK and not clock,
                        'JTAG reset must start driven with low clock')
                self.started_at = self.last_edge_at = self.control_since = cycle
            else:
                require(not clock, 'JTAG clock before reset')
        if self.started_at is not None and self.finished_at is None:
            require(pads.enabled == OUTPUT_MASK, 'JTAG must drive TDI2/TCK3/TMS4')
            if (tms, tdi) != (self.previous_tms, self.previous_tdi):
                require(not clock, 'JTAG TMS/TDI changed outside low phase')
                self.control_since = cycle
            if clock != self.previous_clock:
                require(cycle - self.last_edge_at == self.half_cycles,
                        'JTAG clock half-period spacing')
                self.clock_edges.append((cycle, bool(clock)))
                self.last_edge_at = cycle
                if clock:
                    require(cycle - self.control_since >= self.half_cycles,
                            'JTAG TMS/TDI setup interval')
                    self._rise(tms, tdi, pads)
                elif self.state == 'shift_dr':
                    self.pending = (cycle + self.tco, self.register & 1)
                elif self.state == 'update_dr' and len(self.tms_bits) > 5:
                    self.updated = self.register
                    self.update_count += 1
                if not clock and len(self.tms_bits) == self.bit_count + 11:
                    self.final_fall_at = cycle
            if self.final_fall_at is not None:
                age = cycle - self.final_fall_at
                require(not clock and not tms and not tdi, 'JTAG final idle pins')
                if age >= self.half_cycles:
                    require(age == self.half_cycles, 'JTAG skipped final idle hold')
                    self.finished_at = cycle
        if self.pending is not None and cycle >= self.pending[0]:
            self.tdo, self.pending = self.pending[1], None
        self.previous_clock, self.previous_tms, self.previous_tdi = clock, tms, tdi
        drive = PadDrive(self.tdo, int(self.state == 'shift_dr'))
        pads.validate_drive(drive)
        return drive

    def _rise(self, tms, tdi, pads):
        index = len(self.tms_bits)
        expected_tms = [1] * 5 + [0, 1, 0, 0] + [0] * (self.bit_count - 1) + [1, 1, 0]
        require(index < len(expected_tms) and tms == expected_tms[index],
                'JTAG reset/navigation/last-bit TMS sequence')
        self.tms_bits.append(tms)
        previous = self.state
        if index < 5:
            require(tdi == 0, 'JTAG nonzero TDI during reset')
            self.state = TAP[previous][tms]
            self.states.append(self.state)
            if index == 4:
                require(self.state == 'test_logic_reset', 'JTAG five-clock reset failed')
            return
        if previous == 'capture_dr':
            self.register = self.receive
            self.capture_count += 1
        elif previous == 'shift_dr':
            slot = len(self.bits)
            require(slot < self.bit_count, 'JTAG scan exceeds declared width')
            self.bits.append(bool(tdi))
            self.tdo_bits.append(bool(pads.bit(0)))
            require(pads.bit(0) == (self.receive >> slot) & 1,
                    'JTAG resolved TDO differs from delayed reply')
            self.register = (self.register >> 1) | (tdi << (self.bit_count - 1))
        else:
            require(tdi == 0, 'JTAG TDI outside DR scan')
        self.state = TAP[previous][tms]
        self.states.append(self.state)

    def check(self, rx_bits=None):
        require(self.finished_at is not None, 'JTAG final idle hold missing')
        require(self.bits == [bool((self.transmit >> bit) & 1) for bit in range(self.bit_count)],
                'JTAG outgoing LSB-first scan')
        require(self.capture_count == self.update_count == 1, 'JTAG capture/update counts')
        require(self.updated == self.transmit and self.state == 'run_test_idle',
                'JTAG updated DR/final TAP state')
        clocks = self.bit_count + 11
        require([level for _, level in self.clock_edges] == [True, False] * clocks,
                'JTAG complete rising/falling clock sequence')
        require(self.finished_at - self.started_at == (2 * clocks + 1) * self.half_cycles,
                'JTAG exact scan duration')
        if rx_bits is not None:
            expected = tuple(bool((self.receive >> bit) & 1) for bit in range(self.bit_count))
            require(type(rx_bits) is tuple and all(type(bit) is bool for bit in rx_bits) and rx_bits == expected,
                    'JTAG appended RX differs from target reply')
        return dict(protocol='jtag-reset-dr', transmitted=self.transmit, received=self.receive,
                    sampled_bits=self.bit_count, clocks=clocks, clock_edges=2 * clocks,
                    execution_edges=(2 * clocks + 1) * self.half_cycles,
                    half_cycles=self.half_cycles, peer_tco_cycles=self.tco,
                    callback_delay_cycles=1, sampler_delay_cycles=2,
                    required_half_cycles=self.tco + 3,
                    initial_tap_state=self.initial_state, final_tap_state=self.state,
                    tap_states=list(self.states), last_bit_exits_shift_dr=True)
