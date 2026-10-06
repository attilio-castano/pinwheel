"""Independent JTAG TAP peer observing resolved package wires only.

The state table and DR shift behavior describe the target, not Pinwheel's
instructions. TMS/TDI are consumed on TCK rising edges; TDO is scheduled after
falling edges. The target begins in a declared arbitrary TAP state and has one
eight-bit data register selected by reset. No instruction/engine oracle is read.

Timing references: AMD AM011 JTAG Controller Interface Pins and Altera Virtual
JTAG IP Core User Guide, TAP Controller State Machine. The target is a bounded
digital fixture; this does not qualify a board, an instruction register or chain.

https://docs.amd.com/r/en-US/am011-versal-acap-trm/JTAG-Controller-Interface-Pins
https://docs.altera.com/r/docs/683705/20.3/virtual-jtag-ip-core-user-guide/design-example-tap-controller-state-machine
"""
from pad_io import OUTPUT_MASK, PadDrive
from pad_peers import require


TAP = {
    'test_logic_reset': ('run_test_idle', 'test_logic_reset'),
    'run_test_idle': ('run_test_idle', 'select_dr'),
    'select_dr': ('capture_dr', 'select_ir'),
    'capture_dr': ('shift_dr', 'exit1_dr'),
    'shift_dr': ('shift_dr', 'exit1_dr'),
    'exit1_dr': ('pause_dr', 'update_dr'),
    'pause_dr': ('pause_dr', 'exit2_dr'),
    'exit2_dr': ('shift_dr', 'update_dr'),
    'update_dr': ('run_test_idle', 'select_dr'),
    'select_ir': ('capture_ir', 'test_logic_reset'),
    'capture_ir': ('shift_ir', 'exit1_ir'),
    'shift_ir': ('shift_ir', 'exit1_ir'),
    'exit1_ir': ('pause_ir', 'update_ir'),
    'pause_ir': ('pause_ir', 'exit2_ir'),
    'exit2_ir': ('shift_ir', 'update_ir'),
    'update_ir': ('run_test_idle', 'select_dr'),
}


class JTAGPeer:
    """One reset/navigation/eight-bit DR scan with a delayed target TDO.

    Package pads are TDI2/TCK3/TMS4 and TDO0. The callback's drive applies on
    the next chip edge; the engine consumes it after two sampler edges. A TDO
    change scheduled tco edges after a TCK fall therefore needs tco+3 edges
    before the next TCK rise. Default H4/tco1 meets that digital contract.
    """
    def __init__(self, transmit, receive, half_cycles=4, tco=1,
                 initial_state='pause_ir'):
        if any(type(byte) is not int or not 0 <= byte <= 255
               for byte in (transmit, receive)):
            raise ValueError('JTAG peer bytes must fit eight bits')
        if type(half_cycles) is not int or not 1 <= half_cycles <= 256:
            raise ValueError('JTAG half period must be 1..256')
        if type(tco) is not int or tco < 0 or half_cycles < tco + 3:
            raise ValueError('JTAG receive timing requires half_cycles >= tco + 3')
        if initial_state not in TAP:
            raise ValueError('Unknown initial JTAG TAP state')
        self.transmit, self.receive = transmit, receive
        self.half_cycles, self.tco = half_cycles, tco
        self.initial_state = self.state = initial_state
        self.previous_clock = 0
        self.previous_tms = self.previous_tdi = 0
        self.started_at = self.finished_at = self.last_edge_at = None
        self.control_since = None
        self.clock_edges, self.tms_bits, self.bits, self.tdo_bits = [], [], [], []
        self.states, self.capture_count, self.update_count = [], 0, 0
        self.register, self.updated = 0, None
        self.tdo, self.pending = 0, None
        self.final_fall_at = None

    def drive(self, cycle, pads, ui):
        pads.logical
        clock, tms, tdi = pads.bit(3), pads.bit(4), pads.bit(2)
        if self.finished_at is not None:
            require(not clock, 'JTAG additional clock after the final idle hold')
        if self.started_at is None:
            # The idle profile drives all three signals low. The first reset
            # low phase asserts TMS and uniquely marks this transaction.
            if tms:
                require(pads.enabled == OUTPUT_MASK and not clock,
                        'JTAG reset must start with driven TMS and low TCK')
                self.started_at = self.last_edge_at = cycle
                self.control_since = cycle
            else:
                require(not clock, 'JTAG clock before reset/navigation')
        if self.started_at is not None and self.finished_at is None:
            require(pads.enabled == OUTPUT_MASK, 'JTAG must drive TDI2/TCK3/TMS4')
            if (tms, tdi) != (self.previous_tms, self.previous_tdi):
                require(not clock, 'JTAG TMS/TDI changed outside a low-clock phase')
                self.control_since = cycle
            if clock != self.previous_clock:
                require(cycle - self.last_edge_at == self.half_cycles,
                        'JTAG clock half-period timing')
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
                if not clock and len(self.tms_bits) == 19:
                    self.final_fall_at = cycle
            if self.final_fall_at is not None:
                age = cycle - self.final_fall_at
                require(not clock and not tms and not tdi,
                        'JTAG final idle pins')
                if age >= self.half_cycles:
                    require(age == self.half_cycles, 'JTAG observer skipped final hold')
                    self.finished_at = cycle
        if self.pending is not None and cycle >= self.pending[0]:
            self.tdo = self.pending[1]
            self.pending = None
        self.previous_clock, self.previous_tms, self.previous_tdi = clock, tms, tdi
        drive = PadDrive(self.tdo, int(self.state == 'shift_dr'))
        pads.validate_drive(drive)
        return drive

    def _rise(self, tms, tdi, pads):
        index = len(self.tms_bits)
        expected_tms = ([1] * 5 + [0, 1, 0, 0] + [0] * 7 + [1, 1, 0])
        require(index < len(expected_tms) and tms == expected_tms[index],
                'JTAG reset/navigation/final-bit TMS sequence')
        self.tms_bits.append(tms)
        previous = self.state
        if index < 5:
            require(tdi == 0, 'JTAG TDI during TAP reset')
            self.state = TAP[previous][tms]
            self.states.append(self.state)
            if index == 4:
                require(self.state == 'test_logic_reset', 'JTAG five-clock TAP reset')
            return
        if previous == 'capture_dr':
            self.register = self.receive
            self.capture_count += 1
        elif previous == 'shift_dr':
            slot = len(self.bits)
            require(slot < 8, 'JTAG DR scan exceeds eight bits')
            self.bits.append(tdi)
            self.tdo_bits.append(pads.bit(0))
            require(pads.bit(0) == (self.receive >> slot) & 1,
                    'JTAG resolved TDO differs from the delayed target reply')
            self.register = (self.register >> 1) | (tdi << 7)
        else:
            require(tdi == 0, 'JTAG TDI outside the data-register scan')
        self.state = TAP[previous][tms]
        self.states.append(self.state)

    def check(self, samples=None):
        require(self.finished_at is not None, 'JTAG scan did not finish its final idle hold')
        require(self.bits == [(self.transmit >> k) & 1 for k in range(8)],
                'JTAG outgoing byte/LSB-first wire order')
        require(self.capture_count == self.update_count == 1,
                'JTAG DR capture/update occurrences')
        require(self.updated == self.transmit and self.state == 'run_test_idle',
                'JTAG updated target byte/final TAP state')
        require(len(self.clock_edges) == 38 and
                [rising for _, rising in self.clock_edges] == [True, False] * 19,
                'JTAG nineteen-clock rising/falling sequence')
        require(self.finished_at - self.started_at == 39 * self.half_cycles,
                'JTAG exact scan duration')
        if samples is not None:
            require(type(samples) is int and samples == self.receive,
                    'JTAG capture slots must contain exactly the LSB-first reply byte')
        return dict(transmitted=self.transmit, received=self.receive,
                    half_cycles=self.half_cycles, peer_tco_cycles=self.tco,
                    callback_delay_cycles=1, sampler_delay_cycles=2,
                    required_half_cycles=self.tco + 3,
                    within_receive_timing_contract=True,
                    initial_tap_state=self.initial_state, final_tap_state=self.state,
                    tap_states=list(self.states), clocks=19, clock_edges=38,
                    sampled_bits=len(self.bits), capture_slots=list(range(8)),
                    result_bit_order='lsb-first', execution_edges=39 * self.half_cycles,
                    started_at=self.started_at, finished_at=self.finished_at)
