"""Independent observers for resident programs on resolved package wires.

These peers use payload specifications, physical pins and integer edge counts.
They never inspect instruction words, execution state or the compiler oracle.
"""
from pad_io import OUTPUT_MASK, PadDrive
from pad_peers import SPIPeer, require


class ResidentUARTPeer:
    def __init__(self, byte, bit_cycles=4):
        if type(byte) is not int or not 0 <= byte <= 255:
            raise ValueError('UART peer byte must fit eight bits')
        if type(bit_cycles) is not int or bit_cycles < 1:
            raise ValueError('UART peer bit period must be positive')
        self.byte, self.bit_cycles = byte, bit_cycles
        self.started_at = self.finished_at = None
        self.trace = []
        self.page_zero_edges = 0
        self.symbols = (0, *((byte >> k) & 1 for k in range(8)), 1)

    def drive(self, cycle, pads, ui):
        pads.logical  # Check the fixed physical pad assignment first.
        self.page_zero_edges = self.page_zero_edges + 1 if (ui >> 3) & 3 == 0 else 0
        if self.started_at is None and pads.enabled & 4 and pads.bit(2) == 0:
            self.started_at = cycle
        if self.started_at is not None and self.finished_at is None:
            age = cycle - self.started_at
            if age < 10 * self.bit_cycles:
                require(pads.enabled == OUTPUT_MASK, 'Resident UART output enables changed inside frame')
                level = pads.bit(2)
                require(level == self.symbols[age // self.bit_cycles],
                        'Resident UART pin waveform differs from payload/timing specification')
                self.trace.append(level)
            else:
                require(age == 10 * self.bit_cycles, 'Resident UART observer skipped an execution edge')
                require(pads.bit(2) == 1, 'Resident UART completion failed to restore idle TX')
                require(self.page_zero_edges >= 3 and not pads.status & 1,
                        'Resident UART package busy exceeded the exact frame duration')
                self.finished_at = cycle
        # Change both sampled inputs continuously; transmitting must ignore them.
        return PadDrive(cycle & 3, 3)

    def check(self):
        expected = [bit for bit in self.symbols for _ in range(self.bit_cycles)]
        require(self.trace == expected, 'Resident UART complete frame waveform')
        require(self.finished_at == self.started_at + len(expected), 'Resident UART frame duration')
        return dict(byte=self.byte, bit_cycles=self.bit_cycles,
                    started_at=self.started_at, finished_at=self.finished_at,
                    execution_edges=len(expected), held_edges_do_not_shift=True)


class ResidentSPIPeer(SPIPeer):
    """Mode-0 wire peer with delayed low-phase data and high-phase decoys.

The correct reply is delivered after the declared clock-to-output delay from
each falling edge. During each high phase MISO carries its complement: a
capture at a later, unintended edge should fail the raw-result check.
"""
    def __init__(self, transmit, receive, half_cycles=4, tco=1):
        super().__init__(0, (transmit,), (receive,), half_cycles, tco)
        self.decoy_edges = 0

    def drive(self, cycle, pads, ui):
        drive = super().drive(cycle, pads, ui)
        if self.selected and pads.bit(3):
            self.decoy_edges += 1
            return PadDrive(drive.levels ^ 1, drive.enabled)
        return drive

    def check(self):
        result = super().check()
        require(self.decoy_edges == 8 * self.half_cycles,
                'Resident SPI high-phase decoy coverage incomplete')
        return dict(result, high_phase_decoy_edges=self.decoy_edges)
