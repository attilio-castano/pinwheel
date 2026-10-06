"""Absolute UART wire schedules and independent byte/ownership oracles.

The sender never uses DUT busy, instruction addresses, sample registers or result
values to choose its waveform. Times are integer quanta; the interactive bridge
installs the externally scheduled level before each chip edge.
"""
from dataclasses import asdict, dataclass

from pad_io import PadDrive
from pad_peers import require


@dataclass(frozen=True)
class Frame:
    start: int
    byte: int
    bit_ticks: int
    stop: int = 1

    def __post_init__(self):
        if any(type(n) is not int for n in (self.start, self.byte, self.bit_ticks, self.stop)) or \
                self.start < 0 or not 0 <= self.byte <= 255 or self.bit_ticks < 1 or self.stop not in (0, 1):
            raise ValueError('UART frame requires nonnegative start, byte, positive bit ticks and binary stop')

    @property
    def end(self):
        return self.start + 10 * self.bit_ticks

    def level(self, time):
        symbol = (time - self.start) // self.bit_ticks
        if symbol == 0:
            return 0
        if 1 <= symbol <= 8:
            return self.byte >> (symbol - 1) & 1
        return self.stop if symbol == 9 else 1


@dataclass(frozen=True)
class Completion:
    core_edge: int
    mailbox_edge: int
    byte: int
    framing_error: bool


class UARTStreamPeer:
    def __init__(self, frames, *, input_pin=0, rx_tick=100, rx_phase=0,
                 wire_delay=0, initial_low_until=0, low_pulses=()):
        if type(input_pin) is not int or input_pin not in (0, 1):
            raise ValueError('UART input pin must be physical sense0 or sense1')
        if any(type(n) is not int for n in (rx_tick, rx_phase, wire_delay, initial_low_until)) or \
                rx_tick < 1 or not 0 <= rx_phase < rx_tick or min(wire_delay, initial_low_until) < 0:
            raise ValueError('UART clock/phase/delay bounds')
        self.frames = tuple(f if isinstance(f, Frame) else Frame(**f) for f in frames)
        if not self.frames or any(a.end > b.start for a, b in zip(self.frames, self.frames[1:])):
            raise ValueError('UART frames must form a nonempty ordered nonoverlapping schedule')
        self.low_pulses = tuple(tuple(p) for p in low_pulses)
        if any(len(p) != 2 or any(type(n) is not int for n in p) or not 0 <= p[0] < p[1]
               for p in self.low_pulses):
            raise ValueError('UART low pulses must use ordered nonnegative time intervals')
        self.input_pin, self.rx_tick, self.rx_phase = input_pin, rx_tick, rx_phase
        self.wire_delay, self.initial_low_until = wire_delay, initial_low_until
        self.last_applied = None
        self.observations, self.transitions = [], []

    def edge_time(self, edge):
        return self.rx_phase + edge * self.rx_tick

    def line(self, time):
        time -= self.wire_delay
        if time < 0:
            return 1
        if time < self.initial_low_until or any(a <= time < b for a, b in self.low_pulses):
            return 0
        for frame in self.frames:
            if frame.start <= time < frame.end:
                return frame.level(time)
        return 1

    def consumed_line(self, edge, sampler_stages=2):
        return 1 if edge < sampler_stages else self.line(self.edge_time(edge - sampler_stages))

    def drive(self, cycle, pads, ui):
        require(pads.enabled == 0, 'UART reception must release every output pad')
        if self.last_applied is not None:
            require(pads.bit(self.input_pin) == self.last_applied,
                    'UART resolved input differs from independently scheduled external drive')
        self.observations.append(dict(edge=cycle, time=self.edge_time(cycle),
            pin=pads.bit(self.input_pin), ui=ui, status=pads.status))
        level = self.line(self.edge_time(cycle + 1))
        if level != self.last_applied:
            self.transitions.append(dict(edge=cycle + 1, time=self.edge_time(cycle + 1), level=level))
        self.last_applied = level
        spare = int(cycle % 3 == 0)
        return PadDrive(level << self.input_pin | spare << (1 - self.input_pin), 3)

    def completions(self, bit_cycles, armed_edge, end_edge, *, mailbox_delay=1):
        """Protocol-phase oracle on the independently scheduled sampled history.

        This models 8N1 start validation and the automatic one-edge rearm. It
        contains no compiled instruction, hardware expression or engine PC.
        """
        if type(bit_cycles) is not int or not 8 <= bit_cycles <= 6656:
            raise ValueError('UART receiver period outside8..6656')
        phase, detected, symbol, byte, due = 'idle', 0, 0, 0, 0
        result = []
        for edge in range(armed_edge + 1, end_edge + 1):
            line = self.consumed_line(edge)
            if phase == 'rearm':
                phase = 'idle'
            elif phase == 'idle':
                if line:
                    phase = 'falling'
            elif phase == 'falling':
                if not line:
                    detected, symbol, byte = edge, 0, 0
                    due, phase = detected + bit_cycles // 2, 'sample'
            elif edge == due:
                if symbol == 0 and line:
                    phase = 'idle'
                elif symbol == 9:
                    result.append(Completion(edge, edge + mailbox_delay, byte, not bool(line)))
                    phase = 'rearm'
                else:
                    if symbol:
                        byte |= line << (symbol - 1)
                    symbol += 1
                    due += bit_cycles
        return result

    def report(self):
        return dict(input_pin=self.input_pin, rx_tick=self.rx_tick, rx_phase=self.rx_phase,
            wire_delay_quanta=self.wire_delay, initial_low_until=self.initial_low_until,
            low_pulses=[list(p) for p in self.low_pulses], frames=[asdict(f) for f in self.frames],
            observed_edges=len(self.observations), transitions=self.transitions,
            sampler_delay_cycles=2,
            boundary='Independent integer-quanta sender waveform installed before chip edges; '
                'actual resolved sense pad checked on the following observation. No metastability or analog timing claim.')


class OneEntryOracle:
    """Separate imperative ownership oracle; pop old then push new, with explicit loss."""
    def __init__(self, pending=None, overrun=False):
        self.pending, self.overrun = pending, bool(overrun)
        self.accepted, self.delivered, self.dropped, self.flushed = [], [], [], []

    def edge(self, arrival=None, *, take=False, clear=False, reset=False):
        receipt = dict(accepted=None, delivered=None, dropped=None, flushed=None)
        if reset:
            receipt['flushed'], self.pending = self.pending, None
            self.overrun = False
        else:
            if clear:
                self.overrun = False
            if take:
                receipt['delivered'], self.pending = self.pending, None
            if arrival is not None:
                if self.pending is None:
                    receipt['accepted'], self.pending = arrival, arrival
                else:
                    receipt['dropped'], self.overrun = arrival, True
        for name, value in receipt.items():
            if value is not None:
                getattr(self, name).append(value)
        return receipt
