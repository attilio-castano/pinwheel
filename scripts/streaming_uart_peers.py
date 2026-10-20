"""Absolute-clock UART transmitter and independent public sampling observations.

No DUT phase, status, FIFO or source state determines this waveform. A callback
at public cycle n supplies the external drive for physical edge n+1.
"""
from dataclasses import dataclass

from pad_io import PadDrive
from streaming_compile import integer
from streaming_uart_compile import Profile

PROFILES = ('valid', 'false-start', 'bad-stop', 'held-high', 'sampling-center', 'sampling-off-center')


@dataclass(frozen=True)
class UartPlan:
    quarter_cycles: int
    payload: int
    first_low_edge: int
    profile: str = 'valid'
    rx_input: int = 0
    false_low_edges: int = 1
    diagnostic_bit: int = 3

    def __post_init__(self):
        Profile(self.quarter_cycles, self.rx_input)
        integer(self.payload, 0, 255, 'UART external payload')
        integer(self.first_low_edge, 1, (1 << 63) - 1, 'UART absolute start edge')
        integer(self.false_low_edges, 1, 2 * self.quarter_cycles - 1, 'False start LOW edges')
        integer(self.diagnostic_bit, 0, 7, 'UART diagnostic data index')
        if self.profile not in PROFILES:
            raise ValueError('Unknown absolute UART stimulus profile')
        if self.profile.startswith('sampling-') and self.payload != 0:
            raise ValueError('Sampling-window diagnostics use a zero baseline byte')

    @property
    def bit_cycles(self): return 4 * self.quarter_cycles

    @property
    def samples(self):
        return tuple(self.first_low_edge + (6 + 4 * index) * self.quarter_cycles for index in range(8))

    @property
    def expected_terminal_edge(self):
        if self.profile == 'held-high': return None
        if self.profile == 'false-start': return self.first_low_edge + 2 * self.quarter_cycles + 2
        return self.first_low_edge + 38 * self.quarter_cycles + (2 if self.profile == 'bad-stop' else 3)

    @property
    def expected_fault(self): return self.profile in ('false-start', 'bad-stop')

    @property
    def uart_timing(self): return self.profile in ('valid', 'bad-stop')

    @property
    def expected_bits(self):
        if self.profile in ('held-high', 'false-start'): return ()
        if self.profile == 'sampling-center':
            return tuple(index == self.diagnostic_bit for index in range(8))
        if self.profile == 'sampling-off-center': return (False,) * 8
        return tuple(bool((self.payload >> index) & 1) for index in range(8))

    def level_at(self, edge):
        integer(edge, 0, (1 << 63) - 1, 'UART physical edge')
        f, period = self.first_low_edge, self.bit_cycles
        if self.profile == 'held-high' or edge < f:
            return True
        if self.profile == 'false-start':
            return edge >= f + self.false_low_edges
        offset = edge - f
        if offset < period: return False
        if offset < 9 * period:
            if self.profile.startswith('sampling-'):
                pulse = self.samples[self.diagnostic_bit] + (self.profile == 'sampling-off-center')
                return edge == pulse
            return bool((self.payload >> (offset // period - 1)) & 1)
        if offset < 10 * period and self.profile == 'bad-stop': return False
        return True

    def raw_at(self, edge):
        mask = 1 << self.rx_input
        return 3 if self.level_at(edge) else 3 & ~mask


class AbsoluteUartPeer:
    def __init__(self, plan):
        if type(plan) is not UartPlan:
            raise ValueError('UART peer requires an immutable external waveform plan')
        self.plan, self.last_cycle = plan, None

    def drive(self, cycle, pads, ui=0):
        pads.logical
        if pads.enabled:
            raise RuntimeError('UART receiver unexpectedly drives a protocol pad')
        if self.last_cycle is not None and cycle != self.last_cycle + 1:
            raise RuntimeError('UART peer requires consecutive physical-edge callbacks')
        self.last_cycle = cycle
        mask = 1 << self.plan.rx_input
        return PadDrive(mask if self.plan.level_at(cycle + 1) else 0, mask, links=0)


class FrameObservation:
    """Observe actual public edges; never feed results back into the transmitter."""
    def __init__(self, plan, first_edge, last_edge):
        if type(plan) is not UartPlan or not first_edge < plan.first_low_edge < last_edge:
            raise ValueError('UART observation needs an idle arm window and complete frame')
        self.plan, self.first_edge, self.last_edge = plan, first_edge, last_edge
        self.edges = 0
        self.first_raw_low = self.terminal_edge = None
        self.sampled_raw = {}
        self.idle_high_edges = 0

    def __call__(self, record):
        cycle, pins, observed = record['cycle'], record['pins'], record['observation']
        if not self.first_edge <= cycle <= self.last_edge: return
        if cycle != self.first_edge + self.edges:
            raise RuntimeError('UART physical observation has missing or duplicate edges')
        self.edges += 1
        if pins != dict(initialize=0, csn=1, sck=0, mosi=0):
            raise RuntimeError('UART reception performed host I/O during the frame')
        if observed['enabled'] or observed['levels']:
            raise RuntimeError('UART receiver changed its released protocol pins')
        raw = observed['edge_inputs']
        if raw != self.plan.raw_at(cycle):
            raise RuntimeError('UART actual pre-edge raw input differs from the absolute waveform')
        bit = bool(raw & (1 << self.plan.rx_input))
        if not bit and self.first_raw_low is None: self.first_raw_low = cycle
        if cycle < self.plan.first_low_edge and bit: self.idle_high_edges += 1
        if cycle in self.plan.samples: self.sampled_raw[cycle] = bit
        if not observed['busy'] and self.terminal_edge is None: self.terminal_edge = cycle
        if self.terminal_edge is not None and observed['busy']:
            raise RuntimeError('UART receiver became busy again without another START')

    def result(self):
        if self.edges != self.last_edge - self.first_edge + 1 or self.idle_high_edges < 8:
            raise RuntimeError('UART trace lacks its complete frame or eight idle-high arm clocks')
        expected_first = None if self.plan.profile == 'held-high' else self.plan.first_low_edge
        if self.first_raw_low != expected_first:
            raise RuntimeError('UART actual first LOW edge differs from the external plan')
        if self.plan.profile not in ('held-high', 'false-start') and tuple(
                self.sampled_raw[edge] for edge in self.plan.samples) != self.plan.expected_bits:
            raise RuntimeError('UART raw sample centers differ from independently expected chronological bits')
        return dict(first_edge=self.first_edge, last_edge=self.last_edge, edges=self.edges,
            first_raw_low=self.first_raw_low, public_terminal_edge=self.terminal_edge,
            expected_terminal_edge=self.plan.expected_terminal_edge,
            terminal_delta=(self.terminal_edge - self.plan.expected_terminal_edge
                if self.terminal_edge is not None and self.plan.expected_terminal_edge is not None else None),
            idle_high_arm_edges=self.idle_high_edges, raw_sample_edges=list(self.plan.samples),
            raw_center_bits=[self.sampled_raw.get(edge) for edge in self.plan.samples],
            host_frames_during_reception=0, released_protocol_pins=True,
            stimulus_access='absolute physical clock and external payload only; no DUT status/phase feedback')
