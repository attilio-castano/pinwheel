"""Independent digital wire replay for a reply-driven SWD RDBUFF read.

The peer is already in point-to-point SWD mode, with default turnaround
and overrun detection disabled. Its response models a previously issued
AP read that is ready, outstanding, or faulted.
"""
from dataclasses import asdict, dataclass

from pad_io import PadDrive
from streaming_ready_transport import ReadyHost
from streaming_rtl import QuadRTL
from streaming_transport import Code, Opcode, QuadTransport, StreamTransportError
from streaming_wire_cases import EdgeTrace, require


SWCLK = 2
SWDIO = 3
SENSE = 1
DATA_OE = 1 << SWDIO
HALF_CYCLES = 4
MAX_EXCHANGES = 12
CASES = (
    ("ok", 0b001, 0xDEAD89AF, False),
    ("wait", 0b010, 0, False),
    ("fault", 0b100, 0, False),
    ("bad-parity", 0b001, 0x9E3606F2, True),
    ("invalid-ack", 0b011, 0x34EDAACB, False),
)


def lsb_bits(value, width):
    return tuple(bool(value & (1 << bit)) for bit in range(width))


class SwdPeerError(RuntimeError):
    def __init__(self, reason, message, slot, edge):
        super().__init__(message)
        self.reason = reason
        self.slot = slot
        self.edge = edge


@dataclass(frozen=True)
class Slot:
    phase: str
    host: bool | None = None
    target: bool | None = None


class RdbuffPeer:
    """Resolve the peer's next drive from observed SWCLK falls."""

    def __init__(self, ack, word, bad_parity, *, half_cycles=HALF_CYCLES):
        self.half_cycles = half_cycles
        # SWD request: START, APnDP, RnW, A[2:3], parity, STOP, PARK.
        fields = (False, True, True, True)
        request = (True, *fields, bool(sum(fields) % 2), False, True)
        ack_bits = lsb_bits(ack, 3)
        data = (*lsb_bits(word, 32), bool(word.bit_count() % 2) ^ bad_parity)
        invalid = ack not in (0b001, 0b010, 0b100)
        self.reply = ack_bits + (data if ack == 0b001 else ())
        # After a malformed ACK, keep driving a possible data phase. The
        # host has to stay released even though its decoder rejects the ACK.
        data_phase = "potential-data" if invalid else "data"
        data_slots = [Slot(data_phase, target=bit) for bit in data] if ack == 0b001 or invalid else []
        self.plan = (
            [Slot("request", host=bit) for bit in request]
            + [Slot("turnaround-to-target")]
            + [Slot("ack", target=bit) for bit in ack_bits]
            + data_slots
            + [Slot("turnaround-to-host")]
            + ([] if invalid else [Slot("idle", host=False)] * 8)
        )
        self.target = None
        self.clock = False
        self.host = None
        self.busy_start = None
        self.busy_end = None
        self.slots = []
        self.falling_edges = []

    def expect(self, condition, reason, message, cycle):
        if not condition:
            raise SwdPeerError(reason, message, len(self.slots), cycle)

    def drive(self, cycle, pads, _ui=0):
        if self.busy_start is None and not pads.status:
            return PadDrive()
        clock, data = bool(pads.bit(SWCLK)), bool(pads.bit(SWDIO))
        host = bool(pads.levels & DATA_OE) if pads.enabled & DATA_OE else None
        self.expect(data == bool(pads.bit(SENSE)), "board-link",
                    "SWDIO drive and sense pads differ", cycle)
        self.expect(pads.enabled & (1 << SWCLK) and not pads.enabled & (1 << 4), "pad-map",
                    "SWD needs a driven clock and an unused third output", cycle)
        self.expect(host is None or self.target is None, "contention",
                    "SWDIO host and target overlap", cycle)
        if self.busy_start is None:
            self.expect(not clock and host is None, "start",
                        "SWD START did not first establish idle pins", cycle)
            self.busy_start = cycle
        if clock and self.clock:
            self.expect(host == self.host, "high-drive",
                        "Host changed SWDIO while SWCLK remained high", cycle)
        if self.clock and not clock:
            self.falling_edges.append(cycle)
            self.target = self.plan[len(self.slots)].target if len(self.slots) < len(self.plan) else None
        if not self.clock and clock:
            self.rising(cycle, data, host)
        if not pads.status:
            if self.busy_end is None:
                self.expect(len(self.slots) == len(self.plan), "response-path",
                            "SWD stopped before the expected response path and idle clocks ended", cycle)
                self.busy_end = cycle
            self.expect(not clock and host is None and self.target is None, "terminal",
                        "SWD completion did not release SWDIO at low clock", cycle)
        self.clock, self.host = clock, host
        return PadDrive(DATA_OE if self.target else 0, DATA_OE if self.target is not None else 0)

    def rising(self, cycle, data, host):
        index = len(self.slots)
        self.expect(self.busy_end is None and index < len(self.plan), "response-path",
                    "SWD emitted an extra clock outside the expected response path", cycle)
        slot = self.plan[index]
        if slot.phase.startswith("turnaround"):
            self.expect(host is None and self.target is None, "turnaround-host-drive",
                        "A full SWD turnaround clock must have both SWDIO drivers released", cycle)
        else:
            self.expect(host == slot.host and self.target == slot.target, "slot-ownership",
                        f"SWD {slot.phase} clock has the wrong drive or data owner", cycle)
            driven = slot.host if slot.host is not None else slot.target
            self.expect(driven is not None and data == driven, "slot-data",
                        f"SWD {slot.phase} driven bit differs at SWCLK rise", cycle)
        self.slots.append(dict(cycle=cycle, phase=slot.phase, host_enabled=host is not None,
                               target_enabled=self.target is not None, data=data))

    def check_trace(self, records, captured):
        require(self.busy_end is not None and len(self.slots) == len(self.plan) == len(self.falling_edges),
                "Incomplete SWD command waveform")
        require(tuple(captured) == self.reply, "Runner did not return the exact SWD sample interval")
        by_cycle = {record["cycle"]: record for record in records}
        apertures, low_widths = [], []
        previous_fall = self.busy_start
        for slot, rise, fall in zip(self.plan, self.slots, self.falling_edges, strict=True):
            edge = rise["cycle"]
            require(fall - edge == self.half_cycles and edge - previous_fall >= self.half_cycles,
                    "SWD violated the declared high duration or minimum low duration")
            low_widths.append(edge - previous_fall)
            previous_fall = fall
            if slot.phase.startswith("turnaround"):
                require(all(not ((by_cycle[k]["observation"]["enabled"] << 2) & DATA_OE)
                            and not (by_cycle[k]["drive"]["enabled"] & DATA_OE)
                            for k in range(edge - self.half_cycles, fall)),
                        "SWDIO was driven during a turnaround half-cycle")
            if slot.host is not None:
                for k in range(edge - 2, edge + 1):
                    observed = by_cycle[k]["observation"]
                    require(bool((observed["enabled"] << 2) & DATA_OE)
                            and bool((observed["levels"] << 2) & DATA_OE) == slot.host
                            and bool(observed["edge_inputs"] & (1 << SENSE)) == slot.host,
                            "SWD request or idle bit lacked stable setup before SWCLK rose")
            if slot.target is not None:
                sample_edge = edge - 2
                for k in range(sample_edge, edge + 1):
                    record = by_cycle[k]
                    require(record["drive"]["enabled"] == DATA_OE
                            and bool(record["drive"]["levels"] & DATA_OE) == slot.target
                            and bool(record["observation"]["edge_inputs"] & (1 << SENSE)) == slot.target,
                            "SWD response was unstable at the second-sampler aperture")
                if slot.phase != "potential-data":
                    apertures.append(dict(rise=edge, raw_sample=sample_edge, data=slot.target))
        return dict(busy_start=self.busy_start, busy_end=self.busy_end, clock_pairs=len(self.slots),
                    swclk_high_cycles=self.half_cycles, swclk_low_cycles=low_widths,
                    slots=self.slots, apertures=apertures)


def exchange(rtl, loaded, case, *, observe, execution, peer_factory=RdbuffPeer):
    name, ack, word, bad_parity = case
    peer = peer_factory(ack, word, bad_parity)
    sink, records, core_edges, captures = rtl.record_sink, [], [], []
    produced = observe(rtl)["rx_produced"] if observe is not None else 0
    require(produced == 0, "A SWD transfer inherited a prior capture")

    def record(edge):
        nonlocal produced
        sink(edge)
        records.append(edge)
        if observe is not None:
            state = observe(rtl)
            core_edges.append({"edge": edge["cycle"], "raw": edge["observation"]["edge_inputs"], **state})
            current = state["rx_produced"]
            if current != produced:
                require(current == produced + 1, "SWD capture counter skipped a slot")
                captures.append(dict(edge=edge["cycle"], bit=bool(state["stage2"] & (1 << SENSE))))
                produced = current

    rtl.record_sink = record
    try:
        rtl.device = peer
        pending = loaded.submit()
        started = pending.last
        pending.wait(max_exchanges=MAX_EXCHANGES)
        counters = observe(rtl) if observe is not None else None
        rx = tuple(pending.rx_bits)
        wire = peer.check_trace(records, rx)
        if observe is not None:
            require(captures == [{"edge": a["rise"], "bit": a["data"]} for a in wire["apertures"]],
                    "SWD actual capture cuts differ from the sampled wire slots")
            parked = [record["observation"] for record, cut in zip(records, core_edges, strict=True)
                      if cut["pre_phase"] == cut["phase"] == 2 and cut["pre_stream_flags"] & 7 == 1]
            require(parked and all(not pins["levels"] & 1 and not pins["enabled"] & 2 for pins in parked),
                    "SWD RX service must exercise a low-clock park with SWDIO released")
        projected = execution(core_edges, loaded.image.words) if execution is not None else None
    finally:
        rtl.record_sink = sink
        rtl.device = None

    completed = pending.finish(max_exchanges=MAX_EXCHANGES)
    terminal, release = completed.terminal, completed.release
    require(release is not None and release.code is Code.ACCEPTED and release.tag == started.tag == terminal.tag
            and not terminal.fault and terminal.retained and not terminal.busy
            and terminal.tx_accepted == terminal.rx_valid == terminal.rx_queued == 0
            and terminal.rx_start == len(peer.reply) and completed.rx_bits == rx
            and completed.tx_consumed == completed.tx_cancelled == 0,
            "SWD wire outcome did not settle the exact receive-only owner")
    require(completed.result.outcome == name and completed.result.word == (word if name == "ok" else None),
            "SWD protocol decoder selected the wrong response outcome")
    return dict(name=name, ack=ack, source_word=word, bad_parity=bad_parity, owner_tag=pending.tag,
                result=asdict(completed.result), start=asdict(started), receipt=asdict(terminal),
                release=asdict(release), rx_bits=rx, counters=counters, execution=projected,
                capture_cuts=captures, wire=wire)


def replay(vvp, executable, trace_path, image, *, observe=None, execution=None):
    if execution is not None and observe is None:
        raise ValueError("Core execution projection requires a clocked observer")
    trace = EdgeTrace(trace_path)
    try:
        with QuadRTL(vvp, executable, record_limit=0, record_sink=trace) as rtl:
            transport = QuadTransport(rtl)
            host = ReadyHost(transport, depth=2)
            host.initialize()
            loaded = host.load(image)
            cases = [exchange(rtl, loaded, case, observe=observe, execution=execution) for case in CASES]
            counts = transport.opcode_counts
            require(counts[Opcode.COMMIT] == 1 and counts[Opcode.WARM_RESET] == 0
                    and counts[Opcode.START] == counts[Opcode.RELEASE] == len(cases)
                    and [case["owner_tag"] for case in cases] ==
                    [(loaded.generation << 16) | transfer for transfer in range(1, len(cases) + 1)],
                    "Branching SWD cases did not reuse one image with fresh owners")
    finally:
        recorded = trace.close()
    require(recorded["edges"] == rtl.cycle, "Branching SWD replay lost a public edge")
    return dict(cases=cases, words=list(image.words), trace=recorded)


def replay_negative(vvp, executable, trace_path, image, reason, *, observe=None):
    name, intended = {"inverted-ack": ("ok", "response-path"),
                      "short-turnaround": ("wait", "turnaround-host-drive")}[reason]
    case = next(case for case in CASES if case[0] == name)
    trace = EdgeTrace(trace_path)
    try:
        with QuadRTL(vvp, executable, record_limit=0, record_sink=trace) as rtl:
            host = ReadyHost(QuadTransport(rtl), depth=2)
            host.initialize()
            loaded = host.load(image)
            try:
                exchange(rtl, loaded, case, observe=observe, execution=None)
            except StreamTransportError as error:
                cause = error.cause
                require(isinstance(cause, SwdPeerError) and cause.reason == intended,
                        f"SWD {reason} failed outside the intended wire check: {cause}")
                if reason == "short-turnaround":
                    require(cause.slot == 12, "The incorrect WAIT turnaround failed outside its own slot")
                else:
                    require(cause.slot == 46, "The ACK mutation failed before the incorrect response path ended")
                rejected = dict(reason=cause.reason, slot=cause.slot, edge=cause.edge, message=str(cause))
            else:
                raise RuntimeError(f"SWD {reason} survived its independent wire oracle")
    finally:
        recorded = trace.close()
    require(recorded["edges"] == rtl.cycle, "SWD negative lost a public edge before rejection")
    return dict(rejected=rejected, words=list(image.words), trace=recorded)
