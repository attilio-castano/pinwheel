"""Independent deque/rotating-list oracle for the single-flit packet switch.

Simulation mirrors the specified edge semantics, not Lean's selector algorithm.
The scoreboard tracks distinct acceptance occurrences even when payloads repeat.
All public traces use JSON-compatible dictionaries; observations are pre/post edge.
"""
from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Iterable


@dataclass(frozen=True)
class Packet:
    destination: int
    payload: int

    def json(self):
        return {"destination": self.destination, "payload": self.payload}


@dataclass(frozen=True)
class Delivery:
    source: int
    packet: Packet

    def json(self):
        return {"source": self.source, **self.packet.json()}


@dataclass(frozen=True)
class Stimulus:
    reset: bool
    offered: tuple[Packet | None, ...]
    ready: tuple[bool, ...]

    def json(self):
        return {"reset": self.reset, "offered": [p.json() if p else None for p in self.offered],
                "ready": list(self.ready)}


def dimensions(inputs, outputs, depth):
    if any(type(n) is not int or n <= 0 for n in (inputs, outputs, depth)):
        raise ValueError("Input count, output count and queue depth must be positive integers")


def packet(value, outputs):
    if value is None:
        return None
    if isinstance(value, Packet):
        p = value
    else:
        if not isinstance(value, dict) or set(value) != {"destination", "payload"}:
            raise ValueError("Packet requires exactly destination and payload")
        p = Packet(value["destination"], value["payload"])
    if type(p.destination) is not int or not 0 <= p.destination < outputs:
        raise ValueError("Destination outside the logical Fin output domain")
    if type(p.payload) is not int or p.payload < 0:
        raise ValueError("Payload must be a nonnegative integer")
    return p


def stimulus(value, inputs, outputs):
    if isinstance(value, Stimulus):
        value = value.json()
    if not isinstance(value, dict) or set(value) != {"reset", "offered", "ready"}:
        raise ValueError("Stimulus requires exactly reset, offered and ready")
    if type(value["reset"]) is not bool:
        raise ValueError("Reset must be Boolean")
    if len(value["offered"]) != inputs or len(value["ready"]) != outputs:
        raise ValueError("Stimulus port count mismatch")
    if any(type(r) is not bool for r in value["ready"]):
        raise ValueError("Readiness must be Boolean")
    return Stimulus(value["reset"], tuple(packet(p, outputs) for p in value["offered"]),
                    tuple(value["ready"]))


class SwitchOracle:
    def __init__(self, inputs, outputs, depth):
        dimensions(inputs, outputs, depth)
        self.inputs, self.outputs, self.depth = inputs, outputs, depth
        self.cycle = 0
        self.clear()

    def clear(self):
        self.queues = [deque() for _ in range(self.inputs)]
        self.slots = [None] * self.outputs
        self.order = [deque(range(self.inputs)) for _ in range(self.outputs)]

    def choose(self, output):
        return next((k for k in self.order[output]
                     if self.queues[k] and self.queues[k][0].destination == output), None)

    def grants(self, i):
        return [self.choose(o) if not i.reset and (self.slots[o] is None or i.ready[o]) else None
                for o in range(self.outputs)]

    def observe(self, i):
        selected = set(self.grants(i)) - {None}
        return {"ready": [not i.reset and len(q) - int(k in selected) < self.depth
                          for k, q in enumerate(self.queues)],
                "offered": [d.json() if d is not None and not i.reset else None for d in self.slots]}

    def state(self):
        return {"queues": [[p.json() for p in q] for q in self.queues],
                "slots": [d.json() if d else None for d in self.slots],
                "cursor": [order[0] for order in self.order]}

    def edge(self, value):
        i = stimulus(value, self.inputs, self.outputs)
        pre, grants = self.observe(i), self.grants(i)
        if i.reset:
            self.clear()
        else:
            # Select only old heads; enqueue occurs after all selected heads move.
            deliveries = [Delivery(k, self.queues[k][0]) if k is not None else None for k in grants]
            for k in grants:
                if k is not None:
                    self.queues[k].popleft()
            for k, p in enumerate(i.offered):
                if p is not None and pre["ready"][k]:
                    self.queues[k].append(p)
            for o, k in enumerate(grants):
                if self.slots[o] is None or i.ready[o]:
                    self.slots[o] = deliveries[o]
                if k is not None:
                    while self.order[o][0] != k:
                        self.order[o].rotate(-1)
                    self.order[o].rotate(-1)
        result = {"cycle": self.cycle, "pre": pre, "post": self.observe(i),
                  "grants": grants, "state": self.state()}
        self.cycle += 1
        return result


def simulate(stimuli: Iterable, inputs, outputs, depth):
    model = SwitchOracle(inputs, outputs, depth)
    return [model.edge(i) for i in stimuli]


@dataclass(frozen=True)
class Occurrence:
    source: int
    ordinal: int
    packet: Packet

    def delivery(self):
        return Delivery(self.source, self.packet).json()


def scoreboard(stimuli, frames, inputs, outputs, depth, *, require_drained=False, fairness=True):
    """Check occurrence conservation and FIFO/slot semantics independently of RR choice.

    Legal grant choices are accepted, except a continuously requested head cannot
    lose N successful refill opportunities when fairness=True. Exact cursor scan
    policy and all post-edge readiness are additionally checked by check_trace.
    """
    dimensions(inputs, outputs, depth)
    rows = [stimulus(i, inputs, outputs) for i in stimuli]
    frames = list(frames)
    if len(rows) != len(frames):
        raise AssertionError("Missing or extra frames")
    queues = [deque() for _ in range(inputs)]
    slots = [None] * outputs
    pending = defaultdict(deque)
    sequence, cursors = [0] * inputs, [0] * outputs
    waits = [[0] * inputs for _ in range(outputs)]
    accepted = emitted = discarded = max_wait = 0
    for cycle, (i, frame) in enumerate(zip(rows, frames, strict=True)):
        if frame.get("cycle") != cycle:
            raise AssertionError("Invalid cycle number")
        pre, post, grants, state = (frame[k] for k in ("pre", "post", "grants", "state"))
        if len(grants) != outputs or any(k is not None and (type(k) is not int or not 0 <= k < inputs)
                                         for k in grants):
            raise AssertionError("Malformed grant vector")
        selected = [k for k in grants if k is not None]
        if len(set(selected)) != len(selected):
            raise AssertionError("One input granted to multiple outputs")
        for observation in (pre, post):
            if len(observation["ready"]) != inputs or len(observation["offered"]) != outputs:
                raise AssertionError("Observation port count mismatch")
            if any(type(b) is not bool for b in observation["ready"]):
                raise AssertionError("Readiness must be Boolean")
        expected_offers = [d.delivery() if d is not None and not i.reset else None for d in slots]
        if pre["offered"] != expected_offers:
            raise AssertionError(f"Incorrect or unstable output offer at edge {cycle}")
        if i.reset:
            if selected or any(pre["ready"]):
                raise AssertionError("Transfer enabled during reset")
            discarded += sum(len(q) for q in pending.values())
            queues, slots, pending = [deque() for _ in range(inputs)], [None] * outputs, defaultdict(deque)
            cursors, waits = [0] * outputs, [[0] * inputs for _ in range(outputs)]
        else:
            for o, k in enumerate(grants):
                can_load = slots[o] is None or i.ready[o]
                requests = [bool(q) and q[0].packet.destination == o for q in queues]
                if k is not None and (not can_load or not requests[k]):
                    raise AssertionError(f"Grant is blocked, empty or misrouted at edge {cycle}")
                if can_load and any(requests) and k is None:
                    raise AssertionError("Eligible output failed to select a requester")
                for source, requested in enumerate(requests):
                    if not requested or k == source:
                        waits[o][source] = 0
                    elif can_load and k is not None:
                        waits[o][source] += 1
                    max_wait = max(max_wait, waits[o][source])
                    if fairness and waits[o][source] >= inputs:
                        raise AssertionError("Round-robin fairness bound exceeded in service opportunities")
                if slots[o] is not None and i.ready[o]:
                    occurrence = slots[o]
                    flow = pending[occurrence.source, o]
                    if not flow or flow[0] != occurrence:
                        raise AssertionError("Lost, duplicated or reordered flow occurrence")
                    flow.popleft()
                    slots[o] = None
                    emitted += 1
            expected_ready = [len(q) - int(k in selected) < depth for k, q in enumerate(queues)]
            if pre["ready"] != expected_ready:
                raise AssertionError("Input capacity/full-replacement readiness mismatch")
            for o, k in enumerate(grants):
                if k is not None:
                    slots[o] = queues[k].popleft()
                    cursors[o] = (k + 1) % inputs
            for k, p in enumerate(i.offered):
                if p is not None and pre["ready"][k]:
                    occurrence = Occurrence(k, sequence[k], p)
                    sequence[k] += 1
                    queues[k].append(occurrence)
                    pending[k, p.destination].append(occurrence)
                    accepted += 1
        expected_state = {"queues": [[d.packet.json() for d in q] for q in queues],
                          "slots": [d.delivery() if d is not None else None for d in slots],
                          "cursor": cursors}
        if state != expected_state:
            raise AssertionError(f"State/occurrence conservation mismatch at edge {cycle}")
        expected_post = [d.delivery() if d is not None and not i.reset else None for d in slots]
        if post["offered"] != expected_post or (i.reset and any(post["ready"])):
            raise AssertionError("Post-edge output or reset mismatch")
        if any(len(q) > depth for q in queues):
            raise AssertionError("Input queue overflow")
        stored = sum(len(q) for q in queues) + sum(d is not None for d in slots)
        if stored != sum(len(q) for q in pending.values()) or accepted != emitted + discarded + stored:
            raise AssertionError("Occurrence counts do not balance")
    outstanding = sum(len(q) for q in pending.values())
    if require_drained and outstanding:
        raise AssertionError("Pending occurrences remain after drain")
    return {"accepted": accepted, "emitted": emitted, "discarded_by_reset": discarded,
            "pending": outstanding, "max_competing_services_waited": max_wait}


def check_trace(stimuli, frames, inputs, outputs, depth, *, require_drained=False):
    rows, frames = list(stimuli), list(frames)
    result = scoreboard(rows, frames, inputs, outputs, depth, require_drained=require_drained)
    expected = simulate(rows, inputs, outputs, depth)
    for cycle, (actual, reference) in enumerate(zip(frames, expected, strict=True)):
        for field in ("pre", "post", "grants", "state"):
            if actual[field] != reference[field]:
                raise AssertionError(f"Exact round-robin oracle mismatch at edge {cycle}: {field}")
    return result
