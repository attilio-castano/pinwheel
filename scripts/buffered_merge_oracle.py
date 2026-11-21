"""Independent integer round-robin and occurrence-ledger buffered-merge oracle.

Only accepted inputs enter the single holding slot. Logical source tags are
checked separately from payload-only physical observations; repeated payloads
do not collapse distinct acceptance occurrences.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass


def dimensions(inputs, width):
    if any(type(x) is not int or x <= 0 for x in (inputs, width)):
        raise ValueError("Input count and width must be positive integers")


def stimulus(row, inputs, width):
    dimensions(inputs, width)
    if type(row) is not dict or set(row) != {"reset", "valid", "payload", "ready"}:
        raise ValueError("Stimulus requires exactly reset, valid, payload and ready")
    if type(row["reset"]) is not bool or type(row["ready"]) is not bool:
        raise ValueError("Reset and downstream readiness must be Boolean")
    for key in ("valid", "payload"):
        if type(row[key]) is not list or len(row[key]) != inputs:
            raise ValueError("Wrong stimulus port count")
    if any(type(x) is not bool for x in row["valid"]):
        raise ValueError("Input validity must be Boolean")
    if any(type(x) is not int or not 0 <= x < 1 << width for x in row["payload"]):
        raise ValueError("Payload exceeds physical wire width")
    return row


def same_json(actual, expected):
    """Reject Python's otherwise-equal bool/int and float/int substitutions."""
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return actual.keys() == expected.keys() and all(same_json(actual[k], v) for k, v in expected.items())
    if type(expected) is list:
        return len(actual) == len(expected) and all(same_json(a, b) for a, b in zip(actual, expected, strict=True))
    return actual == expected


class MergeOracle:
    def __init__(self, inputs, width):
        dimensions(inputs, width)
        self.inputs, self.width, self.cycle = inputs, width, 0
        self.cursor, self.slot = 0, None

    def choose(self, row):
        if row["reset"] or (self.slot is not None and not row["ready"]):
            return None
        for offset in range(self.inputs):
            candidate = (self.cursor + offset) % self.inputs
            if row["valid"][candidate]:
                return candidate
        return None

    def observe(self, row):
        winner = self.choose(row)
        return {"ready": [winner == k for k in range(self.inputs)],
                "offered": self.slot.copy() if self.slot is not None and not row["reset"] else None}

    def edge(self, raw):
        row = stimulus(raw, self.inputs, self.width)
        pre, winner = self.observe(row), self.choose(row)
        if row["reset"]:
            self.cursor, self.slot = 0, None
        else:
            if self.slot is None or row["ready"]:
                self.slot = {"source": winner, "payload": row["payload"][winner]} if winner is not None else None
            if winner is not None:
                self.cursor = (winner + 1) % self.inputs
        result = {"cycle": self.cycle, "pre": pre, "post": self.observe(row), "grant": winner,
                  "state": {"cursor": self.cursor, "slot": self.slot.copy() if self.slot is not None else None}}
        self.cycle += 1
        return result


def simulate(rows, inputs, width):
    model = MergeOracle(inputs, width)
    return [model.edge(row) for row in rows]


@dataclass(frozen=True)
class Occurrence:
    source: int
    ordinal: int
    payload: int

    def delivery(self):
        return {"source": self.source, "payload": self.payload}


def scoreboard(rows, frames, inputs, width, *, require_drained=False):
    """Occurrence conservation and opportunity fairness, without choosing a winner.

The exact integer modulo choice is checked separately by check_trace.
"""
    dimensions(inputs, width)
    rows, frames = list(rows), list(frames)
    if len(rows) != len(frames):
        raise AssertionError("Missing or extra logical frames")
    pending = [deque() for _ in range(inputs)]
    sequence, waited = [0] * inputs, [0] * inputs
    slot, cursor = None, 0
    accepted = emitted = discarded = max_wait = 0
    for cycle, (raw, frame) in enumerate(zip(rows, frames, strict=True)):
        row = stimulus(raw, inputs, width)
        if type(frame) is not dict or set(frame) != {"cycle", "pre", "post", "grant", "state"}:
            raise AssertionError("Malformed logical frame")
        if type(frame["cycle"]) is not int or frame["cycle"] != cycle:
            raise AssertionError("Invalid cycle number")
        pre, post, winner, state = (frame[k] for k in ("pre", "post", "grant", "state"))
        if winner is not None and (type(winner) is not int or not 0 <= winner < inputs):
            raise AssertionError("Malformed grant")
        for observation in (pre, post):
            if type(observation) is not dict or set(observation) != {"ready", "offered"} or \
                    type(observation["ready"]) is not list or len(observation["ready"]) != inputs or \
                    any(type(x) is not bool for x in observation["ready"]):
                raise AssertionError("Malformed logical observation")
        expected_offer = slot.delivery() if slot is not None and not row["reset"] else None
        if not same_json(pre["offered"], expected_offer):
            raise AssertionError(f"Lost/unstable/wrong-origin held offer at cycle {cycle}")
        if pre["ready"] != [winner == k for k in range(inputs)]:
            raise AssertionError("Readiness does not identify exactly the accepted source")
        if row["reset"]:
            if winner is not None or any(pre["ready"]):
                raise AssertionError("Transfer enabled during reset")
            discarded += int(slot is not None)
            pending, slot, cursor, waited = [deque() for _ in range(inputs)], None, 0, [0] * inputs
        else:
            can_load = slot is None or row["ready"]
            if winner is not None and (not can_load or not row["valid"][winner]):
                raise AssertionError("Accepted blocked or invalid offer")
            if can_load and any(row["valid"]) and winner is None:
                raise AssertionError("Eligible requests were not serviced")
            for k, requested in enumerate(row["valid"]):
                if not requested or winner == k:
                    waited[k] = 0
                elif can_load:
                    waited[k] += 1
                max_wait = max(max_wait, waited[k])
                if waited[k] >= inputs:
                    raise AssertionError("Persistent request exceeded N eligible refill opportunities")
            if slot is not None and row["ready"]:
                if not pending[slot.source] or pending[slot.source].popleft() != slot:
                    raise AssertionError("Lost, duplicated or reordered occurrence")
                slot = None
                emitted += 1
            if winner is not None:
                occurrence = Occurrence(winner, sequence[winner], row["payload"][winner])
                sequence[winner] += 1
                pending[winner].append(occurrence)
                slot, cursor = occurrence, (winner + 1) % inputs
                accepted += 1
        expected_state = {"slot": slot.delivery() if slot else None, "cursor": cursor}
        if not same_json(state, expected_state):
            raise AssertionError(f"State/occurrence ledger mismatch at cycle {cycle}")
        if not same_json(post["offered"], slot.delivery() if slot is not None and not row["reset"] else None):
            raise AssertionError("Post-edge offer mismatch")
        if row["reset"] and any(post["ready"]):
            raise AssertionError("Post-edge ready asserted during reset")
        stored = sum(map(len, pending))
        if stored != int(slot is not None) or accepted != emitted + discarded + stored:
            raise AssertionError("Acceptance occurrences do not balance")
    if require_drained and slot is not None:
        raise AssertionError("Pending occurrence remains after drain")
    return {"accepted": accepted, "emitted": emitted, "discarded_by_reset": discarded,
            "pending": int(slot is not None), "max_competing_services_waited": max_wait}


def check_trace(rows, frames, inputs, width, *, require_drained=False):
    rows, frames = list(rows), list(frames)
    result = scoreboard(rows, frames, inputs, width, require_drained=require_drained)
    reference = simulate(rows, inputs, width)
    for cycle, (actual, expected) in enumerate(zip(frames, reference, strict=True)):
        if not same_json(actual, expected):
            raise AssertionError(f"Exact modulo-scan oracle mismatch at cycle {cycle}")
    return result
