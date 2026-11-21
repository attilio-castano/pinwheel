"""Independent integer/array oracle for the retained-metadata byte adapter.

No Lean, HDL, or other memory oracle is imported. A valid request samples a
pre-edge word; a store changes memory only when its response is accepted.
Arbitrary startup pending work is accounted separately from admitted requests.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
import random

INPUT_ROLES = ("reset", "request_valid", "write", "signed", "size", "address", "offset", "data", "response_ready")
OUTPUT_ROLES = ("request_ready", "response_valid", "response_code", "response_data")
METADATA_ROLES = ("write", "signed", "size", "address", "offset", "data", "pending")
FLAG_ROLES = ("reset", "request_valid", "write", "signed", "response_ready")
MASK = (1 << 32)-1


@dataclass(frozen=True)
class Metadata:
    write: int
    signed: int
    size: int
    address: int
    offset: int
    data: int
    pending: int


@dataclass(frozen=True)
class State:
    words: tuple[int, ...]
    q: int
    metadata: Metadata

    def registers(self):
        return list(self.words) + [self.q] + [getattr(self.metadata, k) for k in METADATA_ROLES]


def register_widths(a):
    if type(a) is not int or a < 0:
        raise ValueError("Address width must be a nonnegative integer")
    return [32]*((1 << a)+1) + [1, 1, 2, a, 2, 32, 1]


def restore(a, bank):
    widths = register_widths(a)
    if len(bank) != len(widths) or any(type(v) is not int or not 0 <= v < 1 << w for v, w in zip(bank, widths)):
        raise ValueError("Wrong startup register count or out-of-width register")
    depth = 1 << a
    return State(tuple(bank[:depth]), bank[depth], Metadata(*bank[depth+1:]))


def row(**kwargs):
    unknown = set(kwargs)-set(INPUT_ROLES)
    if unknown:
        raise ValueError("Unknown byte adapter input: " + str(sorted(unknown)))
    result = dict.fromkeys(INPUT_ROLES, 0)
    result.update(kwargs)
    for k in FLAG_ROLES:
        if result[k] not in (0, 1):
            raise ValueError("Nonbinary input flag")
        result[k] = bool(result[k])
    return result


def validate_row(a, item):
    if set(item) != set(INPUT_ROLES):
        raise ValueError("Incomplete or unknown input fields")
    for key in FLAG_ROLES:
        if type(item[key]) is not bool:
            raise ValueError("Flag must be a JSON Boolean: " + key)
    for key, width in (("size", 2), ("address", a), ("offset", 2), ("data", 32)):
        if type(item[key]) is not int or not 0 <= item[key] < 1 << width:
            raise ValueError("Input exceeds wire width: " + key)


def fault(size, offset):
    # Reserved size takes priority over alignment.
    return 2 if size == 3 else 3 if offset % (1 << size) else 0


def response(metadata, q):
    code = fault(metadata.size, metadata.offset)
    if code:
        return [code, 0]
    if metadata.write:
        return [1, 0]
    bits = 8*(1 << metadata.size)
    value = (q >> (8*metadata.offset)) & ((1 << bits)-1)
    if metadata.signed and value & (1 << (bits-1)):
        value -= 1 << bits
    return [0, value & MASK]


def patch(q, metadata):
    bits = 8*(1 << metadata.size)
    mask = ((1 << bits)-1) << (8*metadata.offset)
    return ((q & ~mask) | ((metadata.data << (8*metadata.offset)) & mask)) & MASK


def observe(state, item):
    if item["reset"]:
        return [0, 0, 0, 0]
    m = state.metadata
    return [int(not m.pending), m.pending] + (response(m, state.q) if m.pending else [0, 0])


def step(a, state, item):
    validate_row(a, item)
    m = state.metadata
    if item["reset"]:
        return replace(state, metadata=replace(m, pending=0))
    if m.pending:
        if not item["response_ready"]:
            return state
        words = list(state.words)
        if m.write and not fault(m.size, m.offset):
            words[m.address] = patch(state.q, m)
        return State(tuple(words), state.q, replace(m, pending=0))
    if not item["request_valid"]:
        return state
    captured = Metadata(*(int(item[k]) for k in METADATA_ROLES[:-1]), pending=1)
    q = state.words[captured.address] if not fault(captured.size, captured.offset) else state.q
    return State(state.words, q, captured)


def oracle(a, startup, rows):
    state, frames, events = restore(a, startup), [], []
    token = None
    initial_pending = int(bool(state.metadata.pending))
    if initial_pending:
        token = {"origin": "startup", "request": list(state.registers()[-7:-1]),
                 "response": response(state.metadata, state.q), "snapshot": state.q}
    counts = {"startup_pending": initial_pending, "accepted": 0, "completed": 0, "canceled": 0,
              "stores": 0, "reads": 0, "faults": 0}
    for cycle, item in enumerate(rows):
        validate_row(a, item)
        pre, old = observe(state, item), state
        accepted = bool(pre[0] and item["request_valid"])
        completed = bool(pre[1] and item["response_ready"])
        event = {"cycle": cycle, "reset": item["reset"], "accepted": None, "completed": None,
                 "canceled": None, "write": None}
        if item["reset"] and token is not None:
            counts["canceled"] += 1
            event["canceled"] = token
            token = None
        if completed:
            if token is None or token["response"] != pre[2:]:
                raise AssertionError("Response lost or changed its accepted snapshot")
            if token["request"] != state.registers()[-7:-1]:
                raise AssertionError("Pending request metadata changed")
            if token["origin"] == "accepted" and not fault(state.metadata.size, state.metadata.offset):
                if state.q != token["snapshot"] or state.q != state.words[state.metadata.address]:
                    raise AssertionError("Owned RAM snapshot changed before completion")
            event["completed"] = token
            counts["completed"] += 1
            if pre[2] == 1:
                event["write"] = [state.metadata.address, patch(state.q, state.metadata)]
                counts["stores"] += 1
            elif pre[2] == 0:
                counts["reads"] += 1
            else:
                counts["faults"] += 1
            token = None
        if accepted:
            if token is not None:
                raise AssertionError("Accepted request overwrote a pending response")
            metadata = Metadata(*(int(item[k]) for k in METADATA_ROLES[:-1]), pending=1)
            snapshot = state.words[metadata.address] if not fault(metadata.size, metadata.offset) else state.q
            token = {"origin": "accepted", "accepted_cycle": cycle,
                     "request": [getattr(metadata, k) for k in METADATA_ROLES[:-1]],
                     "response": response(metadata, snapshot), "snapshot": snapshot}
            event["accepted"] = token
            counts["accepted"] += 1
        state = step(a, state, item)
        if item["reset"] and state.registers()[:-1] != old.registers()[:-1]:
            raise AssertionError("Reset changed memory, Q, or retained metadata")
        expected_words = list(old.words)
        if event["write"] is not None:
            address, value = event["write"]
            expected_words[address] = value
        if state.words != tuple(expected_words):
            raise AssertionError("Memory effect without accepted store response")
        if not accepted and state.registers()[-7:-1] != old.registers()[-7:-1]:
            raise AssertionError("Inactive metadata was cleared or replaced")
        if bool(token) != bool(state.metadata.pending) or counts["startup_pending"]+counts["accepted"] != \
                counts["completed"]+counts["canceled"]+int(token is not None):
            raise AssertionError("Request occurrence ledger failed")
        events.append(event)
        frames.append({"cycle": cycle, "input": item, "pre": pre, "post": observe(state, item),
                       "registers": state.registers()})
    return frames, events, {**counts, "pending": token, "final_words": list(state.words)}


def stimulus(a):
    depth = 1 << a
    rng = random.Random(0x62797465+a)
    startup = [rng.getrandbits(w) for w in register_widths(a)]
    startup[-1] = 1
    rows = [row(reset=True, request_valid=True, write=True, signed=True, size=2,
                address=depth-1, data=MASK, response_ready=True)]

    def transaction(*, stalls=0, abort=False, **request):
        rows.append(row(request_valid=True, response_ready=True, **request))
        for k in range(stalls):
            rows.append(row(request_valid=True, write=not request.get("write", False), signed=True,
                            size=3, address=depth-1, offset=k%4, data=0xdeadbeef))
        rows.append(row(reset=abort, request_valid=True, write=True, signed=True, size=0,
                        address=depth-1, offset=3, data=0x11223344, response_ready=True))

    # A full-word store does not depend on the previous unknown word/Q. Only
    # after every word is explicitly established do loads/subword stores begin.
    for address in range(depth):
        transaction(write=True, signed=bool(address%2), size=2, address=address,
                    data=(0x80ff7f01 + address*0x10204081) & MASK)
    transaction(size=2, address=0)
    initialization_edges = len(rows)
    for size in range(4):
        for offset in range(4):
            for address in range(depth):
                for write, signed in ((False, False), (False, True), (True, False), (True, True)):
                    transaction(write=write, signed=signed, size=size, address=address, offset=offset,
                                data=(0xa580ff7f + address*37) & MASK, stalls=2)
    # Both legal stores and fault responses are canceled before acknowledgement.
    for size in range(4):
        transaction(write=True, signed=True, size=size, address=depth-1, offset=0,
                    data=0xfedcba98, stalls=2, abort=True)
        transaction(size=2, address=depth-1)
    transaction(write=False, signed=True, size=0, address=0, offset=3, stalls=2, abort=True)
    # A held offer is accepted again only on the later idle edge, never on the
    # completion edge. Each acceptance has an independent occurrence token.
    held = row(request_valid=True, write=True, signed=True, size=0, address=0,
               offset=1, data=0x87654321, response_ready=True)
    rows.extend([held.copy() for _ in range(6)])
    for cycle in range(260):
        rows.append(row(reset=cycle%71 == 0, request_valid=rng.randrange(5) != 0,
                        write=rng.getrandbits(1), signed=rng.getrandbits(1), size=rng.randrange(4),
                        address=rng.randrange(depth), offset=rng.randrange(4), data=rng.getrandbits(32),
                        response_ready=rng.randrange(4) != 0))
    rows.extend([row(response_ready=True), row(response_ready=True)])
    for address in range(depth):
        transaction(size=2, address=address)
    rows.append(row(response_ready=True))
    return startup, rows, {"host_loaded_words": depth, "initialization_edges": initialization_edges,
                          "raw_size_offset_pairs": 16, "signed_unsigned_store_variants": 4,
                          "response_stall_edges_per_exhaustive_request": 2,
                          "explicit_pending_cancellations": 5, "held_offer_edges": 6}
