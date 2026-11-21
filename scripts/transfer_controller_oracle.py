"""Integer reference and adversarial traffic for the open transfer controller.

This module does not import the Lean model, generated circuit, or HDL helpers.
Addresses and command lengths are checked as integers before fixed-width storage.
The environment may supply arbitrary response bits: open-controller refinement
does not assume that an external memory implements its protocol correctly.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
import random


INPUT_ROLES = ("reset", "start_valid", "source_base", "destination_base", "length",
               "source_ready", "response_valid", "response_data", "destination_ready")
OUTPUT_ROLES = ("start_ready", "busy", "done", "error", "source_valid", "source_address",
                "response_ready", "destination_valid", "destination_address", "destination_data", "memory_reset")
REGISTER_ROLES = ("phase", "source_base", "destination_base", "length", "index", "done", "error")


@dataclass(frozen=True)
class Control:
    phase: int = 0
    source_base: int = 0
    destination_base: int = 0
    length: int = 0
    index: int = 0
    done: int = 0
    error: int = 0

    def words(self):
        return [getattr(self, key) for key in REGISTER_ROLES]


def transform(value, wi, wo):
    return ((1 << wi) - 1 - value) & ((1 << wo) - 1)


def observe(a, wi, wo, state, row):
    if row["reset"] or state.phase == 3:
        return [0] * 10 + [1]
    read = state.phase == 1
    write = state.phase == 2 and row["response_valid"]
    return [int(state.phase == 0), int(state.phase != 0), state.done, state.error,
            int(read), (state.source_base + state.index) % (1 << a) if read else 0,
            int(state.phase == 2 and row["destination_ready"]), int(write),
            (state.destination_base + state.index) % (1 << a) if write else 0,
            transform(row["response_data"], wi, wo) if write else 0, 0]


def step(a, state, row):
    if row["reset"]:
        return Control()
    if state.phase == 3:
        return Control(error=1)
    cleared = replace(state, done=0, error=0)
    if state.phase == 0 and row["start_valid"]:
        length, source, destination = (row[k] for k in ("length", "source_base", "destination_base"))
        if source + length > 1 << a or destination + length > 1 << a:
            return Control(error=1)
        return Control(phase=int(length > 0), source_base=source, destination_base=destination,
                       length=length, done=int(length == 0))
    if state.phase == 1 and row["source_ready"]:
        return replace(cleared, phase=2)
    if state.phase == 2 and row["response_valid"] and row["destination_ready"]:
        index = (state.index + 1) % (1 << (a + 1))
        complete = index >= state.length
        return replace(cleared, phase=0 if complete else 1, index=index, done=int(complete))
    return cleared


def oracle(a, wi, wo, startup, rows):
    state, frames, events = Control(*startup), [], []
    for cycle, row in enumerate(rows):
        pre = observe(a, wi, wo, state, row)
        events.append({"cycle": cycle,
                       "start_accepted": bool(pre[0] and row["start_valid"]),
                       "read_accepted": bool(pre[4] and row["source_ready"]),
                       "write_accepted": bool(pre[7] and row["destination_ready"]),
                       "response_retired": bool(pre[6] and row["response_valid"]),
                       "memory_reset": bool(pre[10])})
        if events[-1]["write_accepted"] != events[-1]["response_retired"]:
            raise AssertionError("The controller consumed a response without the matching write")
        state = step(a, state, row)
        frames.append({"cycle": cycle, "input": row, "pre": pre,
                       "post": observe(a, wi, wo, state, row), "registers": state.words()})
    return frames, events


def stimulus(a, wi, wo):
    rng = random.Random(0x5452414E + 1000*a + 100*wi + wo)
    depth, data_limit = 1 << a, 1 << wi
    startup = [3, depth-1, depth-1, 2*depth-1, 2*depth-1, 1, 1]
    rows, state = [], Control(*startup)
    coverage = {"valid_commands": 0, "zero_commands": 0, "invalid_commands": 0,
                "directed_words": 0, "abort_positions": 0}

    def add(**kwargs):
        nonlocal state
        row = dict.fromkeys(INPUT_ROLES, 0)
        row.update(kwargs)
        rows.append(row)
        state = step(a, state, row)

    def quiet():
        # Adversarial inactive fields and unsolicited responses must be ignored.
        add(source_base=depth-1, destination_base=depth-1, length=2*depth-1,
            source_ready=1, response_valid=1, response_data=data_limit-1, destination_ready=1)

    add(reset=1, start_valid=1, source_base=depth-1, destination_base=depth-1,
        length=2*depth-1, source_ready=1, response_valid=1, response_data=data_limit-1, destination_ready=1)
    quiet()
    # Full depth, nonzero bases, last address, zero, and each independent range failure.
    commands = [(0, 0, depth), (0, 1, depth-1), (depth-1, 0, 1), (0, depth-1, 1),
                (depth-1, depth-1, 0), (0, 0, 0), (depth-1, 0, 2), (0, depth-1, 2),
                (0, 0, 2*depth-1)]
    for source, destination, length in commands:
        add(start_valid=1, source_base=source, destination_base=destination, length=length,
            source_ready=1, response_valid=1, response_data=data_limit-1, destination_ready=1)
        valid = source + length <= depth and destination + length <= depth
        coverage["valid_commands" if valid else "invalid_commands"] += 1
        coverage["zero_commands"] += int(valid and length == 0)
        if valid:
            for index in range(length):
                busy_offer = dict(start_valid=1, source_base=depth-1, destination_base=depth-1,
                                  length=2*depth-1)
                add(**busy_offer, response_valid=1, response_data=rng.randrange(data_limit), destination_ready=1)
                add(**busy_offer, source_ready=1, response_valid=1, response_data=rng.randrange(data_limit))
                add(**busy_offer, source_ready=1, destination_ready=1)
                value = (index * 17 + source * 3 + 1) % data_limit
                for _ in range(2):
                    add(**busy_offer, source_ready=1, response_valid=1, response_data=value)
                add(**busy_offer, source_ready=1, response_valid=1, response_data=value, destination_ready=1)
                coverage["directed_words"] += 1
            if state.phase != 0 or not state.done or state.index != length:
                raise AssertionError("Directed command did not complete at its final write")
        elif state != Control(error=1):
            raise AssertionError("Invalid command did not recover empty control with an error pulse")
        quiet()
        if state.done or state.error:
            raise AssertionError("Status pulse did not clear on the next edge")

    # Abort every phase/word boundary of a full-depth transfer, then tempt stale work.
    for cut in range(2*depth + 1):
        add(start_valid=1, length=depth)
        for k in range(cut):
            add(source_ready=1, response_valid=1, response_data=(k+7) % data_limit, destination_ready=1)
        add(reset=1, start_valid=1, length=depth, source_ready=1, response_valid=1,
            response_data=data_limit-1, destination_ready=1)
        quiet()
        quiet()
        coverage["abort_positions"] += 1

    # A held command is accepted on each return to idle; busy command fields cannot replace it.
    for _ in range(10):
        add(start_valid=1, source_base=depth-1, destination_base=depth-1, length=1,
            source_ready=1, response_valid=1, response_data=data_limit-1, destination_ready=1)
    add(reset=1)
    for cycle in range(300):
        add(reset=int(cycle % 47 == 11), start_valid=rng.randrange(2),
            source_base=rng.randrange(depth), destination_base=rng.randrange(depth), length=rng.randrange(2*depth),
            source_ready=rng.randrange(2), response_valid=rng.randrange(2),
            response_data=rng.randrange(data_limit), destination_ready=rng.randrange(2))
    add(reset=1)
    quiet()
    return startup, rows, coverage
