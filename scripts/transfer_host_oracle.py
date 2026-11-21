"""Independent integer/array oracle for the host-facing transfer accelerator.

No Lean model, generated hardware, controller oracle, or HDL helper is imported.
Read responses retain the pre-edge memory snapshot. Transfer jobs retain fixed
source/destination snapshots and check every committed destination prefix.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
import random

INPUT_ROLES = ("reset", "start_valid", "source_base", "destination_base", "length",
               "source_req_valid", "source_req_write", "source_req_address", "source_req_data", "source_resp_ready",
               "destination_req_valid", "destination_req_write", "destination_req_address", "destination_req_data",
               "destination_resp_ready")
OUTPUT_ROLES = ("start_ready", "busy", "done", "error", "source_req_ready", "source_resp_valid",
                "source_resp_data", "destination_req_ready", "destination_resp_valid", "destination_resp_data")
CONTROL_ROLES = ("phase", "source_base", "destination_base", "length", "index", "done", "error")


@dataclass(frozen=True)
class Control:
    phase: int = 0
    source_base: int = 0
    destination_base: int = 0
    length: int = 0
    index: int = 0
    done: int = 0
    error: int = 0


@dataclass(frozen=True)
class Memory:
    words: tuple[int, ...]
    q: int
    pending: int


@dataclass(frozen=True)
class State:
    control: Control
    source: Memory
    destination: Memory

    def registers(self):
        return [getattr(self.control, k) for k in CONTROL_ROLES] + list(self.source.words) + [
            self.source.q, self.source.pending] + list(self.destination.words) + [
            self.destination.q, self.destination.pending]


def restore(a, bank):
    depth = 1 << a
    if len(bank) != 7 + 2*(depth+2):
        raise ValueError("Wrong register count")
    source, destination = bank[7:7+depth+2], bank[7+depth+2:]
    return State(Control(*bank[:7]), Memory(tuple(source[:depth]), *source[depth:]),
                 Memory(tuple(destination[:depth]), *destination[depth:]))


def memory_step(memory, valid=0, write=0, address=0, data=0, ready=1):
    if memory.pending and not ready:
        return memory
    if not valid:
        return replace(memory, pending=0)
    if not write:
        return replace(memory, q=memory.words[address], pending=1)
    words = list(memory.words)
    words[address] = data
    return Memory(tuple(words), memory.q, 0)


def observe(state, row):
    c, s, d = state.control, state.source, state.destination
    if row["reset"] or c.phase == 3:
        return [0]*10
    idle = c.phase == 0
    return [int(idle and not s.pending and not d.pending), int(not idle), c.done, c.error,
            int(idle and not row["start_valid"] and (not s.pending or row["source_resp_ready"])),
            int(idle and s.pending), s.q if idle and s.pending else 0,
            int(idle and not row["start_valid"] and (not d.pending or row["destination_resp_ready"])),
            int(idle and d.pending), d.q if idle and d.pending else 0]


def step(a, wi, wo, state, row):
    c, s, d = state.control, state.source, state.destination
    if row["reset"] or c.phase == 3:
        return State(Control(error=int(not row["reset"])), replace(s, pending=0), replace(d, pending=0))
    cleared = replace(c, done=0, error=0)
    if c.phase == 0:
        if row["start_valid"] and not s.pending and not d.pending:
            base, target, length = (row[k] for k in ("source_base", "destination_base", "length"))
            control = Control(error=1) if base+length > 1 << a or target+length > 1 << a else \
                Control(phase=int(length > 0), source_base=base, destination_base=target,
                        length=length, done=int(length == 0))
            return State(control, s, d)

        def host(prefix, memory):
            return memory_step(memory, row[prefix+"_req_valid"] and not row["start_valid"],
                               row[prefix+"_req_write"], row[prefix+"_req_address"], row[prefix+"_req_data"],
                               row[prefix+"_resp_ready"])

        return State(cleared, host("source", s), host("destination", d))
    if c.phase == 1:
        return State(replace(cleared, phase=1 if s.pending else 2),
                     memory_step(s, valid=1, address=(c.source_base+c.index) % (1 << a), ready=0),
                     memory_step(d))
    # Every source response is consumed with its matching destination write.
    if s.pending:
        index = (c.index+1) % (1 << (a+1))
        completed = index >= c.length
        control = replace(cleared, phase=0 if completed else 1, index=index, done=int(completed))
        payload = ((1 << wi)-1-s.q) % (1 << wo)
        return State(control, memory_step(s),
                     memory_step(d, valid=1, write=1, address=(c.destination_base+c.index) % (1 << a), data=payload))
    return State(cleared, memory_step(s), memory_step(d))


def oracle(a, wi, wo, startup, rows):
    state, frames, events, jobs = restore(a, startup), [], [], []
    pending = {"source": [], "destination": []}
    counts = {k: {"accepted": 0, "emitted": 0, "canceled": 0} for k in pending}
    job = None
    for cycle, row in enumerate(rows):
        pre, old = observe(state, row), state
        event = {"cycle": cycle, "reset": bool(row["reset"]), "phase3": state.control.phase == 3,
                 "start": bool(pre[0] and row["start_valid"]), "reads": {}, "responses": {}, "writes": {}}
        cancellation = row["reset"] or state.control.phase == 3
        for name, ready_index, valid_index, data_index in (("source", 4, 5, 6), ("destination", 7, 8, 9)):
            memory = getattr(state, name)
            if cancellation:
                counts[name]["canceled"] += len(pending[name])
                pending[name].clear()
            accepted = bool(row[name+"_req_valid"] and pre[ready_index])
            retired = bool(row[name+"_resp_ready"] and pre[valid_index])
            if retired:
                if not pending[name] or pending[name].pop(0) != pre[data_index]:
                    raise AssertionError(f"{name} host response did not match accepted pre-edge read snapshot")
                counts[name]["emitted"] += 1
            if accepted and not row[name+"_req_write"]:
                value = memory.words[row[name+"_req_address"]]
                pending[name].append(value)
                counts[name]["accepted"] += 1
                event["reads"][name] = value
            if accepted and row[name+"_req_write"]:
                event["writes"][name] = [row[name+"_req_address"], row[name+"_req_data"]]
            if retired:
                event["responses"][name] = pre[data_index]
            if counts[name]["accepted"] != counts[name]["emitted"] + counts[name]["canceled"] + len(pending[name]):
                raise AssertionError("Host response occurrence ledger failed")
        if event["start"]:
            if job is not None:
                raise AssertionError("New start overwrote an unfinished job")
            length, source, destination = (row[k] for k in ("length", "source_base", "destination_base"))
            if source+length <= 1 << a and destination+length <= 1 << a:
                job = {"accepted": cycle, "source_base": source, "destination_base": destination,
                       "length": length, "committed": 0, "source_snapshot": list(state.source.words),
                       "destination_snapshot": list(state.destination.words)}
        if job is not None and not cancellation and state.control.phase == 2 and state.source.pending:
            job["committed"] += 1
        state = step(a, wi, wo, state, row)
        if cancellation:
            if state.source.words != old.source.words or state.source.q != old.source.q or \
                    state.destination.words != old.destination.words or state.destination.q != old.destination.q:
                raise AssertionError("Reset/recovery changed memory words or Q")
        if job is not None:
            expected = job["destination_snapshot"].copy()
            for offset in range(job["committed"]):
                expected[job["destination_base"]+offset] = ((1 << wi)-1-
                    job["source_snapshot"][job["source_base"]+offset]) % (1 << wo)
            if state.source.words != tuple(job["source_snapshot"]) or state.destination.words != tuple(expected):
                raise AssertionError("Job source snapshot or committed destination prefix changed")
            if cancellation or state.control.done:
                if not cancellation and (job["committed"] != job["length"] or
                                         cycle-job["accepted"] != 2*job["length"]):
                    raise AssertionError("Job completed without the exact full prefix or two-edges-per-word latency")
                jobs.append({**job, "finished": cycle, "aborted": bool(cancellation)})
                job = None
        for name in pending:
            memory = getattr(state, name)
            if state.control.phase == 0 and pending[name] != ([memory.q] if memory.pending else []):
                raise AssertionError("Pending host response differs from snapshot ledger")
        events.append(event)
        frames.append({"cycle": cycle, "input": row, "pre": pre,
                       "post": observe(state, row), "registers": state.registers()})
    return frames, events, {"host_reads": counts, "jobs": jobs, "unfinished_job": job}


def stimulus(a, wi, wo):
    rng = random.Random(0x484F5354 + 1000*a + 100*wi + wo)
    depth = 1 << a
    initial = State(Control(3, depth-1, depth-1, 2*depth-1, 2*depth-1, 1, 1),
                    Memory(tuple(rng.randrange(1 << wi) for _ in range(depth)), (1 << wi)-1, 1),
                    Memory(tuple(rng.randrange(1 << wo) for _ in range(depth)), (1 << wo)-1, 1))
    rows, state = [], initial
    coverage = {"commands": [], "abort_positions": [], "host_loaded_words": 0, "phase3_edges": 2}

    def add(**kwargs):
        nonlocal state
        row = dict.fromkeys(INPUT_ROLES, 0)
        row.update(kwargs)
        rows.append(row)
        state = step(a, wi, wo, state, row)

    def quiet(**kwargs):
        add(source_resp_ready=1, destination_resp_ready=1, **kwargs)

    # Synthesized state is unknown before this edge. Reset masks all outputs,
    # then host writes establish every word before any read/transfer.
    add(reset=1, start_valid=1, source_req_valid=1, source_req_write=1,
        source_req_data=(1 << wi)-1, destination_req_valid=1, destination_req_write=1,
        destination_req_data=(1 << wo)-1)
    for address in range(depth):
        quiet(source_req_valid=1, source_req_write=1, source_req_address=address,
              source_req_data=(address*43+5) % (1 << wi), destination_req_valid=1,
              destination_req_write=1, destination_req_address=address,
              destination_req_data=(address*19+3) % (1 << wo))
        coverage["host_loaded_words"] += 2
    quiet(source_req_valid=1, source_req_address=0, destination_req_valid=1, destination_req_address=depth-1)
    # Both pending responses precede start; new writes remain blocked. A drain
    # edge is deliberately distinct from the following start acceptance.
    for sr, dr in ((0, 0), (1, 0), (0, 0), (0, 1), (1, 1)):
        add(start_valid=1, length=depth, source_resp_ready=sr, destination_resp_ready=dr,
            source_req_valid=1, source_req_write=1, source_req_data=(1 << wi)-1,
            destination_req_valid=1, destination_req_write=1, destination_req_data=(1 << wo)-1)

    def finish():
        limit = 2*depth+3
        for _ in range(limit):
            if state.control.phase == 0:
                return
            add(start_valid=1, source_base=depth-1, destination_base=depth-1, length=2*depth-1,
                source_req_valid=1, source_req_write=1, source_req_data=(1 << wi)-1,
                destination_req_valid=1, destination_req_write=1, destination_req_data=(1 << wo)-1)
        raise AssertionError("Transfer did not complete")

    def readback():
        for address in range(depth):
            quiet(source_req_valid=1, source_req_address=address,
                  destination_req_valid=1, destination_req_address=address)
            add(source_req_valid=1, source_req_write=1, source_req_address=address,
                source_req_data=0, destination_req_valid=1, destination_req_write=1,
                destination_req_address=address, destination_req_data=0)
            quiet()

    finish()
    readback()
    quiet(source_req_valid=1, destination_req_valid=1)
    add(reset=1, source_req_valid=1, source_req_write=1, source_req_data=0,
        destination_req_valid=1, destination_req_write=1, destination_req_data=0)
    quiet(source_req_valid=1, destination_req_valid=1)
    quiet()
    for source, target, length in ((0, 0, depth), (depth-1, 0, 1), (0, depth-1, 1),
                                    (0, 1, depth-1), (depth-1, depth-1, 0),
                                    (depth-1, 0, 2), (0, depth-1, 2), (0, 0, depth+1)):
        quiet(start_valid=1, source_base=source, destination_base=target, length=length,
              source_req_valid=1, source_req_write=1, destination_req_valid=1, destination_req_write=1)
        coverage["commands"].append([source, target, length])
        finish()
        readback()
    # Held valid starts deliberately start the same job again upon returning idle.
    for _ in range(7):
        quiet(start_valid=1, length=1)
    finish()
    quiet()
    # Abort on either phase at every bounded committed prefix, then read back
    # the retained prefix before launching another independent job.
    for edge in range(2*depth):
        quiet(start_valid=1, length=depth)
        for _ in range(edge):
            quiet(source_req_valid=1, source_req_write=1, destination_req_valid=1, destination_req_write=1)
        add(reset=1, start_valid=1, length=depth, source_req_valid=1, source_req_write=1,
            source_req_data=(1 << wi)-1, destination_req_valid=1, destination_req_write=1,
            destination_req_data=(1 << wo)-1)
        coverage["abort_positions"].append(edge)
        readback()
    for cycle in range(220):
        add(reset=int(cycle % 53 == 17), start_valid=rng.randrange(2),
            source_base=rng.randrange(depth), destination_base=rng.randrange(depth), length=rng.randrange(2*depth),
            source_req_valid=rng.randrange(2), source_req_write=rng.randrange(2), source_req_address=rng.randrange(depth),
            source_req_data=rng.randrange(1 << wi), source_resp_ready=rng.randrange(2),
            destination_req_valid=rng.randrange(2), destination_req_write=rng.randrange(2),
            destination_req_address=rng.randrange(depth), destination_req_data=rng.randrange(1 << wo),
            destination_resp_ready=rng.randrange(2))
    add(reset=1)
    readback()
    quiet()
    return initial.registers(), rows, coverage
