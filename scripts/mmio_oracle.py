"""Independent integer MMIO oracle and checked, ordered effect replay.

The CPU port is atomic: every nonreset offer responds on that edge. Frontend
inputs denote already-decoded serial events; this does not model serial wires.
"""
from __future__ import annotations

import random

INPUT_ROLES = ("reset", "request_valid", "device", "write", "word", "data", "gpio_input",
               "tx_complete", "rx_valid", "rx_data", "framing_error")
INPUT_WIDTHS = (1, 1, 2, 1, 6, 32, 32, 1, 1, 8, 1)
OUTPUT_ROLES = ("request_ready", "response_valid", "response_code", "response_data", "gpio_output", "tx_active", "tx_data")
OUTPUT_WIDTHS = (1, 1, 3, 32, 32, 1, 8)
REGISTER_ROLES = ("gpio", "timer", "tx_active", "tx_data", "rx_valid", "rx_data", "overrun", "framing")
REGISTER_WIDTHS = (32, 32, 1, 8, 1, 8, 1, 1)
FLAG_ROLES = tuple(k for k, w in zip(INPUT_ROLES, INPUT_WIDTHS) if w == 1)
MASK = (1 << 32)-1


def restore(bank):
    if type(bank) is not list or len(bank) != len(REGISTER_WIDTHS) or any(
            type(v) is not int or not 0 <= v < 1 << w for v, w in zip(bank, REGISTER_WIDTHS, strict=True)):
        raise ValueError("Wrong startup register count or out-of-width register")
    return bank.copy()


def row(**kwargs):
    if set(kwargs)-set(INPUT_ROLES):
        raise ValueError("Unknown MMIO input")
    result = dict.fromkeys(INPUT_ROLES, 0)
    result.update(kwargs)
    for key in FLAG_ROLES:
        if result[key] not in (0, 1):
            raise ValueError("Nonbinary input flag")
        result[key] = bool(result[key])
    validate_row(result)
    return result


def validate_row(item):
    if type(item) is not dict or set(item) != set(INPUT_ROLES):
        raise ValueError("Incomplete or unknown input fields")
    for key, width in zip(INPUT_ROLES, INPUT_WIDTHS, strict=True):
        if key in FLAG_ROLES:
            if type(item[key]) is not bool:
                raise ValueError("Flag must be a JSON Boolean: " + key)
        elif type(item[key]) is not int or not 0 <= item[key] < 1 << width:
            raise ValueError("Input exceeds wire width: " + key)


def access(state, item):
    """Response pair plus CPU-only update, before timer or frontend progression."""
    nxt = state.copy()
    device, word, write, data = (item[k] for k in ("device", "word", "write", "data"))
    if device == 0:
        if word == 0:
            return ([3, 0] if write else [0, item["gpio_input"]]), nxt
        if word == 1:
            if write:
                nxt[0] = data
            return ([1, 0] if write else [0, state[0]]), nxt
    elif device == 1:
        if word == 0:
            return ([3, 0] if write else [0, state[1]]), nxt
    elif device == 2:
        if word == 0:
            return ([3, 0] if write else [0, (1-state[2])+2*state[4]+4*state[6]+8*state[7]]), nxt
        if word == 1:
            if not write:
                return [3, 0], nxt
            if state[2]:
                return [4, 0], nxt
            nxt[2:4] = [1, data & 255]
            return [1, 0], nxt
        if word == 2:
            if write:
                return [3, 0], nxt
            if not state[4]:
                return [5, 0], nxt
            nxt[4] = 0
            return [0, state[5]], nxt
        if word == 3:
            if not write:
                return [3, 0], nxt
            nxt[6] &= 1-((data >> 2) & 1)
            nxt[7] &= 1-((data >> 3) & 1)
            return [1, 0], nxt
    return [2, 0], nxt


def observe(state, item):
    if item["reset"]:
        return [0]*7
    result = access(state, item)[0] if item["request_valid"] else [0, 0]
    return [1, int(item["request_valid"]), *result, state[0], state[2], state[3] if state[2] else 0]


def step(state, item):
    validate_row(item)
    if item["reset"]:
        return [0]*8
    nxt = access(state, item)[1] if item["request_valid"] else state.copy()
    nxt[1] = (state[1]+1) & MASK
    if state[2] and item["tx_complete"]:
        nxt[2] = 0
    if item["rx_valid"]:
        if nxt[4]:
            nxt[6] = 1
        else:
            nxt[4:6] = [1, item["rx_data"]]
    if item["framing_error"]:
        nxt[7] = 1
    return nxt


def events_for(state, item, observed):
    """Fixed extraction includes actual pre-edge response code/data, even faults."""
    if item["reset"]:
        return [{"kind": "reset"}]
    events = []
    consumed = False
    if item["request_valid"]:
        events.append({"kind": "cpu", "device": item["device"], "word": item["word"],
                       "write": item["write"], "data": item["data"], "gpio_input": item["gpio_input"],
                       "response": observed[2:4]})
        consumed = item["device"] == 2 and item["word"] == 2 and not item["write"] and observed[2] == 0
    events.append({"kind": "tick", "before": state[1], "after": (state[1]+1) & MASK})
    if state[2] and item["tx_complete"]:
        events.append({"kind": "tx_complete", "byte": state[3]})
    if item["rx_valid"]:
        events.append({"kind": "rx_arrival", "byte": item["rx_data"], "accepted": not state[4] or consumed})
    if item["framing_error"]:
        events.append({"kind": "framing_error"})
    return events


def replay_events(state, events):
    """Check responses and reconstruct effects without calling step/access."""
    nxt = state.copy()
    for e in events:
        kind = e["kind"]
        if kind == "reset":
            nxt = [0]*8
        elif kind == "cpu":
            d, w, write, data, response = (e[k] for k in ("device", "word", "write", "data", "response"))
            # Register permissions precede the effect; holes never alias.
            valid = {0: {0: "r", 1: "rw"}, 1: {0: "r"}, 2: {0: "r", 1: "w", 2: "r", 3: "w"}}
            permission = valid.get(d, {}).get(w)
            if permission is None:
                want = [2, 0]
            elif ("w" if write else "r") not in permission:
                want = [3, 0]
            elif d == 2 and w == 1 and nxt[2]:
                want = [4, 0]
            elif d == 2 and w == 2 and not nxt[4]:
                want = [5, 0]
            elif write:
                want = [1, 0]
            else:
                values = {(0, 0): e["gpio_input"], (0, 1): nxt[0], (1, 0): nxt[1],
                          (2, 0): sum(bit << k for k, bit in enumerate((1-nxt[2], nxt[4], nxt[6], nxt[7]))),
                          (2, 2): nxt[5]}
                want = [0, values[d, w]]
            if response != want:
                raise AssertionError("Actual response does not match the pre-edge atomic access")
            if response[0] == 1:
                if (d, w) == (0, 1):
                    nxt[0] = data
                elif (d, w) == (2, 1):
                    nxt[2], nxt[3] = 1, data % 256
                elif (d, w) == (2, 3):
                    for k in (2, 3):
                        if data // (1 << k) % 2:
                            nxt[k+4] = 0
            elif response[0] == 0 and (d, w) == (2, 2):
                nxt[4] = 0
        elif kind == "tick":
            if e["before"] != nxt[1] or e["after"] != (nxt[1]+1) % (1 << 32):
                raise AssertionError("Incorrect timer event")
            nxt[1] = e["after"]
        elif kind == "tx_complete":
            if not nxt[2] or e["byte"] != nxt[3]:
                raise AssertionError("Completion without the pre-existing TX byte")
            nxt[2] = 0
        elif kind == "rx_arrival":
            if e["accepted"] != (nxt[4] == 0):
                raise AssertionError("Incorrect RX room/consume ordering")
            if e["accepted"]:
                nxt[4], nxt[5] = 1, e["byte"]
            else:
                nxt[6] = 1
        elif kind == "framing_error":
            nxt[7] = 1
        else:
            raise ValueError("Unknown event")
    return nxt


def oracle(startup, rows):
    state, frames, events = restore(startup), [], []
    counts = dict.fromkeys(("offers", "responses", "reads", "stores", "faults", "invalid_selectors",
                            "resets", "ticks", "tx_completions", "rx_accepted", "rx_dropped", "framing_errors"), 0)
    for cycle, item in enumerate(rows):
        validate_row(item)
        pre = observe(state, item)
        es = events_for(state, item, pre)
        after = step(state, item)
        if replay_events(state, es) != after:
            raise AssertionError("Actual step differs from the ordered CPU/autonomous event replay")
        if pre[:2] != ([0, 0] if item["reset"] else [1, int(item["request_valid"])]):
            raise AssertionError("Atomic response admission mismatch")
        counts["offers"] += int(item["request_valid"] and not item["reset"])
        counts["responses"] += pre[1]
        for e in es:
            kind = e["kind"]
            if kind == "cpu":
                counts["reads" if e["response"][0] == 0 else "stores" if e["response"][0] == 1 else "faults"] += 1
                counts["invalid_selectors"] += int(e["device"] == 3)
            else:
                counts[{"reset": "resets", "tick": "ticks", "tx_complete": "tx_completions",
                        "framing_error": "framing_errors", "rx_arrival":
                        "rx_accepted" if e.get("accepted") else "rx_dropped"}[kind]] += 1
        if counts["offers"] != counts["responses"]:
            raise AssertionError("An offered operation lost or duplicated its response")
        events.append({"cycle": cycle, "events": es})
        frames.append({"cycle": cycle, "input": item, "pre": pre, "post": observe(after, item), "registers": after})
        state = after
    return frames, events, {**counts, "final_registers": state,
                           "progress_boundary": "responses count CPU accesses; ticks are autonomous and do not imply CPU retirement"}


def stimulus():
    startup = [0x91abcdef, MASK, 1, 0xa5, 1, 0x81, 1, 1]
    rows = [row(reset=True, request_valid=True, device=2, write=True, word=1, data=MASK,
                tx_complete=True, rx_valid=True, rx_data=0x55, framing_error=True)]
    # Directed races are deliberately reachable without forcing synthesized state.
    rows += [row(request_valid=True, device=2, write=True, word=1, data=0x123456a5, tx_complete=True),
             row(request_valid=True, device=2, write=True, word=1, data=0x66, tx_complete=True),
             row(request_valid=True, device=2, word=2, rx_valid=True, rx_data=0x80),
             row(request_valid=True, device=2, word=2, rx_valid=True, rx_data=0x18),
             row(request_valid=True, device=2, write=True, word=3, data=12, rx_valid=True, rx_data=0xff, framing_error=True),
             row(request_valid=True, device=2, word=0),
             row(request_valid=True, device=3, write=True, word=1, data=0xabcdef, tx_complete=True, rx_valid=True, rx_data=7),
             row(request_valid=True, device=0, write=True, word=1, data=0xdeadbeef),
             row(reset=True, request_valid=True, device=0, write=True, word=1, data=0xffffffff,
                 tx_complete=True, rx_valid=True, rx_data=0xfe, framing_error=True)]
    for device in range(4):
        for word in range(64):
            for write in (False, True):
                rows.append(row(request_valid=True, device=device, word=word, write=write,
                    data=(0xfedcba98+word*13) & MASK, gpio_input=(0x12345678+word*7) & MASK,
                    tx_complete=word%2, rx_valid=word//2%2, rx_data=(word*11)%256, framing_error=word//4%2))
    for device, word in ((0, 1), (1, 0), (2, 1), (2, 2), (2, 3), (3, 0)):
        for controls in range(32):
            rows.append(row(reset=controls%2, request_valid=controls//2%2, device=device, word=word,
                write=controls//4%2, data=12, gpio_input=0x89abcdef, tx_complete=controls//8%2,
                rx_valid=controls//16%2, rx_data=0xa5, framing_error=controls//4%2))
    rng = random.Random(0x6d6d696f)
    for cycle in range(400):
        rows.append(row(reset=cycle%59 == 0, request_valid=rng.randrange(5) != 0, device=rng.randrange(4),
            write=rng.getrandbits(1), word=rng.randrange(8), data=rng.getrandbits(32), gpio_input=rng.getrandbits(32),
            tx_complete=rng.getrandbits(1), rx_valid=rng.getrandbits(1), rx_data=rng.randrange(256), framing_error=rng.randrange(5) == 0))
    rows += [row(reset=True), row(), row(request_valid=True, device=2, word=0)]
    return startup, rows, {"all_device_word_direction_codes": 512, "directed_races": 9,
                          "control_matrix_edges": 192, "random_edges": 400,
                          "synthesized_startup": "first synchronous reset; no forced registers"}


def raw_cases():
    cases = []
    for flags in range(16):
        startup = [0x91827364+flags, MASK, flags%2, 0xa5+flags, flags//2%2, 0x80+flags, flags//4%2, flags//8%2]
        rows = [row(request_valid=True, device=1, word=0),
                row(request_valid=True, device=2, word=0),
                row(request_valid=True, device=2, word=2, rx_valid=True, rx_data=0x20+flags),
                row(request_valid=True, device=2, write=True, word=1, data=0xff00+flags, tx_complete=True),
                row(request_valid=True, device=3, word=0, tx_complete=True, rx_valid=True, rx_data=0x30+flags),
                row(request_valid=True, device=2, write=True, word=3, data=12, rx_valid=True, rx_data=0x40+flags, framing_error=True),
                row(), row(reset=True, request_valid=True, device=0, word=1, write=True, data=MASK,
                           tx_complete=True, rx_valid=True, rx_data=255, framing_error=True), row()]
        cases.append({"name": f"raw-flags-{flags}", "startup": startup, "rows": rows})
    return cases
