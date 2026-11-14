"""Count connected public and cell pin observations in retained VCD windows."""

import argparse
from collections import defaultdict
from pathlib import Path

from streaming_8x4_e982_g4_transport import bind, emit, read_bound, require
from streaming_8x4_hold_cap_activity import CYCLE_PS, PORT_WIDTHS, SCHEMA as BASE_SCHEMA, SCOPE, selected_inputs
from streaming_8x4_hold_cap_physical import TARGET, TRIAL
from streaming_8x4_hold_cap_workloads import SCHEMA


def windows(receipt):
    count = receipt["workload_cycles"]
    result = {"full": (0, count * CYCLE_PS)}
    if receipt["workload"] == "reset-upload":
        edges = receipt["protocol_checks"]["phases_at_edge"]
        require(0 < edges["after_cold_reset"] < edges["after_warm_reset"] < edges["after_first_commit"]
                < edges["after_first_idle"] < edges["after_replacement_commit"]
                < edges["after_replacement_idle"] == count, "Reset and upload checkpoints differ")
        intervals = {
            "cold_and_warm_reset": (0, edges["after_warm_reset"]),
            "first_upload": (edges["after_warm_reset"], edges["after_first_commit"]),
            "first_idle": (edges["after_first_commit"], edges["after_first_idle"]),
            "replacement_upload": (edges["after_first_idle"], edges["after_replacement_commit"]),
            "replacement_idle": (edges["after_replacement_commit"], edges["after_replacement_idle"]),
        }
        require(sum(end - start for start, end in intervals.values()) == count, "Phase partition differs")
        result.update({name: (start * CYCLE_PS, end * CYCLE_PS) for name, (start, end) in intervals.items()})
    return result


def declarations(stream, inventory):
    by_id = defaultdict(lambda: defaultdict(int))
    scopes, public = [], set()
    expected = {}
    for name, instance in inventory["instances"].items():
        if name in inventory["physical_only_instances"]:
            continue
        for pin, term in instance["terminals"].items():
            signal = term["signal_type"]
            if signal not in ("SIGNAL", "CLOCK") or term["net"] is None:
                continue
            if signal == "CLOCK":
                group = "cell_clock_pin"
            elif term["direction"] == "OUTPUT":
                group = "cell_output_pin"
            else:
                require(term["direction"] == "INPUT", "Unexpected signal pin direction")
                group = "cell_input_pin"
            expected[(name, pin)] = group
    require(expected, "No connected cell pin census")
    seen = set()
    for raw in stream:
        words = raw.split()
        if not words:
            continue
        if words[0] == b"$scope":
            scopes.append(words[2].decode("ascii").removeprefix("\\"))
        elif words[0] == b"$upscope":
            scopes.pop()
        elif words[0] == b"$enddefinitions":
            break
        elif words[0] == b"$var" and tuple(scopes[:2]) == SCOPE:
            width, code, name = int(words[2]), words[3], words[4].decode("ascii").removeprefix("\\")
            if len(scopes) == 2 and name in PORT_WIDTHS:
                require(width == PORT_WIDTHS[name] and name not in public, "Wrong public waveform bus")
                public.add(name)
                by_id[(code, width)]["public_clock" if name == "clk" else "public_other"] += 1
            elif len(scopes) == 3:
                key = scopes[2], name
                if key in expected:
                    require(width == 1 and key not in seen, "Wrong connected pin waveform declaration")
                    seen.add(key)
                    by_id[(code, width)][expected[key]] += 1
    require(not scopes and seen == set(expected) and public == set(PORT_WIDTHS), "Incomplete connected waveform pins")
    aliases = {code: (width, tuple(groups.items())) for (code, width), groups in by_id.items()}
    require(len(aliases) == len(by_id), "Conflicting widths on one waveform ID")
    pin_counts = defaultdict(int)
    for width, groups in aliases.values():
        for group, count in groups:
            pin_counts[group] += width * count
    return aliases, dict(pin_counts)


def scan(vcd, inventory, epochs):
    with vcd.open("rb") as stream:
        aliases, counts = declarations(stream, inventory)
        # Store events by cycle. A change at each epoch's left boundary
        # belongs to that epoch. The terminating clock edge is separate.
        full_end = epochs["full"][1]
        by_cycle = {}
        values = {}
        last = {}
        now = 0
        unknown_at_end = defaultdict(int)
        unknown = {name: defaultdict(int) for name in epochs}

        def tally(code, value):
            width, groups = aliases[code]
            old = values.get(code, b"x" * width)
            before = last.get(code, 0)
            value = value.rjust(width, value[:1] if value[:1] in (b"x", b"z") else b"0")
            require(len(value) == width, "Waveform bus width changed")
            if old == value:
                return
            if width == 1:
                known_changes = int(old in (b"0", b"1") and value in (b"0", b"1"))
                unknown_bits = int(old not in (b"0", b"1"))
            else:
                known_changes = sum(a in b"01" and b in b"01" and a != b for a, b in zip(old, value))
                unknown_bits = sum(bit not in b"01" for bit in old)
            if known_changes:
                cycle = now // CYCLE_PS
                if cycle not in by_cycle:
                    by_cycle[cycle] = defaultdict(int)
                groups_here = by_cycle[cycle]
                for group, count in groups:
                    groups_here[group] += known_changes * count
            if unknown_bits:
                for epoch, (start, end) in epochs.items():
                    duration = max(0, min(end, now) - max(start, before))
                    if duration:
                        for group, count in groups:
                            unknown[epoch][group] += duration * unknown_bits * count
            values[code], last[code] = value, now

        for raw in stream:
            mark = raw[:1]
            if mark == b"#":
                timestamp = int(raw[1:])
                require(timestamp >= now, "Nonmonotonic waveform")
                now = timestamp
            elif mark in (b"0", b"1", b"x", b"z"):
                code = raw[1:-1]
                if code in aliases:
                    tally(code, mark)
            elif mark == b"b":
                value, code = raw[1:].split()
                if code in aliases:
                    tally(code, value)
        require(now == full_end, "Wrong waveform duration")
        for code, (width, groups) in aliases.items():
            value = values.get(code, b"x" * width)
            bits = sum(bit not in b"01" for bit in value)
            if bits:
                for group, count in groups:
                    unknown_at_end[group] += bits * count
                    for epoch, (start, end) in epochs.items():
                        unknown[epoch][group] += max(0, end - max(start, last.get(code, 0))) * bits * count
        result = {}
        for name, (start, end) in epochs.items():
            window = [by_cycle.get(cycle, {}) for cycle in range(start // CYCLE_PS, end // CYCLE_PS)]
            result[name] = dict(start_ps=start, end_ps=end, connected_pin_transitions={
                group: sum(row.get(group, 0) for row in window) for group in counts},
                peak_connected_pin_transitions_per_cycle={
                    group: max(row.get(group, 0) for row in window) for group in counts},
                peak_nonclock_cell_pin_transitions_per_cycle=max(
                    row.get("cell_input_pin", 0) + row.get("cell_output_pin", 0) for row in window),
                unknown_pin_bit_ps={group: unknown[name][group] for group in counts})
        return dict(connected_pin_bits=counts, distinct_waveform_ids=len(aliases), windows=result,
                    unknown_pin_bits_at_end=dict(unknown_at_end), excluded_final_edge=dict(by_cycle.get(now // CYCLE_PS, {})))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("receipts", nargs="+", type=Path)
    args = parser.parse_args()
    out = args.out.resolve()
    require(out.parent == TRIAL / "power-dc" and not out.exists(), "Use a fresh ignored power-dc receipt")
    pins, results = {}, {}
    producer = bind(pins, __file__)
    _, _, _, _, inventory = selected_inputs(pins)
    for path in args.receipts:
        receipt = read_bound(pins, path)
        require(receipt["schema"] in (BASE_SCHEMA, SCHEMA) and receipt["all_public_observations_replayed"] is True
                and receipt["target_odb_sha256"] == TARGET["odb_sha256"] and receipt["target_gds_sha256"] == TARGET["gds_sha256"],
                "Wrong workload receipt")
        source = receipt["artifacts"]["activity.vcd"]
        vcd = Path(bind(pins, source["path"], source["sha256"])["path"])
        name = receipt["workload"]
        require(name not in results, "Repeated workload")
        results[name] = dict(receipt=bind(pins, path), **scan(vcd, inventory, windows(receipt)))
    for path, digest in tuple(pins.items()):
        bind(pins, path, digest)
    emit(out, dict(schema="pinwheel.streaming-8x4-hold-cap-activity-epochs.v1", status="diagnostic",
                   producer=producer, workloads=results, target_odb_sha256=TARGET["odb_sha256"],
                   target_gds_sha256=TARGET["gds_sha256"], qualified_activity_envelope=False))


if __name__ == "__main__":
    main()
