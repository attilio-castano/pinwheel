#!/usr/bin/env python3
"""Fit per-layer wire RC from a completed run's routed DEF and extracted SPEF.

The resizer estimates wire parasitics from technology-LEF layer values, while
final timing uses extraction. This measures the difference on an existing run;
it starts no physical flow and changes no run evidence.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

POINT = re.compile(r"\( (-?\d+|\*) (-?\d+|\*)(?: -?\d+)? \)")
SEGMENT = re.compile(r"(?:ROUTED|NEW) (\S+)")


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def routed_lengths(def_text):
    """Return {net: ({layer: µm}, via count)} for every routed signal net."""
    units = int(re.search(r"UNITS DISTANCE MICRONS (\d+)", def_text).group(1))
    start = re.search(r"\nNETS \d+", def_text)
    if not start:
        raise ValueError("DEF has no NETS section")
    body = def_text[start.end():]
    body = body[:body.index("\nEND NETS")]
    result = {}
    for block in re.split(r"\n\s*- ", body)[1:]:
        if "ROUTED" not in block:
            continue
        name = block.split()[0].replace("\\", "")
        lengths, vias = {}, 0
        for line in block[block.index("ROUTED"):].split("\n"):
            layer = SEGMENT.search(line)
            if not layer:
                continue
            vias += len(re.findall(r"\) [A-Za-z]\w*", line))
            previous = None
            for x, y in POINT.findall(line):
                x = previous[0] if x == "*" else int(x)
                y = previous[1] if y == "*" else int(y)
                if previous is not None:
                    distance = (abs(x - previous[0]) + abs(y - previous[1])) / units
                    lengths[layer.group(1)] = lengths.get(layer.group(1), 0.0) + distance
                previous = (x, y)
        result[name] = (lengths, vias)
    return result


def extracted(spef_lines):
    """Return ({net: total wire cap}, {net: summed resistance}, units)."""
    names, cap, res, units = {}, {}, {}, {}
    section = current = mode = None
    for line in spef_lines:
        if line.startswith(("*C_UNIT", "*R_UNIT")):
            key, scale, unit = line.split()
            units[key.strip("*")] = f"{scale} {unit}"
        elif line.startswith("*NAME_MAP"):
            section = "map"
        elif line.startswith("*D_NET"):
            section = None
            _, net, total = line.split()
            current = names.get(net, net)
            cap[current], res[current], mode = float(total), 0.0, None
        elif section == "map":
            match = re.match(r"(\*\d+) (\S+)", line)
            if match:
                names[match.group(1)] = match.group(2).replace("\\", "")
        elif current is not None:
            if line.startswith("*END"):
                current = mode = None
            elif line.startswith(("*CONN", "*CAP", "*RES")):
                mode = line.split()[0]
            elif mode == "*RES":
                fields = line.split()
                if len(fields) == 4:
                    res[current] += float(fields[3])
    return cap, res, units


def least_squares(rows, targets):
    size = len(rows[0])
    matrix = [[sum(r[i] * r[j] for r in rows) for j in range(size)] for i in range(size)]
    vector = [sum(r[i] * t for r, t in zip(rows, targets)) for i in range(size)]
    for i in range(size):
        pivot = max(range(i, size), key=lambda k: abs(matrix[k][i]))
        if abs(matrix[pivot][i]) < 1e-12:
            raise ValueError("Singular fit: a layer has no routed length")
        matrix[i], matrix[pivot] = matrix[pivot], matrix[i]
        vector[i], vector[pivot] = vector[pivot], vector[i]
        for k in range(i + 1, size):
            factor = matrix[k][i] / matrix[i][i]
            vector[k] -= factor * vector[i]
            for j in range(i, size):
                matrix[k][j] -= factor * matrix[i][j]
    solution = [0.0] * size
    for i in reversed(range(size)):
        tail = sum(matrix[i][j] * solution[j] for j in range(i + 1, size))
        solution[i] = (vector[i] - tail) / matrix[i][i]
    return solution


def r_squared(rows, targets, solution):
    mean = sum(targets) / len(targets)
    total = sum((t - mean) ** 2 for t in targets)
    residual = sum((t - sum(a * b for a, b in zip(r, solution))) ** 2
                   for r, t in zip(rows, targets))
    return 1 - residual / total if total else 0.0


def fit(lengths, cap, res, minimum_um):
    layers = sorted({layer for v, _ in lengths.values() for layer in v})
    cap_rows, caps, res_rows, ress = [], [], [], []
    for net, (by_layer, vias) in lengths.items():
        if net not in cap or sum(by_layer.values()) < minimum_um:
            continue
        row = [by_layer.get(layer, 0.0) for layer in layers]
        cap_rows.append(row)
        caps.append(cap[net])
        res_rows.append(row + [float(vias)])
        ress.append(res[net])
    if len(caps) < 10 * (len(layers) + 1):
        raise ValueError("Too few routed nets for a fit")
    cap_fit = least_squares(cap_rows, caps)
    res_fit = least_squares(res_rows, ress)
    total = sum(map(sum, cap_rows))
    return {
        "nets": len(caps),
        "routed_um": {layer: sum(r[i] for r in cap_rows) for i, layer in enumerate(layers)},
        "cap_per_um": dict(zip(layers, cap_fit)),
        "cap_per_um_overall": sum(caps) / total,
        "cap_r_squared": r_squared(cap_rows, caps, cap_fit),
        "res_per_um": dict(zip(layers, res_fit[:-1])),
        "res_per_via": res_fit[-1],
        "res_r_squared": r_squared(res_rows, ress, res_fit),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--def", dest="def_path", type=Path, required=True,
                        help="Routed DEF from the completed run")
    parser.add_argument("--spef", type=Path, required=True,
                        help="Extracted SPEF for the same routed design")
    parser.add_argument("--minimum-um", type=float, default=20.0,
                        help="Ignore nets shorter than this; pin stubs dominate them")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    lengths = routed_lengths(args.def_path.read_text())
    with args.spef.open() as stream:
        cap, res, units = extracted(stream)
    report = fit(lengths, cap, res, args.minimum_um)
    report.update({"spef_units": units, "minimum_um": args.minimum_um,
                   "def_sha256": sha(args.def_path), "spef_sha256": sha(args.spef)})
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
