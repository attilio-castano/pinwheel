"""Recover signed heated-case branch feeds at the 48 sparse-source via arrays."""

import argparse
from collections import defaultdict
import math
from pathlib import Path

from streaming_8x4_draft_rc_timing import bound
from streaming_8x4_e982_native import read, require, sha, write
from streaming_8x4_hold_cap_psm_currents import parse_nodes, vectors
from streaming_8x4_hold_cap_via_audit import DBU, VIA, nearest, parse_def
from streaming_8x4_hold_cap_physical import TARGET, TRIAL


ROOT = TRIAL / "power-dc"
VIA_READBACK = ROOT / "via-array-audit-01.json"
VIA_SHA = "a96eed9482c8ac0d2aeb12b5fe2ea4e5159900f99215741984638a4d7f4e7d97"
TERMINALS = ROOT / "terminal-currents-03/readback.json"
TERMINAL_SHA = "88acc8523eef86e47b3cc667b7b4987a02cbdef25218b34937bf1dbf48ac6008"
DUMP_SHA = "e73ce4cdf0e9ce8634f9a3aacddc5824bf35630921c450e66c84d8f349b5b45d"
DEF_SHA = "0ebc4418da924037d2c9cb5beeff5a7d9c830b5ca8091a5cdf1616b790475962"
HEATED = "i2c-sparse-r1-sheet105-01"


def shape(node):
    kind, layer, point, terminal = node
    return dict(kind=kind, layer=layer, point_dbu=point, terminal=terminal)


def find_arrays(path, rail, nodes, ids, voltages, expected, families, physical):
    axes = {}
    for family in families.values():
        cut = family["cut"]
        centers = physical[rail, cut]
        axes[cut] = [sorted({center[i] for center in centers}) for i in range(2)]
    found = {}
    with path.open() as stream:
        for line in stream:
            ends, token = line.strip().rsplit(": ", 1)
            a, b = (ids[name] for name in ends.split(" -> ", 1))
            na, nb = nodes[a], nodes[b]
            if na[0] != "Node" or nb[0] != "Node" or na[1] == nb[1]:
                continue
            cut, cuts = VIA[na[1], nb[1]]
            centers = [tuple(nearest(axis, value) for axis, value in zip(axes[cut], node[2], strict=True))
                       for node in (na, nb)]
            key = cut, centers[0]
            if key not in expected:
                continue
            require(centers[0] == centers[1] and key not in found
                    and abs(20.0 * float(token) - cuts) < 1e-8, "Wrong array or resistance")
            current = (voltages[a] - voltages[b]) * float(token)
            reported = expected[key]["array_current_ma"]
            tolerance = expected[key]["current_upper_rounding_ma"] - reported
            require(abs(abs(current) * 1000 - reported) <= tolerance + 1e-9,
                    "Reconstructed current differs from the reported array")
            found[key] = (a, b, current)
    require(found.keys() == expected.keys(), "Incomplete high-current array census")
    return found


def incident_edges(path, relevant, nodes, ids, voltages, external):
    incident = defaultdict(list)
    with path.open() as stream:
        for line in stream:
            ends, token = line.strip().rsplit(": ", 1)
            a, b = (ids[name] for name in ends.split(" -> ", 1))
            if a not in relevant and b not in relevant:
                continue
            amps = (voltages[a] - voltages[b]) * float(token)
            if a in relevant:
                incident[a].append(dict(neighbor_index=b, neighbor=shape(nodes[b]), outward_a=amps))
            if b in relevant:
                incident[b].append(dict(neighbor_index=a, neighbor=shape(nodes[a]), outward_a=-amps))
    for row in external:
        index = row["grid_index"]
        require(nodes[index][2] == tuple(row["point_dbu"]), "Source location differs")
        if index in relevant:
            source = row["fixed_source_index"]
            incident[index].append(dict(neighbor_index=source, neighbor=shape(nodes[source]),
                                        outward_a=-row["amps_source_to_grid"]))
    return incident


def audit():
    require(sha(VIA_READBACK) == VIA_SHA and sha(TERMINALS) == TERMINAL_SHA and
            sha(TARGET["odb"]) == TARGET["odb_sha256"] and sha(TARGET["gds"]) == TARGET["gds_sha256"],
            "Frozen data changed")
    terminal = read(TERMINALS)
    dump = terminal["dump"]
    require(dump["sha256"] == DUMP_SHA and bound(dump["path"]) == dump, "Wrong heated solver dump")
    raw = read(dump["path"])
    manifest = read(VIA_READBACK)
    case, = [row for row in manifest["cases"] if row["case"] == HEATED]
    def_path = TRIAL / "trial.def"
    require(sha(def_path) == DEF_SHA, "Frozen DEF changed")
    families, arrays = parse_def(def_path)
    physical = {(rail, families[family]["cut"]): centers for (rail, family), centers in arrays.items()}
    results = []
    for rail, cuts in case["rails"].items():
        expected = {(cut, tuple(round(x * DBU) for x in row["center_um"])): row for cut, group in cuts.items()
                    for row in group["arrays_requiring_sharing"]}
        hashes = raw["solver_dumps"][rail]
        for name, item in hashes.items():
            require(bound(item["path"]) == item, f"{rail} {name} changed")
        nodes, ids, _ = parse_nodes(Path(hashes["psm_nodes.txt"]["path"]))
        voltages = vectors(Path(hashes["psm_V.txt"]["path"]), "V", len(nodes))
        j = vectors(Path(hashes["psm_J.txt"]["path"]), "J", len(nodes))
        conductance = Path(hashes["psm_cond.txt"]["path"])
        found = find_arrays(conductance, rail, nodes, ids, voltages, expected, families, physical)
        relevant = {index for a, b, _ in found.values() for index in (a, b)}
        incident = incident_edges(conductance, relevant, nodes, ids, voltages,
                                  terminal["rails"][rail]["external_sources"])
        for (cut, center), (a, b, current) in sorted(found.items()):
            sides = []
            for ix, opposite in ((a, b), (b, a)):
                require(j[ix] == 0 and abs(math.fsum(edge["outward_a"] for edge in incident[ix])) < 5e-9,
                        "Incident feed does not balance at a selected via endpoint")
                own, = [edge for edge in incident[ix] if edge["neighbor_index"] == opposite]
                sides.append(dict(node_index=ix, node=shape(nodes[ix]), via_outward_a=own["outward_a"],
                                  other=[edge for edge in incident[ix] if edge["neighbor_index"] != opposite]))
            results.append(dict(rail=rail, cut=cut, center_dbu=center, lower_to_upper_a=current, sides=sides))
        require(all(bound(item["path"]) == item for item in hashes.values()), "Solver data changed during readback")
    require(len(results) == 48, "Wrong array census")
    return dict(schema="pinwheel.streaming-8x4-hold-cap-via-feeds.v1", case=HEATED,
                target_odb_sha256=TARGET["odb_sha256"], target_gds_sha256=TARGET["gds_sha256"],
                via_readback=bound(VIA_READBACK), terminal_readback=bound(TERMINALS), dump=dump,
                def_view=bound(def_path), arrays=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out.resolve()
    require(out.parent == ROOT and not out.exists(), "Use a fresh result in power-dc")
    write(out, audit())


if __name__ == "__main__":
    main()
