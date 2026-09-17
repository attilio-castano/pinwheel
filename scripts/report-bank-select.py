#!/usr/bin/env python3
"""Compare mapped bank-selection cones, cutting every sequential boundary.

Cell depth and connectivity are structural screens, not timing or sensitization
proofs. ABC mapping estimates and full physical STA are recorded separately.
"""
import argparse
from collections import defaultdict, deque
import importlib.util
import json
from pathlib import Path

import backend_readback as rb
import bank_select_readback as banks

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("command_cones", ROOT / "scripts/report-command-cones.py")
cones = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cones)


def inspect(module, sequential, latches):
    cache = set(module["netnames"]["r_cached_word"]["bits"])
    cursor = [b for b in module["netnames"]["r_loader_cursor"]["bits"] if isinstance(b, int)]
    combinational, targets = {}, {}
    drivers, users = {}, defaultdict(set)
    for name, cell in module["cells"].items():
        if cell["type"] in latches:
            raise ValueError("Latches require a transparency contract")
        ins = {b for port, direction in cell["port_directions"].items() if direction == "input"
               for b in cell["connections"][port] if isinstance(b, int)}
        outs = {b for port, direction in cell["port_directions"].items() if direction == "output"
                for b in cell["connections"][port] if isinstance(b, int)}
        if cell["type"] in sequential:
            if cache & outs:
                for port, direction in cell["port_directions"].items():
                    if direction == "input" and port != "CLK":
                        for bit in cell["connections"][port]:
                            if isinstance(bit, int): targets[f"{name}/{port}"] = bit
            continue
        combinational[name] = (cell["type"], ins, outs)
        for bit in ins: users[bit].add(name)
        for bit in outs:
            if bit in drivers: raise ValueError("Multiple combinational drivers")
            drivers[bit] = name
    if not targets or not cursor:
        raise ValueError("Missing cursor or retained cache register endpoints")
    predecessors = {name: {drivers[b] for b in ins if b in drivers}
                    for name, (_, ins, _) in combinational.items()}
    pending = {name: len(pred) for name, pred in predecessors.items()}
    following = defaultdict(set)
    for name, pred in predecessors.items():
        for parent in pred: following[parent].add(name)
    queue = deque(n for n, count in pending.items() if count == 0)
    order = []
    while queue:
        name = queue.popleft()
        order.append(name)
        for child in following[name]:
            pending[child] -= 1
            if pending[child] == 0: queue.append(child)
    if len(order) != len(combinational): raise ValueError("Combinational cycle")
    families = {"cursor": cursor}
    families.update({label: module["ports"][port]["bits"] for label, port in
                     (("loader_data", "data"), ("protocol", "incoming"), ("command", "command"))})
    families["reset"] = module["ports"]["init"]["bits"] + module["ports"]["reset"]["bits"]
    result = {}
    for label, starts in families.items():
        distance = {b: (0, 0) for b in starts if isinstance(b, int)}
        for name in order:
            kind, ins, outs = combinational[name]
            reached = [distance[b] for b in ins if b in distance]
            if not reached: continue
            logic = 0 if "_buf_" in kind or "_dlygate" in kind else 1
            depth = (max(d[0] for d in reached) + 1, max(d[1] for d in reached) + logic)
            for b in outs: distance[b] = depth
        reached = {name: distance[b] for name, b in targets.items() if b in distance}
        # Restrict the reported load/depth cone to paths that actually reach cache inputs.
        back = {b for b in targets.values() if b in distance}
        for name in reversed(order):
            _, ins, outs = combinational[name]
            if back & outs: back.update(ins & distance.keys())
        result[label] = {"reached_cache_pins": len(reached),
            "maximum_cell_depth": max((v[0] for v in reached.values()), default=0),
            "maximum_logic_depth": max((v[1] for v in reached.values()), default=0),
            "maximum_combinational_fanout": max((len(users[b]) for b in back), default=0),
            "example_pins": sorted(reached)[:3]}
    return {"cache_input_pins": len(targets), "families": result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--control", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists(): raise RuntimeError("Preserve earlier cone evidence")
    sources = [Path(__file__).resolve(), ROOT / "scripts/report-command-cones.py",
               ROOT / "scripts/backend_readback.py", ROOT / "scripts/bank_select_readback.py"]
    stages = {}
    for label, directory in (("control", args.control), ("candidate", args.candidate)):
        receipt_path = directory.parent / "report.json"
        receipt = json.loads(receipt_path.read_text())
        mlir, labels = directory.parent / "composed.mlir", directory.parent / "cuts.tsv"
        if cones.sha(mlir) != receipt["artifact_sha256"]["composed.mlir"]:
            raise RuntimeError("Changed checked source graph")
        sources.extend([receipt_path, mlir, labels])
        graph = rb.read_hints(mlir)
        cuts = banks.read_cuts(labels, graph, receipt["variant"])
        depth = {"r_loader_cursor": 0}
        for n, item in graph.nodes.items():
            reached = [depth[k] for k in item.args if k in depth]
            if reached: depth[n] = max(reached) + 1
        stages[label] = {role: {"cursor_dependency": n in depth, "expression_depth_from_cursor": depth.get(n)}
                         for n, role in cuts.items()}
    results = {}
    for corner, filename in (("typical", "sg13cmos5l_stdcell_typ_1p20V_25C.lib"),
                             ("slow", "sg13cmos5l_stdcell_slow_1p08V_125C.lib")):
        lib = ROOT / "build/tools/ihp-cmos5l" / filename
        sequential, latches = cones.sequential_cells(lib)
        sources.append(lib)
        results[corner] = {}
        for label, directory in (("control", args.control), ("candidate", args.candidate)):
            path = directory / f"{corner}.json"
            receipt = json.loads((directory.parent / "report.json").read_text())
            if cones.sha(path) != receipt["artifact_sha256"][f"measured/{corner}.json"]:
                raise RuntimeError("Changed checked mapping")
            sources.append(path)
            module = json.loads(path.read_text())["modules"][cones.TOP]
            results[corner][label] = inspect(module, sequential, latches)
    receipt = {"results": results, "source_stages": stages,
               # Keep the configured tool path when the cached library is a symlink.
               "source_sha256": {str(p.absolute().relative_to(ROOT)): cones.sha(p) for p in sources},
               "boundary": "Mapped graph reachability and maximum cell depth, cutting every Liberty-declared flip-flop. "
                           "No claim about sensitizable paths, gate delay, or routed closure."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__": main()
