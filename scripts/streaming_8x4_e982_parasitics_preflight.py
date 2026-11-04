"""Check sealed SPEF and OpenSTA annotation evidence without running CAD."""

import argparse
from collections import defaultdict
from decimal import Decimal, DecimalException
import hashlib
import json
from pathlib import Path
import re
import sys

from physical_checkpoint_sta import measurement_quality
from streaming_8x4_e982_g4_transport import TARGET_GDS, TARGET_ODB, TOP
from streaming_8x4_tt_rehearsal import file_spec, local_path
from streaming_tt_quality import inventory_context
from streaming_tt_signoff import decode, require


REQUEST = "pinwheel.e982-parasitics-preflight-request.v1"
ANALYSIS = "pinwheel.e982-spef-annotation-run.v1"
RESULT = "pinwheel.e982-parasitics-preflight.v1"
TARGET = {
    "odb": TARGET_ODB,
    "gds": TARGET_GDS,
    "netlist": "6d3994230c8b56f99db0fce61ca1ebfddbd13de96d792b03605ee8107a05593c",
    "inventory": "00d4790acec3550a6a176566fae6abaa6f150903aeb2a6d4b640cf75dc1afd10",
}
ECO_TARGET = {
    "odb": "e40e40804ddf5c4093f83710ec27b0a5b975f3a047e5c95810e175fbe6aa78f9",
    "gds": "dcc496d71202677f6d2fe3785dca6ff9bb225ef954953bf7925171174d4b7e82",
    "netlist": "3167eaaed4365ffc373f9a8609172eeebca48f792134d84a19f259e5f16951ec",
    "inventory": "af31d89940af5af559d2a8fceb5c0767887faa952298a0e7b684b8ee91658ee8",
}
UNITS = {"*T_UNIT": {"PS", "NS"}, "*C_UNIT": {"FF", "PF"}, "*R_UNIT": {"OHM", "KOHM"}}
META = {"*DATE", "*VENDOR", "*PROGRAM", "*VERSION", "*DESIGN_FLOW"}
NAME = re.compile(r"[A-Za-z0-9_.$:/<>\[\]+-]+")
NUMBER = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")
LABEL = re.compile(r"[A-Za-z0-9_.+-]+")


def fields(value, expected, description):
    require(type(value) is dict and value.keys() == set(expected), f"Invalid {description} fields")


def number(value, *, signed=False):
    require(NUMBER.fullmatch(value), f"Unsupported SPEF scalar: {value}")
    parsed = Decimal(value)
    require(parsed.is_finite() and len(parsed.as_tuple().digits) <= 28 and abs(parsed.adjusted()) <= 100
            and (signed or parsed >= 0), f"Invalid SPEF scalar: {value}")
    return parsed.normalize()


def literal(value):
    value = re.sub(r"\\([.\[\]<>])", r"\1", value)
    require(NAME.fullmatch(value), f"Unsupported SPEF name: {value}")
    return value


def expand(value, names):
    if value.startswith("*"):
        key, separator, suffix = value.partition(":")
        require(key in names, f"Unresolved SPEF name: {value}")
        return names[key] + (separator + literal(suffix) if separator else "")
    return literal(value)


def connection_tail(parts, master=None):
    """Support standard cell-master and coordinate attributes in connection rows."""
    seen = set()
    while parts:
        key, *parts = parts
        require(key in {"*D", "*C"} and key not in seen, "Unsupported SPEF connection attribute")
        seen.add(key)
        if key == "*D":
            require(parts and master is not None and parts[0] == master, "SPEF connection master differs")
            parts = parts[1:]
        else:
            require(len(parts) >= 2, "Incomplete SPEF connection coordinates")
            number(parts[0], signed=True)
            number(parts[1], signed=True)
            parts = parts[2:]


def expected_nets(inventory, context):
    directions = {"INPUT": "I", "OUTPUT": "O", "INOUT": "B"}
    ports = {name: directions[row["direction"].upper()] for name, row in inventory["public_bterms"].items()}
    nets, required = {}, set()
    for name, row in context["nets"].items():
        if row["type"] in {"POWER", "GROUND"}:
            continue
        points = {("P", port): ports[port] for port in row["ports"]}
        points.update({("I", terminal["instance"] + ":" + terminal["pin"]): directions[terminal["direction"]]
                       for terminal in row["terminals"]})
        nets[name] = points
        if any((kind, direction) in {("I", "I"), ("I", "B"), ("P", "O"), ("P", "B")}
               for (kind, _), direction in points.items()):
            required.add(name)
    require(required, "Vacuous consumed-net inventory")
    return nets, required, ports


def net_graph(connections, resistors, capacitors, net):
    graph = defaultdict(set)
    for left, right, _ in resistors:
        graph[left].add(right)
        graph[right].add(left)
    terminals = {name for _, name in connections}
    nodes = terminals | graph.keys()
    reached, pending = set(), [next(iter(terminals))]
    while pending:
        node = pending.pop()
        if node not in reached:
            reached.add(node)
            pending.extend(graph[node] - reached)
    require(reached == nodes, f"Disconnected SPEF resistance graph: {net}")
    remote = set()
    for *points, _ in capacitors:
        require(any(point in nodes for point in points), f"Capacitance has no local endpoint: {net}")
        remote.update(set(points) - nodes)
    return nodes, remote


def spef_evidence(lines, inventory, layout):
    """Validate an explicit scalar, detailed-net SPEF dialect against exact ODB connectivity."""
    expected, required, ports = layout
    header, aliases, seen_ports, seen_nets = {}, {}, {}, {}
    all_nodes, remote_nodes = set(), set()
    stage = "header"
    ports_section = False
    totals = dict(connections=0, resistors=0, capacitors=0)
    net = None
    for line_no, line in enumerate(lines, 1):
        row = line.split()
        if not row or row[0].startswith("//"):
            continue
        key = row[0]
        if stage == "header" and key not in {"*NAME_MAP", "*PORTS", "*D_NET"}:
            require(key in META | UNITS.keys() | {"*SPEF", "*DESIGN", "*DIVIDER", "*DELIMITER",
                                                  "*BUS_DELIMITER", "*L_UNIT"}
                    and key not in header, f"Unsupported or duplicate SPEF header: {key}")
            header[key] = " ".join(row[1:])
        elif key == "*NAME_MAP":
            require(stage == "header" and len(row) == 1, "Unexpected SPEF NAME_MAP")
            stage = "aliases"
        elif key == "*PORTS":
            require(stage in {"header", "aliases"} and len(row) == 1, "Unexpected SPEF PORTS")
            stage = "ports"
            ports_section = True
        elif key == "*D_NET":
            require(stage in {"header", "aliases", "ports", "between"} and len(row) == 3,
                    f"Malformed SPEF D_NET at line {line_no}")
            net = expand(row[1], aliases)
            require(net in expected and net not in seen_nets, f"Unknown or duplicate SPEF net: {net}")
            total = number(row[2])
            connections, capacitors, resistors, cap_ids, res_ids = {}, [], [], set(), set()
            stage = "net"
        elif stage == "aliases":
            require(len(row) == 2 and re.fullmatch(r"\*[0-9]+", key) and key not in aliases,
                    f"Malformed or duplicate SPEF name map at line {line_no}")
            aliases[key] = literal(row[1])
        elif stage == "ports":
            port = expand(key, aliases)
            require(len(row) >= 2 and port not in seen_ports and ports.get(port) == row[1],
                    f"Unknown, wrong-direction or duplicate SPEF port: {port}")
            connection_tail(row[2:])
            seen_ports[port] = row[1]
        elif key in {"*CONN", "*CAP", "*RES"}:
            predecessor = {"*CONN": "net", "*CAP": "*CONN", "*RES": "*CAP"}
            require(stage == predecessor[key] and len(row) == 1, f"Unexpected SPEF {key}: {net}")
            stage = key
        elif key == "*END":
            require(stage == "*RES" and len(row) == 1 and connections and connections == expected[net],
                    f"Incomplete SPEF net or terminal mismatch: {net}")
            nodes, remote = net_graph(connections, resistors, capacitors, net)
            require(not all_nodes.intersection(nodes), f"SPEF graph node belongs to multiple nets: {net}")
            all_nodes.update(nodes)
            remote_nodes.update(remote)
            graph = (str(total), sorted(connections.items()), sorted(resistors),
                     sorted(capacitors, key=lambda entry: (len(entry), entry)))
            seen_nets[net] = hashlib.sha256(repr(graph).encode()).hexdigest()
            totals["connections"] += len(connections)
            totals["resistors"] += len(resistors)
            totals["capacitors"] += len(capacitors)
            stage = "between"
        elif stage == "*CONN":
            require(len(row) >= 3 and key in {"*I", "*P"} and row[2] in {"I", "O", "B"},
                    f"Malformed SPEF terminal at line {line_no}")
            node = expand(row[1], aliases)
            point = (key[1], node)
            require(point not in connections, f"Duplicate SPEF terminal: {node}")
            instance = inventory["instances"].get(node.rsplit(":", 1)[0]) if key == "*I" else None
            connection_tail(row[3:], instance["master"] if instance else None)
            connections[point] = row[2]
        elif stage in {"*CAP", "*RES"}:
            is_cap = stage == "*CAP"
            entries, ids = (capacitors, cap_ids) if is_cap else (resistors, res_ids)
            require(len(row) in ({3, 4} if is_cap else {4}) and key.isascii() and key.isdecimal()
                    and int(key) > 0 and int(key) not in ids, f"Malformed or duplicate SPEF {stage} row: {net}")
            ids.add(int(key))
            points = sorted(expand(token, aliases) for token in row[1:-1])
            require(len(set(points)) == len(points), f"Self edge in SPEF {stage}: {net}")
            entries.append((*points, number(row[-1])))
        else:
            raise ValueError(f"Unsupported SPEF content at line {line_no}")
    require(stage == "between", "Truncated SPEF net")
    require(header.get("*DESIGN") == f'"{TOP}"' and header.get("*DIVIDER") == "/"
            and header.get("*DELIMITER") == ":" and header.get("*BUS_DELIMITER") in {"[]", "<>"}
            and re.fullmatch(r'"ieee 1481-(1998|1999|2009)"', header.get("*SPEF", ""), re.I)
            and re.findall(r'"PIN_CAP ([^"]+)"', header.get("*DESIGN_FLOW", "")) == ["NONE"],
            "Unsupported SPEF header or wrong top")
    require(not ports_section or seen_ports == ports, "SPEF PORTS do not match the public design")
    units = {}
    for key, allowed in UNITS.items():
        row = header.get(key, "").split()
        require(len(row) == 2 and row[1] in allowed and number(row[0]) > 0, f"Missing/invalid SPEF {key}")
        units[key] = [str(number(row[0])), row[1]]
    missing = sorted(required - seen_nets.keys())
    require(not missing, f"SPEF omits {len(missing)} consumed nets: {missing[:5]}")
    require(not remote_nodes - all_nodes, "SPEF coupling references a missing graph node")
    fingerprint = hashlib.sha256(repr((units, sorted(seen_nets.items()))).encode()).hexdigest()
    return dict(**totals, units=units, nets=len(seen_nets), consumed_nets=len(required), graph_sha256=fingerprint)


def annotation_evidence(text, corner, context, disconnected):
    markers = re.findall(r"(?m)^=+\s+([A-Za-z0-9_.+-]+) Corner\s+=+\s*$", text)
    require(markers and set(markers) == {corner}, "OpenSTA annotation report corner differs")
    reports = re.findall(r"^report_parasitic_annotation -report_unannotated[ \t]*\n=+[ \t]*\n(.*?)(?=^=|\Z)",
                         text, re.M | re.S)
    require(len(reports) == 1 and text.count("report_parasitic_annotation -report_unannotated") == 1,
            "Missing or repeated raw annotation section")
    result = measurement_quality(reports[0], context, disconnected)
    annotation = result["wire_annotation"]
    require(annotation["complete_for_consumed_nets"], "OpenSTA reports incomplete annotation on consumed nets")
    require(re.search(r"(?m)^Found 0 partially unannotated drivers\.\s*\Z", reports[0]),
            "OpenSTA raw annotation has trailing rows")
    return annotation


def preflight(workspace, request, *, target_name="baseline"):
    require(target_name in ("baseline", "eco"), "Unsupported preflight target")
    pins = TARGET if target_name == "baseline" else ECO_TARGET
    fields(request, ("schema", "target", "scenarios"), "request")
    require(request["schema"] == REQUEST, "Unsupported preflight request")
    fields(request["target"], pins, "target")
    target = {role: file_spec(workspace, binding) for role, binding in request["target"].items()}
    require({role: row["sha256"] for role, row in target.items()} == pins, "Request is for another frozen target")
    inventory = decode(local_path(workspace, target["inventory"]["path"]).read_bytes())
    require(inventory["top"] == TOP, "Frozen inventory top differs")
    context, disconnected = inventory_context(inventory)
    layout = expected_nets(inventory, context)
    require(type(request["scenarios"]) is dict and request["scenarios"], "Empty scenario matrix")
    results, rc_graphs = {}, {}
    for name, row in sorted(request["scenarios"].items()):
        fields(row, ("rc_corner", "sta_corner", "mode", "sdc", "liberties", "spef", "annotation", "run"), "scenario")
        require(all(type(value) is str and LABEL.fullmatch(value)
                    for value in (name, row["rc_corner"], row["sta_corner"], row["mode"])), "Invalid scenario label")
        files = {role: file_spec(workspace, row[role]) for role in ("sdc", "spef", "annotation", "run")}
        require(type(row["liberties"]) is list and row["liberties"], "Missing Liberty bindings")
        liberties = [file_spec(workspace, binding) for binding in row["liberties"]]
        require(len({item["sha256"] for item in liberties}) == len(liberties), "Duplicate Liberty binding")
        run = decode(local_path(workspace, files["run"]["path"]).read_bytes())
        fields(run, ("schema", "top", "odb_sha256", "gds_sha256", "netlist_sha256", "scenario", "rc_corner",
                     "sta_corner", "mode", "sdc_sha256", "liberty_sha256", "spef_sha256", "annotation_sha256",
                     "runtime_sha256", "annotation_mode", "exit_code"), "analysis run")
        require(run["schema"] == ANALYSIS and run["top"] == TOP and run["scenario"] == name
                and all(run[key] == row[key] for key in ("rc_corner", "sta_corner", "mode"))
                and all(run[role + "_sha256"] == pins[role] for role in ("odb", "gds", "netlist"))
                and all(run[role + "_sha256"] == files[role]["sha256"] for role in ("sdc", "spef", "annotation"))
                and run["liberty_sha256"] == [item["sha256"] for item in liberties]
                and type(run["runtime_sha256"]) is str and re.fullmatch(r"[0-9a-f]{64}", run["runtime_sha256"])
                and run["annotation_mode"] == "read_spef" and type(run["exit_code"]) is int and run["exit_code"] == 0,
                f"Analysis custody differs for scenario {name}")
        with local_path(workspace, files["spef"]["path"]).open(encoding="ascii") as stream:
            spef = spef_evidence(stream, inventory, layout)
        graph = spef["graph_sha256"]
        rc = row["rc_corner"]
        require(rc_graphs.setdefault(rc, graph) == graph, f"Inconsistent SPEF graph for RC corner {rc}")
        annotation = annotation_evidence(local_path(workspace, files["annotation"]["path"]).read_text(),
                                         row["sta_corner"], context, disconnected)
        for binding in (*files.values(), *liberties):
            file_spec(workspace, binding)
        results[name] = dict(rc_corner=rc, sta_corner=row["sta_corner"], mode=row["mode"],
                             bindings=files, liberties=liberties, spef=spef, annotation=annotation)
    require(len(set(rc_graphs.values())) == len(rc_graphs), "Identical SPEF graphs declared as different RC corners")
    for binding in target.values():
        file_spec(workspace, binding)
    return dict(schema=RESULT, software_preflight_passed=True, target=target, scenarios=results,
                extraction_model_qualified=False, qualified_timing=False, tapeout_ready=False)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("request", type=Path)
    parser.add_argument("--request-sha256", required=True)
    parser.add_argument("--target", choices=("baseline", "eco"), default="baseline",
                        help="Require the pinned baseline or five-net ECO target")
    parser.add_argument("--workspace", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args(argv)
    try:
        raw = args.request.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == args.request_sha256, "Preflight request SHA-256 differs")
        result = preflight(args.workspace.resolve(strict=True), decode(raw), target_name=args.target)
    except (OSError, ValueError, KeyError, TypeError, DecimalException) as error:
        print(f"Parasitics preflight rejected: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
