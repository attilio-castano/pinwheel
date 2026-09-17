"""Restricted full-backend artifact interpretation and Lean proof generation.

The emitted MLIR supplies proof hints only: their connection to Backend.netlist
must be proved in Lean. The actual RTL is read through Yosys's trusted frontend.
"""
from dataclasses import dataclass
from pathlib import Path
from collections import defaultdict
import json
import random
import re
import subprocess

TOP = "pinwheel_atomic_small_dense_cached"


INPUTS = {"init": (1, ".init"), "reset": (1, ".reset"),
          "command": (3, ".command"), "data": (64, ".data"),
          "incoming": (2, ".incoming")}
REGISTERS = {"r_loader_" + n: (w, f".control .{n}")
             for n, w in (("active", 1), ("valid", 1), ("pending", 1), ("cursor", 9))}
REGISTERS.update({"r_" + n: (w, f".core .{ctor}") for n, ctor, w in (
    ("mode", "mode", 3), ("pc", "pc", 8), ("remaining", "remaining", 8),
    ("wait_left", "waitLeft", 8), ("levels", "levels", 3), ("enabled", "enabled", 3))})
REGISTERS.update({f"r_sample{k}": (1, f".core (.sample ⟨{k}, by decide⟩)") for k in range(16)})
for bank in (0, 1):
    b = "true" if bank else "false"
    REGISTERS.update({f"r_bank{bank}_word{k}": (55, f".word {b} {k}") for k in range(32)})
    REGISTERS.update({f"r_bank{bank}_index{k}": (5, f".index {b} {k}") for k in range(256)})
    REGISTERS[f"r_bank{bank}_idle"] = (6, f".idle {b}")
    REGISTERS[f"r_bank{bank}_last"] = (8, f".last {b}")
REGISTERS["r_cached_word"] = (64, ".current")
OUTPUTS = {n[2:]: (w, f".control (.state .{n.removeprefix('r_loader_')})")
           for n, (w, _) in REGISTERS.items() if n.startswith("r_loader_")}
OUTPUTS.update({"loader_" + n: (1, f".control .{n}") for n in ("push", "commit", "start", "rejected")})
OUTPUTS.update({n[2:]: (w, f".core (.state {ctor.removeprefix('.core ')})")
                for n, (w, ctor) in REGISTERS.items() if ctor.startswith(".core ")})
OUTPUTS.update({"read_a": (8, ".core .readA"), "read_b": (8, ".core .readB"), "busy": (1, ".core .busy")})


@dataclass(frozen=True)
class Node:
    width: int
    op: str
    args: tuple = ()
    value: object = None


class Graph:
    def __init__(self):
        self.nodes = {}
        self.next = {}
        self.outputs = {}
        self.views = {}
        for name, (width, _) in INPUTS.items():
            self.nodes[name] = Node(width, "input", value=name)
        for name, (width, _) in REGISTERS.items():
            self.nodes[name] = Node(width, "reg", value=name)

    def expression(self, node, ref):
        w, op, args, value = node.width, node.op, node.args, node.value
        a = [ref(n) for n in args]
        if op == "input": return f"i ({INPUTS[value][1]})"
        if op == "reg": return f"s ({REGISTERS[value][1]})"
        if op == "lit": return f"{value}#{w}"
        if op == "slice": return f"({a[0]}).extractLsb' {value} {w}"
        if op == "concat": return f"{a[0]} ++ {a[1]}"
        if op == "not": return f"~~~{a[0]}"
        if op in ("and", "or", "xor", "add", "sub"):
            return f"{a[0]} { {'and': '&&&', 'or': '|||', 'xor': '^^^', 'add': '+', 'sub': '-'}[op]} {a[1]}"
        if op == "eq": return f"BitVec.ofBool (decide ({a[0]} = {a[1]}))"
        if op == "lt": return f"BitVec.ofBool (decide (({a[0]}).toNat < ({a[1]}).toNat))"
        if op == "mux": return f"if {a[0]} = 1 then {a[1]} else {a[2]}"
        raise ValueError(op)

    def definitions(self, namespace, cuts=None):
        cuts = cuts or {}
        parameters = " ".join(f"({label} : BitVec {self.nodes[n].width})" for n, label in cuts.items())
        arguments = " ".join(cuts.values())
        lines = [f"namespace {namespace}"]
        for name, node in self.nodes.items():
            if node.op in ("input", "reg"): continue
            def ref(n):
                if n in cuts: return cuts[n]
                q = self.nodes[n]
                if q.op in ("input", "reg"):
                    return "(" + self.expression(q, None) + ")"
                return f"({n} i s {arguments})"
            lines.append(f"def {name} (i : Values Machine.Input) (s : Values Register) {parameters} : BitVec {node.width} := {self.expression(node, ref)}")
        lines.append(f"end {namespace}")
        return "\n".join(lines) + "\n"

    def signatures(self, samples=256):
        """Untrusted cut-point hints only. Every proposed cut needs a Lean proof."""
        rng = random.Random(0x50494E574845454C)
        values = {}
        def record(value):
            kind = value % 5
            finish = (value >> 41) % 3
            masks = [0x7e001ffff, 0x601ffff,
                     (0x7fffe01ffff, 0x7f87fffe01ffff, 0x7ffffffffe01ffff)[finish],
                     0x1fffffff]
            if kind == 4: return 4
            value = (value & masks[kind] & ~7) | kind
            if kind == 2: value = (value & ~(3 << 41)) | (finish << 41)
            for offset in (29, 35):
                if (value >> offset) & 63: value |= 1 << offset
            return value
        for name, n in self.nodes.items():
            mask = 2 ** n.width - 1
            a = [values[k] for k in n.args]
            if n.op in ("input", "reg"):
                values[name] = tuple(rng.getrandbits(n.width) for _ in range(samples))
                if name == "data":
                    values[name] = tuple(v & (2 ** (64, 55, 35, 32, 8, 5, 3, 1)[k % 8] - 1)
                                         for k, v in enumerate(values[name]))
                if name == "r_cached_word" or re.fullmatch(r"r_bank[01]_word\d+", name):
                    def program_value(k, v):
                        if k % 4 == 0: return v
                        v = record(v)
                        if name == "r_cached_word": return v
                        hi = (v >> 17) & 4095 if v & 7 == 3 else v >> 25
                        return (hi << 17) | (v & 0x1ffff)
                    values[name] = tuple(program_value(k, v) for k, v in enumerate(values[name]))
                if name in ("r_remaining", "r_wait_left"):
                    values[name] = tuple(v if k % 3 == 0 else k % 2 for k, v in enumerate(values[name]))
            elif n.op == "lit": values[name] = (n.value,) * samples
            else:
                def evaluate(k):
                    x = [v[k] for v in a]
                    if n.op == "slice": return x[0] >> n.value
                    if n.op == "concat": return (x[0] << self.nodes[n.args[1]].width) | x[1]
                    if n.op == "not": return ~x[0]
                    if n.op == "and": return x[0] & x[1]
                    if n.op == "or": return x[0] | x[1]
                    if n.op == "xor": return x[0] ^ x[1]
                    if n.op == "add": return x[0] + x[1]
                    if n.op == "sub": return x[0] - x[1]
                    if n.op == "eq": return int(x[0] == x[1])
                    if n.op == "lt": return int(x[0] < x[1])
                    if n.op == "mux": return x[1] if x[0] == 1 else x[2]
                    raise ValueError(n.op)
                values[name] = tuple(evaluate(k) & mask for k in range(samples))
        return {name: (self.nodes[name].width, value) for name, value in values.items()}


def read_hints(path: Path):
    """Decode the small generated MLIR fragment; Lean must certify each hint."""
    graph = Graph()
    text = path.read_text()
    header = next(line for line in text.splitlines() if "hw.module @" in line)
    output_names = re.findall(r"out (\w+) : i(\d+)", header)
    if {n: int(w) for n, w in output_names} != {n: w for n, (w, _) in OUTPUTS.items()}:
        raise ValueError("Changed hint output contract")
    for line in text.splitlines()[3:]:
        line = line.strip()
        if line in ("}",): continue
        if line.startswith("hw.output "):
            names = re.findall(r"%(\w+)", line)
            if len(names) != len(output_names): raise ValueError("Hint output count")
            graph.outputs = dict(zip((n for n, _ in output_names), names))
            continue
        match = re.fullmatch(r"%(\w+) = (.*)", line)
        if not match: raise ValueError(f"Unknown hint line: {line}")
        name, expr = match.groups()
        args = tuple(re.findall(r"%(\w+)", expr))
        widths = list(map(int, re.findall(r"\bi(\d+)\b", expr)))
        if expr.startswith("seq.compreg "):
            if name not in REGISTERS or args[1:] != ("clock",) or widths != [REGISTERS[name][0]]:
                raise ValueError("Hint register contract")
            graph.next[name] = args[0]
            continue
        if name in graph.nodes: raise ValueError("Duplicate hint node")
        if expr.startswith("hw.constant "):
            node = Node(widths[0], "lit", value=int(expr.split()[1]))
        elif expr.startswith("comb.extract "):
            node = Node(widths[1], "slice", args, int(re.search(r"from (\d+)", expr)[1]))
        elif expr.startswith("comb.concat "):
            node = Node(sum(widths), "concat", args)
        elif expr.startswith("comb.icmp "):
            kind = expr.split()[1]
            if kind not in ("eq", "ult"): raise ValueError("Unknown hint comparison")
            node = Node(1, "eq" if kind == "eq" else "lt", args)
        else:
            op = expr.split()[0].removeprefix("comb.")
            if op not in ("xor", "and", "sub", "mux"): raise ValueError(f"Unknown hint op {op}")
            node = Node(widths[0], op, args)
            if op == "xor":
                right = graph.nodes[args[1]]
                if right.op == "lit" and right.value == 2 ** right.width - 1:
                    node = Node(widths[0], "not", args[:1])
        graph.nodes[name] = node
    if set(graph.next) != set(REGISTERS): raise ValueError("Missing hint state")
    return graph


def read_rtl(path: Path):
    """Interpret actual Yosys word-level JSON, rejecting unsupported semantics."""
    modules = json.loads(path.read_text())["modules"]
    if set(modules) != {TOP}: raise ValueError("Expected exactly the selected backend module")
    m = modules[TOP]
    if m.get("memories") or any(m.get("attributes", {}).get(k, "0").strip("0")
                                for k in ("blackbox", "whitebox")):
        raise ValueError("Unsupported memory or black box")
    expected = {"clk": ("input", 1), **{n: ("input", w) for n, (w, _) in INPUTS.items()},
                **{n: ("output", w) for n, (w, _) in OUTPUTS.items()}}
    ports = m["ports"]
    if {n: (p["direction"], len(p["bits"])) for n, p in ports.items()} != expected:
        raise ValueError("Changed port contract")
    if any("init" in n.get("attributes", {}) for n in m.get("netnames", {}).values()):
        raise ValueError("Implicit register initialization is unsupported")
    graph = Graph()
    owners = {}
    buses = {}
    interned = {}

    def bind(bits, name):
        if (not bits or len(bits) != graph.nodes[name].width or
                any(type(b) is not int or b < 0 or b in owners for b in bits) or len(set(bits)) != len(bits)):
            raise ValueError("Invalid, aliased or multiply driven bits")
        for k, b in enumerate(bits): owners[b] = (name, k)
        buses[tuple(bits)] = name

    def node(width, op, args=(), value=None):
        n = Node(width, op, args, value)
        if n in interned: return interned[n]
        name = f"n{len(interned)}"
        graph.nodes[name] = n
        interned[n] = name
        return name

    clock = ports["clk"]["bits"][0]
    if type(clock) is not int or clock < 0: raise ValueError("Clock must be a nonconstant input wire")
    owners[clock] = ("clock", 0)
    for name in INPUTS: bind(ports[name]["bits"], name)
    registers, pending = {}, []
    q_names = defaultdict(list)
    for name in REGISTERS:
        bits = m["netnames"].get(name, {}).get("bits")
        if bits is None: raise ValueError("Missing named backend state")
        q_names[tuple(bits)].append(name)
    for name, c in m["cells"].items():
        kind, wires, p = c["type"], c["connections"], c["parameters"]
        if kind != "$dff":
            pending.append((name, c))
            continue
        if (set(p) != {"CLK_POLARITY", "WIDTH"} or int(p["CLK_POLARITY"], 2) != 1
                or set(wires) != {"CLK", "D", "Q"} or wires["CLK"] != ports["clk"]["bits"]
                or c["port_directions"] != {"CLK": "input", "D": "input", "Q": "output"}):
            raise ValueError("Unsupported register clock/parameters")
        matches = q_names[tuple(wires["Q"])]
        if len(matches) != 1 or matches[0] in registers:
            raise ValueError("Changed state mapping")
        n = matches[0]
        if not (len(wires["D"]) == len(wires["Q"]) == int(p["WIDTH"], 2) == REGISTERS[n][0]):
            raise ValueError("Register width mismatch")
        bind(wires["Q"], n)
        registers[n] = wires["D"]
    if set(registers) != set(REGISTERS): raise ValueError("Missing backend registers")

    def signal(bits):
        key = tuple(bits)
        if key in buses: return buses[key]
        if not bits: raise ValueError("Zero-width signal")
        for b in bits:
            if type(b) is str:
                if b not in ("0", "1"): raise ValueError("Unknown/high-impedance bits are unsupported")
            elif type(b) is not int or b < 0:
                raise ValueError("Invalid signal bit")
            elif b == clock: raise ValueError("Clock used as combinational data")
            elif b not in owners: raise KeyError(b)
        parts, pos = [], 0
        while pos < len(bits):
            start = pos
            if type(bits[pos]) is str:
                while pos < len(bits) and type(bits[pos]) is str: pos += 1
                parts.append(node(pos - start, "lit", value=int("".join(reversed(bits[start:pos])), 2)))
            else:
                owner, offset = owners[bits[pos]]
                pos += 1
                while (pos < len(bits) and type(bits[pos]) is int and
                       owners[bits[pos]] == (owner, offset + pos - start)):
                    pos += 1
                width = pos - start
                parts.append(owner if offset == 0 and width == graph.nodes[owner].width
                             else node(width, "slice", (owner,), offset))
        result = parts[-1]
        for part in reversed(parts[:-1]):
            result = node(graph.nodes[result].width + graph.nodes[part].width, "concat", (result, part))
        buses[key] = result
        return result

    while pending:
        progressed = False
        for name, c in pending[:]:
            kind, wires, p = c["type"], c["connections"], c["parameters"]
            binary = {"$and": "and", "$or": "or", "$xor": "xor", "$sub": "sub", "$add": "add"}
            unary = {"$not", "$logic_not", "$reduce_or", "$reduce_and"}
            compare = {"$eq", "$ne", "$lt", "$ge", "$gt"}
            if kind not in binary and kind not in unary and kind not in compare | {"$mux"}:
                raise ValueError(f"Unsupported cell {kind}")
            ins = ["S", "B", "A"] if kind == "$mux" else ["A"] if kind in unary else ["A", "B"]
            if set(wires) != {*ins, "Y"} or c["port_directions"] != {**{n: "input" for n in ins}, "Y": "output"}:
                raise ValueError("Unexpected cell ports")
            width = len(wires["Y"])
            expected_params = {"WIDTH": width} if kind == "$mux" else {
                "A_SIGNED": 0, "A_WIDTH": len(wires["A"]), "Y_WIDTH": width,
                **({"B_SIGNED": 0, "B_WIDTH": len(wires["B"])} if "B" in ins else {})}
            if {k: int(v, 2) for k, v in p.items()} != expected_params:
                raise ValueError("Unsupported signedness/parameters")
            if kind in compare | {"$logic_not", "$reduce_or", "$reduce_and"}:
                if width != 1 or (kind in compare and len(wires["A"]) != len(wires["B"])):
                    raise ValueError("Comparison/reduction width mismatch")
            elif any(len(wires[n]) != width for n in ins if n != "S"):
                raise ValueError("Implicit extension/truncation is unsupported")
            if kind == "$mux" and len(wires["S"]) != 1: raise ValueError("Invalid mux selection")
            try: args = tuple(signal(wires[n]) for n in ins)
            except KeyError: continue
            if kind in binary: value = node(width, binary[kind], args)
            elif kind == "$not": value = node(width, "not", args)
            elif kind in ("$logic_not", "$reduce_or", "$reduce_and"):
                aw = len(wires["A"])
                constant = node(aw, "lit", value=2 ** aw - 1 if kind == "$reduce_and" else 0)
                value = node(1, "eq", (*args, constant))
                if kind == "$reduce_or": value = node(1, "not", (value,))
            elif kind == "$eq": value = node(1, "eq", args)
            elif kind == "$ne": value = node(1, "not", (node(1, "eq", args),))
            elif kind == "$gt": value = node(1, "lt", tuple(reversed(args)))
            elif kind == "$ge": value = node(1, "not", (node(1, "lt", args),))
            elif kind == "$lt": value = node(1, "lt", args)
            else: value = node(width, "mux", args)
            bind(wires["Y"], value)
            pending.remove((name, c))
            progressed = True
        if not progressed: raise ValueError("Undriven bits or combinational cycle")
    try:
        graph.next = {name: signal(bits) for name, bits in registers.items()}
        graph.outputs = {name: signal(ports[name]["bits"]) for name in OUTPUTS}
    except KeyError as error:
        raise ValueError("Undriven state or output bit") from error
    return graph


HEADER = """import Pinwheel.Hardware.Storage.BackendEmit
open Pinwheel.Hardware
open Pinwheel.Hardware.Loader hiding Register State
open Pinwheel.Hardware.Storage.Backend
namespace Pinwheel.Artifact.Backend
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
"""


def partitions(source: Graph, rtl: Graph, limit=None, *, successor, oracle):
    """Suggest acyclic proof partitions. Simulation never discharges a theorem."""
    ss, rs = source.signatures(1024), rtl.signatures(1024)
    candidates = defaultdict(list)
    for name, sig in rs.items(): candidates[sig].append(name)
    forced = {source.next[n]: rtl.next[n] for n in REGISTERS}
    forced.update({source.outputs[n]: rtl.outputs[n] for n in OUTPUTS})
    scuts, rcuts, pairs = {}, set(), []
    for sn, node in source.nodes.items():
        if limit is not None and len(pairs) >= limit: break
        if node.op in ("lit", "input", "reg"): continue
        scheduler = sn.startswith("v") and int(sn[1:]) > int(successor[1:])
        if sn in forced:
            rn = forced[sn]
        else:
            if len(set(ss[sn][1])) == 1: continue
            choices = candidates.get(ss[sn], [])
            if not choices: continue
            rn = min(choices, key=lambda n: (rtl.nodes[n].op != node.op, rtl.nodes[n].op in ("reg", "input")))
        variables, definitions, dependencies = {}, set(), set()
        allowed = set(rcuts)

        def variable(n):
            item = rtl.nodes[n]
            if item.op in ("input", "reg"):
                key = (item.width, item.op, item.value)
            else:
                used.add(n)
                key = (item.width, "rtl", n)
            if key not in variables: variables[key] = len(variables)
            return (item.width, "var", (), variables[key])

        def view(n, base):
            if n == base: return variable(base)
            item = rtl.nodes[n]
            definitions.add(f"RTL.{n}")
            return (item.width, item.op, tuple(view(a, base) for a in item.args), item.value)

        def expand(g, n, cuts, namespace, root=False):
            key_memo = (namespace, n, root)
            if key_memo in memo: return memo[key_memo]
            item = g.nodes[n]
            if item.op in ("reg", "input"): return variable(n)
            if not root and namespace == "Source" and n in scuts:
                index, matching, base = scuts[n]
                if base in allowed:
                    dependencies.add(index)
                    result = view(matching, base)
                    memo[key_memo] = result
                    return result
            if not root and namespace == "RTL" and n in allowed:
                return variable(n)
            definitions.add(f"{namespace}.{n}")
            result = (item.width, item.op, tuple(expand(g, child, cuts, namespace) for child in item.args), item.value)
            memo[key_memo] = result
            return result

        while True:
            variables, definitions, dependencies = {}, set(), set()
            memo, used = {}, set()
            left = expand(source, sn, scuts, "Source", root=True)
            lcuts = set(used)
            used = set()
            right = expand(rtl, rn, rcuts, "RTL", root=rn not in rcuts)
            rc = set(used)
            remove = lcuts ^ rc
            if not remove: break
            allowed -= remove
        sizes = {}
        def size(t):
            if id(t) not in sizes: sizes[id(t)] = 1 + sum(size(a) for a in t[2])
            return sizes[id(t)]
        pair = {"source": sn, "rtl": rn, "left": left, "right": right,
                "variables": tuple(variables), "definitions": sorted(definitions),
                "dependencies": sorted(dependencies), "size": size(left) + size(right)}
        if pair["size"] > 2000 and sn not in forced:
            continue
        if scheduler and not oracle(pair):
            if sn in forced:
                print(f"unproved endpoint suggestion {sn}: {pair['size']}", flush=True)
            continue
        idx = len(pairs)
        pairs.append(pair)
        if len(pairs) % 500 == 0: print(f"partitioned {len(pairs)} ({sn})", flush=True)
        base = rtl.views.get(rn, rn)
        scuts[sn] = (idx, rn, base)
        rcuts.add(base)
    return pairs


def smt_suggestion(pair):
    """Serialize a proposed local equality for an untrusted cut-selection query."""
    cache = {}
    lines = [f"(declare-fun x{j} () (_ BitVec {w}))"
             for j, (w, _, _) in enumerate(pair["variables"])]
    def go(t):
        w, op, args, value = t
        if op == "var": return f"x{value}"
        if id(t) in cache: return cache[id(t)]
        x = [go(a) for a in args]
        if op == "lit": expr = f"(_ bv{value} {w})"
        elif op == "slice": expr = f"((_ extract {value + w - 1} {value}) {x[0]})"
        elif op == "concat": expr = f"(concat {x[0]} {x[1]})"
        elif op == "not": expr = f"(bvnot {x[0]})"
        elif op in ("eq", "lt"):
            expr = f"(ite ({'=' if op == 'eq' else 'bvult'} {x[0]} {x[1]}) #b1 #b0)"
        elif op == "mux": expr = f"(ite (= {x[0]} #b1) {x[1]} {x[2]})"
        else: expr = f"(bv{op} {x[0]} {x[1]})"
        name = f"t{len(cache)}"
        cache[id(t)] = name
        lines.append(f"(define-fun {name} () (_ BitVec {w}) {expr})")
        return name
    lhs, rhs = go(pair["left"]), go(pair["right"])
    return "\n".join(["(set-logic QF_BV)", *lines,
                       f"(assert (not (= {lhs} {rhs})))", "(check-sat)"])


def cut_oracle(solver):
    """A solver answer can only propose a cut; generated Lean proves every cut."""
    def query(pair):
        result = subprocess.run([str(solver), "-in", "-T:3"], input=smt_suggestion(pair),
                                capture_output=True, text=True, timeout=5)
        return result.returncode == 0 and result.stdout.strip() == "unsat"
    return query


def add_storage_views(graph: Graph, source=None):
    """Proof hints for padding/expansion moved across multiplexers by CIRCT.

    These pure expressions do not change the imported next-state/output roots.
    """
    def add(width, op, args=(), value=None):
        name = f"view{len(graph.nodes)}"
        graph.nodes[name] = Node(width, op, args, value)
        return name
    zero1 = add(1, "lit", value=0)
    zero8 = add(8, "lit", value=0)
    zero35 = add(35, "lit", value=0)
    three = add(3, "lit", value=3)
    for name, n in list(graph.nodes.items()):
        if n.width == 5:
            graph.views[add(6, "concat", (zero1, name))] = name
        if n.width == 55:
            kind = add(3, "slice", (name,), 0)
            qualify = add(1, "eq", (kind, three))
            low = add(17, "slice", (name,), 0)
            hi12 = add(12, "slice", (name,), 17)
            hi38 = add(38, "slice", (name,), 17)
            q = add(64, "concat", (add(47, "concat", (zero35, hi12)), low))
            ordinary = add(64, "concat", (add(47, "concat", (add(39, "concat", (zero1, hi38)), zero8)), low))
            graph.views[add(64, "mux", (qualify, q, ordinary))] = name
    if source is not None:
        # Optimizers discard constant high bits. Propose their explicit wiring
        # again where sampled signatures suggest a match; Lean checks the match.
        candidates = defaultdict(list)
        for name, (width, samples) in graph.signatures(1024).items():
            candidates[samples].append((name, width))
        added = set()
        for width, samples in source.signatures(1024).values():
            if len(set(samples)) == 1: continue
            for name, smaller in candidates[samples]:
                if 0 < smaller < width and (name, width) not in added:
                    pad = add(width - smaller, "lit", value=0)
                    graph.views[add(width, "concat", (pad, name))] = name
                    added.add((name, width))


def render_tree(tree):
    width, op, args, value = tree
    if op == "var": return f"x{value}"
    return "(" + Graph.expression(None, Node(width, op, tuple(range(len(args))), value),
                                    lambda k: render_tree(args[k])) + ")"


def helper_source(pairs, limit=None):
    lines = ["import Lean.Elab.Command\nimport Pinwheel.Hardware.Readback.Boolean\n" + HEADER,
             "set_option linter.unusedSimpArgs false"]
    for k, p in enumerate(pairs[:limit]):
        variables = " ".join(f"(x{j} : BitVec {w})" for j, (w, _, _) in enumerate(p["variables"]))
        lines.append(f"theorem local_{k} {variables} :\n    {render_tree(p['left'])} = {render_tree(p['right'])} := by\n"
                     "  try simp only [BitVec.sub_eq_add_neg]\n"
                     "  all_goals first\n"
                     "  |\n"
                     "    all_goals bv_normalize\n"
                     "    all_goals first | omega | grind\n"
                     "    done\n"
                     "  | (simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ,\n"
                     "      BitVec.getElem_append, BitVec.getElem_extractLsb']; all_goals grind)\n")
        if k % 100 == 0: lines.append(f'run_cmd IO.eprintln "checked local {k}"')
    lines.append("end Pinwheel.Artifact.Backend")
    return "\n".join(lines) + "\n"


def links_source(source, rtl, pairs, helper_module, graph_module):
    lines = [f"import {helper_module}\nimport {graph_module}\n" + HEADER]
    def value(g, n, namespace):
        item = g.nodes[n]
        if item.op in ("input", "reg"):
            return "(" + g.expression(item, None) + ")"
        return f"({namespace}.{n} i s)"
    for k, p in enumerate(pairs):
        args = []
        for _, kind, name in p["variables"]:
            args.append(value(rtl, name, "RTL"))
        lhs, rhs = value(source, p["source"], "Source"), value(rtl, p["rtl"], "RTL")
        rewrites = p["definitions"] + [f"link_{j}" for j in p["dependencies"]]
        lines.append(f"theorem link_{k} (i : Values Machine.Input) (s : Values Register) :\n"
                     f"    {lhs} = {rhs} := by\n"
                     f"  simp only [{', '.join(rewrites)}]\n"
                     f"  all_goals first | exact (local_{k} {' '.join(args)}) | simpa only using (local_{k} {' '.join(args)})\n")
    lines.append("end Pinwheel.Artifact.Backend")
    return "\n".join(lines) + "\n"


def embeddings_source(source, cuts, raw_module, cut_module):
    """Small congruence proofs reconnect every abstract hint to its raw graph."""
    lines = [f"import {raw_module}\nimport {cut_module}\n" + HEADER]
    args = " ".join(f"(Source.{n} i s)" for n in cuts)
    for n, item in source.nodes.items():
        if item.op in ("input", "reg"): continue
        rewrites = [f"Hint.{n}"] + [f"embed_{c}" for c in item.args
            if c not in cuts and source.nodes[c].op not in ("input", "reg")]
        lines.append(f"theorem embed_{n} (i : Values Machine.Input) (s : Values Register) :\n"
                     f"    Hint.{n} i s {args} = Source.{n} i s := by\n"
                     f"  simp only [{', '.join(dict.fromkeys(rewrites))}]\n"
                     f"  all_goals first | rfl | simp only [Source.{n}]\n")
    lines.append("end Pinwheel.Artifact.Backend")
    return "\n".join(lines) + "\n"


def scope_source(source, names, cut_module):
    lines = [f"import {cut_module}\n" + HEADER,
             "set_option linter.unusedSimpArgs false"]
    for kind, name in names:
        n = (source.next if kind == "next" else source.outputs)[name]
        ctor = (REGISTERS if kind == "next" else OUTPUTS)[name][1]
        item = source.nodes[n]
        lhs = source.expression(item, None) if item.op in ("input", "reg") else (
            f"Hint.{n} i s (Readback.target.eval i s) (Readback.selected.eval i s) ix c d")
        lines.append(f"theorem hint_{kind}_{name} (i : Values Machine.Input) (s : Values Register)\n"
                     f"    (ix : BitVec 6) (c : BitVec 64) (d : BitVec 8) :\n"
                     f"    {lhs} = (body.{kind} ({ctor})).eval (WithWire.values (WithWire.values i c) d) s := by\n"
                     f"  simp only [body, Expr.eval_bind, feedFinal, fresh_correct, feed, coreRegF, Expr.eval]\n"
                     f"  rfl\n")
    lines.append("end Pinwheel.Artifact.Backend")
    return "\n".join(lines) + "\n"


def cuts_source(cuts, embeddings_module, pc_module):
    target, selected, index, successor, pc = cuts
    args = " ".join(f"(Source.{n} i s)" for n in cuts)
    header = f"import {embeddings_module}\nimport {pc_module}\n" + HEADER
    return header + f"""
theorem hint_target (i : Values Machine.Input) (s : Values Register)
    (a : BitVec 8) (b : BitVec 1) (ix : BitVec 6) (c : BitVec 64) (d : BitVec 8) :
    Hint.{target} i s a b ix c d = Readback.target.eval i s := by
  simp only [Readback.target, lift, Expr.eval_bind, Storage.Cache.target]
  rfl

theorem hint_selected (i : Values Machine.Input) (s : Values Register)
    (a : BitVec 8) (b : BitVec 1) (ix : BitVec 6) (c : BitVec 64) (d : BitVec 8) :
    Hint.{selected} i s a b ix c d = Readback.selected.eval i s := by
  simp only [Readback.selected, lift, Storage.Cache.liftExpr, Expr.eval_bind]
  rfl

theorem hint_index (i : Values Machine.Input) (s : Values Register)
    (a : BitVec 8) (b : BitVec 1) (ix : BitVec 6) (c : BitVec 64) (d : BitVec 8) :
    Hint.{index} i s a b ix c d = Readback.indexRead.eval (Readback.readInputs b a) s := by
  rfl

theorem hint_word (i : Values Machine.Input) (s : Values Register)
    (a : BitVec 8) (b : BitVec 1) (ix : BitVec 6) (c : BitVec 64) (d : BitVec 8) :
    Hint.{successor} i s a b ix c d = Readback.wordRead.eval (Readback.wordInputs b ix) s := by
  rfl

theorem source_target (i : Values Machine.Input) (s : Values Register) :
    Source.{target} i s = Readback.target.eval i s :=
  (embed_{target} i s).symm.trans (hint_target i s {args})

theorem source_selected (i : Values Machine.Input) (s : Values Register) :
    Source.{selected} i s = Readback.selected.eval i s :=
  (embed_{selected} i s).symm.trans (hint_selected i s {args})

theorem source_index (i : Values Machine.Input) (s : Values Register) :
    Source.{index} i s = Readback.indexRead.eval
      (Readback.readInputs (Readback.selected.eval i s) (Readback.target.eval i s)) s := by
  simpa only [source_target, source_selected] using
    (embed_{index} i s).symm.trans (hint_index i s {args})

theorem source_successor (i : Machine.Inputs) (s : State) :
    Source.{successor} i.values s.values = successor.eval i.values s.values := by
  have h := (embed_{successor} i.values s.values).symm.trans
    (hint_word i.values s.values {args.replace(' i s)', ' i.values s.values)')})
  simp only [source_selected, source_index] at h
  exact h.trans (Readback.read_correct i s)

theorem body_pc (i : Values Machine.Input) (s : Values Register) (c : BitVec 64) (d : BitVec 8) :
    (body.next (.core .pc)).eval (WithWire.values (WithWire.values i c) d) s =
      nextPC.eval (WithWire.values i c) s := by
  simp only [body, nextPC, Expr.eval_bind, feedFinal, fresh_correct, coreRegF, coreRegS, Expr.eval]

theorem source_pc (i : Values Machine.Input) (s : Values Register) :
    Source.{pc} i s = nextPC.eval (WithWire.values i (Source.{successor} i s)) s := by
  have h := (embed_{pc} i s).symm
  simp only [source_target, source_selected] at h
  exact (h.trans (hint_next_r_pc i s (Source.{index} i s) (Source.{successor} i s)
    (Source.{pc} i s))).trans (body_pc i s _ _)

end Pinwheel.Artifact.Backend
"""


def graph_value(graph, n, namespace, i="i", s="s"):
    item = graph.nodes[n]
    if item.op == "input": return f"{i} ({INPUTS[item.value][1]})"
    if item.op == "reg": return f"{s} ({REGISTERS[item.value][1]})"
    return f"{namespace}.{n} {i} {s}"


def model_source(rtl, graph_module):
    lines = [f"import {graph_module}\n" + HEADER]
    for kind, mapping in (("Step", rtl.next), ("Observe", rtl.outputs)):
        interface = REGISTERS if kind == "Step" else OUTPUTS
        result_type = "Register" if kind == "Step" else "Machine.Output"
        lines.append(f"def rtl{kind} (i : Values Machine.Input) (s : Values Register) : Values {result_type}")
        samples = [f"r_sample{k}" if kind == "Step" else f"sample{k}" for k in range(16)]
        banks = [f"r_bank{b}_{field}{k}" for b in (0, 1)
                 for field, count in (("word", 32), ("index", 256)) for k in range(count)] if kind == "Step" else []
        for name, (_, ctor) in interface.items():
            if name in samples or name in banks: continue
            lines.append(f"  | _, {ctor} => {graph_value(rtl, mapping[name], 'RTL')}")
        pattern = ".core (.sample k)" if kind == "Step" else ".core (.state (.sample k))"
        values = ", ".join(f"({graph_value(rtl, mapping[n], 'RTL')})" for n in samples)
        lines.append(f"  | _, {pattern} => (#[{values}])[k.val]'(by exact k.isLt)")
        if kind == "Step":
            for field, count in (("word", 32), ("index", 256)):
                lines.append(f"  | _, .{field} b k => if b then")
                for bank in (1, 0):
                    values = ", ".join(f"({graph_value(rtl, mapping[f'r_bank{bank}_{field}{k}'], 'RTL')})" for k in range(count))
                    lines.append(f"      (#[{values}])[k.toNat]'(by exact k.isLt)" + (" else" if bank == 1 else ""))
    lines.append("end Pinwheel.Artifact.Backend")
    return "\n".join(lines) + "\n"


def endpoints_source(source, rtl, pairs, cuts, names, imports, *, netlist_definitions="netlist"):
    lines = ["\n".join(f"import {m}" for m in imports) + "\n" + HEADER,
             "set_option linter.unusedSimpArgs false"]
    matches = {p["source"]: (k, p["rtl"]) for k, p in enumerate(pairs)}
    for kind, name in names:
        n = (source.next if kind == "next" else source.outputs)[name]
        rn = (rtl.next if kind == "next" else rtl.outputs)[name]
        ctor = (REGISTERS if kind == "next" else OUTPUTS)[name][1]
        lhs = graph_value(source, n, "Source", "i.values", "s.values")
        expr = "step" if kind == "next" else "observe"
        model = "rtlStep" if kind == "next" else "rtlObserve"
        args = " ".join(f"(Source.{n} i.values s.values)" for n in list(cuts)[2:])
        lines.append(f"theorem source_{kind}_{name} (i : Machine.Inputs) (s : State) :\n"
                     f"    {lhs} = netlist.{expr} i.values s.values ({ctor}) := by")
        if source.nodes[n].op in ("input", "reg"):
            lines.append(f"  have h := hint_{kind}_{name} i.values s.values {args}")
        else:
            lines.append(f"  have h := (embed_{n} i.values s.values).symm\n"
                         f"  simp only [source_target, source_selected] at h\n"
                         f"  have h := h.trans (hint_{kind}_{name} i.values s.values {args})")
        lines.append(f"  simpa only [source_target, source_selected, source_pc, source_successor, {netlist_definitions}, Netlist.{expr}, Circuit.{expr}] using h\n")
        lines.append(f"theorem rtl_{kind}_{name} (i : Machine.Inputs) (s : State) :\n"
                     f"    {model} i.values s.values ({ctor}) = netlist.{expr} i.values s.values ({ctor}) := by\n"
                     f"  change ({graph_value(rtl, rn, 'RTL', 'i.values', 's.values')}) = _")
        if n in matches:
            idx, matched = matches[n]
            if rn != matched: raise ValueError(f"Endpoint {name} has a different cut; a separate proof is required")
            lines.append(f"  exact (link_{idx} i.values s.values).symm.trans (source_{kind}_{name} i s)\n")
        else:
            lines.append(f"  exact source_{kind}_{name} i s\n")
    lines.append("end Pinwheel.Artifact.Backend")
    return "\n".join(lines) + "\n"


def proof_source(imports, *, next_theorem="Storage.Backend.netlist_next",
                 output_theorem="Storage.Backend.netlist_output"):
    lines = ["\n".join(f"import {m}" for m in imports) + "\n" + HEADER]
    def finite(indent, model, operation, ctor, names, bitvec=False):
        n = len(names)
        term = "(fun j => Fin.elim0 j)"
        for name in reversed(names):
            term = f"(Fin.cases (rtl_{operation}_{name} i s) {term})"
        expression = "step" if operation == "next" else "observe"
        lines.extend([
            f"{indent}have h : ∀ j : Fin {n}, {model} i.values s.values ({ctor}) =",
            f"{indent}    netlist.{expression} i.values s.values ({ctor}) := {term}",
            f"{indent}exact h {'k.toFin' if bitvec else 'k'}"])

    lines.append("theorem model_next (i : Machine.Inputs) (s : State) (r : Register w) :\n"
                 "    rtlStep i.values s.values r = netlist.step i.values s.values r := by\n"
                 "  cases r with\n  | control r =>\n    cases r")
    lines.append("    all_goals first | " + " | ".join(f"exact rtl_next_r_loader_{n} i s" for n in ("active", "valid", "pending", "cursor")))
    lines.append("  | core r =>\n    cases r with")
    for ctor, label in (("mode", "mode"), ("pc", "pc"), ("remaining", "remaining"),
                        ("waitLeft", "wait_left"), ("levels", "levels"), ("enabled", "enabled")):
        lines.append(f"    | {ctor} => exact rtl_next_r_{label} i s")
    lines.append("    | sample k =>")
    finite("      ", "rtlStep", "next", ".core (.sample j)", [f"r_sample{k}" for k in range(16)])
    for field, count in (("word", 32), ("index", 256)):
        lines.append(f"  | {field} b k =>\n    cases b with")
        for bank in (0, 1):
            b = "true" if bank else "false"
            lines.append(f"    | {b} =>")
            finite("      ", "rtlStep", "next", f".{field} {b} (BitVec.ofFin j)",
                   [f"r_bank{bank}_{field}{k}" for k in range(count)], True)
    for field in ("idle", "last"):
        lines.append(f"  | {field} b =>\n    cases b with\n"
                     f"    | false => exact rtl_next_r_bank0_{field} i s\n"
                     f"    | true => exact rtl_next_r_bank1_{field} i s")
    lines.append("  | current => exact rtl_next_r_cached_word i s\n")

    lines.append("theorem model_output (i : Machine.Inputs) (s : State) (o : Machine.Output w) :\n"
                 "    rtlObserve i.values s.values o = netlist.observe i.values s.values o := by\n"
                 "  cases o with\n  | control o =>\n    cases o with\n    | state r =>\n      cases r")
    lines.append("      all_goals first | " + " | ".join(f"exact rtl_output_loader_{n} i s" for n in ("active", "valid", "pending", "cursor")))
    for field in ("push", "commit", "start", "rejected"):
        lines.append(f"    | {field} => exact rtl_output_loader_{field} i s")
    lines.append("  | core o =>\n    cases o with\n    | state r =>\n      cases r with")
    for ctor, label in (("mode", "mode"), ("pc", "pc"), ("remaining", "remaining"),
                        ("waitLeft", "wait_left"), ("levels", "levels"), ("enabled", "enabled")):
        lines.append(f"      | {ctor} => exact rtl_output_{label} i s")
    lines.append("      | sample k =>")
    finite("        ", "rtlObserve", "output", ".core (.state (.sample j))", [f"sample{k}" for k in range(16)])
    for ctor, label in (("readA", "read_a"), ("readB", "read_b"), ("busy", "busy")):
        lines.append(f"    | {ctor} => exact rtl_output_{label} i s")
    lines.append("""
def rtlComponent : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  ⟨fun i s => rtlStep i.values s, fun i s => rtlObserve i.values s⟩

def rtlRefinement : Timed.Refinement rtlComponent Storage.Backend.component where
  Rel := fun r s => @r = @s.values
  step := fun i r s h => by
    subst r
    exact funext fun w => funext fun p =>
      (model_next i s p).trans (Storage.Backend.netlist_next i s p)
  observe := fun i r s h => by
    subst r
    exact funext fun w => funext fun p =>
      (model_output i s p).trans (Storage.Backend.netlist_output i s p)

def completeRefinement : Timed.Refinement rtlComponent referenceComponent :=
  rtlRefinement.trans Storage.Backend.refinement

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    rtlComponent.trace s.values inputs = referenceComponent.trace s.reference.machine inputs :=
  completeRefinement.trace_eq s.values s.reference.machine ⟨s, rfl, h, rfl⟩ inputs

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    rtlComponent.trace (rtlStep i.values s.values) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs := by
  have hn : (rtlStep i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
    funext fun w => funext fun r => (model_next i s r).trans (Storage.Backend.netlist_next i s r)
  rw [hn, ← initialize_machine_next i s hi]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs

#print axioms model_next
#print axioms model_output
#print axioms initialized_trace
end Pinwheel.Artifact.Backend
""")
    return ("\n".join(lines) + "\n").replace("Storage.Backend.netlist_next", next_theorem).replace(
        "Storage.Backend.netlist_output", output_theorem)
