"""Fail-closed interpretation of the countdown's Yosys word-level JSON.

This adapter and Yosys's Verilog frontend are trusted parsers. The resulting
transition equality is checked by Lean's kernel, not accepted from this script.
Only the observed unsigned, same-width primitives and two positive-edge DFFs
are supported. There are no black boxes, implicit extensions, or X coercions.
"""
import json
from pathlib import Path


def interpret(path: Path) -> str:
    modules = json.loads(path.read_text())["modules"]
    if set(modules) != {"pinwheel_countdown"}:
        raise ValueError("Expected exactly the countdown module")
    m = modules["pinwheel_countdown"]
    if m.get("memories") or any(m.get("attributes", {}).get(k, "0").strip("0")
                                for k in ("blackbox", "whitebox")):
        raise ValueError("Unsupported memory or black box")
    expected = {"clk": ("input", 1), "reset": ("input", 1), "load": ("input", 1),
                "duration": ("input", 8), "remaining": ("output", 8),
                "active": ("output", 1), "boundary": ("output", 1)}
    ports = m["ports"]
    if {n: (p["direction"], len(p["bits"])) for n, p in ports.items()} != expected:
        raise ValueError("Changed port contract")
    if any("init" in n.get("attributes", {}) for n in m.get("netnames", {}).values()):
        raise ValueError("Implicit register initialization is unsupported")
    known = {}
    driven = set()

    def bind(bits, name):
        if not bits or any(type(b) is not int or b in driven for b in bits) or len(set(bits)) != len(bits):
            raise ValueError("Invalid or multiply driven bits")
        driven.update(bits)
        known[tuple(bits)] = name

    for p, expression in (("reset", "BitVec.ofBool i.reset"), ("load", "BitVec.ofBool i.load"),
                          ("duration", "i.duration"), ("remaining", "s.remaining"), ("active", "s.active")):
        bind(ports[p]["bits"], expression)
    clock = ports["clk"]["bits"][0]
    if type(clock) is not int or clock in driven:
        raise ValueError("Clock must be a distinct input wire")
    driven.add(clock)

    def signal(bits):
        key = tuple(bits)
        if key in known:
            return f"({known[key]})"
        if bits and all(b in ("0", "1") for b in bits):
            return f"({int(''.join(reversed(bits)), 2)}#{len(bits)})"
        raise KeyError(key)

    registers, pending = {}, []
    for name, c in m["cells"].items():
        if c["type"] != "$dff":
            pending.append((name, c))
            continue
        p, wires = c["parameters"], c["connections"]
        if (set(p) != {"CLK_POLARITY", "WIDTH"} or int(p["CLK_POLARITY"], 2) != 1
                or set(wires) != {"CLK", "D", "Q"} or wires["CLK"] != ports["clk"]["bits"]):
            raise ValueError("Unsupported register clock/parameters")
        matches = [n for n in ("remaining", "active") if wires["Q"] == ports[n]["bits"]]
        if len(matches) != 1 or matches[0] in registers or len(wires["D"]) != int(p["WIDTH"], 2):
            raise ValueError("Changed state mapping")
        if len(wires["Q"]) != int(p["WIDTH"], 2):
            raise ValueError("Register width mismatch")
        registers[matches[0]] = wires["D"]
    if set(registers) != {"remaining", "active"}:
        raise ValueError("Missing countdown registers")
    lines = []
    while pending:
        progressed = False
        for name, c in pending[:]:
            kind, wires, p = c["type"], c["connections"], c["parameters"]
            binary = {"$and": "&&&", "$or": "|||", "$xor": "^^^", "$sub": "-"}
            unary = {"$not", "$logic_not"}
            if kind not in binary and kind not in unary and kind not in {"$eq", "$mux"}:
                raise ValueError(f"Unsupported cell {kind}")
            ins = ["A", "B", "S"] if kind == "$mux" else ["A"] if kind in unary else ["A", "B"]
            if set(wires) != {*ins, "Y"}:
                raise ValueError("Unexpected cell ports")
            width = len(wires["Y"])
            expected_params = {"WIDTH": width} if kind == "$mux" else {
                "A_SIGNED": 0, "A_WIDTH": len(wires["A"]), "Y_WIDTH": width,
                **({"B_SIGNED": 0, "B_WIDTH": len(wires["B"])} if "B" in ins else {})}
            if {k: int(v, 2) for k, v in p.items()} != expected_params:
                raise ValueError("Unsupported signedness/parameters")
            if kind in {"$eq", "$logic_not"}:
                if width != 1 or (kind == "$eq" and len(wires["A"]) != len(wires["B"])):
                    raise ValueError("Comparison width mismatch")
            elif any(len(wires[n]) != width for n in ins if n != "S"):
                raise ValueError("Implicit extension/truncation is unsupported")
            if kind == "$mux" and len(wires["S"]) != 1:
                raise ValueError("Invalid mux selection")
            try:
                v = {n: signal(wires[n]) for n in ins}
            except KeyError:
                continue
            if kind in binary:
                expression = f'{v["A"]} {binary[kind]} {v["B"]}'
            elif kind == "$not":
                expression = f'~~~{v["A"]}'
            elif kind == "$logic_not":
                expression = f'BitVec.ofBool (decide ({v["A"]} = 0))'
            elif kind == "$eq":
                expression = f'BitVec.ofBool (decide ({v["A"]} = {v["B"]}))'
            else:
                expression = f'if {v["S"]} = 1 then {v["B"]} else {v["A"]}'
            var = f"v{len(lines)}"
            lines.append(f"  let {var} : BitVec {width} := {expression}")
            bind(wires["Y"], var)
            pending.remove((name, c))
            progressed = True
        if not progressed:
            raise ValueError("Undriven bits, unsupported bus wiring, or combinational cycle")
    remaining, active = (signal(registers[n]) for n in ("remaining", "active"))
    boundary = signal(ports["boundary"]["bits"])
    return "\n".join(lines + [f"  (⟨{remaining}, {active}⟩, (s, decide ({boundary} = 1)))"])


def lean_source(path: Path) -> str:
    return '''import Pinwheel.Hardware.CountdownContract
open Pinwheel.Hardware
open Pinwheel.Hardware.Countdown
namespace Pinwheel.Artifact.Countdown
def model (i : Inputs) (s : State) : State × (State × Bool) :=
''' + interpret(path) + '''

theorem model_correct (i : Inputs) (s : State) : model i s = (tick i s, observations i s) := by
  cases hr : i.reset <;> cases hl : i.load
  all_goals simp [model, tick, observations, boundary, circuit, progressing, nonzero,
    Circuit.step, Circuit.observe, Expr.eval, Inputs.values, State.values, BitVec.and_assoc, hr, hl]
  all_goals bv_normalize
  done

theorem trace_correct (s : State) (inputs : List Inputs) :
    (Timed.Component.mk (fun i s => (model i s).1) (fun i s => (model i s).2)).trace s inputs =
      component.trace s inputs :=
  artifact_trace _ _ (fun i s => congrArg Prod.fst (model_correct i s))
    (fun i s => congrArg Prod.snd (model_correct i s)) s inputs

#print axioms model_correct
#print axioms trace_correct
end Pinwheel.Artifact.Countdown
'''
