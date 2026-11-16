"""Generic stream artifact certificates using the existing restricted RTL importer.

Yosys and the JSON adapter remain trusted interpretation boundaries. Solver and
simulation results only suggest cuts; Lean checks every generated equality.
No Pinwheel protocol register map or proof is assumed by this adapter.
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


def importer(descriptor):
    # An isolated module instance prevents descriptor changes leaking into other
    # existing readback clients in the same Python process.
    name = "_stream_backend_readback"
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts/backend_readback.py")
    rb = importlib.util.module_from_spec(spec)
    sys.modules[name] = rb
    spec.loader.exec_module(rb)
    rb.TOP = "pinwheel_stream"
    rb.INPUTS = {p["name"]: (p["width"], ["reset", "valid", "ready", "payload"][p["index"]])
                 for p in descriptor["inputs"]}
    rb.OUTPUTS = {p["name"]: (p["width"], ["inReady", "outValid", "outData"][p["index"]])
                  for p in descriptor["outputs"]}
    rb.REGISTERS = {"r_" + p["name"]: (p["width"],
        f"reg_{p['index']}")
        for p in descriptor["registers"]}
    rb.HEADER = """import Design
open Pinwheel.Hardware Pinwheel.Hardware.Stream
namespace Pinwheel.StreamArtifact
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
"""
    return rb


def prepare_json(original: Path, destination: Path, descriptor, hierarchical: bool):
    document = json.loads(original.read_text())
    if hierarchical:
        module = document["modules"]["pinwheel_stream"]
        for p, actual in zip(descriptor["registers"], descriptor["hierarchical_registers"], strict=True):
            canonical = "r_" + p["name"]
            if actual not in module["netnames"]:
                raise ValueError(f"Missing hierarchical state {actual}")
            if canonical in module["netnames"]:
                raise ValueError(f"Ambiguous canonical state {canonical}")
            module["netnames"][canonical] = module["netnames"][actual]
    destination.write_text(json.dumps(document))


def generate(directory: Path, configuration, descriptor, hints: Path, rtl: Path, solver: Path,
             *, design_expression=None, design_import="Pinwheel.Hardware.Stream.Normalize"):
    rb = importer(descriptor)
    source, actual = rb.read_hints(hints), rb.read_rtl(rtl)
    pairs = rb.partitions(source, actual, successor="v-1", oracle=rb.cut_oracle(solver))
    w, d, stages = configuration
    wi = next(p["width"] for p in descriptor["inputs"] if p["index"] == 3)
    wo = next(p["width"] for p in descriptor["outputs"] if p["index"] == 2)
    design_expression = design_expression or f"adderDesign {w} {d} {stages - 1} (by decide +kernel)"
    design = f"""import {design_import}
import Pinwheel.Hardware.Stream.Normalize
open Pinwheel.Hardware Pinwheel.Hardware.Stream
namespace Pinwheel.StreamArtifact
set_option backward.isDefEq.respectTransparency false
abbrev baseComponent := ({design_expression}).flatten
abbrev component := baseComponent.normalized
"""
    for p in descriptor["registers"]:
        design += (f"def reg_{p['index']} : component.Register {p['width']} := "
                   f"(component.registers.signal ⟨{p['index']}, by decide +kernel⟩).2\n")
    (directory / "Design.lean").write_text(design + "end Pinwheel.StreamArtifact\n")

    def adapt(text):
        return (text.replace("Values Machine.Input", f"Values (In {wi})")
                .replace("Values Register", "Values component.Register")
                .replace("end Pinwheel.Artifact.Backend", "end Pinwheel.StreamArtifact"))

    def write(name, body):
        (directory / f"{name}.lean").write_text(adapt(body))

    write("Graphs", rb.HEADER + source.definitions("Source") + actual.definitions("RTL") +
          "end Pinwheel.StreamArtifact\n")
    write("LocalProofs", rb.helper_source(pairs))
    write("Links", rb.links_source(source, actual, pairs, "LocalProofs", "Graphs"))

    def value(graph, node, namespace):
        item = graph.nodes[node]
        return graph.expression(item, None) if item.op in ("input", "reg", "lit") else f"{namespace}.{node} i s"

    matches = {(p["source"], p["rtl"]): k for k, p in enumerate(pairs)}
    lines = ["import Links\n" + rb.HEADER]
    endpoint_count = 0
    tables = {}
    for kind, names, constructors in (("next", source.next, rb.REGISTERS), ("output", source.outputs, rb.OUTPUTS)):
        entries = []
        for name, sn in names.items():
            rn = (actual.next if kind == "next" else actual.outputs)[name]
            ctor = constructors[name][1]
            lhs, rhs = value(source, sn, "Source"), value(actual, rn, "RTL")
            operation = "step" if kind == "next" else "observe"
            stem = f"{kind}_{endpoint_count}"
            parameters = f"(i : Values (In {wi})) (s : Values component.Register)"
            lines.append(f"theorem hint_{stem} {parameters} :\n"
                         f"  {lhs} = component.circuit.{operation} i s ({ctor}) := by rfl\n")
            index = matches.get((sn, rn))
            proof = f"exact link_{index} i s" if index is not None else "rfl"
            lines.append(f"theorem rtl_{stem} {parameters} :\n"
                         f"  {rhs} = component.circuit.{operation} i s ({ctor}) := by\n"
                         f"  have h : {lhs} = {rhs} := by {proof}\n"
                         f"  exact h.symm.trans (hint_{stem} i s)\n")
            entries.append((rhs, f"rtl_{stem}"))
            endpoint_count += 1
        tables[kind] = entries
    parameters = f"(i : Values (In {wi})) (s : Values component.Register)"
    for kind, descriptor_name, operation, result_type in (
            ("next", "component.registers", "step", "component.Register"),
            ("output", f"(outputPorts {wo}).interface", "observe", f"Out {wo}")):
        entries = tables[kind]
        n = len(entries)
        lines.append(f"def {kind}Table {parameters} : (k : Fin ({descriptor_name}).size) → "
                     f"BitVec (({descriptor_name}).signal k).1\n")
        for index, (expression, _) in enumerate(entries):
            lines.append(f"  | ⟨{index}, _⟩ => {expression}\n")
        lines.append(f"  | ⟨k + {n}, h⟩ => False.elim (by change k + {n} < {n} at h; omega)\n")
        lines.append(f"theorem {kind}Table_correct {parameters} (k : Fin ({descriptor_name}).size) :\n"
                     f"  {kind}Table i s k = component.circuit.{operation} i s (({descriptor_name}).signal k).2 := by\n"
                     f"  match k with\n")
        for index, (_, theorem) in enumerate(entries):
            lines.append(f"  | ⟨{index}, _⟩ => exact {theorem} i s\n")
        lines.append(f"  | ⟨k + {n}, h⟩ => exact False.elim (by change k + {n} < {n} at h; omega)\n")
        lines.append(f"def rtl_{operation} {parameters} : Values ({result_type}) :=\n"
                     f"  assemble ({descriptor_name}) ({kind}Table i s)\n"
                     f"theorem rtl_{operation}_eq {parameters} :\n"
                     f"  (fun {{b : Nat}} (p : {result_type} b) => rtl_{operation} i s p) = "
                     f"(fun {{b : Nat}} (p : {result_type} b) => component.circuit.{operation} i s p) :=\n"
                     f"  assemble_eq _ _ _ ({kind}Table_correct i s)\n")
    lines.append(f"""
def rtlSimulator : Timed.Component (Input (BitVec {wi}))
    (Values component.Register) (Output (BitVec {wo})) :=
  ⟨fun i s => rtl_step (inputValues i) s,
   fun i s => decodeOutput (rtl_observe (inputValues i) s)⟩
theorem rtlSimulator_eq : rtlSimulator = component.simulator := by
  simp only [rtlSimulator, Certified.simulator, rtl_step_eq, rtl_observe_eq]
theorem rtl_transactions (inputs : List (Input (BitVec {wi}))) :
    let actual := runHistory rtlSimulator (component.encode component.initial) {{}} inputs
    let model := runHistory component.machine.component component.initial {{}} inputs
    actual.2.inputs.map component.function = actual.2.outputs ++ component.contract.pending model.1 := by
  rw [rtlSimulator_eq]
  exact component.simulator_transactions inputs

def rtlRawSimulator : Timed.Component (Values (In {wi}))
    (Values component.Register) (Output (BitVec {wo})) :=
  ⟨fun i s => rtl_step i s, fun i s => decodeOutput (rtl_observe i s)⟩
theorem rtlRawSimulator_eq : rtlRawSimulator = baseComponent.rawSimulator := by
  simp only [rtlRawSimulator, Certified.rawSimulator, rtl_step_eq, rtl_observe_eq]
  rfl
/-- Actual imported RTL from arbitrary register bits, after a cold-reset edge,
for arbitrary digital inputs, including invalid payload bits. -/
theorem rtl_initialized_trace (initial : Values component.Register)
    (resetInput : Values (In {wi})) (hr : resetInput reset = 1)
    (inputs : List (Values (In {wi}))) :
    rtlRawSimulator.trace (rtlRawSimulator.step resetInput initial) inputs =
      baseComponent.rawModel.trace baseComponent.initial inputs := by
  rw [rtlRawSimulator_eq]
  exact baseComponent.raw_initialized_trace initial resetInput hr inputs
""")
    lines.append("end Pinwheel.StreamArtifact\n")
    write("Proof", "\n".join(lines))
    audit = (ROOT / "test/StreamAudit.lean").read_text()
    audit = audit.replace("import Pinwheel.Hardware.Stream.Timing", "import Proof\nimport Pinwheel.Hardware.Stream.Timing")
    audit = audit.replace('name.toString.startsWith "Pinwheel.Hardware.Stream."',
        '(name.toString.startsWith "Pinwheel.Hardware.Stream." || name.toString.startsWith "Pinwheel.StreamArtifact.")')
    write("Audit", audit)
    return ["Design", "Graphs", "LocalProofs", "Links", "Proof", "Audit"], {
        "local_equalities": len(pairs), "endpoints": endpoint_count,
        "source_nodes": len(source.nodes), "rtl_nodes": len(actual.nodes)}
