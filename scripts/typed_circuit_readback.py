"""Complete typed-interface certificates using the restricted Pinwheel importer.

The profile is trusted Lean source configuration. RTL JSON and source hints are
parsed fail-closed; generated endpoint equalities are checked by Lean. Yosys and
the JSON interpretation remain outside the kernel's trust boundary.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
HEADER = """import Design
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
"""


def source_paths():
    return (
        Path(__file__).resolve(),
        ROOT / "scripts/backend_readback.py",
        ROOT / "Pinwheel/Hardware/Artifact.lean",
        ROOT / "Pinwheel/Hardware/Readback/Boolean.lean",
    )


def validate_descriptor(descriptor):
    if not isinstance(descriptor.get("module"), str) or not IDENTIFIER.fullmatch(descriptor["module"]):
        raise ValueError("Invalid top module name")
    names = {"clk"}
    for kind in ("inputs", "registers", "outputs"):
        ports = descriptor.get(kind)
        if not isinstance(ports, list):
            raise ValueError(f"Missing typed {kind} enumeration")
        for index, port in enumerate(ports):
            if not isinstance(port, dict):
                raise ValueError("Malformed port")
            name, width = port.get("name"), port.get("width")
            if not isinstance(name, str) or not IDENTIFIER.fullmatch(name) or name in names:
                raise ValueError(f"Invalid or duplicate signal: {name}")
            ordinal = port.get("index", index)
            if type(width) is not int or width <= 0 or type(ordinal) is not int or ordinal != index:
                raise ValueError(f"Invalid width or enumeration index: {name}")
            if kind == "registers" and (not isinstance(port.get("reference", "r_" + name), str) or
                    not IDENTIFIER.fullmatch(port.get("reference", "r_" + name))):
                raise ValueError(f"Invalid register reference: {name}")
            names.add(name)
    references = [p.get("reference", "r_" + p["name"]) for p in descriptor["registers"]]
    if len(set(references)) != len(references):
        raise ValueError("Duplicate register references")
    external = {p["name"] for kind in ("inputs", "outputs") for p in descriptor[kind]} | {"clk", "clock"}
    if set(references) & external:
        raise ValueError("Register references alias an external port or clock")
    # The reused restricted importer reserves these internal SSA node names.
    if any(re.fullmatch(r"[nv][0-9]+", name) or name == "clock"
           for name in [p["name"] for p in descriptor["inputs"]] + references):
        raise ValueError("Signal aliases a reserved importer node name")


def importer(descriptor):
    validate_descriptor(descriptor)
    name = "_typed_circuit_backend_readback"
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts/backend_readback.py")
    rb = importlib.util.module_from_spec(spec)
    sys.modules[name] = rb
    spec.loader.exec_module(rb)
    rb.TOP = descriptor["module"]
    rb.INPUTS = {p["name"]: (p["width"], f"input_{k}") for k, p in enumerate(descriptor["inputs"])}
    rb.OUTPUTS = {p["name"]: (p["width"], f"output_{k}") for k, p in enumerate(descriptor["outputs"])}
    rb.REGISTERS = {p.get("reference", "r_" + p["name"]): (p["width"], f"register_{k}")
                    for k, p in enumerate(descriptor["registers"])}
    rb.HEADER = HEADER
    return rb


def local_proofs(rb, pairs):
    lines = ["import Lean.Elab.Command\nimport Pinwheel.Hardware.Readback.Boolean\n" + HEADER,
             "set_option linter.unusedSimpArgs false"]
    for k, pair in enumerate(pairs):
        variables = " ".join(f"(x{j} : BitVec {w})" for j, (w, _, _) in enumerate(pair["variables"]))
        lines.append(f"theorem local_{k} {variables} :\n"
                     f"    {rb.render_tree(pair['left'])} = {rb.render_tree(pair['right'])} := by\n"
                     "  try simp only [BitVec.sub_eq_add_neg, Pinwheel.Hardware.Readback.zero_lt_bit]\n"
                     "  all_goals first\n"
                     "  | rfl\n"
                     "  |\n"
                     "    all_goals bv_normalize\n"
                     "    all_goals first | omega | grind\n"
                     "    done\n"
                     "  | (simp [Pinwheel.Hardware.Readback.eq_bits, Fin.forall_fin_succ,\n"
                     "      BitVec.getElem_append, BitVec.getElem_extractLsb']; all_goals grind)\n")
        if sum(w for w, _, _ in pair["variables"]) <= 8:
            names = " ".join(f"x{j}" for j in range(len(pair["variables"])))
            # Kernel reduction closes small comparison/Boolean identities whose
            # arithmetic and bitwise normal forms otherwise need a bridge.
            lines.append(f"  | ({'revert ' + names + '; ' if names else ''}decide +kernel)\n")
        if k % 100 == 0:
            lines.append(f'run_cmd IO.eprintln "checked local {k}"')
    lines.append("end Pinwheel.TypedArtifact\n")
    return "\n".join(lines)


def generate(directory: Path, descriptor, hints: Path, rtl: Path, solver: Path, *, profile: str,
             interface_checks: str = ""):
    """Profile defines Input/Register/Output, circuit, inputs/registers/outputs.

    Each descriptor must have the corresponding Interface type. Source-hint
    endpoint proofs must reduce to the declared circuit by rfl, so metadata
    cannot silently substitute a different circuit or omit a typed endpoint.
    A trusted client can add binding assertions checked in the design module.
    The returned certificate concerns every bit, including unreachable states.
    """
    rb = importer(descriptor)
    source, actual = rb.read_hints(hints), rb.read_rtl(rtl)
    pairs = rb.partitions(source, actual, successor="v-1", oracle=rb.cut_oracle(solver))
    matches = {(p["source"], p["rtl"]) for p in pairs}
    for left, right in [(source.next[name], actual.next[name]) for name in rb.REGISTERS] + [
            (source.outputs[name], actual.outputs[name]) for name in rb.OUTPUTS]:
        if (left, right) not in matches:
            # A suggested cut can erase correlations needed at an endpoint.
            # Fall back to its complete expressions, still proved by Lean.
            variables, definitions = {}, set()

            def expand(graph, name, namespace):
                node = graph.nodes[name]
                if node.op in ("input", "reg"):
                    key = (node.width, node.op, node.value)
                    if key not in variables:
                        variables[key] = len(variables)
                    return node.width, "var", (), variables[key]
                definitions.add(f"{namespace}.{name}")
                return node.width, node.op, tuple(expand(graph, arg, namespace) for arg in node.args), node.value

            lhs, rhs = expand(source, left, "Source"), expand(actual, right, "RTL")
            pairs.append({"source": left, "rtl": right, "variables": list(variables),
                          "definitions": sorted(definitions), "dependencies": [], "left": lhs, "right": rhs})
            matches.add((left, right))
    # Imports belong before the namespace; profiles put all imports first.
    lines = profile.splitlines()
    imports = [line for line in lines if line.startswith("import ")]
    body = [line for line in lines if not line.startswith("import ")]
    design = "\n".join(imports) + "\nimport Pinwheel.Hardware.Artifact\n"
    design += "open Pinwheel.Hardware\nnamespace Pinwheel.TypedArtifact\n"
    design += "set_option backward.isDefEq.respectTransparency false\n" + "\n".join(body) + "\n"
    for kind, typ, stem in (("inputs", "Input", "input"), ("registers", "Register", "register"),
                            ("outputs", "Output", "output")):
        design += f"example : ({kind} : Interface {typ}).size = {len(descriptor[kind])} := by decide +kernel\n"
        for index, port in enumerate(descriptor[kind]):
            design += (f"def {stem}_{index} : {typ} {port['width']} := by with_unfolding_all exact "
                       f"({kind}.signal ⟨{index}, by decide +kernel⟩).2\n")
            label = f'{kind}.label {stem}_{index}'
            expected = port["name"]
            if kind == "registers":
                label = f'"r_" ++ ({label})'
                expected = port.get("reference", "r_" + expected)
            design += f'example : {label} = "{expected}" := by decide +kernel\n'
    (directory / "Design.lean").write_text(design + interface_checks + "\nend Pinwheel.TypedArtifact\n")

    def write(name, text):
        text = text.replace("Values Machine.Input", "Values Input")
        text = text.replace("end Pinwheel.Artifact.Backend", "end Pinwheel.TypedArtifact")
        (directory / f"{name}.lean").write_text(text)

    write("Graphs", HEADER + source.definitions("Source") + actual.definitions("RTL") +
          "end Pinwheel.TypedArtifact\n")
    write("LocalProofs", local_proofs(rb, pairs))
    write("Links", rb.links_source(source, actual, pairs, "LocalProofs", "Graphs"))

    def value(graph, name, namespace):
        node = graph.nodes[name]
        return graph.expression(node, None) if node.op in ("input", "reg", "lit") else f"{namespace}.{name} i s"

    matches = {(p["source"], p["rtl"]): k for k, p in enumerate(pairs)}
    lines = ["import Links\n" + HEADER]
    parameters = "(i : Values Input) (s : Values Register)"
    endpoint_count = 0
    for kind, mapping, constructors, desc, typ, operation in (
            ("next", source.next, rb.REGISTERS, "registers", "Register", "step"),
            ("output", source.outputs, rb.OUTPUTS, "outputs", "Output", "observe")):
        entries = []
        # Descriptor order, never an incidental parser or dictionary order.
        for name, (_, ctor) in constructors.items():
            sn, rn = mapping[name], (actual.next if kind == "next" else actual.outputs)[name]
            lhs, rhs = value(source, sn, "Source"), value(actual, rn, "RTL")
            stem = f"{kind}_{len(entries)}"
            lines.append(f"theorem hint_{stem} {parameters} :\n"
                         f"  {lhs} = circuit.{operation} i s {ctor} := by rfl\n")
            index = matches.get((sn, rn))
            proof = f"exact link_{index} i s" if index is not None else "rfl"
            lines.append(f"theorem rtl_{stem} {parameters} :\n"
                         f"  {rhs} = circuit.{operation} i s {ctor} := by\n"
                         f"  have h : {lhs} = {rhs} := by {proof}\n"
                         f"  exact h.symm.trans (hint_{stem} i s)\n")
            entries.append((rhs, f"rtl_{stem}"))
        size = len(entries)
        endpoint_count += size
        lines.append(f"def {kind}Table {parameters} : (k : Fin {desc}.size) → BitVec ({desc}.signal k).1\n")
        for index, (expression, _) in enumerate(entries):
            lines.append(f"  | ⟨{index}, _⟩ => by with_unfolding_all exact {expression}\n")
        lines.append(f"  | ⟨k + {size}, h⟩ => False.elim (by change k + {size} < {size} at h; omega)\n")
        lines.append(f"theorem {kind}Table_correct {parameters} (k : Fin {desc}.size) :\n"
                     f"  {kind}Table i s k = circuit.{operation} i s ({desc}.signal k).2 := by\n"
                     f"  match k with\n")
        for index, (_, theorem) in enumerate(entries):
            lines.append(f"  | ⟨{index}, _⟩ => with_unfolding_all exact {theorem} i s\n")
        lines.append(f"  | ⟨k + {size}, h⟩ => exact False.elim (by change k + {size} < {size} at h; omega)\n")
        lines.append(f"def rtl_{operation} {parameters} : Values {typ} :=\n"
                     f"  {desc}.assemble ({kind}Table i s)\n"
                     f"theorem rtl_{operation}_eq {parameters} :\n"
                     f"  (fun {{w}} (p : {typ} w) => rtl_{operation} i s p) = "
                     f"(fun {{w}} (p : {typ} w) => circuit.{operation} i s p) :=\n"
                     f"  Interface.assemble_eq _ _ _ ({kind}Table_correct i s)\n")
    lines.append("""
def rtlComponent : Timed.Component (Values Input) (Values Register) (Values Output) :=
  ⟨rtl_step, rtl_observe⟩

theorem correspondence : Artifact.Correspondence circuit rtlComponent :=
  ⟨rtl_step_eq, rtl_observe_eq⟩

theorem trace_eq (s : Values Register) (inputs : List (Values Input)) :
    rtlComponent.trace s inputs = circuit.component.trace s inputs :=
  correspondence.refinement.trace_eq _ _ rfl inputs

end Pinwheel.TypedArtifact
""")
    write("Proof", "\n".join(lines))
    write("Audit", """import Lean
import Proof
open Lean Elab Command
elab "#audit_typed_artifact" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.TypedArtifact." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty artifact proof audit"
  logInfo m!"Typed artifact audit: {count} declarations, standard axioms only."
#audit_typed_artifact
""")
    return ["Design", "Graphs", "LocalProofs", "Links", "Proof", "Audit"], {
        "local_equalities": len(pairs), "endpoints": endpoint_count,
        "source_nodes": len(source.nodes), "rtl_nodes": len(actual.nodes)}
